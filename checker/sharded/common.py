"""Shared integrity and bounded Lean execution for restartable C7 pieces.

These gates implement the owner's persisted-piece acceptance, not new policy.
Revisit them only if the source/pin/data/theorem/artifact contract changes.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import subprocess
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SCHEMA = "siteperc-c7-shard-v1"


class GateError(RuntimeError):
    pass


def require(ok, reason):
    if not ok:
        raise GateError(reason)


def canon(obj):
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def digest(obj):
    return hashlib.sha256(canon(obj)).hexdigest()


def sha(path):
    with Path(path).open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


def put(path, obj):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_bytes(canon(obj))
    tmp.replace(path)


def utc():
    return datetime.now(timezone.utc).isoformat()


def file_record(path, base):
    path, base = Path(path), Path(base)
    return {"path": str(path.relative_to(base)), "bytes": path.stat().st_size, "sha256": sha(path)}


def check_record(base, rec):
    path = Path(base) / rec["path"]
    require(path.is_file(), "MISSING_ARTIFACT:" + str(path))
    require(path.stat().st_size == rec["bytes"] and sha(path) == rec["sha256"],
            "ARTIFACT_HASH_MISMATCH:" + str(path))
    return path


def run(argv, *, cwd, log, env=None, timeout=120, cpus=(0,)):
    """Run once with an inherited CPU affinity and a finite per-phase cap."""
    log = Path(log)
    log.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ if env is None else env)
    env["LEAN_NUM_THREADS"] = str(len(cpus))
    command = ["taskset", "-c", ",".join(map(str, cpus)), *map(str, argv)]
    start = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    with log.open("wb") as handle:
        proc = subprocess.Popen(command, cwd=cwd, env=env, stdout=handle,
                                stderr=subprocess.STDOUT, start_new_session=True)
        try:
            rc = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            import signal
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            raise GateError("PHASE_TIMEOUT:" + str(log)) from None
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    result = {"argv": command, "cwd": str(cwd), "rc": rc, "wall_s": time.monotonic()-start,
              "user_s": after.ru_utime-before.ru_utime, "sys_s": after.ru_stime-before.ru_stime,
              "process_children_maxrss_kib_cumulative": after.ru_maxrss,
              "log_sha256": sha(log), "log": str(log), "utc": utc()}
    put(log.with_suffix(log.suffix + ".json"), result)
    require(rc == 0, "PHASE_FAILED:" + str(log))
    return result


def environment(project):
    project = Path(project).resolve()
    raw = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=project, text=True)
    env = dict(os.environ, LEAN_PATH=raw.strip(), LEAN_NUM_THREADS="1")
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], cwd=project, text=True).strip())
    return env, prefix


def imports(path):
    """Source headers only, including the pinned Lean `public import` form."""
    text = Path(path).read_text()
    return re.findall(r"(?m)^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_'.]+)", text)


def source_closure(project, roots):
    project = Path(project)
    seen = {}
    def visit(module):
        if not module.startswith("SitePerc.") or module in seen:
            return
        rel = Path(*module.split(".")).with_suffix(".lean")
        path = project / rel
        require(path.is_file(), "MISSING_SAFE_SOURCE:" + str(rel))
        seen[module] = {"path": str(rel), "sha256": sha(path)}
        for child in imports(path):
            visit(child)
    for module in roots:
        visit(module)
    return [seen[key] for key in sorted(seen)]


def source_pin(project):
    project = Path(project).resolve()
    files = source_closure(project, ["SitePerc.Checker.ShardedDefs"])
    lockfiles = {name: sha(project/name) for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")}
    manifest = load(project/"lake-manifest.json")
    deps = []
    for package in manifest["packages"]:
        path = project/".lake/packages"/package["name"]
        head = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        require(head == package["rev"], "PACKAGE_PIN_MISMATCH:" + package["name"])
        # Exact revisions, and hash every tracked local modification if present.
        modified = subprocess.check_output(["git", "-C", str(path), "diff", "--name-only", "HEAD"], text=True).splitlines()
        edits = {name: sha(path/name) if (path/name).is_file() else "DELETED" for name in modified}
        deps.append({"name": package["name"], "rev": head, "edits": edits})
    githash = subprocess.check_output(["lean", "--githash"], cwd=project, text=True).strip()
    return {"schema": SCHEMA, "files": files, "lockfiles": lockfiles,
            "toolchain": (project/"lean-toolchain").read_text().strip(),
            "lean_git": githash, "dependencies": sorted(deps, key=lambda rec: rec["name"]),
            "producer_source_sha256": sha(HERE/"Producer.lean")}


def snapshot_read(path, project, *, current=True):
    snap = load(path)
    require(snap["source_pin_id"] == digest(snap["source_pin"]), "SNAPSHOT_SELF_HASH_MISMATCH")
    if current:
        require(source_pin(project) == snap["source_pin"], "SOURCE_PIN_MISMATCH")
    return snap


def compiler_identity(prefix):
    return {"architecture": platform.machine(), "lean_binary_sha256": sha(prefix/"bin/lean"),
            "lean_version": subprocess.check_output([str(prefix/"bin/lean"), "--version"], text=True).strip()}


def lean_build(project, env, prefix, source_root, module, build_root, log, *, timeout=120, c=False):
    source_root, build_root = Path(source_root), Path(build_root)
    path = source_root.joinpath(*module.split(".")).with_suffix(".lean")
    output = build_root.joinpath(*module.split("."))
    output.parent.mkdir(parents=True, exist_ok=True)
    penv = dict(env, LEAN_PATH=str(build_root) + ":" + env["LEAN_PATH"])
    argv = [str(prefix/"bin/lean"), "--root="+str(source_root), str(path), "-j1",
            "-DmaxHeartbeats=0", "-DmaxRecDepth=20000",
            "-o", str(output.with_suffix(".olean")), "-i", str(output.with_suffix(".ilean"))]
    if c:
        argv += ["-c", str(output.with_suffix(".c"))]
    result = run(argv, cwd=project, log=log, env=penv, timeout=timeout)
    artifacts = sorted(output.parent.glob(output.name+".*"))
    require(output.with_suffix(".olean").is_file(), "NO_OLEAN:"+module)
    return result, artifacts


def module_path(root, module):
    return Path(root).joinpath(*module.split(".")).with_suffix(".lean")


def write_module(root, module, text):
    path = module_path(root, module)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return path


def axiom_names(log, theorem):
    text = Path(log).read_text()
    marker = re.escape("'" + theorem + "' depends on axioms: ")
    hit = re.search(marker + r"\[([^\]]*)\]", text, re.S)
    if not hit:
        if "'"+theorem+"' does not depend on any axioms" in text:
            return []
        raise GateError("MISSING_AXIOM_AUDIT:" + theorem)
    return [name.strip() for name in hit.group(1).split(",") if name.strip()]


def native_axioms(names):
    bad = [name for name in names if name not in STANDARD_AXIOMS and "._native.native_decide.ax_" not in name]
    require(not bad, "UNEXPECTED_AXIOMS:" + repr(bad))
    return [name for name in names if name not in STANDARD_AXIOMS]


def spec(m, shards, mode, index):
    require(m in (2, 4, 6), "UNSUPPORTED_M")
    require(shards >= 0 and mode in range(3), "INVALID_SHARD_SPEC")
    workers = max(1, shards)
    require(0 <= index < workers, "INVALID_SHARD_INDEX")
    total = 2**(4*m-4)
    width = (total+workers-1)//workers
    start = index*width
    count = min(width, max(0, total-start))
    return {"m": m, "shards": shards, "mode": mode, "index": index,
            "workers": workers, "total": total, "start": start, "count": count, "stride": 1}


def data_check(data, expected):
    require(data["schema"] == 1, "BAD_DATA_SCHEMA")
    require(all(data[key] == expected[key] for key in ("m", "shards", "mode", "index", "start", "count")),
            "DATA_REGION_MISMATCH")
    keys = []
    for key, counts in data["rows"]:
        require(isinstance(key, int) and key >= 0, "BAD_DATA_KEY")
        require(len(counts) == expected["m"]**2+1, "BAD_COUNT_SHAPE")
        require(all(isinstance(n, int) and n >= 0 for n in counts), "BAD_COUNT_VALUE")
        keys.append(key)
    require(keys == sorted(set(keys)), "UNSORTED_OR_DUPLICATE_DATA_KEYS")


def data_source(module, data):
    rows = ["("+str(key)+", #["+",".join(map(str, counts))+"])" for key, counts in data["rows"]]
    header = "import SitePerc.Checker.ShardedDefs\nnamespace "+module+"\n"
    if len(rows) <= 128:
        return (header + "def stored : SitePerc.Checker.CountMap := Std.HashMap.ofList [\n"
                + ",\n".join(rows) + "\n]\nend "+module+"\n")
    # Bounded literal expressions avoid linear elaboration recursion in one
    # enormous list. These blocks contain data only, never a C7 computation.
    blocks = [rows[start:start+128] for start in range(0, len(rows), 128)]
    text = header
    for index, block in enumerate(blocks):
        text += (f"def literalBlock_{index} : List (Nat × Array Nat) := [\n"
                 + ",\n".join(block) + "\n]\n")
    text += ("def stored : SitePerc.Checker.CountMap := Std.HashMap.ofList (["
             + ",".join(f"literalBlock_{index}" for index in range(len(blocks)))
             + "].flatten)\nend "+module+"\n")
    return text


def checked_type(data_module, region):
    return ("SitePerc.Checker.regionalShardPass " + " ".join(str(region[key]) for key in ("m", "mode", "shards", "index"))
            + " " + data_module + ".stored = true")


def checked_source(module, data_module, region):
    return ("import "+data_module+"\nimport Lean.Elab.Tactic.Decide\nnamespace "+module+"\n"
            + "theorem checked : "+checked_type(data_module, region)+" := by native_decide\n"
            + "set_option pp.fullNames true in\n#print axioms checked\nend "+module+"\n")
