#!/usr/bin/env python3
"""Immutable independently native-checked C7 shards, imports, and complete merge.

No producer law table or external PASS is trusted. Snapshot/source/build hashes
are integrity receipts; the mathematical bridge is A's checked-map contract.
"""
from __future__ import annotations

import argparse
import fcntl
import json
from pathlib import Path
import shutil
import sys
import uuid

from common import (HERE, ROOT, SCHEMA, GateError, axiom_names, check_record,
                    checked_source, checked_type, compiler_identity, data_check,
                    data_source, digest, environment, file_record, imports, lean_build,
                    load, module_path, native_axioms, put, require, run, sha,
                    snapshot_read, source_closure, source_pin, spec, utc, write_module)


def snapshot_payload(snap):
    keys = ["schema", "source_pin", "source_pin_id", "harness"]
    if "adopted_snapshots" in snap:
        keys.append("adopted_snapshots")
    return {key: snap[key] for key in keys}


def accepted_snapshots(snap):
    return {snap["snapshot_id"]} | {rec["snapshot_id"] for rec in snap.get("adopted_snapshots", [])}


def snapshot(project, output, adopt=()):
    project, output = Path(project).resolve(), Path(output).resolve()
    require(not output.exists(), "SNAPSHOT_ALREADY_EXISTS")
    output.parent.mkdir(parents=True, exist_ok=True)
    env, prefix = environment(project)
    build = run(["lake", "--no-cache", "build", "+SitePerc.Checker.ShardedDefs:o"],
                cwd=project, env=env, log=output.parent/"snapshot_build.log", timeout=120)
    pin = source_pin(project)
    snap = {"schema": SCHEMA, "source_pin": pin, "source_pin_id": digest(pin),
            "harness": {name: sha(HERE/name) for name in ("common.py", "shards.py", "Producer.lean")},
            "compiler_at_snapshot": compiler_identity(prefix), "build": build, "utc": utc()}
    adopted = {}
    for old_path in adopt:
        old = snapshot_read(old_path, project)
        require(old["snapshot_id"] == digest(snapshot_payload(old)), "ADOPTED_SNAPSHOT_ID_MISMATCH")
        require(old["source_pin_id"] == snap["source_pin_id"], "CANNOT_ADOPT_DIFFERENT_RUNTIME_PIN")
        adopted[old["snapshot_id"]] = {"snapshot_id": old["snapshot_id"], "snapshot_file_sha256": sha(old_path),
                                        "harness": old["harness"], "reason": "explicit same-runtime transport/compiler-driver adoption; no C7 reevaluation"}
        for rec in old.get("adopted_snapshots", []):
            adopted[rec["snapshot_id"]] = rec
    if adopted:
        snap["adopted_snapshots"] = [adopted[key] for key in sorted(adopted)]
    snap["snapshot_id"] = digest(snapshot_payload(snap))
    put(output, snap)
    for name in snap["harness"]:
        dest = output.parent/"frozen-harness"/name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(HERE/name, dest)
    for rec in pin["files"]:
        dest = output.parent/"frozen-source"/rec["path"]
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(project/rec["path"], dest)
    return snap


def check_snapshot(path, project):
    snap = snapshot_read(path, project)
    require(snap["snapshot_id"] == digest(snapshot_payload(snap)),
            "SNAPSHOT_ID_MISMATCH")
    require(all(sha(HERE/name) == value for name, value in snap["harness"].items()), "HARNESS_HASH_MISMATCH")
    return snap


def runtime_objects(project):
    """Only the actual runtime import closure; never build the entire library."""
    seen = set()
    def visit(module):
        if module in seen or module.split(".")[0] in ("Init", "Lean", "Std"):
            return
        if module.startswith("SitePerc."):
            base = project
        elif module.startswith("Batteries.") or module == "Batteries":
            base = project/".lake/packages/batteries"
        else:
            raise GateError("UNEXPECTED_RUNTIME_IMPORT:"+module)
        path = base.joinpath(*module.split(".")).with_suffix(".lean")
        require(path.is_file(), "MISSING_RUNTIME_SOURCE:"+str(path))
        seen.add(module)
        for child in imports(path):
            visit(child)
    visit("SitePerc.Checker.ShardedDefs")
    result = []
    for module in sorted(seen):
        base = project if module.startswith("SitePerc.") else project/".lake/packages/batteries"
        path = base.joinpath(".lake/build/ir", *module.split(".")).with_suffix(".c.o.export")
        require(path.is_file(), "MISSING_RUNTIME_NATIVE_OBJECT:"+str(path))
        result.append(path)
    return result


def prepare(project, snap, out, env, prefix, timeout):
    kit = Path(out).resolve()/"kit"
    kit.mkdir(parents=True, exist_ok=True)
    identity = compiler_identity(prefix)
    with (kit/"lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        receipt_path = kit/"KIT.json"
        if receipt_path.is_file():
            receipt = load(receipt_path)
            require(receipt["snapshot_id"] in accepted_snapshots(snap) and receipt["compiler"] == identity,
                    "KIT_PIN_MISMATCH")
            for rec in receipt["artifacts"]:
                check_record(kit, rec)
            return kit/"producer"
        src = kit/"src"
        src.mkdir(exist_ok=True)
        shutil.copy2(HERE/"Producer.lean", src/"Producer.lean")
        compiled, _ = lean_build(project, env, prefix, src, "Producer", kit/"build",
                                  kit/"compile.log", timeout=timeout, c=True)
        objects = runtime_objects(project)
        linked = run([str(prefix/"bin/leanc"), "-O3", "-o", str(kit/"producer"),
                      str(kit/"build/Producer.c"), *map(str, objects)], cwd=project,
                     env=env, log=kit/"link.log", timeout=timeout)
        artifacts = [file_record(path, kit) for path in sorted(kit.rglob("*"))
                     if path.is_file() and path.name not in ("lock", "KIT.json")]
        receipt = {"schema": SCHEMA, "snapshot_id": snap["snapshot_id"], "compiler": identity,
                   "compile": compiled, "link": linked, "runtime_objects":
                   [{"path": str(path.relative_to(project)), "sha256": sha(path)} for path in objects],
                   "artifacts": artifacts, "utc": utc()}
        put(receipt_path, receipt)
        return kit/"producer"


def verify_piece(path, snap):
    path = Path(path).resolve()
    manifest_path = path/"manifest.json"
    require(manifest_path.is_file(), "MISSING_SHARD_MANIFEST:"+str(path))
    manifest = load(manifest_path)
    require(manifest["schema"] == SCHEMA and manifest["state"] == "VERIFIED", "NOT_VERIFIED_SHARD")
    require(manifest["source_pin_id"] == snap["source_pin_id"] and manifest["snapshot_id"] in accepted_snapshots(snap),
            "SHARD_SOURCE_PIN_MISMATCH:"+str(path))
    expected_digest = digest({key: val for key, val in manifest.items() if key != "manifest_sha256"})
    require(manifest["manifest_sha256"] == expected_digest, "MANIFEST_SELF_HASH_MISMATCH")
    region = manifest["region"]
    require(region == spec(*(region[key] for key in ("m", "shards", "mode", "index"))), "REGION_BINDING_MISMATCH")
    listed = {rec["path"] for rec in manifest["files"]}
    for rec in manifest["files"]:
        check_record(path, rec)
    data = load(path/"data.json")
    data_check(data, region)
    data_module, check_module = manifest["data_module"], manifest["check_module"]
    expected_module = ("SPC7.P"+snap["source_pin_id"][:16]+".M"+str(region["m"])+".S"+str(region["shards"])
                       +".Mode"+str(region["mode"])+".I"+str(region["index"])+".H"+sha(path/"data.json")[:16])
    require(data_module == expected_module+".Data" and check_module == expected_module+".Check", "MODULE_ID_MISMATCH")
    require(module_path(path/"src", data_module).read_text() == data_source(data_module, data), "LITERAL_DATA_SOURCE_MISMATCH")
    require(module_path(path/"src", check_module).read_text() == checked_source(check_module, data_module, region),
            "CHECKED_THEOREM_SOURCE_MISMATCH")
    statement = checked_type(data_module, region)
    require(manifest["theorem"] == check_module+".checked" and manifest["theorem_type"] == statement and
            manifest["theorem_type_sha256"] == digest(statement), "THEOREM_TYPE_BINDING_MISMATCH")
    for module in (data_module, check_module):
        stem = "build/" + module.replace(".", "/")
        require(stem+".olean" in listed, "MISSING_OLEAN_IN_MANIFEST:"+module)
    for name in ("data.json", "logs/data_compile.log", "logs/check_compile.log"):
        require(name in listed, "MISSING_REQUIRED_BINDING:"+name)
    names = axiom_names(path/"logs/check_compile.log", manifest["theorem"])
    natives = native_axioms(names)
    require(len(natives) == 1 and names == manifest["axioms"], "BAD_NATIVE_AXIOM_BINDING")
    return manifest


def audit_import(project, env, prefix, piece, manifest, output, timeout):
    output = Path(output)
    module = "ImportAudit"+uuid.uuid4().hex
    text = ("import "+manifest["check_module"]+"\n"
            + "example : "+manifest["theorem_type"]+" := "+manifest["theorem"]+"\n"
            + "set_option pp.fullNames true in\n#print axioms "+manifest["theorem"]+"\n")
    write_module(output/"src", module, text)
    penv = dict(env, LEAN_PATH=str(Path(piece)/"build")+":"+env["LEAN_PATH"])
    result, _ = lean_build(project, penv, prefix, output/"src", module, output/"build",
                           output/"import.log", timeout=timeout)
    names = axiom_names(output/"import.log", manifest["theorem"])
    require(names == manifest["axioms"], "IMPORTED_AXIOMS_MISMATCH")
    result.update({"C7_evaluations": 0, "native_decide_invocations": 0,
                   "imported_theorem": manifest["theorem"], "manifest_sha256": manifest["manifest_sha256"]})
    put(output/"IMPORT.json", result)
    return result


def produce(project, snapshot_path, out, m, shards, mode, index, *, timeout=120, snap=None, context=None):
    project, out = Path(project).resolve(), Path(out).resolve()
    snap = check_snapshot(snapshot_path, project) if snap is None else snap
    env, prefix = environment(project) if context is None else context
    region = spec(m, shards, mode, index)
    name = f"m{m}_s{shards}_mode{mode}_i{index}"
    final = out/"pieces"/name
    if final.exists():
        manifest = verify_piece(final, snap)
        imported = audit_import(project, env, prefix, final, manifest, out/"reuses"/(name+"_"+uuid.uuid4().hex), timeout)
        return {"action": "REUSED", "piece": str(final), "manifest_sha256": manifest["manifest_sha256"],
                "producer_evaluations": 0, "native_checker_evaluations": 0, "shard_compilations": 0, "import": imported}
    producer = prepare(project, snap, out, env, prefix, timeout)
    staging = out/"incomplete"/(name+"_"+uuid.uuid4().hex)
    staging.mkdir(parents=True)
    produced = run([str(producer), str(m), str(mode), str(shards), str(index), str(staging/"raw.json")],
                   cwd=project, env=env, log=staging/"logs/producer.log", timeout=timeout)
    data = load(staging/"raw.json")
    data_check(data, region)
    put(staging/"data.json", data)
    (staging/"raw.json").unlink()
    base = ("SPC7.P"+snap["source_pin_id"][:16]+f".M{m}.S{shards}.Mode{mode}.I{index}.H"+sha(staging/"data.json")[:16])
    data_module, check_module = base+".Data", base+".Check"
    write_module(staging/"src", data_module, data_source(data_module, data))
    write_module(staging/"src", check_module, checked_source(check_module, data_module, region))
    data_compile, _ = lean_build(project, env, prefix, staging/"src", data_module, staging/"build",
                                 staging/"logs/data_compile.log", timeout=timeout, c=True)
    checked_compile, _ = lean_build(project, env, prefix, staging/"src", check_module, staging/"build",
                                    staging/"logs/check_compile.log", timeout=timeout, c=True)
    names = axiom_names(staging/"logs/check_compile.log", check_module+".checked")
    natives = native_axioms(names)
    require(len(natives) == 1, "EXPECTED_ONE_NATIVE_AXIOM")
    theorem_type = checked_type(data_module, region)
    manifest = {"schema": SCHEMA, "state": "VERIFIED", "source_pin_id": snap["source_pin_id"],
                "snapshot_id": snap["snapshot_id"], "region": region, "data_module": data_module,
                "check_module": check_module, "theorem": check_module+".checked", "theorem_type": theorem_type,
                "theorem_type_sha256": digest(theorem_type), "axioms": names,
                "trust": "standard-three plus the one disclosed native_decide axiom; not a kernel-only proof",
                "compiler": compiler_identity(prefix), "producer": produced,
                "data_compile": data_compile, "native_check_compile": checked_compile,
                "producer_kit_manifest_sha256": sha(out/"kit/KIT.json"), "utc": utc(),
                "files": [file_record(path, staging) for path in sorted(staging.rglob("*")) if path.is_file()]}
    manifest["manifest_sha256"] = digest(manifest)
    put(staging/"manifest.json", manifest)
    verify_piece(staging, snap)
    # A fresh import, not a second native evaluation, is the completion gate.
    audit = audit_import(project, env, prefix, staging, manifest, out/"imports"/(name+"_"+uuid.uuid4().hex), timeout)
    final.parent.mkdir(parents=True, exist_ok=True)
    require(not final.exists(), "CONCURRENT_SAME_SHARD_OWNER")
    staging.rename(final)
    return {"action": "CREATED", "piece": str(final), "manifest_sha256": manifest["manifest_sha256"],
            "producer_evaluations": 1, "native_checker_evaluations": 1, "shard_compilations": 2,
            "rows": len(data["rows"]), "import": audit}


def inventory(paths, snap, m, shards):
    selected = {}
    for directory in paths:
        directory = Path(directory)
        manifests = sorted(directory.glob("*/manifest.json"))
        require(bool(manifests), "NO_SHARD_MANIFESTS:"+str(directory))
        for manifest_path in manifests:
            manifest = verify_piece(manifest_path.parent, snap)
            region = manifest["region"]
            require(region["m"] == m and region["shards"] == shards, "MERGE_PARTITION_MISMATCH")
            key = (region["mode"], region["index"])
            require(key not in selected, "DUPLICATE_OR_OVERLAPPING_SHARD:"+repr(key))
            selected[key] = (manifest_path.parent, manifest)
    expected = {(mode, index) for mode in range(3) for index in range(max(1, shards))}
    missing = sorted(expected-set(selected))
    require(not missing, "MISSING_SHARDS:"+repr(missing[:50])+f" total={len(missing)}")
    return selected


def merge(project, snapshot_path, paths, m, shards, out, *, timeout=120, soundness=True):
    project, out = Path(project).resolve(), Path(out).resolve()
    snap = check_snapshot(snapshot_path, project)
    selected = inventory(paths, snap, m, shards)
    require(not (out/"MERGE.json").exists(), "MERGE_ALREADY_EXISTS")
    env, prefix = environment(project)
    # Lean resolves one package prefix from one search root. Stage all SPC7
    # shards beside the SPC7 merge module, not under a shadowed second root.
    import_root = out/"build"
    for path, manifest in selected.values():
        for rec in manifest["files"]:
            if rec["path"].startswith("build/"):
                dest = import_root/rec["path"][6:]
                dest.parent.mkdir(parents=True, exist_ok=True)
                if dest.exists():
                    require(sha(dest) == rec["sha256"], "IMPORTED_MODULE_CONFLICT")
                else:
                    shutil.copy2(path/rec["path"], dest)
    inputs = [{"region": list(key), "manifest_sha256": selected[key][1]["manifest_sha256"]} for key in sorted(selected)]
    module = "SPC7.Merge.H"+digest(inputs)[:20]
    body = "".join("import "+selected[key][1]["check_module"]+"\n" for key in sorted(selected))
    body += "import Mathlib.Tactic.FinCases\n"
    if soundness:
        require((project/"SitePerc/Checker/ShardedSoundness.lean").is_file(), "MISSING_A_SOUNDNESS")
        body += "import SitePerc.Checker.ShardedSoundness\n"
    body += "namespace "+module+"\nopen SitePerc.Checker\n"
    body += f"def data : ShardFamily {shards} := fun mode index =>\n  match mode.val, index.val with\n"
    for key in sorted(selected):
        body += f"  | {key[0]}, {key[1]} => "+selected[key][1]["data_module"]+".stored\n"
    body += "  | _, _ => {}\n"
    body += f"theorem receipts : ShardReceipts {m} {shards} data := by\n  intro mode index\n  fin_cases mode <;> fin_cases index\n"
    for key in sorted(selected):
        body += "  · exact "+selected[key][1]["theorem"]+"\n"
    if soundness:
        body += (f"theorem exact_laws : ExactRegionalLaws {m} (shardedRegionalLaws {m} {shards} data) :=\n"
                 + f"  shardedRegionalLaws_exact {m} (by decide) {shards} data receipts\n")
    body += "set_option pp.fullNames true in\n#print axioms receipts\n"
    if soundness:
        body += "set_option pp.fullNames true in\n#print axioms exact_laws\n"
    body += "end "+module+"\n"
    write_module(out/"src", module, body)
    penv = dict(env, LEAN_PATH=str(import_root)+":"+env["LEAN_PATH"])
    built, _ = lean_build(project, penv, prefix, out/"src", module, out/"build", out/"merge.log", timeout=timeout, c=True)
    names = axiom_names(out/"merge.log", module+".receipts")
    expected_native = sorted(name for _, manifest in selected.values() for name in native_axioms(manifest["axioms"]))
    require(sorted(native_axioms(names)) == expected_native, "MERGE_NATIVE_CLOSURE_MISMATCH")
    exact_names = axiom_names(out/"merge.log", module+".exact_laws") if soundness else None
    if soundness:
        require(sorted(native_axioms(exact_names)) == expected_native, "EXACT_LAWS_NATIVE_CLOSURE_MISMATCH")
    result = {"schema": SCHEMA, "state": "COMPLETE_EXACT_LAWS" if soundness else "RECEIPTS_ONLY",
              "m": m, "shards": shards, "coverage": "all three modes, every clipped boundary shard exactly once",
              "piece_count": len(selected), "source_pin_id": snap["source_pin_id"], "snapshot_id": snap["snapshot_id"],
              "inputs": inputs, "module": module, "receipts_theorem": module+".receipts",
              "exact_laws_theorem": module+".exact_laws" if soundness else None,
              "soundness_source_closure": source_closure(project, ["SitePerc.Checker.ShardedSoundness"]) if soundness else [],
              "axioms": names, "exact_laws_axioms": exact_names, "native_axiom_count": len(expected_native),
              "C7_evaluations": 0, "native_decide_invocations": 0, "build": built, "utc": utc(),
              "files": [file_record(path, out) for path in sorted(out.rglob("*")) if path.is_file()]}
    result["manifest_sha256"] = digest(result)
    put(out/"MERGE.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=ROOT)
    sub = parser.add_subparsers(dest="command", required=True)
    sp = sub.add_parser("snapshot"); sp.add_argument("--out", type=Path, required=True)
    sp.add_argument("--adopt", nargs="*", type=Path, default=[], help="explicitly reuse same-runtime snapshot pieces across driver-only fixes")
    for command in ("prepare", "produce", "validate", "merge"):
        p = sub.add_parser(command)
        p.add_argument("--snapshot", type=Path, required=True)
        p.add_argument("--timeout", type=int, default=120)
        if command != "validate":
            p.add_argument("--out", type=Path, required=True)
        if command in ("produce", "merge"):
            p.add_argument("--m", type=int, required=True)
            p.add_argument("--shards", type=int, required=True)
        if command == "produce":
            p.add_argument("--mode", type=int, required=True)
            p.add_argument("--index", type=int, required=True)
        elif command == "validate":
            p.add_argument("--piece", type=Path, required=True)
            p.add_argument("--import-audit", type=Path)
        elif command == "merge":
            p.add_argument("--pieces", nargs="+", type=Path, required=True)
            p.add_argument("--receipts-only", action="store_true")
    a = parser.parse_args()
    try:
        if a.command == "snapshot":
            answer = snapshot(a.project, a.out, a.adopt)
        elif a.command == "prepare":
            snap = check_snapshot(a.snapshot, a.project)
            env, prefix = environment(a.project)
            answer = {"producer": str(prepare(a.project, snap, a.out, env, prefix, a.timeout))}
        elif a.command == "produce":
            answer = produce(a.project, a.snapshot, a.out, a.m, a.shards, a.mode, a.index, timeout=a.timeout)
        elif a.command == "validate":
            snap = check_snapshot(a.snapshot, a.project)
            answer = verify_piece(a.piece, snap)
            if a.import_audit:
                env, prefix = environment(a.project)
                answer = audit_import(a.project, env, prefix, a.piece, answer, a.import_audit, a.timeout)
        else:
            answer = merge(a.project, a.snapshot, a.pieces, a.m, a.shards, a.out,
                           timeout=a.timeout, soundness=not a.receipts_only)
        print(json.dumps(answer, indent=2))
    except (GateError, KeyError, ValueError, FileNotFoundError) as exc:
        print(json.dumps({"state": "REJECTED", "reason": str(exc)}), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
