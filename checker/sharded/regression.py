#!/usr/bin/env python3
"""Small real C7 production/restart/distribution/negative regressions."""
from __future__ import annotations

import argparse
from copy import deepcopy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import uuid

from common import (ROOT, GateError, axiom_names, checked_source, compiler_identity,
                    data_source, environment, file_record, lean_build,
                    load, native_axioms, put, require, sha, utc, write_module)
from shards import (check_snapshot, inventory, merge, produce,
                    verify_piece)


def worker(base, m, index):
    return base/("worker"+str(index) if m == 2 else "m4worker"+str(index))


def production(project, snapshot_path, base, m):
    snap = check_snapshot(snapshot_path, project)
    context = environment(project)
    results = []
    for mode in range(3):
        for index in range(2):
            result = produce(project, snapshot_path, worker(base, m, index), m, 2,
                             mode, index, timeout=120, snap=snap, context=context)
            results.append(result)
            put(base/f"PRODUCTION_m{m}.json", {"utc": utc(), "m": m, "pieces": results})
    check_snapshot(snapshot_path, project)
    return {"m": m, "pieces": len(results), "created": sum(r["action"] == "CREATED" for r in results),
            "reused": sum(r["action"] == "REUSED" for r in results),
            "all_native_checked": all(verify_piece(r["piece"], snap)["state"] == "VERIFIED" for r in results)}


def restarts(project, snapshot_path, base):
    snap = check_snapshot(snapshot_path, project)
    results = []
    for m in (2, 4):
        out = worker(base, m, 0)
        piece = out/"pieces"/f"m{m}_s2_mode0_i0"
        manifest = verify_piece(piece, snap)
        before = {rec["path"]: (sha(piece/rec["path"]), (piece/rec["path"]).stat().st_mtime_ns)
                  for rec in manifest["files"]}
        argv = [sys.executable, str(Path(__file__).with_name("shards.py")), "--project", str(project),
                "produce", "--snapshot", str(snapshot_path), "--out", str(out), "--m", str(m),
                "--shards", "2", "--mode", "0", "--index", "0", "--timeout", "60"]
        raw = subprocess.check_output(argv, text=True)
        result = json.loads(raw)
        after = {rec["path"]: (sha(piece/rec["path"]), (piece/rec["path"]).stat().st_mtime_ns)
                 for rec in manifest["files"]}
        require(result["action"] == "REUSED" and before == after and
                result["producer_evaluations"] == result["native_checker_evaluations"] == result["shard_compilations"] == 0,
                "RESTART_RECOMPUTED_OR_CHANGED_ARTIFACTS")
        results.append({"m": m, "fresh_process": True, "piece_bytes_and_mtimes_unchanged": before == after, **result})
    receipt = {"utc": utc(), "PASS": True, "cases": results}
    put(base/"RESTART.json", receipt)
    return {"PASS": True, "fresh_processes": len(results), "C7_recomputations": 0}


def merges(project, snapshot_path, base, *, soundness):
    results = []
    for m in (2, 4):
        output = base/(f"merged_m{m}" if soundness else f"receipts_m{m}")
        result = merge(project, snapshot_path, [worker(base, m, index)/"pieces" for index in range(2)],
                       m, 2, output, timeout=90, soundness=soundness)
        results.append({"m": m, "state": result["state"], "piece_count": result["piece_count"],
                        "C7_evaluations": result["C7_evaluations"],
                        "native_axiom_count": result["native_axiom_count"], "path": str(output/"MERGE.json")})
    put(base/("MERGES.json" if soundness else "RECEIPT_MERGES.json"), {"utc": utc(), "cases": results})
    return results


def negatives(project, snapshot_path, base):
    snap = check_snapshot(snapshot_path, project)
    env, prefix = environment(project)
    source = worker(base, 2, 0)/"pieces/m2_s2_mode0_i0"
    manifest = verify_piece(source, snap)
    root = base/"negative"
    root.mkdir(exist_ok=True)
    results = []
    def reject(label, fn, expected):
        try:
            fn()
        except GateError as exc:
            require(expected in str(exc), "WRONG_NEGATIVE_REASON:"+label+":"+str(exc))
            results.append({"case": label, "rejected": True, "reason": str(exc)})
        else:
            raise GateError("NEGATIVE_ACCEPTED:"+label)
    reject("missing-partition-piece", lambda: inventory([worker(base, 2, 0)/"pieces"], snap, 2, 2), "MISSING_SHARDS")
    reject("duplicate-overlapping-piece", lambda: inventory([worker(base, 2, 0)/"pieces"]*2, snap, 2, 2), "DUPLICATE_OR_OVERLAPPING")
    def copied(label):
        dest = root/label
        require(not dest.exists(), "NEGATIVE_FIXTURE_ALREADY_EXISTS:"+label)
        shutil.copytree(source, dest)
        return dest
    dest = copied("missing-data"); (dest/"data.json").unlink()
    reject("missing-data", lambda: verify_piece(dest, snap), "MISSING_ARTIFACT")
    dest = copied("changed-data"); data = load(dest/"data.json"); data["rows"][0][1][0] += 1; put(dest/"data.json", data)
    reject("changed-data", lambda: verify_piece(dest, snap), "ARTIFACT_HASH_MISMATCH")
    dest = copied("changed-olean")
    artifact = next(rec for rec in manifest["files"] if rec["path"].endswith("Check.olean"))
    path = dest/artifact["path"]; raw = bytearray(path.read_bytes()); raw[-1] ^= 1; path.write_bytes(raw)
    reject("changed-olean", lambda: verify_piece(dest, snap), "ARTIFACT_HASH_MISMATCH")
    dest = copied("changed-theorem")
    artifact = next(rec for rec in manifest["files"] if rec["path"].endswith("Check.lean"))
    path = dest/artifact["path"]; path.write_text(path.read_text()+"\n-- mutation\n")
    reject("changed-theorem", lambda: verify_piece(dest, snap), "ARTIFACT_HASH_MISMATCH")
    other = deepcopy(snap); other["source_pin_id"] = "0"*64
    reject("different-source-pin", lambda: verify_piece(source, other), "SHARD_SOURCE_PIN_MISMATCH")
    other = deepcopy(snap); other["snapshot_id"] = "1"*64; other.pop("adopted_snapshots", None)
    reject("different-generator-snapshot", lambda: verify_piece(source, other), "SHARD_SOURCE_PIN_MISMATCH")
    # Isolated project clone: never alter the canonical safe source.
    clone = root/"source-clone"
    clone.mkdir()
    for rec in snap["source_pin"]["files"]:
        path = clone/rec["path"]; path.parent.mkdir(parents=True, exist_ok=True); shutil.copy2(project/rec["path"], path)
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        shutil.copy2(project/name, clone/name)
    (clone/".lake").mkdir(); (clone/".lake/packages").symlink_to(project/".lake/packages", target_is_directory=True)
    path = clone/"SitePerc/Checker/ShardedDefs.lean"; path.write_text(path.read_text()+"\n-- isolated source-pin mutation\n")
    reject("actual-source-byte-drift", lambda: check_snapshot(snapshot_path, clone), "SOURCE_PIN_MISMATCH")
    # Rehashing a wrong table cannot make the independent actual native checker pass.
    for label, change in (("wrong-coefficient", lambda rows: rows[0][1].__setitem__(0, rows[0][1][0]+1)),
                          ("omitted-support", lambda rows: rows.pop(0))):
        case = root/label
        data = load(source/"data.json"); change(data["rows"])
        data_module = "Negative.H"+uuid.uuid4().hex+".Data"
        check_module = data_module[:-4]+"Check"
        write_module(case/"src", data_module, data_source(data_module, data))
        write_module(case/"src", check_module, checked_source(check_module, data_module, manifest["region"]))
        lean_build(project, env, prefix, case/"src", data_module, case/"build", case/"data.log", timeout=60)
        reject(label, lambda: lean_build(project, env, prefix, case/"src", check_module, case/"build", case/"check.log", timeout=60), "PHASE_FAILED")
        require("is false" in (case/"check.log").read_text(), "NATIVE_REJECT_NOT_FALSE")
    check_snapshot(snapshot_path, project)
    receipt = {"utc": utc(), "PASS": True, "all_rejected": True, "cases": results,
               "cases_count": len(results), "safe_source_unchanged": True}
    put(base/"NEGATIVE.json", receipt)
    return {"PASS": True, "cases": len(results), "all_rejected": True}


def flows(project, base, sizes=(2, 4)):
    env, prefix = environment(project)
    # Existing lossless pure data only; no direct-path theorem or producer laws are imported.
    data_root = project.parent/"lean-data/g/direct_regression"
    require((data_root/"build/SitePercDirectRegressionData.olean").is_file(), "MISSING_SMALL_PURE_FLOW_DATA")
    results = []
    for m in sizes:
        merged = base/f"merged_m{m}"
        info = load(merged/"MERGE.json")
        require(info["state"] == "COMPLETE_EXACT_LAWS", "FLOW_REQUIRES_EXACT_MERGE")
        module = "SPC7Flow.M"+str(m)+".H"+info["manifest_sha256"][:16]
        if m == 2:
            one, two = "⟨1,1,2,0,586668,1000000,2^100⟩", "⟨2,586668,1000000,0,679493,1000000,2^100⟩"
        else:
            one, two = "⟨1,1,2,0,5823347,10000000,2^100⟩", "⟨2,5823347,10000000,0,65185,100000,2^100⟩"
        text = ("import "+info["module"]+"\nimport SitePercDirectRegressionData\nimport Lean.Elab.Tactic.Decide\n"
                + "namespace "+module+"\nopen SitePerc.Checker SitePercDirectRegressionData\n"
                + f"def flowPass : Bool := shardedRegionalPass {m} 2 {info['module']}.data {one} {two}\n"
                + f"  m{m}Stage1Nodes m{m}Stage1Edges m{m}Stage2Nodes m{m}Stage2Edges\n"
                + "theorem flow_checked : flowPass = true := by native_decide\n"
                + "set_option pp.fullNames true in\n#print axioms flow_checked\nend "+module+"\n")
        output = base/f"flow_m{m}"
        write_module(output/"src", module, text)
        penv = dict(env, LEAN_PATH=":".join(map(str, [merged/"build", merged/"imports", data_root/"build"]))+":"+env["LEAN_PATH"])
        built, _ = lean_build(project, penv, prefix, output/"src", module, output/"build", output/"flow.log", timeout=90, c=True)
        names = axiom_names(output/"flow.log", module+".flow_checked")
        require(len(native_axioms(names)) == 1, "EXPECTED_ONE_SEPARATE_FLOW_NATIVE_AXIOM")
        result = {"m": m, "PASS": True, "theorem": module+".flow_checked", "axioms": names,
                  "C7_evaluations": 0, "flow_native_checks": 1, "merged_manifest_sha256": info["manifest_sha256"],
                  "pure_flow_source_files": [file_record(path, data_root/"src") for path in sorted((data_root/"src").rglob("*.lean"))],
                  "compiler": compiler_identity(prefix), "build": built,
                  "files": [file_record(path, output) for path in sorted(output.rglob("*")) if path.is_file()]}
        put(output/"FLOW.json", result)
        results.append({"m": m, "PASS": True, "C7_evaluations": 0, "flow_native_checks": 1})
    put(base/"FLOWS.json", {"utc": utc(), "cases": results})
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("production", "restart", "merge", "receipt-merge", "negative", "flow"))
    parser.add_argument("--project", type=Path, default=ROOT)
    parser.add_argument("--snapshot", type=Path, required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--m", type=int, choices=(2, 4))
    a = parser.parse_args()
    a.project, a.base, a.snapshot = a.project.resolve(), a.base.resolve(), a.snapshot.resolve()
    if a.phase == "production":
        require(a.m is not None, "PRODUCTION_REQUIRES_M")
        result = production(a.project, a.snapshot, a.base, a.m)
    elif a.phase == "restart":
        result = restarts(a.project, a.snapshot, a.base)
    elif a.phase in ("merge", "receipt-merge"):
        result = merges(a.project, a.snapshot, a.base, soundness=a.phase == "merge")
    elif a.phase == "negative":
        result = negatives(a.project, a.snapshot, a.base)
    else:
        result = flows(a.project, a.base, (a.m,) if a.m else (2, 4))
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
