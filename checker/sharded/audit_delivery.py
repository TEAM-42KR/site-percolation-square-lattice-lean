#!/usr/bin/env python3
"""Collect the already-completed bounded gates; never run C7 during delivery."""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from common import (HERE, ROOT, STANDARD_AXIOMS, check_record, digest, file_record,
                    load, native_axioms, put, require, sha, utc)
from shards import check_snapshot, verify_piece


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--project", type=Path, default=ROOT)
    ap.add_argument("--base", type=Path, required=True)
    ap.add_argument("--snapshot", type=Path, required=True)
    a = ap.parse_args()
    project, base = a.project.resolve(), a.base.resolve()
    root = project/"logs/L2/B"
    snap = check_snapshot(a.snapshot, project)
    paths = sorted((base/"worker0/pieces").glob("*/manifest.json")) + sorted((base/"worker1/pieces").glob("*/manifest.json"))
    require(len(paths) == 6, "EXPECTED_SIX_M2_PIECES")
    pieces = [verify_piece(path.parent, snap) for path in paths]
    m4path = base/"m4worker0/pieces/m4_s2_mode0_i0"
    m4 = verify_piece(m4path, snap)
    pieces.append(m4)
    merged = load(base/"merged_m2/MERGE.json")
    require(merged["manifest_sha256"] == digest({key: value for key, value in merged.items() if key != "manifest_sha256"}),
            "MERGE_MANIFEST_HASH_MISMATCH")
    for rec in merged["files"]:
        check_record(base/"merged_m2", rec)
    for rec in merged["soundness_source_closure"]:
        require(sha(project/rec["path"]) == rec["sha256"], "SOUNDNESS_SOURCE_DRIFT")
    require(merged["state"] == "COMPLETE_EXACT_LAWS" and merged["piece_count"] == 6 and
            merged["C7_evaluations"] == merged["native_decide_invocations"] == 0, "BAD_M2_MERGE")
    restart = load(base/"RESTART.json")
    require(restart["PASS"] and len(restart["cases"]) == 2 and
            all(rec["producer_evaluations"] == rec["native_checker_evaluations"] == rec["shard_compilations"] == 0 and
                rec["piece_bytes_and_mtimes_unchanged"] for rec in restart["cases"]), "BAD_RESTART")
    negative = load(base/"NEGATIVE.json")
    require(negative["PASS"] and negative["cases_count"] == 11 and all(rec["rejected"] for rec in negative["cases"]), "BAD_NEGATIVES")
    flow = load(base/"flow_m2/FLOW.json")
    require(flow["PASS"] and flow["C7_evaluations"] == 0, "BAD_M2_FLOW")
    for rec in flow["files"]:
        check_record(base/"flow_m2", rec)
    generic = load(project/"logs/L2/A/AXIOMS.json")
    require(generic["gate"] == "PASS", "A_STANDARD_AXIOM_GATE_NOT_PASS")
    # Keep the original source/pin and every explicitly adopted generator identity.
    sources = {"runtime_source_pin_id": snap["source_pin_id"], "selected_snapshot": file_record(a.snapshot.resolve(), project),
               "runtime_sources": snap["source_pin"]["files"], "lockfiles": snap["source_pin"]["lockfiles"],
               "toolchain": snap["source_pin"]["toolchain"], "lean_git": snap["source_pin"]["lean_git"],
               "dependencies": snap["source_pin"]["dependencies"],
               "harness": snap["harness"], "adopted_snapshots": snap.get("adopted_snapshots", []),
               "B_source_files": [file_record(path, project) for path in sorted(HERE.iterdir()) if path.is_file()],
               "A_soundness_sources": merged["soundness_source_closure"]}
    put(root/"SOURCE_HASHES.json", sources)
    axioms = {"standard_allowed": sorted(STANDARD_AXIOMS), "generic_A": file_record(project/"logs/L2/A/AXIOMS.json", project),
              "concrete_pieces": [{"theorem": rec["theorem"], "axioms": rec["axioms"],
                                   "native_axiom_count": len(native_axioms(rec["axioms"]))} for rec in pieces],
              "m2_merge": {"theorem": merged["exact_laws_theorem"], "axioms": merged["exact_laws_axioms"]},
              "m2_flow": {"theorem": flow["theorem"], "axioms": flow["axioms"]},
              "native_is_not_kernel_only": True}
    put(root/"AXIOMS.json", axioms)
    matrix = {"m2_complete_six_pieces": True, "m2_complete_exact_laws_merge": True,
              "m2_stored_only_two_flow_native_check": True, "m4_one_large_piece_native_checked": True,
              "fresh_process_restart_and_same_runtime_adoption": True, "persisted_artifact_bytes_and_mtimes_unchanged": True,
              "all_eleven_negatives_rejected": True, "exact_source_pin_data_theorem_artifact_bindings": True,
              "A_generic_standard_three_separate_from_concrete_native": True}
    regression = {"utc": utc(), "matrix": matrix, "m2": {"pieces": 6, "partition_shards": 2,
                  "mode_count": 3, "merge_C7_calls": 0, "merge_native_decide_calls": 0, "flow_C7_calls": 0},
                  "m4": {"completed_pieces": 1, "total_partition_pieces": 6, "full_merge_executed": False,
                         "region": m4["region"], "rows": len(load(m4path/"data.json")["rows"]),
                         "producer_wall_s": m4["producer"]["wall_s"],
                         "data_compile_wall_s": m4["data_compile"]["wall_s"],
                         "native_check_compile_wall_s": m4["native_check_compile"]["wall_s"]},
                  "restart": {"fresh_processes": 2, "C7_recomputations": 0},
                  "negative_cases": negative["cases_count"],
                  "evidence": [file_record(path, project) for path in
                    [base/"RESTART.json", base/"NEGATIVE.json", base/"merged_m2/MERGE.json", base/"flow_m2/FLOW.json", m4path/"manifest.json"]],
                  "full_m6_witness": False,
                  "limitations": ["m4 full partition/merge not executed by B; remaining pieces are C-conditional",
                    "whole m6 merge fin_cases elaboration and final flow runtime/cost are unmeasured",
                    "hashes are integrity receipts against selected trusted manifests, not signatures"]}
    put(root/"REGRESSION.json", regression)
    acceptance = {"utc": utc(), "gate": "PASS_B_CONTROLLER_ACCEPTED_SCOPE", "all_frozen_B_core_gates": all(matrix.values()),
                  "actual_scope": "m2 complete six-piece exact merge; m4 single large-piece native/import extension; not full m4/m6",
                  "gates": matrix, "partial_original_full_m4_acceptance": True,
                  "C7_calls_during_delivery": 0, "artifacts": [file_record(root/name, project) for name in
                    ("SOURCE_HASHES.json", "AXIOMS.json", "REGRESSION.json")]}
    put(root/"ACCEPTANCE.json", acceptance)
    print(json.dumps({"gate": acceptance["gate"], "all_B_core": acceptance["all_frozen_B_core_gates"],
                      "m2_pieces": 6, "m4_pieces": 1, "negative_cases": 11,
                      "restart_C7": 0, "merge_C7": 0, "m2_flow_C7": 0}, indent=2))


if __name__ == "__main__":
    main()
