#!/usr/bin/env python3
"""Reproduce the small direct-path regressions without producer law inputs.

All binary inputs are read-only. Generated sources, negative fixtures, oleans,
logs and receipts stay under --output. No Lake configuration is changed.
Only m=2 and m=4 are supported here; full six-by-six computation is excluded.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
from pathlib import Path
import re
import resource
import struct
import subprocess
import sys
import time


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def generate(args: argparse.Namespace) -> dict:
    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(root / "checker"))
    from encode_compact_certificate import encode_window, decode

    out = args.output.resolve()
    for child in ("inputs", "src", "build", "logs"):
        (out / child).mkdir(parents=True, exist_ok=True)
    inputs, blobs = [], {}
    directories = {"M2": args.m2.resolve(), "M4": args.m4.resolve(),
                   "Wierman1995": args.wierman.resolve()}
    for label, directory in directories.items():
        prefix = ("s1ok", "s2ok") if label != "Wierman1995" else ("s1", "s2")
        for stage, stem in enumerate(prefix, 1):
            for kind in ("nodes", "edges"):
                path = directory / f"{stem}_{kind}.bin"
                raw = path.read_bytes()
                if len(raw) > 2 * 1024 * 1024:
                    raise ValueError("small-regression per-file bound exceeded")
                name = f"{label.lower()}Stage{stage}{kind.title()}"
                blobs[name] = (raw, kind == "nodes")
                inputs.append({"file": str(path), "constant": name, "bytes": len(raw),
                               "sha256": sha(raw), "stage": stage, "kind": kind})
                (out / "inputs" / f"{name}.bin").write_bytes(raw)
    if sum(row["bytes"] for row in inputs) > 4 * 1024 * 1024:
        raise ValueError("small-regression total input bound exceeded")

    # OWN-ONLY H1/H2 patterns, instantiated at 2x2. No original 6x6 probe runs.
    edge_empty = b"R10AEDGE" + struct.pack("<Q", 0)
    scale = 1 << 100
    for stage, num, den in ((1, 586668, 1000000), (2, 679493, 1000000)):
        capacity = scale * (den - num) ** 4 // den ** 4
        body = bytes(16) + bytes(16) + capacity.to_bytes(16, "little") + bytes(16)
        raw = b"R10ANODE" + struct.pack("<IIQII", 4, 4, 1, stage, 0) + body
        blobs[f"dummyStage{stage}Nodes"] = (raw, True)
    blobs["emptyEdges"] = (edge_empty, False)
    base = blobs["m2Stage1Nodes"][0]
    first = int.from_bytes(base[32:48], "little")
    for name, key in (("noncanonicalNodes", 32),
                      ("highBitNodes", first + (1 << 20))):
        data = bytearray(base)
        data[32:48] = key.to_bytes(16, "little")
        blobs[name] = (bytes(data), True)
    data = bytearray(base)
    data[96:112] = data[32:48]
    blobs["duplicateNodes"] = (bytes(data), True)
    blobs["zeroNodes"] = (b"R10ANODE" + struct.pack("<IIQII", 4, 4, 0, 1, 0), True)

    source = ["import " + args.codec_module + "\n\n",
              "/-! Pure exact flow bytes. Producer laws and verdicts are not inputs. -/\n",
              "namespace SitePercDirectRegressionData\n\n"]
    transport = []
    for name, (raw, is_node) in blobs.items():
        chunks = []
        replay = bytearray()
        for offset in range(0, len(raw), 16384):
            encoded, _ = encode_window(raw[offset:offset + 16384], offset, is_node)
            replay.extend(decode(encoded))
            chunks.append(encoded)
        if bytes(replay) != raw:
            raise ValueError(f"byte-exact replay failed: {name}")
        (out / "inputs" / f"{name}.bin").write_bytes(raw)
        part_names = []
        for index in range(0, len(chunks), 6):
            part_name = f"{name}Part{index // 6:03d}"
            part_names.append(part_name)
            literal = ",\n    ".join(json.dumps(chunk, ensure_ascii=True)
                                     for chunk in chunks[index:index + 6])
            source.append(f"def {part_name} : Array String := #[\n    {literal}\n  ]\n\n")
        concatenated = " ++ ".join(part_names) if part_names else "#[]"
        source.append(f"/-- Exact input SHA-256 {sha(raw)}. -/\ndef {name} : ByteArray :=\n"
                      "  SitePerc.Checker.CompactCertificateBytes.decodeChunks ("
                      + concatenated + ")\n\n")
        transport.append({"constant": name, "bytes": len(raw), "sha256": sha(raw),
                          "chunks": len(chunks), "encoded_characters": sum(map(len, chunks)),
                          "independent_decode_equal": True, "node_format": is_node})
    source.append("end SitePercDirectRegressionData\n")
    module_source = "".join(source)
    module = out / "src" / "SitePercDirectRegressionData.lean"
    module.write_text(module_source, encoding="utf-8")
    source_paths = [Path(__file__).resolve(), root / "checker/encode_compact_certificate.py",
                    root / "SitePerc/Checker/DirectDefs.lean",
                    root / "SitePerc/Checker/PrunedDefs.lean",
                    root / "SitePerc/Checker/RegionalDefs.lean",
                    root / "SitePerc/Checker/CompactCertificateBytes.lean",
                    root / "SitePerc/Checker/DirectRegression.lean"]
    pending = list(source_paths)
    while pending:
        candidate = pending.pop()
        if candidate.suffix != ".lean" or not candidate.exists():
            continue
        for imported in re.findall(r"(?m)^import (SitePerc(?:\.[A-Za-z0-9_]+)+)",
                                   candidate.read_text()):
            dep = root.joinpath(*imported.split(".")).with_suffix(".lean")
            if dep.exists() and dep not in source_paths:
                source_paths.append(dep)
                pending.append(dep)
    source_paths += [root / "lean-toolchain", root / "lake-manifest.json"]
    receipt = {"schema": 1, "utc": dt.datetime.now(dt.timezone.utc).isoformat(),
               "scope": "small direct-path regression, OWN-ONLY H1/H2 at 2x2",
               "workers": 1, "sizes": [2, 4], "producer_laws_input": False,
               "producer_verdict_input": False, "large_computation": False,
               "inputs": inputs, "transport": transport,
               "all_independent_replays_equal": True,
               "generated_module": "SitePercDirectRegressionData",
               "generated_source_bytes": len(module_source.encode()),
               "generated_source_sha256": sha(module_source.encode()),
               "source_sha256": {str(p.relative_to(root)): sha(p.read_bytes())
                                 for p in source_paths if p.exists()},
               "python_version": sys.version.split()[0], "commands": []}
    write_json(out / "GENERATION.json", receipt)
    return receipt


def run(args: argparse.Namespace, receipt: dict) -> dict:
    root = Path(__file__).resolve().parents[1]
    out = args.output.resolve()
    runs = []
    commands = [
        ("dependencies", ["lake", "build", "SitePerc.Checker.DirectDefs",
                          args.codec_module]),
        ("pure_data", ["lake", "env", "lean", "-j1", "-M2048",
                       "--root=" + str(out / "src"),
                       "-o", str(out / "build/SitePercDirectRegressionData.olean"),
                       str(out / "src/SitePercDirectRegressionData.lean")]),
        ("native_regression", ["lake", "env", "bash", "-c",
          'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -j1 -M2048 -o "$2" '
          'SitePerc/Checker/DirectRegression.lean', "direct-regression",
          str(out / "build"), str(out / "build/DirectRegression.olean")])]
    for name, command in commands:
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        start = time.monotonic()
        try:
            proc = subprocess.run(command, cwd=root, text=True, capture_output=True, timeout=120)
            returncode, log = proc.returncode, proc.stdout + proc.stderr
        except subprocess.TimeoutExpired as error:
            def text(value: object) -> str:
                return value.decode(errors="replace") if isinstance(value, bytes) else str(value or "")
            returncode = 124
            log = text(error.stdout) + text(error.stderr) + "\nREGRESSION_TIMEOUT 120s\n"
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        (out / "logs" / f"{name}.log").write_text(log)
        row = {"name": name, "command": command, "returncode": returncode,
               "wall_s": time.monotonic() - start,
               "user_cpu_s": after.ru_utime - before.ru_utime,
               "system_cpu_s": after.ru_stime - before.ru_stime,
               "children_maxrss_kib_highwater": after.ru_maxrss,
               "log_sha256": sha(log.encode())}
        runs.append(row)
        if returncode:
            write_json(out / "RUN.json", {"all_pass": False, "runs": runs})
            raise RuntimeError(f"{name} failed; inspect owned log")
    log = (out / "logs/native_regression.log").read_text()
    expected = {"m2": True, "m4": True, "wierman1995": True,
                "H1_omitted_nonbottom": False, "H1_zero_nodes": False,
                "H2_noncanonical_orbit": False, "H2_ignored_high_bit": False,
                "H2_duplicate_key": False}
    actual = {name: value == "true" for name, value in
              re.findall(r"DIRECT_RESULT ([A-Za-z0-9_]+) (true|false)", log)}
    axioms = {name: re.split(r",\s*", body.strip()) for name, body in
              re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)}
    unchanged = all(sha(Path(row["file"]).read_bytes()) == row["sha256"]
                    for row in receipt["inputs"])
    source_after = {name: sha((root / name).read_bytes())
                    for name in receipt["source_sha256"]}
    result = {"schema": 1, "all_pass": actual == expected and unchanged,
              "expected": expected, "actual": actual, "inputs_unchanged": unchanged,
              "runs": runs, "native_axioms_exact": axioms,
              "semantic_boundary_domination_claimed": False,
              "source_sha256_after": source_after,
              "sources_unchanged": source_after == receipt["source_sha256"],
              "generated_source_sha256": receipt["generated_source_sha256"]}
    write_json(out / "RUN.json", result)
    if not result["all_pass"]:
        raise RuntimeError("regression expectation or input preservation failed")
    return result


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--m2", type=Path, required=True)
    ap.add_argument("--m4", type=Path, required=True)
    ap.add_argument("--wierman", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--codec-module", default="SitePerc.Checker.CompactCertificateBytesDefs")
    ap.add_argument("--run", action="store_true")
    args = ap.parse_args()
    start = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_SELF)
    receipt = generate(args)
    after = resource.getrusage(resource.RUSAGE_SELF)
    receipt["generation_resources"] = {"wall_s": time.monotonic() - start,
        "user_cpu_s": after.ru_utime - before.ru_utime,
        "system_cpu_s": after.ru_stime - before.ru_stime,
        "maxrss_kib": after.ru_maxrss}
    receipt["codec_module"] = args.codec_module
    write_json(args.output.resolve() / "GENERATION.json", receipt)
    result = run(args, receipt) if args.run else None
    print(json.dumps({"generated_source_bytes": receipt["generated_source_bytes"],
                      "all_literal_replays_equal": receipt["all_independent_replays_equal"],
                      "all_pass": result["all_pass"] if result else None,
                      "actual": result["actual"] if result else None,
                      "total_wall_s": time.monotonic() - start}, indent=2))


if __name__ == "__main__":
    main()
