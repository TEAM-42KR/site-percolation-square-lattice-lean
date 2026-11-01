#!/usr/bin/env python3
"""Transport the five supplied Wierman certificate files into pure Lean constants.

No producer verdict, serialization library, network, or runtime IO enters the
Lean constants. Run from the existing Lake project, for example:

  python3 scripts/generate_concrete_data.py \
    --input-dir ../lean-data/g/wierman1995 \
    --output-dir ../lean-data/g/concrete

The external source root is consumed by the same Lake project's optional
SitePercConcreteData library. Do not copy the generated constants into the
public source tree. The generation receipt records exact input and output
hashes and verifies literal-to-byte round trips independently of the checker.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
from pathlib import Path


INPUTS = (
    ("laws.bin", "lawsBytes"),
    ("s1_nodes.bin", "stageOneNodes"),
    ("s1_edges.bin", "stageOneEdges"),
    ("s2_nodes.bin", "stageTwoNodes"),
    ("s2_edges.bin", "stageTwoEdges"),
)
MODULE = Path("SitePercConcreteData") / "Wierman1995.lean"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def atomic_write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(text, encoding="utf-8")
    temporary.replace(path)


def declaration(name: str, data: bytes) -> str:
    rows = [", ".join(map(str, data[i:i + 24])) for i in range(0, len(data), 24)]
    literal = ",\n    ".join(rows)
    return (
        f"/-- Supplied certificate bytes; SHA-256 {digest(data)}. -/\n"
        f"def {name} : ByteArray :=\n"
        f"  ByteArray.mk #[\n    {literal}\n  ]\n"
    )


def generate(input_dir: Path, output_dir: Path) -> dict:
    parts = [
        "import Init.Data.ByteArray.Basic\n\n",
        "/-! Deterministic byte transport only. No checker verdict is encoded. -/\n",
        "namespace SitePercConcreteData.Wierman1995\n\n",
    ]
    inputs = []
    for filename, name in INPUTS:
        raw = (input_dir / filename).read_bytes()
        decl = declaration(name, raw)
        match = re.search(r"ByteArray\.mk #\[(.*?)\]", decl, re.S)
        assert match is not None
        recovered = bytes(int(token) for token in re.findall(r"\d+", match.group(1)))
        if recovered != raw:
            raise ValueError(f"literal byte round-trip mismatch: {filename}")
        parts.append(decl + "\n")
        inputs.append({
            "file": filename, "constant": name, "bytes": len(raw),
            "sha256": digest(raw), "literal_roundtrip_equal": True,
        })
    parts.append("end SitePercConcreteData.Wierman1995\n")
    source = "".join(parts)
    target = output_dir / MODULE
    atomic_write(target, source)
    if target.read_bytes() != source.encode("utf-8"):
        raise ValueError("generated source write mismatch")
    receipt = {
        "schema": 1,
        "utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "generator": "scripts/generate_concrete_data.py",
        "generator_sha256": digest(Path(__file__).read_bytes()),
        "lean_module": "SitePercConcreteData.Wierman1995",
        "source_relative": MODULE.as_posix(),
        "source_sha256": digest(source.encode("utf-8")),
        "source_bytes": len(source.encode("utf-8")),
        "inputs": inputs,
        "all_literal_roundtrips_equal": all(row["literal_roundtrip_equal"] for row in inputs),
        "producer_verdict_used": False,
    }
    atomic_write(output_dir / "GENERATION_RECEIPT.json", json.dumps(receipt, indent=2) + "\n")
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    receipt = generate(args.input_dir, args.output_dir)
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
