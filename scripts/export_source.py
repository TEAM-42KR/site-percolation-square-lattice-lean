#!/usr/bin/env python3
"""Export the public source allowlist; never push or publish anything."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil


def source_files(root: Path) -> list[Path]:
    fixed = [
        "README.md", "LICENSE", "NOTICE", ".gitignore", "lean-toolchain",
        "lakefile.toml", "lake-manifest.json", "SitePerc.lean",
        "data/README.md", "data/MANIFEST.sha256", "data/FLOW_MANIFEST.sha256",
        "data/NATIVE_EXECUTION.json", "data/AXIOM_AUDIT.json", "scripts/export_source.py",
        "data/L2_SHARDED_SUPPORT.json",
        "data/L2_PROFILE.json", "data/PAPER13_AXIOMS.log",
        "scripts/audit_axioms.py", "scripts/generate_concrete_data.py", "scripts/generate_final_target.py",
        "scripts/generate_direct_regression.py",
        "checker/README.md", "checker/regression.py", "checker/encode_certificate.py",
        "checker/encode_compact_certificate.py",
        "checker/Audit.lean",
        "INTERFACE_L2_A.md", "INTERFACE_L2_B.md",
        "checker/sharded/USAGE.md", "checker/sharded/Producer.lean",
        "checker/sharded/common.py", "checker/sharded/shards.py",
        "checker/sharded/regression.py", "checker/sharded/audit_delivery.py",
        "checker/sharded/PATCH.sha256",
    ]
    files = [root / name for name in fixed]
    files.extend(sorted((root / "SitePerc").rglob("*.lean")))
    files.extend(p for p in sorted((root / "data/small-native").rglob("*")) if p.is_file())
    missing = [str(p.relative_to(root)) for p in files if not p.is_file()]
    if missing:
        raise SystemExit("Missing source files: " + ", ".join(missing))
    return sorted(set(files))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    target = args.output.resolve()
    if target == root or root in target.parents:
        raise SystemExit("The export directory must be outside the working project.")
    if target.exists() and any(target.iterdir()):
        raise SystemExit("Refusing to overwrite a nonempty export directory.")
    files = source_files(root)
    private_prefixes = ["/" + "opt" + "/", "/" + "root" + "/", "/" + "home" + "/"]
    errors = []
    records = []
    for path in files:
        rel = path.relative_to(root)
        body = path.read_bytes()
        if len(body) > 8 * 1024 * 1024:
            errors.append(f"oversize source: {rel}")
        text = "" if path.suffix == ".bin" and "small-native" in rel.parts else body.decode("utf-8")
        # README reproduction instructions are the sole allowed location for a
        # host-specific path; all shipped executable sources stay portable.
        if rel.name != "README.md" and any(p in text for p in private_prefixes):
            errors.append(f"private host path: {rel}")
        records.append({"path": str(rel), "bytes": len(body),
                        "sha256": hashlib.sha256(body).hexdigest()})
    if errors:
        raise SystemExit("Export refused:\n" + "\n".join(errors))
    target.mkdir(parents=True, exist_ok=True)
    for path in files:
        dest = target / path.relative_to(root)
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, dest)
    (target / "SOURCE_MANIFEST.json").write_text(
        json.dumps({"schema": 1, "files": records}, indent=2) + "\n"
    )
    print(json.dumps({"output": str(target), "files": len(files),
                      "bytes": sum(r["bytes"] for r in records)}))


if __name__ == "__main__":
    main()
