#!/usr/bin/env python3
"""Compile explicit #print axioms requests and audit their exact dependencies."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def lean_code(text: str) -> str:
    """Remove nested comments and strings without joining adjacent tokens."""
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                break
            out.append("\n")
            i = j + 1
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unterminated block comment")
    return "".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", action="append", required=True)
    parser.add_argument("--theorem", action="append", required=True)
    parser.add_argument("--source-file", type=Path, action="append")
    parser.add_argument("--allow-native", action="append", default=[],
                        help="Exact generated native axiom, never a wildcard")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    identifier = re.compile(r"[A-Za-z_][A-Za-z_0-9.']*\Z")
    for name in args.module + args.theorem + args.allow_native:
        if not identifier.fullmatch(name):
            parser.error("Not a qualified Lean identifier: " + name)
    sources = args.source_file or sorted((root / "SitePerc").rglob("*.lean"))
    flags = []
    # This enforces the proof-delivery contract. Revisit only if that contract
    # explicitly changes; imported standard-library code is outside this scan.
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|unsafe|implemented_by|extern)\b")
    for path in sources:
        code = lean_code(path.read_text())
        for match in forbidden.finditer(code):
            flags.append({"path": str(path.relative_to(root)),
                          "line": code.count("\n", 0, match.start()) + 1,
                          "token": match.group()})
    program = "".join("import " + m + "\n" for m in args.module)
    program += "".join("#print axioms " + n + "\n" for n in args.theorem)
    with tempfile.TemporaryDirectory(prefix="siteperc-axioms-") as scratch:
        source = Path(scratch) / "Audit.lean"
        source.write_text(program)
        result = subprocess.run(["lake", "env", "lean", str(source)], cwd=root,
                                capture_output=True, text=True, check=False)
    text = result.stdout + result.stderr
    parsed = {}
    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text):
        parsed[match.group(1)] = [x.strip() for x in match.group(2).split(",") if x.strip()]
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        parsed[match.group(1)] = []
    allowed = STANDARD | set(args.allow_native)
    missing = [name for name in args.theorem if name not in parsed]
    unexpected = {name: [x for x in axioms if x not in allowed]
                  for name, axioms in parsed.items() if any(x not in allowed for x in axioms)}
    report = {"pass": result.returncode == 0 and not flags and not missing and not unexpected,
              "returncode": result.returncode, "source_files": len(sources),
              "source_flags": flags, "requested": args.theorem, "axioms": parsed,
              "allowed_native_exact": args.allow_native, "missing": missing,
              "unexpected": unexpected, "compiler_output": text}
    rendered = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(rendered)
    raise SystemExit(0 if report["pass"] else 1)


if __name__ == "__main__":
    main()
