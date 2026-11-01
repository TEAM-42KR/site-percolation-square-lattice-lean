#!/usr/bin/env python3
"""Generate optional, pure Lean certificate byte modules in an external directory.

Format: a byte is two A--P hexadecimal letters; Z followed by a two-letter
byte appends that many zero bytes. Tokens never cross string boundaries.
The pure decoder and semantic round-trip proofs are in CertificateBytes.lean.

Bounded sample example, run from the existing Lake project directory:
  python3 checker/encode_certificate.py --input-dir INPUT --output-dir OUTPUT \
    --module SitePercCertificateData.SampleSmall --max-bytes-per-file 1024 \
    --chunk-bytes 256 --chunks-per-module 2 --emit-native-check

For an authorized large-data generation use --all-bytes instead of the bounded
sample option, on its designated compute host. This generator never starts
compute, downloads data, runs the checker, or accepts a producer verdict.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
from pathlib import Path


FILES = (
    ("s1_nodes.bin", "S1Nodes", "s1Nodes"),
    ("s1_edges.bin", "S1Edges", "s1Edges"),
    ("s2_nodes.bin", "S2Nodes", "s2Nodes"),
    ("s2_edges.bin", "S2Edges", "s2Edges"),
)
ALPHABET = "ABCDEFGHIJKLMNOP"
NATIVE_CHECK_BYTE_CAP = 256 * 1024


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def pair(value: int) -> str:
    if not 0 <= value < 256:
        raise ValueError("not a byte")
    return ALPHABET[value // 16] + ALPHABET[value % 16]


def encode(raw: bytes) -> tuple[str, int, int]:
    """Greedy bounded zero runs; ordinary bytes always have a fixed width."""
    result: list[str] = []
    i = 0
    literal_count = zero_run_count = 0
    while i < len(raw):
        stop = i
        if raw[i] == 0:
            while stop < min(i + 255, len(raw)) and raw[stop] == 0:
                stop += 1
        if stop - i >= 3:
            result.append("Z" + pair(stop - i))
            i = stop
            zero_run_count += 1
        else:
            result.append(pair(raw[i]))
            literal_count += 1
            i += 1
    return "".join(result), literal_count, zero_run_count


def decode(encoded: str) -> bytes:
    """Independent strict token replay, not a producer's result flag."""
    result = bytearray()
    i = 0
    while i < len(encoded):
        is_run = encoded[i] == "Z"
        width = 3 if is_run else 2
        token = encoded[i + int(is_run):i + width]
        if len(token) != 2 or any(c not in ALPHABET for c in token):
            raise ValueError("malformed token")
        value = 16 * (ord(token[0]) - 65) + ord(token[1]) - 65
        if is_run:
            result.extend(bytes(value))
        else:
            result.append(value)
        i += width
    return bytes(result)


def module_path(root: Path, module: str) -> Path:
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def write_source(root: Path, module: str, source: str) -> dict:
    path = module_path(root, module)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(".lean.tmp")
    temporary.write_text(source, encoding="utf-8")
    temporary.replace(path)
    return {
        "module": module, "source": path.relative_to(root).as_posix(),
        "bytes": path.stat().st_size, "sha256": sha256(path.read_bytes()),
    }


def read_manifest(path: Path | None) -> tuple[dict[str, str], str | None]:
    if path is None:
        return {}, None
    raw = path.read_bytes()
    result = {}
    for line in raw.decode("utf-8").splitlines():
        match = re.fullmatch(r"([0-9a-fA-F]{64})\s+\*?(.+)", line)
        if match:
            result[Path(match.group(2)).name] = match.group(1).lower()
    return result, sha256(raw)


def native_check_source(module: str, raw_samples: dict[str, bytes]) -> str:
    """Bound even the independent raw equality references to 1-KiB literals."""
    namespace = module + ".NativeCheck"
    source = "import " + module + "\nimport Lean.Elab.Tactic.Decide\n\n"
    source += "namespace " + namespace + "\n\n"
    source += "set_option maxRecDepth 8192\nset_option maxHeartbeats 2000000\n\n"
    for _, _, name in FILES:
        raw = raw_samples[name]
        parts = []
        for offset in range(0, len(raw), 1024):
            part = name + f"Expected{offset // 1024:06d}"
            chunk = raw[offset:offset + 1024]
            source += "private def " + part + " : ByteArray := ByteArray.mk #[\n"
            source += ",\n".join("  " + ", ".join(map(str, chunk[i:i + 64]))
                                  for i in range(0, len(chunk), 64))
            source += "\n]\n\n"
            parts.append(part)
        source += "private def " + name + "Expected : ByteArray :=\n"
        source += "  (#[" + ", ".join(parts) + "]).foldl (· ++ ·) ByteArray.empty\n\n"
    comparisons = ["(" + module + "." + name + " == " + name + "Expected)"
                   for _, _, name in FILES]
    source += "def sampleExact : Bool :=\n  " + " &&\n  ".join(comparisons) + "\n\n"
    source += "theorem sample_decode_exact : sampleExact = true := by native_decide\n\n"
    source += "set_option pp.fullNames true in\n#print axioms sample_decode_exact\n#eval sampleExact\n\n"
    return source + "end " + namespace + "\n"


def generate(args: argparse.Namespace) -> dict:
    if not re.fullmatch(r"SitePercCertificateData(?:\.[A-Za-z][A-Za-z0-9_]*)*", args.module):
        raise ValueError("module must be in the SitePercCertificateData optional library")
    if args.sample_parts <= 0:
        raise ValueError("sample parts must be positive")
    if args.chunk_bytes <= 0 or args.chunks_per_module <= 0:
        raise ValueError("chunk and module sizes must be positive")
    if args.max_bytes_per_file is not None and args.max_bytes_per_file <= 0:
        raise ValueError("bounded sample size must be positive")
    if args.emit_native_check and (args.all_bytes or 4 * args.max_bytes_per_file > NATIVE_CHECK_BYTE_CAP):
        raise ValueError("raw-literal native equality references are bounded samples only")
    expected, manifest_hash = read_manifest(args.source_manifest)
    if expected and any(filename not in expected for filename, _, _ in FILES):
        raise ValueError("source manifest must cover all four flow files")
    modules: list[dict] = []
    input_rows = []
    raw_samples: dict[str, bytes] = {}
    aggregators = []
    for filename, label, constant in FILES:
        path = args.input_dir / filename
        original_size = path.stat().st_size
        part_names: list[str] = []
        encoded_chunks: list[str] = []
        raw_hash = hashlib.sha256()
        literal_hash = hashlib.sha256()
        raw_count = encoded_count = chunk_count = literal_tokens = zero_tokens = 0
        sample = bytearray()

        def flush() -> None:
            if not encoded_chunks:
                return
            part = args.module + "." + label + f".Part{len(part_names):06d}"
            source = "import Init.Data.String.Basic\n\nnamespace " + part + "\n\n"
            source += "def encoded : Array String := #[\n"
            source += ",\n".join('  "' + text + '"' for text in encoded_chunks)
            source += "\n]\n\nend " + part + "\n"
            modules.append(write_source(args.output_dir, part, source))
            part_names.append(part)
            encoded_chunks.clear()

        if args.all_bytes:
            windows = [(0, original_size)]
        else:
            cap = min(args.max_bytes_per_file, original_size)
            parts = min(args.sample_parts, cap) if cap else 1
            lengths = [cap // parts + int(i < cap % parts) for i in range(parts)]
            windows = [((original_size - length) * i // (parts - 1) if parts > 1 else 0, length)
                       for i, length in enumerate(lengths)]
        window_stats = [{"offset": offset, "bytes": size, "encoded_characters": 0}
                        for offset, size in windows]
        with path.open("rb") as stream:
            def raw_blocks():
                for window_index, (offset, window_bytes) in enumerate(windows):
                    stream.seek(offset)
                    remaining = window_bytes
                    while remaining:
                        raw = stream.read(min(args.chunk_bytes, remaining))
                        if not raw:
                            raise ValueError("source ended within a selected window")
                        remaining -= len(raw)
                        yield raw, window_index
            for raw, window_index in raw_blocks():
                text, literals, zeros = encode(raw)
                window_stats[window_index]["encoded_characters"] += len(text)
                if decode(text) != raw:
                    raise ValueError(f"strict token replay mismatch: {filename}, chunk {chunk_count}")
                # The safe alphabet guarantees a Lean string literal needs no escaping.
                if any(c not in ALPHABET + "Z" for c in text):
                    raise ValueError("unsafe literal alphabet")
                encoded_chunks.append(text)
                raw_hash.update(raw)
                literal_hash.update(text.encode("ascii"))
                raw_count += len(raw)
                encoded_count += len(text)
                chunk_count += 1
                literal_tokens += literals
                zero_tokens += zeros
                if args.emit_native_check:
                    sample.extend(raw)
                if len(encoded_chunks) >= args.chunks_per_module:
                    flush()
        flush()
        sampled_hash = raw_hash.hexdigest()
        if args.all_bytes and filename in expected and sampled_hash != expected[filename]:
            raise ValueError(f"full source SHA-256 does not match manifest: {filename}")
        data_module = args.module + "." + label
        source = "import SitePerc.Checker.CertificateBytes\n"
        source += "".join("import " + name + "\n" for name in part_names)
        source += "\nnamespace " + args.module + "\n\n"
        source += "/-- Token-aligned strings; source SHA-256 " + sampled_hash + ". -/\n"
        source += "def " + constant + "Encoded : Array String :=\n"
        if part_names:
            source += "  (#[" + ", ".join(name + ".encoded" for name in part_names) + "]).foldl (· ++ ·) #[]\n\n"
        else:
            source += "  #[]\n\n"
        source += "def " + constant + " : ByteArray :=\n"
        source += "  SitePerc.Checker.CertificateBytes.decodeChunks " + constant + "Encoded\n\n"
        source += "end " + args.module + "\n"
        modules.append(write_source(args.output_dir, data_module, source))
        aggregators.append(data_module)
        if args.emit_native_check:
            raw_samples[constant] = bytes(sample)
        input_rows.append({
            "file": filename, "constant": constant, "original_file_bytes": original_size,
            "transported_bytes": raw_count, "transported_sha256": sampled_hash,
            "is_complete_file": windows == [(0, original_size)],
            "sample_windows": window_stats,
            "expected_full_sha256_from_manifest": expected.get(filename),
            "expected_full_hash_verified": bool(args.all_bytes and filename in expected),
            "encoded_characters": encoded_count,
            "encoded_payload_sha256": literal_hash.hexdigest(),
            "raw_chunk_bytes": args.chunk_bytes, "chunks": chunk_count,
            "part_modules": len(part_names), "literal_tokens": literal_tokens,
            "zero_run_tokens": zero_tokens, "all_chunk_replays_exact": True,
        })
    root_source = "".join("import " + module + "\n" for module in aggregators)
    root_source += "\n/-! Four pure byte arrays for the unchanged flow-checker consumer. -/\n"
    modules.append(write_source(args.output_dir, args.module, root_source))
    native_module = None
    if args.emit_native_check:
        native_module = args.module + ".NativeCheck"
        source = native_check_source(args.module, raw_samples)
        modules.append(write_source(args.output_dir, native_module, source))
    receipt = {
        "schema": 1, "utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "generator": "checker/encode_certificate.py", "generator_sha256": sha256(Path(__file__).read_bytes()),
        "module": args.module, "format": "AP-hex/Zxx-zero-run-v1",
        "source_manifest_sha256": manifest_hash,
        "mode": "full" if args.all_bytes else ("bounded-prefix-sample" if args.sample_parts == 1 else "bounded-stratified-sample"),
        "sample_parts": args.sample_parts,
        "max_bytes_per_file": args.max_bytes_per_file,
        "raw_chunk_bytes": args.chunk_bytes, "chunks_per_module": args.chunks_per_module,
        "producer_verdict_used": False, "inputs": input_rows,
        "transported_bytes": sum(row["transported_bytes"] for row in input_rows),
        "encoded_characters": sum(row["encoded_characters"] for row in input_rows),
        "encoded_chunks": sum(row["chunks"] for row in input_rows),
        "part_modules": sum(row["part_modules"] for row in input_rows),
        "module_count": len(modules), "source_bytes": sum(row["bytes"] for row in modules),
        "all_chunk_replays_exact": all(row["all_chunk_replays_exact"] for row in input_rows),
        "native_check_module": native_module, "modules": modules,
        "full_compile_authorized": False,
    }
    receipt_path = args.receipt or args.output_dir / (args.module.replace(".", "_") + ".json")
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--module", default="SitePercCertificateData")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--max-bytes-per-file", type=int)
    mode.add_argument("--all-bytes", action="store_true")
    parser.add_argument("--sample-parts", type=int, default=1,
                        help="stratified equally spaced windows within the bounded per-file byte limit")
    parser.add_argument("--chunk-bytes", type=int, default=16384)
    parser.add_argument("--chunks-per-module", type=int, default=32)
    parser.add_argument("--source-manifest", type=Path)
    parser.add_argument("--emit-native-check", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    receipt = generate(args)
    print(json.dumps({key: receipt[key] for key in (
        "module", "mode", "transported_bytes", "encoded_characters", "encoded_chunks",
        "part_modules", "module_count", "source_bytes", "all_chunk_replays_exact", "native_check_module"
    )}, indent=2))


if __name__ == "__main__":
    main()
