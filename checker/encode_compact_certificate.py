#!/usr/bin/env python3
"""Structure-aware, byte-exact optional Lean certificate transport.

The consumer still receives four ByteArrays. Node records are four original
16-byte little-endian fields; edge records are four 4-byte fields followed
by a 16-byte flow. Headers and partial records are raw-byte tokens. No field,
leading zero, reserved byte or original header is reconstructed from a guess.

Sample mode reads only previously saved sample bytes and their window/hash
receipt. Full mode is a separate explicit command for an authorized compute
host; this program never launches compute or accepts a producer verdict.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import re
from pathlib import Path

# Reuse only bounded independent raw-reference emission, not the RLE codec.
from encode_certificate import native_check_source

FILES = (
    ("s1_nodes.bin", "S1Nodes", "s1Nodes", True),
    ("s1_edges.bin", "S1Edges", "s1Edges", False),
    ("s2_nodes.bin", "S2Nodes", "s2Nodes", True),
    ("s2_edges.bin", "S2Edges", "s2Edges", False),
)
FORMAT = "R10A-tuples-sixbit-varint-v1"


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def encode_nat(value: int) -> str:
    if value < 0:
        raise ValueError("natural number required")
    digits = []
    while value:
        digits.append(chr(48 + value % 64))
        value //= 64
    return "".join(digits) + "z"


def read_nat(text: str, start: int) -> tuple[int, int]:
    value, scale = 0, 1
    while start < len(text):
        code = ord(text[start])
        start += 1
        if code == 122:
            return value, start
        if not 48 <= code < 112:
            raise ValueError("invalid six-bit digit")
        value += (code - 48) * scale
        scale *= 64
    raise ValueError("unterminated varint")


def decode(text: str) -> bytes:
    """Independent replay of the actual pure tuple/raw stream grammar."""
    out = bytearray()
    i = 0
    while i < len(text):
        tag = text[i]
        i += 1
        if tag == "p":
            widths = (16, 16, 16, 16)
        elif tag == "q":
            widths = (4, 4, 4, 4, 16)
        elif tag == "r":
            widths = (1,)
        else:
            raise ValueError("invalid token tag")
        for width in widths:
            value, i = read_nat(text, i)
            if value >= 256 ** width:
                raise ValueError("fixed-width field overflow")
            out.extend(value.to_bytes(width, "little"))
    return bytes(out)


def encode_window(raw: bytes, absolute_offset: int, is_node: bool) -> tuple[str, dict]:
    header, record_size, widths = (32, 64, (16,) * 4) if is_node else (16, 32, (4,) * 4 + (16,))
    i = 0
    pieces = []
    counts = {"node_tokens": 0, "edge_tokens": 0, "raw_byte_tokens": 0}
    while i < len(raw):
        absolute = absolute_offset + i
        if absolute >= header and (absolute - header) % record_size == 0 and i + record_size <= len(raw):
            fields = []
            j = i
            for width in widths:
                field_bytes = raw[j:j + width]
                value = int.from_bytes(field_bytes, "little")
                if value.to_bytes(width, "little") != field_bytes:
                    raise ValueError("fixed-width/leading-zero round trip failed")
                fields.append(encode_nat(value))
                j += width
            pieces.append(("p" if is_node else "q") + "".join(fields))
            counts["node_tokens" if is_node else "edge_tokens"] += 1
            i += record_size
        else:
            pieces.append("r" + encode_nat(raw[i]))
            counts["raw_byte_tokens"] += 1
            i += 1
    encoded = "".join(pieces)
    if decode(encoded) != raw:
        raise ValueError("exact tuple replay differs from original bytes")
    return encoded, counts


def write_module(root: Path, module: str, text: str) -> dict:
    path = root.joinpath(*module.split(".")).with_suffix(".lean")
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".lean.tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)
    return {"module": module, "source": path.relative_to(root).as_posix(),
            "bytes": path.stat().st_size, "sha256": sha256(path.read_bytes())}


def load_manifest(path: Path | None) -> tuple[dict[str, str], str | None]:
    if path is None:
        return {}, None
    raw = path.read_bytes()
    hashes = {}
    for line in raw.decode("utf-8").splitlines():
        match = re.fullmatch(r"([0-9a-fA-F]{64})\s+\*?(.+)", line)
        if match:
            hashes[Path(match.group(2)).name] = match.group(1).lower()
    return hashes, sha256(raw)


def generate(args: argparse.Namespace) -> dict:
    if not re.fullmatch(r"SitePercCompactCertificateData(?:\.[A-Za-z][A-Za-z0-9_]*)*", args.module):
        raise ValueError("unexpected optional-library module root")
    if args.chunk_bytes <= 0 or args.chunks_per_module <= 0:
        raise ValueError("positive chunk sizes required")
    if args.all_bytes and args.sample_receipt is not None:
        raise ValueError("full and saved-sample modes cannot be combined")
    if not args.all_bytes and (args.sample_receipt is None or args.sample_dir is None):
        raise ValueError("bounded mode requires saved sample directory and receipt")
    if args.all_bytes and args.input_dir is None:
        raise ValueError("full mode requires an explicit input directory")
    if args.emit_native_check and (args.all_bytes or not 0 < args.sample_limit <= 16384):
        raise ValueError("native raw equality references are limited to bounded samples")
    if args.sample_limit <= 0:
        raise ValueError("sample limit must be positive")
    saved_raw = args.sample_receipt.read_bytes() if args.sample_receipt else None
    saved = json.loads(saved_raw) if saved_raw is not None else None
    sample_rows = {row["file"]: row for row in saved.get("rows", saved.get("inputs", []))} if saved else {}
    expected, manifest_sha = load_manifest(args.source_manifest)
    modules, inputs, data_modules = [], [], []
    references = {}
    for filename, label, constant, is_node in FILES:
        row = sample_rows.get(filename)
        if args.all_bytes:
            path = args.input_dir / filename
            file_size = path.stat().st_size
            expected_hash = expected.get(filename)
            if expected and expected_hash is None:
                raise ValueError("full source manifest does not cover every input")
            selected = None
        else:
            if row is None:
                raise ValueError("sample receipt lacks an input")
            path = args.sample_dir / filename
            selected = path.read_bytes()
            if len(selected) != row["transported_bytes"] or sha256(selected) != row["transported_sha256"]:
                raise ValueError("saved sample bytes differ from the prior exact-byte receipt")
            file_size = row["original_file_bytes"]
            expected_hash = row.get("expected_full_sha256_from_manifest")
        parts, strings, window_stats = [], [], []
        input_hash, encoded_hash = hashlib.sha256(), hashlib.sha256()
        raw_bytes = encoded_chars = escaped_chars = string_count = 0
        token_counts = {"node_tokens": 0, "edge_tokens": 0, "raw_byte_tokens": 0}
        reference = bytearray()

        def flush() -> None:
            if not strings:
                return
            name = args.module + "." + label + f".Part{len(parts):06d}"
            text = "import Init.Data.String.Basic\n\nnamespace " + name + "\n\n"
            text += "def encoded : Array String := #[\n"
            text += ",\n".join("  " + json.dumps(value, ensure_ascii=True) for value in strings)
            text += "\n]\n\nend " + name + "\n"
            modules.append(write_module(args.output_dir, name, text))
            parts.append(name)
            strings.clear()

        def blocks():
            if args.all_bytes:
                with path.open("rb") as stream:
                    offset = 0
                    while True:
                        chunk = stream.read(args.chunk_bytes)
                        if not chunk:
                            return
                        yield chunk, offset, 0
                        offset += len(chunk)
            else:
                cursor, remaining = 0, min(args.sample_limit, len(selected))
                for index, window in enumerate(row["sample_windows"]):
                    window_raw = selected[cursor:cursor + window["bytes"]]
                    cursor += window["bytes"]
                    take = min(remaining, len(window_raw))
                    if take <= 0:
                        break
                    for j in range(0, take, args.chunk_bytes):
                        chunk = window_raw[j:min(take, j + args.chunk_bytes)]
                        yield chunk, window["offset"] + j, index
                    remaining -= take

        for chunk, offset, window_index in blocks():
            encoded, counts = encode_window(chunk, offset, is_node)
            literal = json.dumps(encoded, ensure_ascii=True)
            # Escaping is checked independently: the Lean string value is unchanged.
            if json.loads(literal) != encoded:
                raise ValueError("escaped string round trip failed")
            strings.append(encoded)
            input_hash.update(chunk)
            encoded_hash.update(encoded.encode("ascii"))
            raw_bytes += len(chunk)
            encoded_chars += len(encoded)
            escaped_chars += len(literal) - 2
            string_count += 1
            for key, count in counts.items():
                token_counts[key] += count
            window_stats.append({"offset": offset, "bytes": len(chunk), "window_index": window_index,
                                 "encoded_characters": len(encoded), "escaped_payload_characters": len(literal) - 2,
                                 "source_chunk_sha256": sha256(chunk), **counts})
            if args.emit_native_check:
                reference.extend(chunk)
            if len(strings) >= args.chunks_per_module:
                flush()
        flush()
        if args.all_bytes and expected_hash is not None and input_hash.hexdigest() != expected_hash:
            raise ValueError("full source SHA-256 differs from canonical manifest")
        data_module = args.module + "." + label
        source = "import SitePerc.Checker.CompactCertificateBytesDefs\n"
        source += "".join("import " + name + "\n" for name in parts)
        source += "\nnamespace " + args.module + "\n\n"
        source += "def " + constant + "Encoded : Array String :=\n"
        source += "  (#[" + ", ".join(name + ".encoded" for name in parts) + "]).foldl (· ++ ·) #[]\n\n" if parts else "  #[]\n\n"
        source += "def " + constant + " : ByteArray :=\n"
        source += "  SitePerc.Checker.CompactCertificateBytes.decodeChunks " + constant + "Encoded\n\n"
        source += "end " + args.module + "\n"
        modules.append(write_module(args.output_dir, data_module, source))
        data_modules.append(data_module)
        if args.emit_native_check:
            references[constant] = bytes(reference)
        inputs.append({"file": filename, "constant": constant, "original_file_bytes": file_size,
                       "transported_bytes": raw_bytes, "transported_sha256": input_hash.hexdigest(),
                       "expected_full_sha256_from_manifest": expected_hash,
                       "full_hash_measured_and_verified": bool(args.all_bytes and expected_hash),
                       "encoded_characters": encoded_chars, "escaped_payload_characters": escaped_chars,
                       "encoded_payload_sha256": encoded_hash.hexdigest(), "chunks": string_count,
                       "part_modules": len(parts), "windows": window_stats, "all_replays_exact": True,
                       **token_counts})
    source = "".join("import " + name + "\n" for name in data_modules)
    source += "\n/-! Four exact pure ByteArrays; no checker verdict is encoded. -/\n"
    modules.append(write_module(args.output_dir, args.module, source))
    native_module = args.module + ".NativeCheck" if args.emit_native_check else None
    if native_module:
        modules.append(write_module(args.output_dir, native_module,
                                    native_check_source(args.module, references)))
    helper = Path(__file__).with_name("encode_certificate.py")
    receipt = {"schema": 1, "utc": dt.datetime.now(dt.timezone.utc).isoformat(), "format": FORMAT,
               "generator": "checker/encode_compact_certificate.py", "generator_sha256": sha256(Path(__file__).read_bytes()),
               "native_reference_helper_sha256": sha256(helper.read_bytes()) if args.emit_native_check else None,
               "mode": "full" if args.all_bytes else "reused-bounded-sample", "module": args.module,
               "source_manifest_sha256": manifest_sha,
               "saved_sample_receipt_sha256": sha256(saved_raw) if saved_raw else None,
               "original_inputs_read_again": bool(args.all_bytes), "sample_limit_per_file": args.sample_limit,
               "raw_chunk_bytes": args.chunk_bytes, "chunks_per_module": args.chunks_per_module,
               "transported_bytes": sum(row["transported_bytes"] for row in inputs),
               "encoded_characters": sum(row["encoded_characters"] for row in inputs),
               "escaped_payload_characters": sum(row["escaped_payload_characters"] for row in inputs),
               "chunks": sum(row["chunks"] for row in inputs),
               "part_modules": sum(row["part_modules"] for row in inputs), "module_count": len(modules),
               "source_bytes": sum(row["bytes"] for row in modules), "native_check_module": native_module,
               "producer_verdict_used": False, "inputs": inputs, "modules": modules,
               "all_replays_exact": True, "full_compile_authorized": False}
    receipt_path = args.receipt or args.output_dir / (args.module.replace(".", "_") + ".json")
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-dir", type=Path)
    parser.add_argument("--all-bytes", action="store_true")
    parser.add_argument("--sample-dir", type=Path)
    parser.add_argument("--sample-receipt", type=Path)
    parser.add_argument("--sample-limit", type=int, default=16384)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--module", default="SitePercCompactCertificateData")
    parser.add_argument("--chunk-bytes", type=int, default=16384)
    parser.add_argument("--chunks-per-module", type=int, default=32)
    parser.add_argument("--source-manifest", type=Path)
    parser.add_argument("--emit-native-check", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    receipt = generate(args)
    print(json.dumps({key: receipt[key] for key in ("mode", "module", "transported_bytes", "encoded_characters",
                                                 "escaped_payload_characters", "chunks", "part_modules",
                                                 "module_count", "source_bytes", "all_replays_exact")}, indent=2))


if __name__ == "__main__":
    main()
