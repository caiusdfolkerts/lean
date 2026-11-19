#!/usr/bin/env python3
"""Replace generated packed numbers with exact sparse hexadecimal data literals.

Only closed Nat.lor/Nat.shiftLeft expressions and large natural literals are
accepted. The emitted sparse_nat% syntax expands to an ordinary Lean Nat
literal, so the existing kernel certificate checks are unchanged. This tool
does not produce a proof or certify the input data.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

from fold_packed_numerals import MAX_BITS, NotClosedNumeral, code_segments, parse_closed_nat

TOKEN = re.compile(r"\(\s*Nat\.(?:lor|shiftLeft)(?=\s|\()|"
                   r"(?<![\w.])(?:0[xX][0-9a-fA-F_]+|[0-9][0-9_]*)(?![\w])")
ZERO_RUN = re.compile(r"0{16,}")
META_IMPORT = "public meta import SparseNatLiteral"


def encode(value: int) -> str:
    if value < 0:
        raise ValueError("certificate natural must be nonnegative")
    return ZERO_RUN.sub(lambda m: "z" + format(len(m.group()), "x") + ";", format(value, "x"))


def decode(encoded: str, max_bits: int = MAX_BITS) -> int:
    """Independent exact integer decoder used to validate every replacement."""
    if not encoded:
        raise ValueError("empty sparse numeral")
    value, width, position = 0, 0, 0
    while position < len(encoded):
        if encoded[position] == "z":
            end = encoded.find(";", position + 1)
            if end < 0 or not re.fullmatch("[0-9a-fA-F]+", encoded[position + 1:end]):
                raise ValueError("invalid sparse zero run")
            count = int(encoded[position + 1:end], 16)
            if count == 0 or 4 * (width + count) > max_bits:
                raise ValueError("invalid sparse zero-run width")
            value <<= 4 * count
            width += count
            position = end + 1
        else:
            match = re.match("[0-9a-fA-F]+", encoded[position:])
            if match is None:
                raise ValueError("invalid sparse hexadecimal digit")
            digits = match.group()
            width += len(digits)
            if 4 * width > max_bits:
                raise ValueError("sparse numeral exceeds the size limit")
            value = (value << (4 * len(digits))) | int(digits, 16)
            position += len(digits)
    return value


def compress_source(source: str, minimum_chars: int = 256):
    replacements = []
    for begin, end in code_segments(source):
        position = begin
        while match := TOKEN.search(source, position, end):
            start = match.start()
            if source[start] == "(":
                value, stop, operations = parse_closed_nat(source, start)
                if stop > end:
                    raise NotClosedNumeral("packed numeral crosses a comment or string")
            else:
                stop, operations = match.end(), 0
                raw = match.group().replace("_", "")
                if stop - start < minimum_chars:
                    position = stop
                    continue
                value = int(raw, 16 if raw.lower().startswith("0x") else 10)
            position = stop
            if stop - start < minimum_chars:
                continue
            encoded = encode(value)
            if decode(encoded) != value:
                raise AssertionError("sparse numeral round trip changed its value")
            replacements.append({
                "start": start, "end": stop,
                "replacement": 'sparse_nat% "' + encoded + '"',
                "bits": value.bit_length(), "operations": operations,
                "value_sha256": hashlib.sha256(format(value, 'x').encode('ascii')).hexdigest(),
            })
    if not replacements:
        return source, []
    chunks, position = [], 0
    for item in replacements:
        chunks.extend((source[position:item['start']], item['replacement']))
        position = item['end']
    chunks.append(source[position:])
    transformed = ''.join(chunks)
    if not re.search(r'(?m)^public meta import SparseNatLiteral\s*$', transformed):
        header = re.match(r'module\s*\n(?:prelude\s*\n)?', transformed)
        if header is None:
            raise NotClosedNumeral('expected a generated Lean module header')
        transformed = transformed[:header.end()] + META_IMPORT + '\n' + transformed[header.end():]
    return transformed, replacements


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='+', type=Path)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--report', type=Path)
    parser.add_argument('--minimum-chars', type=int, default=256)
    args = parser.parse_args()
    if args.minimum_chars < 1:
        parser.error('--minimum-chars must be positive')
    rows = []
    for path in args.paths:
        before = path.read_bytes()
        transformed, replacements = compress_source(before.decode(), args.minimum_chars)
        if not replacements:
            continue
        after = transformed.encode()
        rows.append({'path': str(path), 'before_bytes': len(before), 'after_bytes': len(after),
                     'before_sha256': hashlib.sha256(before).hexdigest(),
                     'after_sha256': hashlib.sha256(after).hexdigest(),
                     'numerals': len(replacements),
                     'value_hashes': [r['value_sha256'] for r in replacements]})
        if args.write:
            path.write_bytes(after)
    summary = {'format': 'sparse-certificate-numerals-v1', 'written': args.write,
               'files': len(rows), 'before_bytes': sum(r['before_bytes'] for r in rows),
               'after_bytes': sum(r['after_bytes'] for r in rows),
               'numerals': sum(r['numerals'] for r in rows)}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps({**summary, 'records': rows}, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
