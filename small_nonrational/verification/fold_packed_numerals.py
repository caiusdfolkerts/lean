#!/usr/bin/env python3
"""Parse and normalize closed packed-Nat expressions for certificate generation.

The generated certificate data contains large trees built exclusively from
natural literals, ``Nat.lor``, and ``Nat.shiftLeft``.  Their arithmetic is fixed
at generation time. This module supplies the exact parser used by data
compression and audit tools, and an optional ``hexnat%`` literal normalizer. The existing
HexNatLiteral elaborator emits an ordinary Lean Nat literal, and every property
of the certificate is still checked by the kernel.

This is a source-generation tool, not a proof checker.  It uses no eval, does
not change predicates or proofs, and records both source and value digests.
It deliberately accepts only the tiny closed arithmetic grammar above.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys


OPERATIONS = {"Nat.lor", "Nat.shiftLeft"}
TOKEN = re.compile(r"\s*(?:(?P<op>Nat\.(?:lor|shiftLeft))(?=\s|\()|"
                   r"(?P<number>0[xX][0-9a-fA-F_]+|[0-9][0-9_]*)|(?P<paren>[()]))")
CANDIDATE = re.compile(r"\(\s*Nat\.(?:lor|shiftLeft)(?=\s|\()")
SPECIAL = re.compile(r'--|/-|«|(?<!\w)r#*"|"')
BLOCK_EDGE = re.compile(r"/-|-/")
STRING = re.compile(r'"(?:\\[\s\S]|[^"\\])*"')
META_IMPORT = "public meta import HexNatLiteral"
MAX_BITS = 64 * 1024 * 1024


class NotClosedNumeral(ValueError):
    """The expression is not in the supported closed packed-Nat grammar."""


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_closed_nat(source: str, start: int, max_bits: int = MAX_BITS):
    """Return (value, end, operations) without using Python/Lean evaluation.

    An explicit stack permits the deep generated expressions without changing
    Python's recursion limit.  Every parenthesis and operand must be accounted
    for; identifiers, negative literals, comments, and trailing operands fail.
    """
    position = start
    stack = []
    operations = 0
    value = None
    while True:
        token = TOKEN.match(source, position)
        if token is None:
            raise NotClosedNumeral(f"unsupported token at character {position}")
        position = token.end()
        kind = token.lastgroup
        if kind == "paren" and token.group(kind) == "(":
            operation = TOKEN.match(source, position)
            if operation is None or operation.lastgroup != "op":
                raise NotClosedNumeral(f"expected a packed Nat operation at {position}")
            stack.append([operation.group("op"), []])
            position = operation.end()
            continue
        if kind != "number":
            raise NotClosedNumeral(f"expected a natural operand at {position}")
        number = token.group(kind).replace("_", "")
        value = int(number, 16 if number.lower().startswith("0x") else 10)
        if value.bit_length() > max_bits:
            raise NotClosedNumeral("packed numeral exceeds the configured size limit")
        while stack:
            operation, operands = stack[-1]
            operands.append(value)
            if len(operands) < 2:
                break
            closing = TOKEN.match(source, position)
            if closing is None or closing.lastgroup != "paren" or closing.group("paren") != ")":
                raise NotClosedNumeral(f"expected exactly two operands at {position}")
            position = closing.end()
            left, right = operands
            if operation == "Nat.lor":
                value = left | right
            elif operation == "Nat.shiftLeft":
                if right > max_bits or left.bit_length() + right > max_bits:
                    raise NotClosedNumeral("packed shift exceeds the configured size limit")
                value = left << right
            else:  # The tokenizer and operation gate intentionally fail closed.
                raise NotClosedNumeral(f"unsupported operation {operation}")
            operations += 1
            stack.pop()
        if not stack:
            return value, position, operations


def code_segments(source: str):
    """Yield source intervals outside comments, strings and quoted names.

    Lean block comments may nest. Ordinary and raw strings, escaped quotes,
    and guillemet-delimited identifiers are skipped, so reruns cannot parse or
    rewrite existing ``hexnat%`` payloads, documentation or identifier text.
    """
    begin = position = 0
    length = len(source)
    while match := SPECIAL.search(source, position):
        position = match.start()
        if match.group() == "--":
            if begin < position:
                yield begin, position
            newline = source.find("\n", position + 2)
            position = length if newline < 0 else newline + 1
            begin = position
        elif match.group() == "/-":
            if begin < position:
                yield begin, position
            depth = 1
            position += 2
            while depth and (edge := BLOCK_EDGE.search(source, position)):
                position = edge.end()
                if edge.group() == "/-":
                    depth += 1
                else:
                    depth -= 1
            if depth:
                raise NotClosedNumeral("unterminated Lean block comment")
            begin = position
        elif match.group() == "«":
            if begin < position:
                yield begin, position
            closing = source.find("»", position + 1)
            if closing < 0:
                raise NotClosedNumeral("unterminated Lean quoted identifier")
            position = closing + 1
            begin = position
        elif match.group().startswith("r"):
            if begin < position:
                yield begin, position
            closing_token = '"' + "#" * (len(match.group()) - 2)
            closing = source.find(closing_token, match.end())
            if closing < 0:
                raise NotClosedNumeral("unterminated Lean raw string")
            position = closing + len(closing_token)
            begin = position
        else:
            if begin < position:
                yield begin, position
            string = STRING.match(source, position)
            if string is None:
                raise NotClosedNumeral("unterminated Lean string")
            position = string.end()
            begin = position
    if begin < length:
        yield begin, length


def fold_source(source: str, minimum_chars: int = 256):
    replacements = []
    for begin, end in code_segments(source):
        position = begin
        while match := CANDIDATE.search(source, position, end):
            value, stop, operations = parse_closed_nat(source, match.start())
            if stop > end:
                raise NotClosedNumeral("closed numeral crosses a comment or string")
            position = stop
            if stop - match.start() < minimum_chars:
                continue
            hexadecimal = format(value, "x")
            replacement = 'hexnat% "' + hexadecimal + '"'
            # The digest is over a canonical representation, independent of
            # source indentation or the old expression's parenthesization.
            replacements.append({"start": match.start(), "end": stop,
                                 "replacement": replacement,
                                 "operations_removed": operations,
                                 "bits": value.bit_length(),
                                 "value_sha256": sha(hexadecimal.encode("ascii"))})
    if not replacements:
        return source, []
    chunks, position = [], 0
    for row in replacements:
        chunks.extend((source[position:row["start"]], row["replacement"]))
        position = row["end"]
    chunks.append(source[position:])
    transformed = "".join(chunks)
    if not re.search(r"(?m)^public meta import HexNatLiteral\s*$", transformed):
        # Existing sources put module/prelude before their imports.  The helper
        # is imported only as metaprogramming support, never as a trusted axiom.
        header = re.match(r"module\s*\n(?:prelude\s*\n)?", transformed)
        if header is None:
            raise NotClosedNumeral("expected generated Lean module header")
        transformed = transformed[:header.end()] + META_IMPORT + "\n" + transformed[header.end():]
    return transformed, replacements


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", type=Path, nargs="+", help="Exact Lean source files to inspect")
    parser.add_argument("--write", action="store_true", help="Replace the inspected source files")
    parser.add_argument("--report", type=Path, help="Write a JSON report of exact source/value digests")
    parser.add_argument("--minimum-chars", type=int, default=256)
    args = parser.parse_args()
    if args.minimum_chars < 1:
        parser.error("--minimum-chars must be positive")
    totals = Counter()
    records = []
    for path in args.paths:
        before = path.read_bytes()
        transformed, replacements = fold_source(before.decode("utf-8"), args.minimum_chars)
        after = transformed.encode("utf-8")
        if not replacements:
            continue
        record = {"path": str(path), "before_sha256": sha(before), "after_sha256": sha(after),
                  "before_bytes": len(before), "after_bytes": len(after),
                  "numerals": len(replacements),
                  "operations_removed": sum(row["operations_removed"] for row in replacements),
                  "largest_bits": max(row["bits"] for row in replacements),
                  "values": [{k: v for k, v in row.items() if k != "replacement"} for row in replacements]}
        records.append(record)
        for key in ("before_bytes", "after_bytes", "numerals", "operations_removed"):
            totals[key] += record[key]
        if args.write:
            path.write_bytes(after)
    report = {"format": "packed-nat-constant-fold-v1", "written": args.write,
              "minimum_chars": args.minimum_chars, "files": len(records),
              "totals": dict(totals), "records": records}
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ("format", "written", "files", "totals")}, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, UnicodeError, ValueError) as error:
        print(f"Packed numeral generation stopped: {error}", file=sys.stderr)
        raise SystemExit(1)
