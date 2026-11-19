#!/usr/bin/env python3
"""Share identical compact-certificate geometry without changing its semantics.

The graph rows have different facet quotas, but often use exactly the same
candidate cells, incidence matrices, and embedding into the global cell pool.
This pass factors those repeated scalar fields into ordinary Lean record
updates.  It also replaces repeated geometry checks by references to an
earlier theorem with the same definitionally equal statement.  Every local
incompatibility check and every growth-node check remains in the proof graph.

This is an untrusted source generator.  Its hashes select possible sharing;
Lean's kernel still checks every use of a shared theorem and every remaining
finite check.  No hash comparison or Python calculation is an assumption of
the resulting Lean theorems.

The input may already contain the record updates emitted here, making the
pass idempotent.  Run before folding large natural-number expressions, or
again afterwards: closed scalar expressions are treated as source text and
are never evaluated by this pass.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import sys


RECORD_START = re.compile(r"^def (record\d+) : RawData := \{", re.MULTILINE)
NAMESPACE = re.compile(r"^namespace (\S+)\s*$", re.MULTILINE)
FIELD = re.compile(r"^  (\w+) := (.+)$", re.MULTILINE)
DECLARATION = re.compile(
    r"^theorem (record\d+_[A-Za-z0-9_]+)\b.*?(?=^theorem |^#print |^end |\Z)",
    re.MULTILINE | re.DOTALL,
)

# These determine the expensive metadata independently of the numerical
# quotas and of the sparse incompatibility pairs used by an individual DAG.
GEOMETRY_FIELDS = (
    "cellPred", "kindPred", "cellWidth", "cells", "faceMasks",
    "candidateMatrix", "kindLists", "kindMasks", "edgeLists", "edgeMasks",
    "edgeMatrix", "missingLists", "missingMasks", "missingMatrix",
    "vertexRows", "embedding",
)
LOCAL_FIELDS = GEOMETRY_FIELDS + ("badLists", "badMasks")
GEOMETRY_SUFFIX = re.compile(
    r"(?:alignment_(?:\d+|checked)|kind_checked|ridge_matrix|edge_matrix|"
    r"missing_matrix|vertex_width|vertex_code)\Z"
)
LOCAL_SUFFIX = re.compile(r"local_(?:\d+|checked)\Z")


@dataclass(frozen=True)
class Record:
    path: Path
    namespace: str
    name: str
    start: int
    end: int
    fields: dict[str, str]
    base: str | None = None

    @property
    def qualified(self) -> str:
        return f"{self.namespace}.{self.name}"

    @property
    def module(self) -> str:
        return self.namespace.rsplit(".", 1)[-1]

    @property
    def metadata_path(self) -> Path:
        return self.path.with_name(self.path.name.replace("_data.lean", "_metadata.lean"))


def fingerprint(record: Record, names: tuple[str, ...]) -> bytes:
    """A discovery key only; exact source equality is also checked below."""
    digest = hashlib.sha256()
    for name in names:
        encoded = record.fields[name].encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
    return digest.digest()


@dataclass(frozen=True)
class IndexEntry:
    path: Path
    metadata_path: Path
    namespace: str
    name: str
    order: int
    geometry_key: bytes
    local_key: bytes

    @property
    def qualified(self) -> str:
        return f"{self.namespace}.{self.name}"

    @property
    def module(self) -> str:
        return self.namespace.rsplit(".", 1)[-1]

def schema_fields(root: Path) -> tuple[str, ...]:
    text = (root / "source/geometry/packed_graph_certificate.lean").read_text()
    match = re.search(r"structure RawData where\n(.*?)\nnamespace RawData", text, re.DOTALL)
    if match is None:
        raise ValueError("RawData schema was not found")
    names = tuple(re.findall(r"^  (\w+) : ", match.group(1), re.MULTILINE))
    if len(names) != len(set(names)) or not set(LOCAL_FIELDS) <= set(names):
        raise ValueError("Unexpected RawData schema")
    return names


def parse_records(path: Path, text: str) -> list[Record]:
    records: list[Record] = []
    ns = NAMESPACE.search(text)
    if ns is None:
        raise ValueError(f"Missing namespace: {path}")
    for start in RECORD_START.finditer(text):
        # RawData has scalar fields only, and each field occupies one line
        # in these modules.  Refuse nested record syntax rather than guess.
        closing = text.find("}", start.end())
        if closing < 0:
            raise ValueError(f"Unterminated record: {path}:{start.group(1)}")
        body = text[start.end():closing]
        if "{" in body:
            raise ValueError(f"Unsupported nested record: {path}:{start.group(1)}")
        fields = dict(FIELD.findall(body.rstrip()))
        update = re.match(r"\s*([\w.]+) with\s*\n", body)
        records.append(Record(path, ns.group(1), start.group(1), start.start(), closing + 1,
                              fields, update.group(1) if update else None))
    return records


def add_imports(text: str, modules: set[str]) -> str:
    existing = set(re.findall(r"^(?:public )?import (\S+)$", text, re.MULTILINE))
    missing = sorted(modules - existing)
    if not missing:
        return text
    imports = list(re.finditer(r"^(?:public )?import \S+\n", text, re.MULTILINE))
    if not imports:
        raise ValueError("Generated module has no import section")
    point = imports[-1].end()
    return text[:point] + "".join(f"public import {module}\n" for module in missing) + text[point:]


def replace_spans(text: str, replacements: list[tuple[int, int, str]]) -> str:
    for lo, hi, replacement in sorted(replacements, reverse=True):
        text = text[:lo] + replacement + text[hi:]
    return text


def signature(declaration: str) -> str:
    mark = declaration.find(":=")
    if mark < 0:
        raise ValueError("Generated metadata theorem lacks :=")
    return declaration[:mark + 2]


def run_pass(root: Path, write: bool) -> dict[str, object]:
    schema = schema_fields(root)
    paths = sorted((root / "source/finite/graph_inputs_row").rglob("*_data.lean"))
    metadata_paths = {path.name: path for path in
                      (root / "source/finite/graph_inputs_row").rglob("*_metadata.lean")}
    records: list[IndexEntry] = []
    locations: dict[str, tuple[Path, int]] = {}
    by_path: dict[Path, list[IndexEntry]] = {}
    geometry_owner: dict[bytes, IndexEntry] = {}
    local_owner: dict[bytes, IndexEntry] = {}

    # Keep only compact hashes and source locations for the whole corpus.
    # Full scalar data are read through bounded caches, so this pass does
    # not require several gigabytes of memory to factor a gigabyte corpus.
    @lru_cache(maxsize=3)
    def parsed_file(path: Path) -> dict[str, Record]:
        return {record.qualified: record for record in parse_records(path, path.read_text())}

    @lru_cache(maxsize=96)
    def expanded_fields(qualified: str) -> dict[str, str]:
        path, order = locations[qualified]
        record = parsed_file(path)[qualified]
        if record.base:
            if record.base not in locations or locations[record.base][1] >= order:
                raise ValueError(f"Record update must name an earlier record: {record.base}")
            result = {**expanded_fields(record.base), **record.fields}
        else:
            result = record.fields
        if set(result) != set(schema):
            raise ValueError(
                f"Incomplete RawData at {qualified}: missing={set(schema) - set(result)}, "
                f"extra={set(result) - set(schema)}"
            )
        return result

    for path in paths:
        for parsed in parsed_file(path).values():
            if parsed.qualified in locations:
                raise ValueError(f"Duplicate record name: {parsed.qualified}")
            locations[parsed.qualified] = path, len(records)
            fields = expanded_fields(parsed.qualified)
            full = Record(path, parsed.namespace, parsed.name, 0, 0, fields)
            metadata_path = metadata_paths[path.name.replace("_data.lean", "_metadata.lean")]
            entry = IndexEntry(path, metadata_path, parsed.namespace, parsed.name, len(records),
                               fingerprint(full, GEOMETRY_FIELDS), fingerprint(full, LOCAL_FIELDS))
            records.append(entry)
            by_path.setdefault(path, []).append(entry)
            geometry_owner.setdefault(entry.geometry_key, entry)
            local_owner.setdefault(entry.local_key, entry)
    if not records:
        raise ValueError("No compact graph records found")

    changes: list[str] = []
    sharing: list[dict[str, str]] = []
    original_data_bytes = 0
    proposed_data_bytes = 0

    def finish_file(path: Path, text: str, proposed: str) -> None:
        if text != proposed:
            changes.append(str(path.relative_to(root)))
            if write:
                path.write_text(proposed)

    for path, entries in by_path.items():
        text = path.read_text()
        original_data_bytes += len(text.encode())
        parsed = {record.name: record for record in parse_records(path, text)}
        replacements: list[tuple[int, int, str]] = []
        imports: set[str] = set()
        for record in entries:
            owner = geometry_owner[record.geometry_key]
            if owner is record:
                continue
            fields = expanded_fields(record.qualified)
            owner_fields = expanded_fields(owner.qualified)
            if any(fields[name] != owner_fields[name] for name in GEOMETRY_FIELDS):
                raise ValueError("Hash collision while selecting shared geometry")
            # All omitted fields are literally the same source expression.
            # Every differing field, including all search and quota fields,
            # is supplied explicitly in the update.
            differing = [name for name in schema if fields[name] != owner_fields[name]]
            reconstructed = {**owner_fields, **{name: fields[name] for name in differing}}
            if reconstructed != fields:
                raise ValueError(f"Record update changed a scalar: {record.qualified}")
            body = f"def {record.name} : RawData := {{ {owner.qualified} with\n"
            body += "".join(f"  {name} := {fields[name]}\n" for name in differing)
            body += "}"
            span = parsed[record.name]
            replacements.append((span.start, span.end, body))
            if owner.path != record.path:
                imports.add(owner.module + "Data")
            sharing.append({"record": record.qualified, "geometry_owner": owner.qualified})
        proposed = add_imports(replace_spans(text, replacements), imports)
        proposed_data_bytes += len(proposed.encode())
        finish_file(path, text, proposed)

    @lru_cache(maxsize=3)
    def metadata_declarations(path: Path) -> dict[str, str]:
        return {declaration.group(1): declaration.group(0)
                for declaration in DECLARATION.finditer(path.read_text())}

    alias_counts: Counter[str] = Counter()
    new_finite_check_aliases: Counter[str] = Counter()
    for data_path, entries in by_path.items():
        path = entries[0].metadata_path
        text = path.read_text()
        records_by_name = {record.name: record for record in entries}
        replacements = []
        imports: set[str] = set()
        for declaration in DECLARATION.finditer(text):
            theorem_name = declaration.group(1)
            record_name, suffix = theorem_name.split("_", 1)
            record = records_by_name[record_name]
            if GEOMETRY_SUFFIX.fullmatch(suffix):
                owner = geometry_owner[record.geometry_key]
                category = "geometry"
            elif LOCAL_SUFFIX.fullmatch(suffix):
                owner = local_owner[record.local_key]
                category = "local"
            else:
                continue
            if owner is record:
                continue
            if category == "local":
                fields = expanded_fields(record.qualified)
                owner_fields = expanded_fields(owner.qualified)
                if any(fields[name] != owner_fields[name] for name in LOCAL_FIELDS):
                    raise ValueError("Hash collision while selecting shared local checks")
            owner_name = owner.name + "_" + suffix
            original_owner = metadata_declarations(owner.metadata_path).get(owner_name)
            if original_owner is None:
                raise ValueError(f"Missing owner theorem: {owner.qualified}_{suffix}")
            current_signature = signature(declaration.group(0))
            owner_signature = signature(original_owner)
            renamed_signature = current_signature.replace(theorem_name, owner_name, 1)
            renamed_signature = re.sub(rf"\b{re.escape(record.name)}\b", owner.name, renamed_signature)
            if " ".join(renamed_signature.split()) != " ".join(owner_signature.split()):
                raise ValueError(f"Metadata theorem statements do not match: {record.qualified}_{suffix}")
            replacement = current_signature + f"\n  {owner.qualified}_{suffix}\n\n"
            replacements.append((declaration.start(), declaration.end(), replacement))
            if owner.metadata_path != path:
                imports.add(owner.module + "Metadata")
            alias_counts[category] += 1
            old_body = declaration.group(0)[len(current_signature):].strip()
            if (("interval_of_check" in old_body and "decide +kernel" in old_body) or
                    re.fullmatch(r"by\s+decide \+kernel", old_body)):
                new_finite_check_aliases[category] += 1
        proposed = add_imports(replace_spans(text, replacements), imports)
        finish_file(path, text, proposed)

    report: dict[str, object] = {
        "records": len(records),
        "distinct_geometries": len(geometry_owner),
        "shared_geometry_records": len(sharing),
        "distinct_local_checks": len(local_owner),
        "aliased_theorems": dict(alias_counts),
        "finite_checks_replaced": dict(new_finite_check_aliases),
        "original_data_bytes": original_data_bytes,
        "proposed_data_bytes": proposed_data_bytes,
        "changed_files": sorted(changes),
        "sharing": sharing,
    }
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--write", action="store_true", help="Apply the exact source sharing")
    parser.add_argument("--check", action="store_true", help="Fail if sharing has not been applied")
    parser.add_argument("--report", type=Path, help="Write the complete sharing map as JSON")
    args = parser.parse_args()
    if args.write and args.check:
        parser.error("choose at most one of --write and --check")
    root = args.root.resolve()
    report = run_pass(root, args.write)
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")
    concise = {key: value for key, value in report.items() if key not in {"sharing", "changed_files"}}
    concise["changed_files"] = len(report["changed_files"])
    concise["applied"] = args.write
    print(json.dumps(concise, indent=2))
    return 1 if args.check and report["changed_files"] else 0


if __name__ == "__main__":
    sys.exit(main())
