#!/usr/bin/env python3
"""Inspect every exported project proof occurrence and its library axiom boundary.

This supplements source compilation and Lean's assembled-environment name audit.
It does not replay proof bodies or replace the kernel. Original project axioms
are rejected, every recorded reference must resolve, and Lean checks the
transitive axioms of all referenced names at the pinned library boundary.
Compiler-generated partial implementations are recorded separately and must
be absent from every safe declaration's logical dependency graph.
"""
from __future__ import annotations

import argparse
from collections import Counter
import fcntl
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import time


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, f"Cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def inspect_graph(path, manifest):
    owners, kinds, references, boundary, compatible = {}, {}, set(), {}, {}
    counts, modules = Counter(), set()
    partial_rows, logical_references = [], {}
    for line in gzip.open(path, "rt"):
        row = json.loads(line)
        kind = row["record"]
        if kind == "declaration":
            name, owner = row["name"], row["module"]
            require(row["kind"] != "axiom", f"Original project axiom: {name} in {owner}")
            require(not row["unsafe"], f"Unsafe original project declaration: {name}")
            require(not row["partial"] or row["kind"] == "definition",
                    f"Partial flag on a non-definition: {name}")
            require(row["kind"] not in {"theorem", "definition", "opaque"} or row["has_body"],
                    f"Missing original project body: {name}")
            require(owner not in owners.setdefault(name, set()), f"Repeated occurrence: {name} in {owner}")
            if name in kinds:
                require(kinds[name] == row["kind"] == "theorem", f"Non-theorem collision: {name}")
            owners[name].add(owner)
            kinds[name] = row["kind"]
            modules.add(owner)
            counts[row["kind"]] += 1
            for field in ("type_dependencies", "body_dependencies", "structural_dependencies"):
                references.update(row[field])
                if not row["partial"]:
                    for dependency in row[field]:
                        logical_references.setdefault(dependency, (name, owner, field))
            if row["partial"]:
                partial_rows.append(row)
        elif kind == "boundary_declaration":
            name = row["name"]
            require(name not in boundary, f"Repeated boundary record: {name}")
            require(row["module_occurrences"], f"Missing boundary owner: {name}")
            boundary[name] = row
        elif kind == "compatible_theorem_occurrences":
            require(row["name"] not in compatible, "Repeated compatibility record")
            compatible[row["name"]] = row
        else:
            raise RuntimeError(f"Unknown declaration graph record: {kind}")
    require(sum(counts.values()) == manifest["project_declarations"], "Project occurrence count mismatch")
    require(len(owners) == manifest["distinct_project_declarations"], "Distinct project name count mismatch")
    require(len(boundary) == manifest["boundary_declarations_referenced"], "Boundary count mismatch")
    # Some source modules intentionally contain imports only and no declarations.
    require(len(modules) <= manifest["project_modules"], "More declaration owners than source modules")
    require(not (references - owners.keys() - boundary.keys()), "Unresolved full-body reference")
    # Lean emits efficient recursive implementation declarations alongside some
    # total definitions. They are not kernel proofs: the safe logical definition
    # instead uses recursors. Taking *every* safe project declaration as a root
    # makes this direct-edge check also a transitive separation check: any path
    # from such a root to a partial implementation has a first forbidden edge.
    # The check depends on artifact flags and actual references, not name suffixes.
    nonlogical = {row["name"] for row in partial_rows}
    nonlogical.update(name for name, row in boundary.items()
                      if row["unsafe"] or row["partial"])
    for name in sorted(nonlogical & logical_references.keys()):
        source, owner, field = logical_references[name]
        raise RuntimeError(f"Safe declaration {source} in {owner} references "
                           f"nonlogical implementation {name} through {field}")
    duplicated = {name: sorted(values) for name, values in owners.items() if len(values) > 1}
    for name, values in duplicated.items():
        row = compatible.get(name)
        require(row is not None, f"Missing compatibility evidence: {name}")
        actual = sorted(item["module"] for item in row["occurrences"] if item["scope"] == "project")
        require(actual == values, f"Incorrect project occurrences: {name}")
    occurrences = []
    if duplicated:
        for line in gzip.open(path, "rt"):
            row = json.loads(line)
            if row["record"] == "declaration" and row["name"] in duplicated:
                occurrences.append(row)
    return {"project_declaration_occurrences": sum(counts.values()),
            "distinct_project_declarations": len(owners), "declaration_kinds": dict(counts),
            "original_project_axioms": [], "unresolved_references": [],
            "isolated_partial_implementation_occurrences": partial_rows,
            "safe_declarations_referencing_nonlogical_implementations": [],
            "repeated_project_names": duplicated, "repeated_project_proof_rows": occurrences}, boundary


def audit_source(modules, names):
    imports = "\n".join(["module", "import Lean.Elab.BuiltinEvalCommand",
                           "meta import Lean.Elab.Command", "meta import Lean.Data.Json",
                           "meta import Lean.Util.CollectAxioms",
                           *("import all " + name for name in modules)])
    strings = ", ".join(json.dumps(name, ensure_ascii=False) for name in sorted(names))
    return imports + "\n\n" + r'''
open Lean in
run_cmd do
  let env ← getEnv
  if (← getOptions).getBool `debug.skipKernelTC false then
    throwError "Kernel checking is disabled"
  if env.header.trustLevel > 1 then
    throwError "Unexpected compiler trust level"
  let allowed : NameSet := NameSet.ofList [`propext, `Classical.choice, `Quot.sound]
  let mut remaining : Std.HashSet String := Std.HashSet.ofList [WANTED_NAMES]
  let mut count : Nat := 0
  for data in env.header.moduleData do
    for name in data.constNames do
      if remaining.contains name.toString then
        unless (env.find? name).isSome do
          throwError "Missing library declaration: {name}"
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "Unapproved library axiom {axiomName} in {name}"
        IO.println <| "BOUNDARY_AXIOMS_JSON: " ++ (Json.mkObj [
          ("name", toJson name.toString),
          ("axioms", toJson (axioms.map Name.toString))]).compress
        remaining := remaining.erase name.toString
        count := count + 1
  unless remaining.isEmpty do
    throwError "Some requested library names were not imported: {remaining.toList}"
  IO.println s!"BOUNDARY_AXIOM_AUDIT_OK: {count} declarations"
'''.replace("WANTED_NAMES", strings)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--export", type=Path, required=True)
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--allow-diagnostic", action="store_true")
    parser.add_argument("--batch-modules", type=int, default=32)
    parser.add_argument("--memory", type=int, default=4096)
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    require(1 <= args.batch_modules <= 64 and args.memory >= 1024 and args.timeout > 0,
            "Invalid bounded audit resource limits")
    root, export, output = args.project.resolve(), args.export.resolve(), args.output.resolve()
    verifier = load(root / "scripts/verify.py", "body_audit_verifier")
    exporter = load(root / "scripts/export_dependencies.py", "body_audit_exporter")
    manifest_path = export / "extraction-manifest.json"
    manifest = read(manifest_path)
    require(manifest.get("extraction_passed") is True, "A successful declaration export is required")
    complete = manifest.get("mode") == "complete-successful-build"
    require(complete or (args.allow_diagnostic and manifest.get("mode") == "accepted-subgraph-NON-FINAL"),
            "Final auditing requires a complete successful export")
    lock = (root / ".lake/build/verification/build.lock").open("a+")
    if complete:
        try:
            fcntl.flock(lock, fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError("A source build is active")
    index_path = root / "audit/source-index.json"
    index = read(index_path)
    require(manifest["source_index_sha256"] == sha(index_path), "Stale exported source index")
    if complete:
        entries = {entry["module"]: entry for entry in index["entries"]}
        result = read(root / ".lake/build/verification/result.json")
        exporter.validate_complete_build_result(result, entries, set(entries), verifier.FORMAT)
        require(result["external_environment"] == manifest["external_environment"], "Build/export environment mismatch")
        require(manifest["wrapper_sha256"] == sha(root / "scripts/export_dependencies.py")
                and manifest["exporter_sha256"] == sha(root / "scripts/ExportDependencies.lean"),
                "The completed export used different exporter code")
    graph_path = export / "declarations.jsonl.gz"
    require(sha(graph_path) == manifest["files"][graph_path.name], "Declaration graph bytes changed")
    graph_report, boundary = inspect_graph(graph_path, manifest)
    lean_name = shutil.which("lean")
    require(lean_name is not None, "Lean was not found")
    lean = Path(lean_name).resolve()
    require(verifier.run(str(lean), "--githash") == verifier.LEAN_COMMIT, "Wrong Lean commit")
    require(sha(lean) == manifest["compiler_sha256"], "Different Lean compiler bytes")
    mathlib = (args.mathlib or root / ".lake/packages/mathlib").resolve()
    paths, _, revisions, prefix, _ = verifier.library_environment(lean, mathlib, root)
    require(revisions == manifest["library_revisions"], "Different library revisions")
    identities = {str(manifest_path): sha(manifest_path), str(graph_path): sha(graph_path),
                  str(index_path): sha(index_path), str(lean): sha(lean),
                  str(Path(__file__).resolve()): sha(__file__)}
    # Bind the supplement to every input that produced the accepted export,
    # including project sources, receipts, full artifact facets and the final
    # build result. A graph detached from changed inputs is not current evidence.
    inputs_path = export / "verified-inputs.jsonl.gz"
    require(sha(inputs_path) == manifest["files"][inputs_path.name], "Exported input inventory changed")
    identities[str(inputs_path)] = sha(inputs_path)
    input_identities = 0
    for line in gzip.open(inputs_path, "rt"):
        item = json.loads(line)
        if item.get("record") == "identity":
            path, expected = item["path"], item["sha256"]
            require(path not in identities or identities[path] == expected,
                    f"Conflicting input identity: {path}")
            require(sha(path) == expected, f"An export input changed before the audit: {path}")
            identities[path] = expected
            input_identities += 1
    require(input_identities > 0, "The export has no authenticated input identities")
    environment = read(root / ".lake/build/verification/external-environment.json")
    environment_key = verifier.digest_json({key: value for key, value in environment.items()
                                            if key not in {"verifier_sha256", "import_parser_sha256"}})
    require(environment_key == manifest["external_environment"], "Current library artifact environment differs from export")
    require(verifier.artifact_inventory(paths) == environment["artifacts"],
            "The complete pinned library artifact inventory differs from the build")
    for path, expected in environment["artifacts"].items():
        identities[path] = expected
    require(not output.exists() or not any(output.iterdir()), "Output must be new or empty")
    output.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    for key in ("LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN_PLUGIN_PATH"):
        env.pop(key, None)
    env["PATH"] = str(prefix / "bin") + os.pathsep + env.get("PATH", "")
    by_module = {}
    for name, row in boundary.items():
        by_module.setdefault(sorted(row["module_occurrences"])[0], []).append(name)
    modules = sorted(by_module)
    reports, all_axioms = [], {}
    for start in range(0, len(modules), args.batch_modules):
        selected = modules[start:start + args.batch_modules]
        names = {name for module in selected for name in by_module[module]}
        source = output / f"BoundaryAudit{start // args.batch_modules:04d}.lean"
        log = source.with_suffix(".log")
        source.write_text(audit_source(selected, names))
        command = [str(lean), "-t1", "-j1", f"-M{args.memory}", "-DmaxHeartbeats=0",
                   "-DElab.async=false", "-Ddebug.skipKernelTC=false", str(source)]
        began = time.monotonic()
        with log.open("w") as stream:
            code = subprocess.run(command, env=env, stdout=stream, stderr=subprocess.STDOUT,
                                  timeout=args.timeout).returncode
        require(code == 0, f"Boundary audit failed; see {log}")
        found = {}
        for line in log.read_text().splitlines():
            if line.startswith("BOUNDARY_AXIOMS_JSON: "):
                row = json.loads(line.split(": ", 1)[1])
                require(row["name"] in names and row["name"] not in found,
                        "Unexpected or repeated boundary audit declaration")
                require(not set(row["axioms"]) - verifier.ALLOWED_AXIOMS, "Unapproved boundary axiom")
                found[row["name"]] = row["axioms"]
        require(set(found) == names, "Incomplete boundary-name audit")
        require(f"BOUNDARY_AXIOM_AUDIT_OK: {len(names)} declarations" in log.read_text(),
                "Missing boundary audit completion marker")
        all_axioms.update(found)
        reports.append({"modules": selected, "names": sorted(names), "command": command,
                        "seconds": round(time.monotonic() - began, 3),
                        "source_sha256": sha(source), "log_sha256": sha(log)})
        print(f"Boundary axioms: {len(all_axioms)}/{len(boundary)} declarations", flush=True)
    require(set(all_axioms) == set(boundary), "Incomplete total library boundary audit")
    for path, expected in identities.items():
        require(sha(path) == expected, f"Input changed during audit: {path}")
    verifier.library_environment(lean, mathlib, root)
    require(verifier.artifact_inventory(paths) == environment["artifacts"],
            "The library artifact inventory changed during the audit")
    report = {"passed": True, "mode": "complete" if complete else "diagnostic-NON-FINAL",
              "scope": "Original project declaration occurrences and referenced library logical names; not proof replay.",
              "source_index_sha256": sha(index_path), "extraction_manifest_sha256": sha(manifest_path),
              "script_sha256": sha(__file__), "graph": graph_report,
              "boundary_declarations": len(boundary), "boundary_axioms": all_axioms,
              "allowed_axioms": sorted(verifier.ALLOWED_AXIOMS), "batches": reports,
              "checked_inputs": identities, "created_unix": time.time()}
    verifier.write_json(output / "proof-body-audit.json", report)
    print(json.dumps({"passed": True, "mode": report["mode"],
                      "project_declaration_occurrences": graph_report["project_declaration_occurrences"],
                      "boundary_declarations": len(boundary)}))


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"Exported proof audit stopped: {error}")
        raise SystemExit(1)
