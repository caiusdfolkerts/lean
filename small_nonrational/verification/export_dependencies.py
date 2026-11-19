#!/usr/bin/env python3
"""Export a bounded, receipt-checked documentation graph from fresh Lean artifacts.

This is a syntactic reference graph, not proof replay or an independent kernel
check. Full mode requires the complete successful source build and axiom audit.
--accepted-subgraph is an explicitly non-final diagnostic mode. Library boundary
names are read from the pinned artifact closure, never guessed from namespaces.
"""
from __future__ import annotations

import argparse
import fcntl
import gzip
import importlib.util
import json
import os
from pathlib import Path
import shutil
import sqlite3
import subprocess
import sys
import time

LEAN_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
MATHLIB_COMMIT = "56a005855ea17e0b0958f73ec801ae140b0a1679"
FORMAT = "syntactic-declaration-graph-v1"
LOGICAL_FLAGS = ["-t1", "-j1", "-s65536", "-DmaxHeartbeats=0",
                 "-DElab.async=false", "-Ddebug.skipKernelTC=false"]
REFERENCE_FIELDS = ("type_dependencies", "body_dependencies", "structural_dependencies")
DISCLAIMER = (
    "Documentation of syntactic constant references, not proof replay, a new kernel check, "
    "or a minimal semantic dependency graph. Structural edges include legitimate inductive "
    "and constructor cycles. Compiler-only extraConstNames and executable IR references are "
    "excluded. The boundary is the pinned existing Lean/Mathlib library environment; its "
    "declaration bodies are not recursively exported. Repeated theorem occurrences "
    "are retained only after direct equality checks of their full types, universe parameters, "
    "names, and mutual-theorem groups, matching Lean's theorem/theorem import compatibility "
    "rule; their modules are listed explicitly and every project occurrence retains its "
    "own proof references. Fresh source compilation and the "
    "separate axiom audit remain the evidence for mathematical verification."
)


def comparison_batches(comparisons, bases, module_limit, byte_limit):
    """Group exact theorem comparisons while bounding unique mapped inputs.

    The Lean reader caches a module only for the lifetime of one batch.  All
    comparisons, including several with the same first owner, remain separate
    equality checks; this only shares artifact loading and process startup.
    """
    if module_limit < 1 or byte_limit < 1:
        raise ValueError("Theorem comparison batches need positive module and byte budgets")
    sizes = {}
    batch, modules, total = [], set(), 0
    for first_owner, other_owner, names in comparisons:
        if first_owner == other_owner or not names or len(names) != len(set(names)):
            raise RuntimeError("Invalid repeated-theorem comparison")
        pair = {first_owner, other_owner}
        if len(pair) > module_limit:
            raise RuntimeError("Repeated-theorem comparison exceeds --batch-modules")
        for name in pair:
            if name not in sizes:
                base = Path(bases[name])
                sizes[name] = sum(Path(str(base) + suffix).stat().st_size
                                  for suffix in ("", ".server", ".private")
                                  if Path(str(base) + suffix).is_file())
        if sum(sizes[name] for name in pair) > byte_limit:
            raise RuntimeError("Repeated-theorem comparison exceeds --batch-input-mib")
        incoming = pair - modules
        additional = sum(sizes[name] for name in incoming)
        if batch and (len(modules | pair) > module_limit or total + additional > byte_limit):
            yield batch, sorted(modules), total
            batch, modules, total = [], set(), 0
            incoming, additional = pair, sum(sizes[name] for name in pair)
        batch.append((first_owner, other_owner, names))
        modules.update(incoming)
        total += additional
    if batch:
        yield batch, sorted(modules), total


def validate_complete_build_result(result, entries, selected, index_hash, policy_hash, verifier):
    """Require exactly the requested closure, allowing redundant priority roots.

    Root order is a scheduling choice. Independently reconstruct the build's
    closure and require one successful axiom-audit occurrence of every module;
    neither an omitted branch nor a duplicated audit entry is acceptable.
    """
    roots = result.get("roots", [])
    if not roots or len(set(roots)) != len(roots):
        raise RuntimeError("Missing or duplicated source-build roots")
    actual, active, order = set(), set(), []

    def visit(name):
        if name in active or name not in entries:
            raise RuntimeError("Invalid source-build root/dependency closure")
        if name in actual:
            return
        active.add(name)
        for dep in entries[name]["imports"]:
            if dep in entries:
                visit(dep)
        active.remove(name)
        actual.add(name)
        order.append(name)

    for root in roots:
        visit(root)
    audit = result.get("closure_axiom_audit") or {}
    covered = audit.get("covered_modules", [])
    if (result.get("format") != verifier.FORMAT or result.get("passed") is not True
            or actual != selected
            or result.get("checked_modules") != len(selected)
            or result.get("total_modules") != len(selected)
            or result.get("failures") or result.get("blocked_modules")
            or result.get("changed_at_closeout")
            or audit.get("passed") is not True
            or covered != order):
        raise RuntimeError("Final mode requires the complete successful build and full closure axiom audit")
    binding = result.get("verification_binding") or {}
    if (binding.get("format") != verifier.FINAL_BINDING_FORMAT
            or binding.get("source_index_sha256") != index_hash
            or binding.get("axiom_policy_sha256") != policy_hash
            or not binding.get("accepted_receipts_sha256")):
        raise RuntimeError("Final mode requires a fresh closure audit bound to this source index and verifier")
    return order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--index", type=Path)
    parser.add_argument("--output", type=Path, required=True, help="A new, empty output directory")
    parser.add_argument("--accepted-subgraph", action="store_true",
                        help="NON-FINAL: export only the accepted closure of explicit --module roots")
    parser.add_argument("--module", action="append", help="Root for accepted-subgraph mode only")
    parser.add_argument("--batch-modules", type=int, default=8)
    parser.add_argument("--batch-input-mib", type=int, default=128,
                        help="Maximum total mapped artifact bytes in one process")
    parser.add_argument("--memory", type=int, default=2048, help="Lean heap cap in MiB per process")
    parser.add_argument("--timeout", type=int, default=300, help="Seconds per serial batch")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--memory-budget", type=int, default=49152)
    parser.add_argument("--compression-level", type=int, default=6)
    parser.add_argument("--retry-memory", type=int, default=0)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 32 or args.memory > args.memory_budget or not 0 <= args.retry_memory <= args.memory_budget or not 0 <= args.compression_level <= 9:
        parser.error("Export concurrency must fit the memory budget; compression must be 0-9")
    if not 1 <= args.batch_modules <= 64 or args.batch_input_mib < 1 or args.memory < 2048 or args.timeout < 1:
        parser.error("Use 1–64 modules per batch, positive input/time limits, and at least 2048 MiB")
    if args.accepted_subgraph != bool(args.module):
        parser.error("Explicit --module roots are required exactly in --accepted-subgraph mode")

    root = args.project.resolve()
    verifier_path = root / "scripts/verify.py"
    spec = importlib.util.spec_from_file_location("fresh_source_verifier", verifier_path)
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot load the reviewed source verifier's identity helpers")
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    if (verifier.LEAN_COMMIT, verifier.MATHLIB_COMMIT) != (LEAN_COMMIT, MATHLIB_COMMIT):
        raise RuntimeError("The source verifier and exporter disagree on the exact pins")
    hash_file, digest_json = verifier.hash_file, verifier.digest_json
    module_path = verifier.module_path
    identities = {}

    def remember(path, expected=None, *, measured=None):
        path = path.resolve()
        value = hash_file(path) if measured is None else measured
        if expected is not None and value != expected:
            raise RuntimeError(f"Identity mismatch: {path}")
        previous = identities.setdefault(str(path), value)
        if previous != value:
            raise RuntimeError(f"Input changed during extraction: {path}")
        return value

    def remember_json(path):
        value, checksum = verifier.read_json_identity(path)
        return value, remember(path, measured=checksum)

    lean_name = shutil.which(args.lean)
    if lean_name is None:
        raise RuntimeError("Pinned Lean executable was not found")
    lean = Path(lean_name).resolve()
    if verifier.run(str(lean), "--githash") != LEAN_COMMIT:
        raise RuntimeError("Wrong Lean compiler commit")
    compiler_hash = remember(lean)
    version = verifier.run(str(lean), "--version")
    mathlib = (args.mathlib or root / ".lake/packages/mathlib").resolve()
    external_paths, _, revisions, prefix, external_owners = verifier.library_environment(lean, mathlib, root)
    policy_hash = remember(verifier_path)
    exporter = Path(__file__).with_name("ExportDependencies.lean").resolve()
    remember(exporter)
    remember(Path(__file__))
    audits = root / ".lake/build/verification"
    build = root / ".lake/build/lib/lean"
    sources = root / "Sources"
    build_lock = (audits / "build.lock").open("a+")
    if not args.accepted_subgraph:
        try:
            fcntl.flock(build_lock, fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError("A source build is still active; final export requires a stable complete build")
    # Diagnostic mode may coexist with compilation of unrelated modules. Every
    # selected receipt and input byte is still rehashed at the end.
    origin_path = audits / "fresh-build-origin.json"
    origin, _ = remember_json(origin_path)
    if origin.get("format") != verifier.FORMAT or not origin.get("nonce"):
        raise RuntimeError("Missing fresh-build origin")
    index_path = args.index or root / "audit/source-index.json.gz"
    if args.index is None and not index_path.exists():
        index_path = root / "audit/source-index.json"
    index, index_hash = remember_json(index_path)
    entries = {}
    for entry in index["entries"]:
        if entry["module"] in entries:
            raise RuntimeError(f"Duplicate source owner: {entry['module']}")
        entries[entry["module"]] = entry
    roots = args.module or index.get("roots", [])
    if not roots or len(set(roots)) != len(roots):
        raise RuntimeError("Missing or duplicate export roots")
    selected, active, order = set(), set(), []

    def visit(name):
        if name in active:
            raise RuntimeError(f"Circular project import: {name}")
        if name in selected:
            return
        if name not in entries or name.split(".")[0] in verifier.LIBRARY_NAMESPACES:
            raise RuntimeError(f"Invalid project module: {name}")
        active.add(name)
        for dep in entries[name]["imports"]:
            if dep in entries:
                visit(dep)
            elif (sources / module_path(dep).with_suffix(".lean")).exists():
                raise RuntimeError(f"Project import missing from manifest: {dep}")
        active.remove(name)
        selected.add(name)
        order.append(name)

    for name in roots:
        visit(name)
    build_result = result_hash = None
    receipt_hashes = {}
    if not args.accepted_subgraph:
        result_path = audits / "result.json"
        build_result, result_hash = remember_json(result_path)
        audited_order = validate_complete_build_result(
            build_result, entries, selected, index_hash, policy_hash, verifier)
    environment_path = audits / "external-environment.json"
    environment, _ = remember_json(environment_path)
    environment_identity = {k: v for k, v in environment.items()
                            if k not in {"verifier_sha256", "import_parser_sha256"}}
    environment_key = digest_json(environment_identity)
    if (environment.get("lean") != version or environment.get("compiler_sha256") != compiler_hash
            or environment.get("revisions") != revisions):
        raise RuntimeError("Current compiler/library pins do not match the source-build environment")
    if build_result and (build_result.get("external_environment") != environment_key
                         or build_result.get("lean") != version
                         or build_result.get("library_revisions") != revisions):
        raise RuntimeError("The final build result names a different compiler/library environment")
    if not args.accepted_subgraph:
        # Full mode binds the report to every artifact in the successful build
        # environment, including executable IR and compiler-library support.
        # The diagnostic mode checks only the boundary facets actually read.
        for path, expected in environment["artifacts"].items():
            remember(Path(path), expected)
    native_toolchain = environment.get("native_toolchain", {})
    # The recorded environment contains the lexical native inventory. Rebuild
    # it at both ends to check alias paths as well as the bytes they resolve to.
    verifier.check_native_toolchain(prefix, native_toolchain)
    native_specs = {name: verifier.native_producer_spec(name, prefix, native_toolchain)
                    for name in selected if native_toolchain and name in verifier.NATIVE_PRODUCERS}
    native_dependencies = {}
    for name in order:
        ancestors = set()
        for dep in entries[name]["imports"]:
            ancestors.update(native_dependencies.get(dep, ()))
            if dep in native_specs:
                ancestors.add(dep)
        native_dependencies[name] = sorted(ancestors)

    old_environments = {}

    def receipt_environment(key):
        if key in old_environments:
            return
        path = audits / "environments" / (key + ".json")
        old, _ = remember_json(path)
        logical = {k: v for k, v in old.items() if k not in {"verifier_sha256", "import_parser_sha256"}}
        if key not in {digest_json(old), digest_json(logical)}:
            raise RuntimeError(f"Incorrect environment identity: {key}")
        if any(old.get(k) != environment.get(k) for k in ("lean", "compiler_sha256", "revisions")):
            raise RuntimeError("A receipt used different compiler/library pins")
        # Additional official cache files may have arrived since a receipt.
        # Every previously recorded artifact must still have the same identity.
        if any(environment["artifacts"].get(k) != v for k, v in old["artifacts"].items()):
            raise RuntimeError("A receipt's library artifact environment is incompatible")
        old_environments[key] = old

    records, artifact_maps, inputs, native_plugins = {}, {}, [], {}
    for name in order:
        source = sources / module_path(name).with_suffix(".lean")
        remember(source, entries[name]["source_sha256"])
        receipt_path = verifier.module_receipt_path(audits, name)
        record, receipt_hash = remember_json(receipt_path)
        receipt_hashes[name] = receipt_hash
        if (record.get("format") != verifier.FORMAT or record.get("module") != name
                or record.get("passed") is not True or record.get("exit_code") != 0
                or record.get("source_unchanged") is not True
                or record.get("dependencies_unchanged") is not True
                or record.get("unexpected_axioms")
                or set(record.get("reported_axioms", [])) - verifier.ALLOWED_AXIOMS
                or record.get("source_sha256") != entries[name]["source_sha256"]
                or record.get("created_unix", 0) < origin["created_unix"]):
            raise RuntimeError(f"Invalid accepted source-build receipt: {name}")
        command = record["command"]
        plugins = [native_plugins[dep] for dep in native_dependencies[name]]
        if (record.get("native_plugins", []) != plugins
                or (plugins and record.get("native_plugins_unchanged") is not True)):
            raise RuntimeError(f"Incorrect native producer plugin identities: {name}")
        logical_flags = LOGICAL_FLAGS + verifier.native_plugin_flags(plugins, root)
        flags = command[1:command.index("-R")]
        if ([flag for flag in flags if not flag.startswith("-M")] != logical_flags
                or len([flag for flag in flags if flag.startswith("-M")]) != 1
                or Path(command[0]).resolve() != lean
                or Path(command[command.index("-R") + 1]).resolve() != sources.resolve()
                or Path(command[-1]).resolve() != source.resolve()):
            raise RuntimeError(f"Unrecognized source-build command: {name}")
        tail = command[command.index("-R"):]
        spec = native_specs.get(name)
        if (len(tail) != (7 if spec is not None else 5) or tail[2] != "-o"
                or not Path(tail[3]).resolve().is_relative_to((audits / "staging").resolve())
                or Path(tail[3]).name != source.with_suffix(".olean").name):
            raise RuntimeError(f"Unexpected source-build output command: {name}")
        if spec is not None and (tail[4] != "-c"
                or Path(tail[5]) != Path(tail[3]).with_suffix(".c")):
            raise RuntimeError(f"Unexpected native code-generation command: {name}")
        receipt_environment(record["external_environment"])
        expected_dependencies = {dep: {"key": records[dep]["key"], "artifacts": artifact_maps[dep]}
                                 for dep in entries[name]["imports"] if dep in selected}
        if record["dependencies"] != expected_dependencies:
            raise RuntimeError(f"Receipt dependency identities disagree: {name}")
        key = verifier.source_fingerprint(record["source_sha256"], record["external_environment"],
                                          logical_flags, record["dependencies"], plugins, spec)
        if record["key"] != key:
            raise RuntimeError(f"Receipt fingerprint mismatch: {name}")
        base = build / module_path(name).with_suffix(".olean")
        permitted = {str(base.with_suffix(f).relative_to(root)) for f in verifier.FACETS}
        artifacts = {}
        for artifact in record["artifacts"]:
            path = artifact["path"]
            if path not in permitted or path in artifacts:
                raise RuntimeError(f"Unexpected or duplicate artifact in receipt: {name}: {path}")
            remember(root / path, artifact["sha256"])
            artifacts[path] = artifact["sha256"]
        if str(base.relative_to(root)) not in artifacts:
            raise RuntimeError(f"Receipt lacks a main artifact: {name}")
        for facet in verifier.FACETS:
            path = base.with_suffix(facet)
            if path.exists() != (str(path.relative_to(root)) in artifacts):
                raise RuntimeError(f"Unrecorded or missing artifact facet: {path}")
        native_artifacts = verifier.native_artifact_values(record, root, spec,
                                                           lambda path: remember(path))
        if spec is not None:
            path = f".lake/build/verification/native/{name}/lib{name}.so"
            native_plugins[name] = {"module": name, "path": path,
                                    "sha256": native_artifacts[path],
                                    "initializer": spec["initializer"]}
        records[name], artifact_maps[name] = record, artifacts
        inputs.append({"scope": "project", "module": name, "source_sha256": record["source_sha256"],
                       "receipt_sha256": receipt_hash, "receipt_key": key,
                       "artifacts": artifacts, "base": str(base),
                       "native_artifacts": native_artifacts, "native_plugins": plugins})

    if build_result:
        verifier.check_accepted_receipts(build_result["verification_binding"], audited_order, receipt_hashes)

    output = args.output.resolve()
    if output.exists() and any(output.iterdir()):
        raise RuntimeError("Output directory must be new or empty")
    output.mkdir(parents=True, exist_ok=True)
    batches_dir = output / "batches"
    batches_dir.mkdir()
    database = output / "declarations.sqlite3"
    db = sqlite3.connect(database)
    db.execute("PRAGMA cache_size=-16384")
    db.execute("CREATE TABLE declarations(name TEXT PRIMARY KEY, owner TEXT NOT NULL, scope TEXT NOT NULL, row TEXT NOT NULL)")
    db.execute("CREATE TABLE references_used(name TEXT PRIMARY KEY)")
    db.execute("CREATE TABLE repeated_theorems(name TEXT, first_owner TEXT, other_owner TEXT, "
               "first_scope TEXT, other_scope TEXT, "
               "PRIMARY KEY(name, other_owner))")
    graph_path = output / "declarations.jsonl.gz"
    graph = gzip.open(graph_path, "wt", encoding="utf-8", compresslevel=args.compression_level)
    env = os.environ.copy()
    # This reader imports only the pinned compiler's own implementation. It
    # never imports or evaluates project modules or their initialization code.
    env["LEAN_PATH"] = str(prefix / "lib/lean")
    env.pop("LEAN_SRC_PATH", None)
    env.pop("LEAN_SYSROOT", None)
    env.pop("LEAN_PLUGIN_PATH", None)
    env["PATH"] = str(prefix / "bin") + os.pathsep + env.get("PATH", "")

    # Compile this exact, hashed reader once. Re-running `lean --run` on its
    # full source would elaborate the same extraction code for every batch.
    # The runner imports only these freshly compiled tool artifacts and the
    # pinned compiler libraries, never any project module. All generated tool
    # bytes are included in the extraction's authenticated input inventory.
    reader_directory = output / "reader"
    reader_directory.mkdir()
    reader_artifact = reader_directory / "ExportDependencies.olean"
    reader_log = reader_directory / "compile.log"
    reader_command = [str(lean), "-t1", "-j1", f"-M{args.memory}", "-DElab.async=false",
                      "-Ddebug.skipKernelTC=false", "-R", str(exporter.parent),
                      "-o", str(reader_artifact), str(exporter)]
    memory_budget = verifier.LeanMemoryBudget(args.memory_budget, args.retry_memory)
    began = time.monotonic()
    reader_command, code = memory_budget.run(reader_command, env, reader_log, args.timeout)
    if code or not reader_artifact.is_file():
        raise RuntimeError(f"Fresh dependency-reader compilation failed; see {reader_log}")
    reader_facets = {}
    for suffix in verifier.FACETS:
        path = reader_artifact.with_suffix(suffix)
        if path.is_file():
            reader_facets[path.name] = remember(path)
    runner = reader_directory / "RunExport.lean"
    runner.write_text("import ExportDependencies\n")
    runner_hash = remember(runner)
    reader_log_hash = remember(reader_log)
    reader_files = set(reader_facets) | {runner.name, reader_log.name}

    def check_reader_inventory():
        actual = list(reader_directory.iterdir())
        if (any(not path.is_file() for path in actual)
                or {path.name for path in actual} != reader_files):
            raise RuntimeError("The private reader import directory contains unexpected inputs")

    check_reader_inventory()
    reader_build = {"command": reader_command, "seconds": round(time.monotonic() - began, 3),
                    "source_sha256": identities[str(exporter)], "artifacts": reader_facets,
                    "runner_sha256": runner_hash, "log_sha256": reader_log_hash}
    env["LEAN_PATH"] = str(reader_directory) + os.pathsep + env["LEAN_PATH"]

    # The manifest records written imports. Compiled metadata also contains
    # Lean's implicit Init import, except in a prelude module. Ask the pinned
    # parser for both forms instead of silently allowing an extra import.
    header_input = output / "source-imports.tsv"
    header_output = output / "source-imports.jsonl"
    header_log = output / "source-imports.log"
    header_input.write_text("".join(
        f"{name}\t{sources / module_path(name).with_suffix('.lean')}\n" for name in order))
    header_command = [str(lean), "-t1", "-j1", f"-M{args.memory}", "-DElab.async=false",
                      "-Ddebug.skipKernelTC=false", "--run", str(runner), "source-imports",
                      str(header_input), str(header_output)]
    with header_log.open("w") as stream:
        header_result = subprocess.run(header_command, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, timeout=args.timeout)
    if header_result.returncode:
        raise RuntimeError(f"Source import parsing failed; see {header_log}")
    source_headers = {}
    for line in header_output.read_text().splitlines():
        row = json.loads(line)
        name = row["module"]
        if (name not in selected or name in source_headers
                or row["path"] != str(sources / module_path(name).with_suffix(".lean"))
                or set(row["explicit_imports"]) != set(entries[name]["imports"])):
            raise RuntimeError(f"Source import parser disagrees with manifest: {name}")
        source_headers[name] = row
    if set(source_headers) != selected:
        raise RuntimeError("Incomplete effective source import coverage")
    header_check = {"command": header_command, "modules": len(source_headers),
                    "input_sha256": hash_file(header_input),
                    "output_sha256": hash_file(header_output), "log_sha256": hash_file(header_log)}
    batches, summaries, boundary_pending, boundary_seen = [], {}, set(), set()
    project_declarations = 0

    def external_input(name):
        if name in entries or (sources / module_path(name).with_suffix(".lean")).exists():
            raise RuntimeError(f"Project dependency was omitted from selected closure: {name}")
        rel = module_path(name).with_suffix(".olean")
        matches = [(path / rel).resolve() for path in external_paths if (path / rel).is_file()]
        if len(set(matches)) != 1:
            raise RuntimeError(f"Ambiguous or missing pinned library artifact: {name}")
        base = matches[0]
        if name.split(".")[0] in {"Init", "Lean", "Std", "Lake"}:
            owners = [(prefix / "lib/lean" / rel).resolve()]
            source_candidates = [prefix / "src/lean" / rel.with_suffix(".lean")]
            if name.split(".")[0] == "Lake":
                source_candidates.append(prefix / "src/lean/lake" / rel.with_suffix(".lean"))
            sources_found = {path.resolve() for path in source_candidates if path.is_file()}
            if len(sources_found) != 1:
                raise RuntimeError(f"No unique bundled runtime source for library module: {name}")
            source = sources_found.pop()
        else:
            owners = external_owners.get(name, [])
            # An owner is registered only from a clean pinned checkout's
            # tracked source list by library_environment.
            source = None
        if len(owners) != 1 or base != owners[0]:
            raise RuntimeError(f"No unique pinned source owner for library module: {name}")
        artifacts = {}
        for suffix in ("", ".server", ".private"):
            path = Path(str(base) + suffix)
            if path.is_file():
                expected = environment["artifacts"].get(str(path))
                if expected is None:
                    raise RuntimeError(f"Library facet absent from recorded build environment: {path}")
                artifacts[str(path)] = remember(path, expected)
        item = {"scope": "library_boundary", "module": name, "base": str(base), "artifacts": artifacts}
        if source is not None:
            item["runtime_source_sha256"] = remember(source)
        inputs.append(item)
        return item

    def chunks(items):
        batch, size = [], 0
        limit = args.batch_input_mib * 1024 * 1024
        for item in items:
            base = Path(item["base"])
            amount = sum(Path(str(base) + suffix).stat().st_size
                         for suffix in ("", ".server", ".private")
                         if Path(str(base) + suffix).is_file())
            if amount > limit:
                raise RuntimeError(f"Module exceeds mapped-input limit; explicitly raise --batch-input-mib: {item['module']}")
            if batch and (len(batch) >= args.batch_modules or size + amount > limit):
                yield batch, size
                batch, size = [], 0
            batch.append(item)
            size += amount
        if batch:
            yield batch, size

    def extract(items, mode):
        nonlocal project_declarations
        first_number = len(batches)

        def execute(task):
            index, (items_batch, mapped_bytes) = task
            number = first_number + index
            stem = batches_dir / f"{number:05d}"
            tsv, jsonl, log = (stem.with_suffix(s) for s in (".tsv", ".jsonl", ".log"))
            tsv.write_text("".join(f"{mode}\t{item['module']}\t{item['base']}\n" for item in items_batch))
            command = [str(lean), "-t1", "-j1", f"-M{args.memory}", "-DElab.async=false",
                       "-Ddebug.skipKernelTC=false", "--run", str(runner), str(tsv), str(jsonl)]
            started = time.monotonic()
            command, code = memory_budget.run(command, env, log, args.timeout)
            if code:
                raise RuntimeError(f"Extraction batch failed ({code}); see {log}")
            return number, items_batch, mapped_bytes, tsv, jsonl, log, command, started

        # Independent Lean readers run concurrently. All ownership, reference,
        # completeness and SQLite checks below remain ordered on the main thread.
        for item in verifier.bounded_parallel_map(execute, enumerate(chunks(items)), args.jobs):
            number, items_batch, mapped_bytes, tsv, jsonl, log, command, started = item
            expected = {item["module"] for item in items_batch}
            seen, counts = set(), {name: 0 for name in expected}
            with jsonl.open() as stream:
                for line in stream:
                    row = json.loads(line)
                    name = row["module"]
                    if name not in expected:
                        raise RuntimeError(f"Batch emitted an unexpected module: {name}")
                    if row["record"] == "module":
                        if name in seen or name in summaries or row["mode"] != mode:
                            raise RuntimeError(f"Duplicate or wrong module summary: {name}")
                        seen.add(name)
                        summaries[name] = row
                        if mode == "project" and (
                                set(row["imports"]) != set(source_headers[name]["effective_imports"])
                                or row["is_module"] != source_headers[name]["is_module"]):
                            raise RuntimeError(f"Compiled/effective-source import mismatch: {name}")
                        if mode == "boundary" and any(dep in entries for dep in row["imports"]):
                            raise RuntimeError(f"Pinned library module imports a project module: {name}")
                        for dep in row["imports"]:
                            if dep not in selected and dep not in boundary_seen:
                                boundary_pending.add(dep)
                    else:
                        if name not in seen:
                            raise RuntimeError("Declaration appeared before its module summary")
                        kind = "project" if mode == "project" else "library_boundary"
                        expected_record = "declaration" if mode == "project" else "boundary_declaration"
                        if row["record"] != expected_record:
                            raise RuntimeError("Incorrect declaration record type")
                        counts[name] += 1
                        try:
                            db.execute("INSERT INTO declarations VALUES (?, ?, ?, ?)",
                                       (row["name"], name, kind, line.strip()))
                        except sqlite3.IntegrityError:
                            owner, prior_scope, prior_row = db.execute(
                                "SELECT owner, scope, row FROM declarations WHERE name=?", (row["name"],)).fetchone()
                            if (owner == name or row["kind"] != "theorem"
                                    or json.loads(prior_row)["kind"] != "theorem"):
                                raise RuntimeError(f"Duplicate declaration owner: {row['name']}: {owner} and {name}")
                            # These are provisional occurrences, not accepted
                            # owners. Direct Lean type comparisons below must
                            # succeed before any output manifest is published.
                            db.execute("INSERT INTO repeated_theorems VALUES (?, ?, ?, ?, ?)",
                                       (row["name"], owner, name, prior_scope, kind))
                        if mode == "project":
                            if row["kind"] in {"theorem", "definition", "opaque"} and not row["has_body"]:
                                raise RuntimeError(f"Missing full declaration body: {row['name']}")
                            for field in REFERENCE_FIELDS:
                                db.executemany("INSERT OR IGNORE INTO references_used VALUES (?)",
                                               ((dep,) for dep in row[field]))
                            graph.write(line)
                            project_declarations += 1
            if seen != expected or any(counts[name] != summaries[name]["declarations"] for name in expected):
                raise RuntimeError("Incomplete batch declaration coverage")
            db.commit()
            batches.append({"number": number, "mode": mode, "modules": sorted(expected),
                            "mapped_input_bytes": mapped_bytes, "seconds": round(time.monotonic() - started, 3),
                            "command": command, "input_sha256": hash_file(tsv),
                            "output_sha256": hash_file(jsonl), "log_sha256": hash_file(log),
                            "declarations": sum(counts.values())})
            # Keep logs/input lists and checksums, but avoid retaining a second
            # uncompressed copy of the complete declaration graph.
            jsonl.unlink()
            print(f"Exported {mode} batch {number}: {len(expected)} modules, {sum(counts.values())} declarations", flush=True)

    extract(list(inputs), "project")
    while boundary_pending:
        names = sorted(boundary_pending - boundary_seen)
        boundary_pending.clear()
        if not names:
            break
        boundary_seen.update(names)
        extract([external_input(name) for name in names], "boundary")
    # Lean intentionally permits the same equational theorem to be generated
    # in several modules. Check the exact theorem/theorem compatibility branch
    # of its importer, and record all such theorem occurrences explicitly.
    bases = {item["module"]: Path(item["base"]) for item in inputs}
    repeated_count = 0
    pairs = list(db.execute("SELECT DISTINCT first_owner, other_owner FROM repeated_theorems ORDER BY 1, 2"))
    if pairs and args.batch_modules < 2:
        raise RuntimeError("Repeated-theorem comparisons require --batch-modules of at least two")
    first_comparison = len(batches)

    def comparison_inputs():
        for first_owner, other_owner in pairs:
            names = [row[0] for row in db.execute(
                "SELECT name FROM repeated_theorems WHERE first_owner=? AND other_owner=? ORDER BY name",
                (first_owner, other_owner))]
            yield first_owner, other_owner, names

    def compare(task):
        index, (comparisons, modules, mapped_bytes) = task
        number = first_comparison + index
        stem = batches_dir / f"{number:05d}"
        tsv, jsonl, log = (stem.with_suffix(s) for s in (".tsv", ".jsonl", ".log"))
        tsv.write_text("".join("\t".join(["compare", str(bases[left]), str(bases[right]), *names])
                               + "\n" for left, right, names in comparisons))
        command = [str(lean), "-t1", "-j1", f"-M{args.memory}", "-DElab.async=false",
                   "-Ddebug.skipKernelTC=false", "--run", str(runner), str(tsv), str(jsonl)]
        started = time.monotonic()
        command, code = memory_budget.run(command, env, log, args.timeout)
        if code:
            raise RuntimeError(f"Repeated-theorem compatibility check failed; see {log}")
        expected = [(name, str(bases[left]), str(bases[right]))
                    for left, right, names in comparisons for name in names]
        with jsonl.open() as stream:
            for name, left, right in expected:
                line = stream.readline()
                if not line:
                    raise RuntimeError("Incomplete repeated-theorem compatibility check")
                row = json.loads(line)
                if (row.get("record"), row.get("name"), row.get("left"), row.get("right")) != (
                        "compatible_theorem", name, left, right):
                    raise RuntimeError("Incorrect repeated-theorem compatibility check")
            if stream.readline():
                raise RuntimeError("Unexpected repeated-theorem compatibility row")
        return {"number": number, "mode": "theorem-compatibility",
                "modules": modules, "mapped_input_bytes": mapped_bytes,
                "seconds": round(time.monotonic() - started, 3), "command": command,
                "input_sha256": hash_file(tsv), "output_sha256": hash_file(jsonl),
                "log_sha256": hash_file(log), "repeated_theorems": len(expected),
                "comparison_pairs": len(comparisons)}

    tasks = enumerate(comparison_batches(comparison_inputs(), bases, args.batch_modules,
                                         args.batch_input_mib * 1024 * 1024))
    for report in verifier.bounded_parallel_map(compare, tasks, args.jobs):
        repeated_count += report["repeated_theorems"]
        batches.append(report)
        print(f"Checked theorem compatibility batch {report['number']}: {report['repeated_theorems']} repeated theorems", flush=True)
    missing = db.execute("SELECT r.name FROM references_used r LEFT JOIN declarations d ON d.name=r.name "
                         "WHERE d.name IS NULL ORDER BY r.name LIMIT 30").fetchall()
    if missing:
        raise RuntimeError(f"Unresolved declaration references (no verified project/library owner): {missing}")
    boundary_count = 0
    for row, in db.execute("SELECT d.row FROM declarations d JOIN references_used r ON d.name=r.name "
                           "WHERE d.scope='library_boundary' ORDER BY d.owner, d.name"):
        value = json.loads(row)
        occurrences = [value.pop("module"), *(r[0] for r in db.execute(
            "SELECT other_owner FROM repeated_theorems WHERE name=?", (value["name"],)))]
        value["module_occurrences"] = sorted(occurrences)
        graph.write(json.dumps(value, sort_keys=True) + "\n")
        boundary_count += 1
    # A theorem generated on demand may occur in several project modules.
    # Keep every occurrence's own body-reference row above, then make the
    # equivalent ownership explicit. References by logical name resolve to
    # these type-compatible occurrences, not to an arbitrarily chosen proof.
    for name, in db.execute("SELECT DISTINCT name FROM repeated_theorems ORDER BY name"):
        owner, scope = db.execute("SELECT owner, scope FROM declarations WHERE name=?", (name,)).fetchone()
        occurrences = [{"module": owner, "scope": scope}]
        occurrences.extend({"module": other, "scope": other_scope} for other, other_scope in db.execute(
            "SELECT other_owner, other_scope FROM repeated_theorems WHERE name=? ORDER BY other_owner", (name,)))
        graph.write(json.dumps({"record": "compatible_theorem_occurrences", "name": name,
                                "occurrences": sorted(occurrences, key=lambda item: item["module"])},
                               sort_keys=True) + "\n")
    graph.close()
    all_declarations = db.execute("SELECT COUNT(*) FROM declarations").fetchone()[0]
    distinct_project_declarations = db.execute(
        "SELECT COUNT(*) FROM declarations WHERE scope='project'").fetchone()[0]
    reference_targets = db.execute("SELECT COUNT(*) FROM references_used").fetchone()[0]
    db.close()
    # A successful extraction is published only after all recorded bytes have
    # been rehashed. This also catches concurrent changes in diagnostic mode.
    for path, expected in identities.items():
        if hash_file(path) != expected:
            raise RuntimeError(f"Input changed before extraction closeout: {path}")
    check_reader_inventory()
    verifier.library_environment(lean, mathlib, root)  # recheck pinned clean source checkouts
    verifier.check_native_toolchain(prefix, native_toolchain)
    input_path = output / "verified-inputs.jsonl.gz"
    with gzip.open(input_path, "wt", encoding="utf-8", compresslevel=args.compression_level) as stream:
        for item in inputs:
            stream.write(json.dumps(item, sort_keys=True) + "\n")
        for path, value in sorted(identities.items()):
            stream.write(json.dumps({"record": "identity", "path": path, "sha256": value}, sort_keys=True) + "\n")
    manifest = {"format": FORMAT, "extraction_passed": True,
                "mode": "accepted-subgraph-NON-FINAL" if args.accepted_subgraph else "complete-successful-build",
                "mathematical_verification_claim": False, "explanation": DISCLAIMER,
                "build_passed": build_result["passed"] if build_result else None,
                "build_result_sha256": result_hash,
                "verification_binding": build_result["verification_binding"] if build_result else None,
                "roots": roots, "project_modules": len(order), "library_boundary_modules": len(boundary_seen),
                "project_declarations": project_declarations, "boundary_declarations_referenced": boundary_count,
                "distinct_project_declarations": distinct_project_declarations,
                "compatible_repeated_theorem_occurrences": repeated_count,
                "all_boundary_and_project_names_indexed": all_declarations,
                "distinct_reference_targets": reference_targets, "unresolved_references": 0,
                "source_index_sha256": index_hash, "fresh_build_origin": origin,
                "lean_commit": LEAN_COMMIT, "compiler_sha256": compiler_hash, "library_revisions": revisions,
                "external_environment": environment_key,
                "exporter_sha256": identities[str(exporter)],
                "wrapper_sha256": identities[str(Path(__file__).resolve())],
                "reader_build": reader_build,
                "source_import_check": header_check,
                "batch_limits": {"modules": args.batch_modules, "mapped_input_mib": args.batch_input_mib,
                                 "lean_memory_mib": args.memory, "seconds": args.timeout, "processes": args.jobs, "memory_budget_mib": args.memory_budget, "retry_memory_mib": args.retry_memory},
                "batches": batches,
                "files": {graph_path.name: hash_file(graph_path), input_path.name: hash_file(input_path)},
                "created_unix": time.time()}
    verifier.write_json(output / "extraction-manifest.json", manifest)
    database.unlink()
    print(json.dumps({k: manifest[k] for k in ("mode", "extraction_passed", "project_modules",
                                              "project_declarations", "boundary_declarations_referenced")}, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, KeyError, subprocess.SubprocessError, sqlite3.Error) as exc:
        print(f"Dependency extraction stopped: {exc}", file=sys.stderr)
        raise SystemExit(1)
