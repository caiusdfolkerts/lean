#!/usr/bin/env python3
"""Compile a selected Lean source dependency graph with authenticated local receipts.

Python schedules ordinary Lean invocations; it proves no mathematical statement.
The compiler always checks new declarations with trust level one and kernel
checking enabled. Project artifacts from recovery archives are never imported.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import fcntl
import gzip
import hashlib
import heapq
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
import uuid

LEAN_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
MATHLIB_COMMIT = "56a005855ea17e0b0958f73ec801ae140b0a1679"
FACETS = (".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORMAT = "fresh-source-verifier-v1"
LIBRARY_NAMESPACES = {"Mathlib", "Init", "Lean", "Std", "Lake", "Batteries", "Qq",
                      "Aesop", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def digest_json(value):
    return digest(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def hash_file(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_json(path):
    opener = gzip.open if str(path).endswith(".gz") else open
    with opener(path, "rt") as stream:
        return json.load(stream)


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def module_path(name):
    parts = name.split(".")
    if any(not part or any(c in part for c in "/\\\n\r\0") for part in parts):
        raise ValueError(f"Invalid module name: {name!r}")
    return Path(*parts)


def run(*command, **kwargs):
    return subprocess.check_output(command, text=True, **kwargs).strip()


def check_checkout(path, expected):
    actual = run("git", "-C", str(path), "rev-parse", "HEAD")
    if actual != expected:
        raise RuntimeError(f"Wrong source revision at {path}: {actual}")
    if run("git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"):
        raise RuntimeError(f"Modified tracked library source at {path}")


def dependency_checkouts(mathlib, manifest, project=None):
    """Select one pinned checkout per upstream package in either Lake layout.

    ``read_json`` and ``check_checkout`` are supplied by the reviewed verifier.
    Lake flattens a downstream workspace's dependencies into its own packages
    directory. A standalone Mathlib checkout instead keeps them below Mathlib.
    Resolved symlinks to the same directory are harmless; two distinct copies
    are rejected so source ownership and the import search path stay unique.
    """
    roots = [mathlib / manifest["packagesDir"]]
    upstream = manifest["packages"]
    if project is not None:
        workspace = read_json(project / "lake-manifest.json")
        locked = {}
        for package in workspace["packages"]:
            name = package["name"]
            if name in locked:
                raise RuntimeError(f"Duplicate workspace dependency: {name}")
            locked[name] = package
        for package in upstream:
            entry = locked.get(package["name"], {})
            if entry.get("type") != "git" or entry.get("rev") != package["rev"]:
                raise RuntimeError(f"Workspace dependency pin mismatch: {package['name']}")
        roots.insert(0, project / workspace["packagesDir"])
    seen = set()
    for package in upstream:
        name = package["name"]
        if package["type"] != "git":
            raise RuntimeError("Unpinned upstream dependency in Mathlib manifest")
        if name in seen:
            raise RuntimeError(f"Duplicate upstream dependency: {name}")
        seen.add(name)
        candidates = list(dict.fromkeys(
            (root / name).resolve() for root in roots if (root / name).is_dir()
        ))
        if len(candidates) != 1:
            raise RuntimeError(
                f"Expected one checkout for {name}, found {len(candidates)}: {candidates}"
            )
        directory = candidates[0]
        check_checkout(directory, package["rev"])
        yield name, directory, package["rev"]


def library_environment(lean, mathlib, project=None):
    """Construct paths from pinned checkouts, ignoring inherited LEAN_PATH."""
    check_checkout(mathlib, MATHLIB_COMMIT)
    manifest = read_json(mathlib / "lake-manifest.json")
    libraries = [(mathlib, mathlib / ".lake/build/lib/lean")]
    revisions = {"mathlib": MATHLIB_COMMIT}
    for name, directory, revision in dependency_checkouts(mathlib, manifest, project):
        libraries.append((directory, directory / ".lake/build/lib/lean"))
        revisions[name] = revision
    prefix = Path(run(str(lean), "--print-prefix")).resolve()
    paths = [compiled.resolve() for _, compiled in libraries]
    paths.append(prefix / "lib/lean")
    sources = [source.resolve() for source, _ in libraries]
    sources.append(prefix / "src/lean")
    owners = {}
    for source, compiled in libraries:
        tracked = run("git", "-C", str(source), "ls-files", "*.lean").splitlines()
        for filename in tracked:
            name = filename.removesuffix(".lean").replace("/", ".")
            owners.setdefault(name, []).append((compiled / filename).with_suffix(".olean").resolve())
    return paths, sources, revisions, prefix, owners


def artifact_inventory(paths):
    """Hash every available external import facet, including executable IR."""
    records = {}
    for root in paths:
        if not root.is_dir():
            continue  # A pinned package can be unused by the selected cache closure.
        for path in sorted(root.rglob("*")):
            if path.is_file() and path.name.endswith(FACETS + (".so", ".dylib")):
                records[str(path)] = hash_file(path)
    return records


def closure_axiom_batch(roots, modules, lean, flags, env, audits, timeout):
    """Ask Lean to audit every available declaration from the selected modules.

    Lean 4.35 records transitive axioms during module serialization. Every
    project artifact supplying those records was produced by this source build.
    """
    # Expose the selected modules' private declarations without exposing every
    # transitive dependency's private proof bodies. Every canonical source in
    # this project uses Lean 4.35's module system.
    imports = "\n".join(["module", "import Lean.Elab.BuiltinEvalCommand",
                          "meta import Lean.Elab.Command",
                          "meta import Lean.Util.CollectAxioms",
                          *("import all " + name for name in dict.fromkeys(roots))])
    names = ", ".join("`" + name for name in modules)
    source = imports + "\n\n" + """
open Lean in
run_cmd do
  let env ← getEnv
  if (← getOptions).getBool `debug.skipKernelTC false then
    throwError "Kernel checking is disabled"
  if env.header.trustLevel > 1 then
    throwError "Unexpected compiler trust level"
  let project : NameSet := NameSet.ofList [PROJECT_MODULES]
  let allowed : NameSet := NameSet.ofList [`propext, `Classical.choice, `Quot.sound]
  let moduleNames := env.header.moduleNames
  for name in project.toArray do
    unless moduleNames.contains name do
      throwError "Requested module is not imported: {name}"
  let mut count : Nat := 0
  for idx in [:moduleNames.size] do
    if project.contains moduleNames[idx]! then
      for name in env.header.moduleData[idx]!.constNames do
        unless (env.find? name).isSome do
          throwError "Missing declaration {name} from selected module {moduleNames[idx]!}"
        count := count + 1
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "Unapproved axiom {axiomName} in {name}"
  IO.println s!"CLOSURE_AXIOM_AUDIT_OK: {count} declarations"
""".replace("PROJECT_MODULES", names)
    audits.mkdir(parents=True, exist_ok=True)
    audit_source = audits / "ClosureAxiomAudit.lean"
    audit_source.write_text(source)
    log = audits / "closure-axioms.log"
    command = [str(lean), *flags, str(audit_source)]
    with log.open("w") as stream:
        try:
            code = subprocess.run(command, env=env, stdout=stream, stderr=subprocess.STDOUT,
                                  timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            code = 124
    text = log.read_text(errors="replace")
    match = re.search(r"CLOSURE_AXIOM_AUDIT_OK: (\d+) declarations", text)
    result = {"passed": code == 0 and match is not None, "exit_code": code,
              "modules": list(modules),
              "declarations": int(match.group(1)) if match else None,
              "source_sha256": hash_file(audit_source), "log_sha256": hash_file(log),
              "command": command}
    write_json(audits / "closure-axioms.json", result)
    if not result["passed"]:
        print(text[-6000:], file=sys.stderr)
    return result


def closure_axiom_audit(roots, modules, lean, flags, env, audits, timeout):
    """Cover every selected module in serial, bounded import batches.

    Each batch imports the modules it audits, so their ordinary transitive
    dependencies remain available. Batching avoids importing unrelated branches
    into the same diagnostic environment. It does not replace any compilation.
    """
    modules = list(modules)
    if len(modules) != len(set(modules)) or not set(roots).issubset(modules):
        raise RuntimeError("Invalid module coverage for the closure axiom audit")
    batches = []
    for offset in range(0, len(modules), 64):
        selected = modules[offset:offset + 64]
        directory = audits / "axiom-batches" / f"{offset // 64:05d}"
        result = closure_axiom_batch(selected, selected, lean, flags, env, directory, timeout)
        batches.append(result)
        print(f"Axiom audit: {min(offset + 64, len(modules))}/{len(modules)} modules.", flush=True)
        if not result["passed"]:
            break
    covered = [name for batch in batches for name in batch["modules"]]
    passed = covered == modules and all(batch["passed"] for batch in batches)
    result = {"passed": passed, "modules": modules, "covered_modules": covered,
              "declarations": sum(batch["declarations"] or 0 for batch in batches),
              "batches": batches}
    write_json(audits / "closure-axioms.json", result)
    return result


class ReadyModules:
    """Release a module only after each selected prerequisite was accepted.

    Small heaps partition ready modules by memory allowance and dependency
    class. Admission preserves the original topological-order priority among
    jobs that fit the available resources, without rescanning the source tree.
    """
    def __init__(self, order, imports, memory_for, heavy):
        self.rank = {name: rank for rank, name in enumerate(order)}
        if len(self.rank) != len(order):
            raise RuntimeError("Repeated module in scheduler order")
        self.memory_for, self.heavy = memory_for, heavy
        self.dependents = {name: [] for name in order}
        self.remaining, self.groups, self.accepted = {}, {}, set()
        for name in order:
            dependencies = set(imports[name]) & self.rank.keys()
            self.remaining[name] = len(dependencies)
            for dependency in dependencies:
                self.dependents[dependency].append(name)
        for name in order:
            if self.remaining[name] == 0:
                self._push(name)

    def _push(self, name):
        key = (self.memory_for(name), name in self.heavy)
        heapq.heappush(self.groups.setdefault(key, []), (self.rank[name], name))

    def pop_available(self, memory_free, heavy_slots):
        candidates = [(queue[0][0], key) for key, queue in self.groups.items()
                      if queue and key[0] <= memory_free and (not key[1] or heavy_slots > 0)]
        if not candidates:
            return None
        _, key = min(candidates)
        return heapq.heappop(self.groups[key])[1]

    def complete(self, name):
        if name in self.accepted or name not in self.rank:
            raise RuntimeError(f"Invalid scheduler completion: {name}")
        self.accepted.add(name)
        for dependent in self.dependents[name]:
            self.remaining[dependent] -= 1
            if self.remaining[dependent] == 0:
                self._push(dependent)


class HashCache:
    """Avoid rereading immutable artifacts between jobs; rehash all at closeout."""
    def __init__(self):
        self.records = {}
        self.lock = threading.Lock()

    def get(self, path):
        path = Path(path)
        st = path.stat()
        signature = (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)
        with self.lock:
            old = self.records.get(path)
            if old and old[0] == signature:
                return old[1]
        value = hash_file(path)
        with self.lock:
            self.records[path] = (signature, value)
        return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--mathlib", type=Path)
    parser.add_argument("--index", type=Path, help="Source manifest (default: audit/source-index.json[.gz])")
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--module", action="append", help="Root module (repeatable)")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--memory", type=int, default=1024, help="MiB per Lean process")
    parser.add_argument("--module-memory", action="append", default=[], metavar="MODULE=MIB",
                        help="Per-module memory allowance (repeatable; resource limits only)")
    parser.add_argument("--finite-memory", type=int,
                        help="MiB for modules whose project closure has no Mathlib imports")
    parser.add_argument("--heavy-jobs", type=int,
                        help="Maximum simultaneous modules whose closure imports Mathlib")
    parser.add_argument("--memory-budget", type=int,
                        help="Maximum sum of memory caps for simultaneous compiler processes")
    parser.add_argument("--audit-memory", type=int, default=4096,
                        help="MiB for each serial declaration-audit process")
    parser.add_argument("--timeout", type=int, default=14400, help="Seconds per module")
    parser.add_argument("--fresh", action="store_true", help="Ignore this verifier's local receipts")
    parser.add_argument("--keep-going", action="store_true", help="Continue independent branches after a failure")
    parser.add_argument("--plan", action="store_true", help="Validate sources and print order without compiling")
    args = parser.parse_args()
    memory_overrides = {}
    for setting in args.module_memory:
        name, separator, amount = setting.rpartition("=")
        try:
            cap = int(amount)
        except ValueError:
            parser.error(f"Invalid module memory allowance: {setting}")
        if not separator or not name or name in memory_overrides or cap < 128:
            parser.error(f"Invalid or repeated module memory allowance: {setting}")
        module_path(name)
        memory_overrides[name] = cap
    finite_memory = args.memory if args.finite_memory is None else args.finite_memory
    heavy_jobs = args.jobs if args.heavy_jobs is None else args.heavy_jobs
    largest_cap = max(args.memory, finite_memory, *memory_overrides.values())
    memory_budget = (args.jobs * largest_cap
                     if args.memory_budget is None else args.memory_budget)
    if (not 1 <= args.jobs <= 64 or not 1 <= heavy_jobs <= args.jobs
            or min(args.memory, finite_memory, args.audit_memory) < 128
            or memory_budget < largest_cap or args.timeout <= 0):
        parser.error("Use 1–64 jobs, valid heavy-job and memory limits, and a positive timeout")

    root = args.project.resolve()
    sources = root / "Sources"
    audits = root / ".lake/build/verification"
    build = root / ".lake/build/lib/lean"
    audits.mkdir(parents=True, exist_ok=True)
    lock = (audits / "build.lock").open("a+")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise RuntimeError("Another verifier is already using this project's build directory")

    lean_name = shutil.which(args.lean)
    if lean_name is None:
        raise RuntimeError("Lean not found; use the pinned runtime or `lake env`")
    lean = Path(lean_name).resolve()
    if run(str(lean), "--githash") != LEAN_COMMIT:
        raise RuntimeError("The Lean executable does not have the required exact commit")
    version = run(str(lean), "--version")
    mathlib = (args.mathlib or root / ".lake/packages/mathlib").resolve()
    external_paths, external_sources, revisions, prefix, external_owners = library_environment(lean, mathlib, root)

    index_path = args.index or root / "audit/source-index.json.gz"
    if not args.index and not index_path.exists():
        index_path = root / "audit/source-index.json"
    index = read_json(index_path)
    entries = {}
    for entry in index["entries"]:
        name = entry["module"]
        if name in entries:
            raise RuntimeError(f"Duplicate source-manifest module: {name}")
        entries[name] = entry
    roots = args.module or index.get("roots", [])
    if not roots:
        raise RuntimeError("Specify a root with --module or in the source manifest")
    selected, active, order = set(), set(), []
    external_imports = set()

    def source_path(name):
        return sources / module_path(name).with_suffix(".lean")

    def external_exists(name):
        rel = module_path(name).with_suffix(".olean")
        found = next(((path / rel).resolve() for path in external_paths if (path / rel).is_file()), None)
        if found is None:
            return False
        if name.split(".")[0] in {"Init", "Lean", "Std", "Lake"}:
            expected = [(prefix / "lib/lean" / rel).resolve()]
        else:
            expected = external_owners.get(name, [])
        if len(expected) != 1:
            raise RuntimeError(f"External module has ambiguous or missing pinned source ownership: {name}")
        if found not in expected:
            raise RuntimeError(f"External import has no matching pinned source owner: {name}: {found}")
        return True

    def visit(name):
        if name in active:
            raise RuntimeError(f"Circular project import at {name}")
        if name in selected:
            return
        if name not in entries:
            raise RuntimeError(f"Requested project module is absent: {name}")
        if name.split(".")[0] in LIBRARY_NAMESPACES:
            raise RuntimeError(f"Project manifest attempts to replace a pinned library module: {name}")
        path = source_path(name)
        if not path.is_file() or hash_file(path) != entries[name]["source_sha256"]:
            raise RuntimeError(f"Missing or changed canonical source: {name}")
        if external_exists(name):
            raise RuntimeError(f"Project module shadows a pinned library module: {name}")
        active.add(name)
        for dep in entries[name]["imports"]:
            if dep in entries:
                visit(dep)
            elif source_path(dep).exists():
                raise RuntimeError(f"Reachable source is omitted from the manifest: {dep}")
            elif external_exists(dep):
                external_imports.add(dep)
            else:
                raise RuntimeError(f"Missing reachable import {dep}, needed by {name}")
        active.remove(name)
        selected.add(name)
        order.append(name)

    for name in roots:
        visit(name)
    if set(memory_overrides) - selected:
        parser.error("Module memory overrides must belong to the selected source closure: "
                     + ", ".join(sorted(set(memory_overrides) - selected)))
    mathlib_dependent = set()
    for name in order:
        if any(dep == "Mathlib" or dep.startswith("Mathlib.") or dep in mathlib_dependent
               for dep in entries[name]["imports"]):
            mathlib_dependent.add(name)

    def memory_for(name):
        return memory_overrides.get(name, args.memory if name in mathlib_dependent else finite_memory)

    # Independently parse the selected headers using the pinned Lean parser.
    source_list = audits / "selected-sources.txt"
    source_list.write_text("".join(str(source_path(name)) + "\n" for name in order))
    parse_command = [str(lean), "-j1", "--run", str(root / "scripts/ParseImports.lean"), str(source_list)]
    parsed = subprocess.run(parse_command, text=True, capture_output=True)
    if parsed.returncode:
        raise RuntimeError("Lean import parser failed:\n" + parsed.stdout + parsed.stderr)
    actual = {row["path"]: row for line in parsed.stdout.splitlines() if line.strip()
              for row in [json.loads(line)]}
    for name in order:
        row = actual.get(str(source_path(name)))
        if row is None or row["errors"]:
            raise RuntimeError(f"Failed to parse imports of {name}: {row}")
        if set(row["imports"]) != set(entries[name]["imports"]):
            raise RuntimeError(f"Source-manifest import mismatch in {name}: {row['imports']}")

    plan = {"roots": roots, "order": order, "external_imports": sorted(external_imports)}
    write_json(audits / "plan.json", plan)
    print(f"Validated {len(order)} reachable source modules for {', '.join(roots)}.", flush=True)
    if args.plan:
        return 0

    # A marker prevents accidental use of a recovered project artifact tree.
    marker = audits / "fresh-build-origin.json"
    if not marker.exists():
        if build.exists() and any(build.rglob("*.olean")):
            raise RuntimeError("Refusing existing project artifacts without a fresh-build origin")
        write_json(marker, {"format": FORMAT, "created_unix": time.time(), "nonce": uuid.uuid4().hex})
    elif read_json(marker).get("format") != FORMAT:
        raise RuntimeError("Unrecognized project artifact provenance")
    build.mkdir(parents=True, exist_ok=True)
    for namespace in LIBRARY_NAMESPACES:
        if (build / namespace).exists() or (build / (namespace + ".olean")).exists():
            raise RuntimeError(f"Project artifact tree shadows a library namespace: {namespace}")
    print("Hashing the pinned external import environment.", flush=True)
    external_artifacts = artifact_inventory(external_paths)
    environment = {"lean": version, "compiler_sha256": hash_file(lean),
                   "revisions": revisions, "artifacts": external_artifacts,
                   "verifier_sha256": hash_file(Path(__file__).resolve()),
                   "import_parser_sha256": hash_file(root / "scripts/ParseImports.lean")}
    environment_identity = {k: v for k, v in environment.items()
                            if k not in {"verifier_sha256", "import_parser_sha256"}}
    environment_key = digest_json(environment_identity)
    # Resource-only flag changes and additions of unrelated official cache files
    # do not invalidate already checked proofs. Previously read external bytes
    # must still match exactly, and import ownership is checked above.
    environment_directory = audits / "environments"
    previous_environments = list(environment_directory.glob("*.json"))
    if (audits / "external-environment.json").is_file():
        previous_environments.append(audits / "external-environment.json")
    compatible_environments = {environment_key}
    for path in previous_environments:
        old = read_json(path)
        same_pin = all(old.get(k) == environment.get(k) for k in ("lean", "compiler_sha256", "revisions"))
        same_bytes = all(external_artifacts.get(k) == v for k, v in old.get("artifacts", {}).items())
        if same_pin and same_bytes:
            compatible_environments.add(digest_json(old))
            compatible_environments.add(digest_json({k: v for k, v in old.items()
                                        if k not in {"verifier_sha256", "import_parser_sha256"}}))
            write_json(environment_directory / (digest_json(old) + ".json"), old)
    write_json(environment_directory / (environment_key + ".json"), environment)
    write_json(audits / "external-environment.json", environment)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, [build, *external_paths]))
    env["LEAN_SRC_PATH"] = os.pathsep.join(map(str, [sources, *external_sources]))
    env["PATH"] = str(prefix / "bin") + os.pathsep + env.get("PATH", "")
    for key in ("LEAN_SYSROOT", "LEAN_PLUGIN_PATH"):
        env.pop(key, None)
    flags = ["-t1", "-j1", "-s65536", f"-M{args.memory}", "-DmaxHeartbeats=0",
             "-DElab.async=false", "-Ddebug.skipKernelTC=false"]
    logical_flags = [flag for flag in flags if not flag.startswith("-M")]
    hash_cache = HashCache()
    completed, failures, running = {}, {}, {}
    pending = set(order)

    def receipt_path(name):
        return audits / "modules" / module_path(name).with_suffix(".json")

    def artifact_values(record, force=False):
        values = {}
        for artifact in record["artifacts"]:
            path = root / artifact["path"]
            value = hash_file(path) if force else hash_cache.get(path)
            if value != artifact["sha256"]:
                raise RuntimeError(f"Changed project artifact: {path}")
            values[artifact["path"]] = value
        return values

    def dependency_context(name):
        return {dep: {"key": completed[dep]["key"], "artifacts": artifact_values(completed[dep])}
                for dep in entries[name]["imports"] if dep in selected}

    def fingerprint(name, dependencies):
        return digest_json({"format": FORMAT, "source": entries[name]["source_sha256"],
                            "external_environment": environment_key, "flags": logical_flags,
                            "dependencies": dependencies})

    def reusable(name, key, dependencies):
        path = receipt_path(name)
        if args.fresh or not path.is_file():
            return None
        try:
            record = read_json(path)
            if record.get("format") != FORMAT or record.get("passed") is not True:
                return None
            if record.get("source_sha256") != entries[name]["source_sha256"]:
                return None
            if record.get("external_environment") not in compatible_environments:
                return None
            old_flags = record["command"][1:record["command"].index("-R")]
            if [flag for flag in old_flags if not flag.startswith("-M")] != logical_flags:
                return None
            if set(record.get("dependencies", {})) != set(dependencies):
                return None
            if any(record["dependencies"][d]["artifacts"] != dependencies[d]["artifacts"] for d in dependencies):
                return None
            if not any(a["path"].endswith(".olean") for a in record.get("artifacts", [])):
                return None
            artifact_values(record)
            if record["key"] != key:
                record["revalidated_from_key"] = record["key"]
                record["key"] = key
                record["dependencies"] = dependencies
                record["external_environment"] = environment_key
                write_json(path, record)
            return record
        except (ValueError, KeyError, OSError, RuntimeError):
            return None

    def compile_one(name, key, dependencies):
        source = source_path(name)
        if hash_cache.get(source) != entries[name]["source_sha256"]:
            raise RuntimeError(f"Source changed before compilation: {name}")
        output = build / module_path(name).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        stage = audits / "staging" / uuid.uuid4().hex
        stage.mkdir(parents=True)
        staged = stage / output.name
        logfile = receipt_path(name).with_suffix(".log")
        logfile.parent.mkdir(parents=True, exist_ok=True)
        module_flags = [f"-M{memory_for(name)}" if flag.startswith("-M") else flag for flag in flags]
        command = [str(lean), *module_flags, "-R", str(sources), "-o", str(staged), str(source)]
        started = time.monotonic()
        with logfile.open("w") as log:
            try:
                result = subprocess.run(command, cwd=root, env=env, stdout=log,
                                        stderr=subprocess.STDOUT, timeout=args.timeout)
                code = result.returncode
            except subprocess.TimeoutExpired:
                code = 124
        text = logfile.read_text(errors="replace")
        axioms = {a.strip() for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", text)
                  for a in group.split(",") if a.strip()}
        bad_axioms = sorted(axioms - ALLOWED_AXIOMS)
        passed = (code == 0 and staged.is_file() and not bad_axioms
                  and not re.search(r"sorryAx|declaration uses [^\n]*sorry|PANIC", text))
        source_unchanged = hash_file(source) == entries[name]["source_sha256"]
        dependencies_unchanged = dependency_context(name) == dependencies
        passed = passed and source_unchanged and dependencies_unchanged
        record = {"format": FORMAT, "module": name, "key": key, "passed": passed,
                  "source_sha256": entries[name]["source_sha256"], "dependencies": dependencies,
                  "external_environment": environment_key, "exit_code": code,
                  "memory_limit_mib": memory_for(name),
                  "imports_mathlib": name in mathlib_dependent,
                  "seconds": round(time.monotonic() - started, 3), "command": command,
                  "reported_axioms": sorted(axioms), "unexpected_axioms": bad_axioms,
                  "source_unchanged": source_unchanged, "dependencies_unchanged": dependencies_unchanged,
                  "artifacts": [], "created_unix": time.time()}
        if passed:
            # Publish the main olean last. Dependents are scheduled only after receipt completion.
            for facet in (*FACETS[1:], FACETS[0]):
                target = output.with_suffix(facet)
                produced = staged.with_suffix(facet)
                if produced.is_file():
                    value = hash_file(produced)
                    produced.replace(target)
                    record["artifacts"].append({"path": str(target.relative_to(root)), "sha256": value})
                elif target.exists():
                    target.unlink()
        else:
            # Remove obsolete outputs from this verifier so failed modules cannot be imported.
            for facet in FACETS:
                output.with_suffix(facet).unlink(missing_ok=True)
        write_json(receipt_path(name), record)
        shutil.rmtree(stage)
        if not passed:
            print(f"FAILED {name}\n{text[-6000:]}", file=sys.stderr, flush=True)
        return record

    ready = ReadyModules(order, {name: entries[name]["imports"] for name in order},
                         memory_for, mathlib_dependent)

    def accept(name, record):
        completed[name] = record
        ready.complete(name)

    # A requested stop drains ordinary Lean invocations and preserves their
    # receipts. It never marks the uncompiled remainder as verified.
    stop_requested = threading.Event()
    previous_interrupt = signal.getsignal(signal.SIGINT)
    signal.signal(signal.SIGINT, lambda _signum, _frame: stop_requested.set())
    print(f"Checking with at most {args.jobs} Lean processes; finite cap {finite_memory} MiB, "
          f"Mathlib-dependent cap {args.memory} MiB, at most {heavy_jobs} heavier jobs, "
          f"total reserved caps {memory_budget} MiB.", flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        while pending or running:
            if not stop_requested.is_set() and (not failures or args.keep_going):
                reserved = sum(memory_for(name) for name in running.values())
                heavier = sum(name in mathlib_dependent for name in running.values())
                while len(running) < args.jobs:
                    name = ready.pop_available(memory_budget - reserved, heavy_jobs - heavier)
                    if name is None:
                        break
                    if name not in pending:
                        raise RuntimeError(f"Repeated ready module: {name}")
                    dependencies = dependency_context(name)
                    key = fingerprint(name, dependencies)
                    previous = reusable(name, key, dependencies)
                    pending.remove(name)
                    if previous:
                        accept(name, previous)
                    else:
                        running[executor.submit(compile_one, name, key, dependencies)] = name
                        reserved += memory_for(name)
                        heavier += name in mathlib_dependent
            if not running:
                break
            done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                try:
                    record = future.result()
                    if record["passed"]:
                        accept(name, record)
                        print(f"[{len(completed)}/{len(order)}] {name} ({record['seconds']:.1f}s)", flush=True)
                    else:
                        failures[name] = {"receipt": str(receipt_path(name))}
                except Exception as exc:
                    failures[name] = {"error": str(exc)}
            write_json(audits / "progress.json", {"roots": roots, "completed": len(completed),
                       "total": len(order), "running": list(running.values()), "failures": failures})
    signal.signal(signal.SIGINT, previous_interrupt)

    axiom_audit = None
    if not failures and not pending and len(completed) == len(order):
        print("Auditing transitive axioms of all selected project declarations.", flush=True)
        audit_flags = [f"-M{args.audit_memory}" if flag.startswith("-M") else flag for flag in flags]
        axiom_audit = closure_axiom_audit(roots, order, lean, audit_flags, env, audits, args.timeout)

    # Rehash accepted bytes without a stat cache at closeout.
    print("Rechecking source and artifact identities for closeout.", flush=True)
    changed = []
    for name, record in completed.items():
        if hash_file(source_path(name)) != entries[name]["source_sha256"]:
            changed.append(str(source_path(name)))
        try:
            artifact_values(record, force=True)
        except (OSError, RuntimeError) as exc:
            changed.append(str(exc))
    for path, expected in external_artifacts.items():
        if not Path(path).is_file() or hash_file(path) != expected:
            changed.append(path)
    if hash_file(lean) != environment["compiler_sha256"]:
        changed.append(str(lean))
    result = {"format": FORMAT, "passed": (not failures and not pending and not changed
                                             and len(completed) == len(order)
                                             and axiom_audit is not None and axiom_audit["passed"]),
              "roots": roots, "lean": version, "library_revisions": revisions,
              "external_environment": environment_key, "checked_modules": len(completed),
              "total_modules": len(order), "failures": failures,
              "stop_requested": stop_requested.is_set(),
              "resource_limits": {"jobs": args.jobs, "finite_memory_mib": finite_memory,
                                  "mathlib_memory_mib": args.memory, "heavy_jobs": heavy_jobs,
                                  "reserved_memory_budget_mib": memory_budget,
                                  "module_memory_overrides_mib": memory_overrides,
                                  "audit_memory_mib": args.audit_memory},
              "blocked_modules": sorted(pending), "changed_at_closeout": changed,
              "closure_axiom_audit": axiom_audit}
    write_json(audits / "result.json", result)
    print(json.dumps(result, indent=2))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        print(f"Verification stopped: {exc}", file=sys.stderr)
        raise SystemExit(1)
