#!/usr/bin/env python3
"""Compile a selected Lean source dependency graph with authenticated local receipts.

Python schedules ordinary Lean invocations; it proves no mathematical statement.
The compiler always checks new declarations with trust level one and kernel
checking enabled. Project artifacts from recovery archives are never imported.
"""
from __future__ import annotations

import argparse
import concurrent.futures
from collections import deque
from contextlib import contextmanager
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
FINAL_BINDING_FORMAT = "closure-audited-receipts-v1"
LIBRARY_NAMESPACES = {"Mathlib", "Init", "Lean", "Std", "Lake", "Batteries", "Qq",
                      "Aesop", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli"}
NATIVE_PRODUCERS = {"RupProofTerm": "initialize_RupProofTerm",
                    "FacetSatInitials": "initialize_FacetSatInitials",
                    "FacetSatFacts": "initialize_FacetSatFacts"}
NATIVE_FORMAT = "fresh-native-proof-producer-v1"


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


def read_json_identity(path):
    data = Path(path).read_bytes()
    return json.loads(gzip.decompress(data) if str(path).endswith(".gz") else data), digest(data)


def write_json(path, value, *, identify=False):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + "." + uuid.uuid4().hex + ".tmp")
    data = (json.dumps(value, indent=2) + "\n").encode("utf-8")
    temporary.write_bytes(data)
    temporary.replace(path)
    if identify:
        return digest(data)


def accepted_receipt_digest(order, receipt_hashes):
    # Each receipt hash covers its complete artifact and native producer inventory.
    return digest_json([(name, receipt_hashes[name]) for name in order])


def check_accepted_receipts(binding, order, receipt_hashes):
    if (receipt_hashes.keys() != set(order)
            or accepted_receipt_digest(order, receipt_hashes) != binding["accepted_receipts_sha256"]):
        raise RuntimeError("Current receipts differ from the successful closure axiom audit")


def module_path(name):
    parts = name.split(".")
    if any(not part or any(c in part for c in "/\\\n\r\0") for part in parts):
        raise ValueError(f"Invalid module name: {name!r}")
    return Path(*parts)


def module_receipt_path(audits, name):
    return audits / "modules" / module_path(name).with_suffix(".json")


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


def native_toolchain_inventory(prefix):
    """Bind native code generation to the bundled compiler, headers and libraries.

    Lean artifacts are already authenticated by artifact_inventory. The native
    driver also reads C headers, archives and its bundled sysroot, so include
    those inputs instead of trusting a system compiler or inherited flags.
    """
    prefix = Path(prefix).resolve()
    paths = {prefix / "bin" / name for name in ("leanc", "clang", "ld.lld")}
    for directory in (prefix / "include", prefix / "lib"):
        if not directory.is_dir():
            raise RuntimeError(f"Missing bundled native toolchain directory: {directory}")
        for path in directory.rglob("*"):
            if path.is_file() and not path.name.endswith(FACETS):
                resolved = path.resolve()
                if not resolved.is_relative_to(prefix):
                    raise RuntimeError(f"Native toolchain input escapes its pinned prefix: {path}")
                paths.add(path)
    values, resolved_hashes = {}, {}
    for path in sorted(paths):
        resolved = path.resolve()
        if not resolved.is_relative_to(prefix):
            raise RuntimeError(f"Native compiler input escapes its pinned prefix: {path}")
        if resolved not in resolved_hashes:
            resolved_hashes[resolved] = hash_file(resolved)
        values[str(path)] = resolved_hashes[resolved]
    return values


def check_native_toolchain(prefix, expected):
    if expected and native_toolchain_inventory(prefix) != expected:
        raise RuntimeError("The bundled native producer toolchain inventory changed")


def native_compile_environment(env):
    """Do not allow user compiler configuration to replace bundled inputs."""
    clean = dict(env)
    for key in ("LEAN_CC", "LEAN_CFLAGS", "LEAN_LDFLAGS", "CC", "CXX", "CFLAGS",
                "CPPFLAGS", "CXXFLAGS", "LDFLAGS", "LIBRARY_PATH", "CPATH",
                "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "OBJC_INCLUDE_PATH",
                "GCC_EXEC_PREFIX", "COMPILER_PATH", "LD_PRELOAD", "LD_LIBRARY_PATH",
                "SDKROOT", "MACOSX_DEPLOYMENT_TARGET", "LEAN_PLUGIN_PATH", "LEAN_SYSROOT"):
        clean.pop(key, None)
    for key in list(clean):
        if key.startswith(("CLANG_", "CCC_", "DYLD_")):
            clean.pop(key)
    return clean


def run_native_command(command, cwd, env, logfile, timeout):
    """Stop the compiler driver and its children together on a bounded timeout."""
    with Path(logfile).open("w") as log:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=log,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            return process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            return 124


def native_producer_spec(name, prefix, toolchain):
    if name not in NATIVE_PRODUCERS:
        raise RuntimeError(f"Native compilation is not permitted for module {name}")
    return {"format": NATIVE_FORMAT, "module": name,
            "initializer": NATIVE_PRODUCERS[name],
            "compiler": str(Path(prefix) / "bin/leanc"),
            "toolchain_sha256": digest_json(toolchain)}


def native_commands(spec, c_source, plugins=(), root=None):
    c_source = Path(c_source)
    obj = c_source.with_suffix(".o")
    library = c_source.with_name("lib" + spec["module"] + ".so")
    native_plugin_flags(plugins, root)
    dependencies = [str(Path(root) / plugin["path"]) for plugin in plugins]
    # Disable clang's implicit user/system configuration files. Its complete
    # bundled sysroot and the explicit arguments are authenticated above.
    return ([spec["compiler"], "--no-default-config", "-O3", "-DNDEBUG",
             "-DLEAN_EXPORTING", "-fPIC", "-c", "-o", str(obj), str(c_source)],
            [spec["compiler"], "--no-default-config", "-shared", "-o", str(library), str(obj),
             *dependencies])


def native_artifact_values(record, root, spec, hasher=hash_file):
    """Validate every fresh native input/output without admitting extra plugins."""
    producer = record.get("native_producer")
    if spec is None:
        if producer is not None:
            raise RuntimeError(f"Unexpected native producer receipt: {record['module']}")
        return {}
    if (producer is None or any(producer.get(key) != value for key, value in spec.items())
            or producer.get("source_sha256") != record.get("source_sha256")
            or producer.get("passed") is not True
            or producer.get("compile_exit_code") != 0 or producer.get("link_exit_code") != 0):
        raise RuntimeError(f"Missing or stale native producer receipt: {record['module']}")
    root = Path(root).resolve()
    name = spec["module"]
    directory = root / ".lake/build/verification/native" / name
    expected = {str((directory / filename).relative_to(root)) for filename in
                (name + ".c", name + ".o", "lib" + name + ".so", "compile.log", "link.log")}
    values = {}
    for artifact in producer.get("artifacts", []):
        relative = artifact["path"]
        path = root / relative
        if (relative not in expected or relative in values or path.is_symlink()
                or path.resolve() != directory / path.name):
            raise RuntimeError(f"Unexpected native artifact: {relative}")
        value = hasher(path)
        if value != artifact["sha256"]:
            raise RuntimeError(f"Changed native producer artifact: {path}")
        values[relative] = value
    if values.keys() != expected:
        raise RuntimeError(f"Incomplete native artifact inventory: {name}")
    if ({str(path.relative_to(root)) for path in directory.iterdir()} != expected
            or any(not path.is_file() for path in directory.iterdir())):
        raise RuntimeError(f"Unexpected native producer directory contents: {name}")
    command = record["command"]
    if command.count("-c") != 1:
        raise RuntimeError(f"Missing unique native code-generation output: {name}")
    c_source = Path(command[command.index("-c") + 1])
    if (c_source.name != name + ".c"
            or not c_source.resolve().is_relative_to(root / ".lake/build/verification/staging")
            or c_source.parent != Path(command[command.index("-o") + 1]).parent):
        raise RuntimeError(f"Unexpected native code-generation path: {name}")
    plugins = record.get("native_plugins", [])
    if any(plugin.get("module") == name for plugin in plugins):
        raise RuntimeError(f"Native producer links itself: {name}")
    compile_command, link_command = native_commands(spec, c_source, plugins, root)
    if (producer.get("compile_command") != compile_command
            or producer.get("link_command") != link_command):
        raise RuntimeError(f"Unrecognized native build commands: {name}")
    return values


def native_plugin(record, root, spec, hasher=hash_file):
    values = native_artifact_values(record, root, spec, hasher)
    name = spec["module"]
    path = f".lake/build/verification/native/{name}/lib{name}.so"
    return {"module": name, "path": path, "sha256": values[path],
            "initializer": spec["initializer"]}


def native_plugin_flags(plugins, root):
    names, flags = [], []
    for plugin in plugins:
        name = plugin.get("module")
        if (set(plugin) != {"module", "path", "sha256", "initializer"}
                or name not in NATIVE_PRODUCERS
                or plugin["initializer"] != NATIVE_PRODUCERS[name]
                or plugin["path"] != f".lake/build/verification/native/{name}/lib{name}.so"
                or not re.fullmatch(r"[0-9a-f]{64}", plugin["sha256"])):
            raise RuntimeError("Unrecognized native producer plugin")
        path = Path(root).resolve() / plugin["path"]
        if "=" in str(path):
            raise RuntimeError("The native plugin path cannot contain an equals sign")
        flags.append(f"--plugin={path}={plugin['initializer']}")
        names.append(name)
    if names != sorted(set(names)):
        raise RuntimeError("Native plugins must be unique and ordered")
    return flags


def source_fingerprint(source, environment, flags, dependencies, plugins=(), producer=None):
    payload = {"format": FORMAT, "source": source, "external_environment": environment,
               "flags": flags, "dependencies": dependencies}
    if plugins:
        payload["native_plugins"] = list(plugins)
    if producer is not None:
        payload["native_producer"] = producer
    return digest_json(payload)


def closure_axiom_batch(roots, modules, lean, flags, env, audits, timeout, memory_budget=None):
    """Ask Lean to audit every available declaration from the selected modules.

    Lean 4.35 records transitive axioms during module serialization. Every
    project artifact supplying those records was produced by this source build.
    Share Lean's traversal state across roots, as its own serializer does. This
    checks the union of reachable axioms, not separate per-declaration reports:
    any cached cycle contribution was already traversed from an earlier root,
    whose discovered axioms are also checked. All selected roots remain covered.
    """
    # Expose the selected modules' private declarations without exposing every
    # transitive dependency's private proof bodies. Every canonical source in
    # this project uses Lean 4.35's module system.
    imports = "\n".join(["module", "import Lean.Elab.BuiltinEvalCommand",
                          "meta import Lean.Elab.Command",
                          "meta import all Lean.Util.CollectAxioms",
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
  let privateEnv := env.setExporting false
  let axiomExtension := Lean.exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let mut axiomState : Lean.CollectAxioms.State := {}
  let mut count : Nat := 0
  for idx in [:moduleNames.size] do
    if project.contains moduleNames[idx]! then
      unless idx < axiomExtension.importedModuleEntries.size do
        throwError "Missing serialized axiom table for module {moduleNames[idx]!}"
      let ownAxioms := axiomExtension.importedModuleEntries[idx]!
      for name in env.header.moduleData[idx]!.constNames do
        unless (env.find? name).isSome do
          throwError "Missing declaration {name} from selected module {moduleNames[idx]!}"
        count := count + 1
        -- Imports can merge repeated theorem names. Inspect this occurrence's
        -- own serialized axioms before the ordinary environment traversal,
        -- which may resolve the name to another compatible occurrence.
        if let some (_, axioms) := ownAxioms.binSearch (name, #[])
            (fun a b => Name.quickLt a.1 b.1) then
          for axiomName in axioms do
            unless allowed.contains axiomName do
              throwError "Unapproved axiom {axiomName} in {name} from module {moduleNames[idx]!}"
        let (axioms, nextState) := ((Lean.CollectAxioms.collectAndGet axiomExtension.find? name).run privateEnv).run axiomState
        axiomState := nextState
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
    cap = int(next(flag[2:] for flag in flags if flag.startswith('-M')))
    budget = memory_budget or LeanMemoryBudget(cap)
    command, code = budget.run(command, env, log, timeout)
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


class LeanMemoryBudget:
    """Reserve compiler heap caps across concurrent processes and bounded retries."""
    def __init__(self, total, retry_memory=0):
        self.total = total
        self.available = total
        self.retry_memory = retry_memory
        self.condition = threading.Condition()

    @contextmanager
    def reserve(self, amount):
        if not 0 < amount <= self.total:
            raise ValueError("Compiler heap cap exceeds the total memory budget")
        with self.condition:
            self.condition.wait_for(lambda: self.available >= amount)
            self.available -= amount
        try:
            yield
        finally:
            with self.condition:
                self.available += amount
                self.condition.notify_all()

    def run(self, command, env, log, timeout):
        command = list(command)
        positions = [i for i, flag in enumerate(command) if flag.startswith('-M')]
        if len(positions) != 1:
            raise ValueError("Expected exactly one explicit compiler memory cap")
        position = positions[0]
        while True:
            memory = int(command[position][2:])
            with self.reserve(memory), log.open('w') as stream:
                try:
                    code = subprocess.run(command, env=env, stdout=stream,
                                          stderr=subprocess.STDOUT, timeout=timeout).returncode
                except subprocess.TimeoutExpired:
                    code = 124
            text = log.read_text(errors='replace')
            if (code not in (0, 124) and 'excessive memory consumption detected' in text
                    and memory < self.retry_memory <= self.total):
                shutil.copyfile(log, log.with_name(log.stem + f'.memory-{memory}.log'))
                command[position] = f'-M{self.retry_memory}'
                print(f'Retrying memory-limited audit with {self.retry_memory} MiB: {log}', flush=True)
                continue
            return command, code


def bounded_parallel_map(function, items, jobs):
    """Run independent tasks with bounded lookahead and deterministic output order."""
    if jobs < 1:
        raise ValueError("Concurrency must be positive")
    iterator = iter(items)
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        pending = deque()
        # A few queued batches keep workers busy when the next ordered result
        # is slower than its neighbours, without materialising every output.
        for _ in range(jobs * 4):
            try:
                item = next(iterator)
            except StopIteration:
                break
            pending.append(pool.submit(function, item))
        while pending:
            result = pending.popleft().result()
            try:
                item = next(iterator)
            except StopIteration:
                pass
            else:
                pending.append(pool.submit(function, item))
            yield result


def closure_axiom_audit(roots, modules, lean, flags, env, audits, timeout, jobs=1, memory_budget=None, retry_memory=0):
    """Cover every selected module in independently checked, bounded batches.

    Each batch imports the modules it audits, so their ordinary transitive
    dependencies remain available. Batching avoids importing unrelated branches
    into the same diagnostic environment. It does not replace any compilation.
    """
    modules = list(modules)
    if len(modules) != len(set(modules)) or not set(roots).issubset(modules):
        raise RuntimeError("Invalid module coverage for the closure axiom audit")
    if jobs < 1:
        raise RuntimeError("Invalid axiom audit concurrency")
    cap = int(next((flag[2:] for flag in flags if flag.startswith('-M')), '1'))
    budget = LeanMemoryBudget(memory_budget or jobs * cap, retry_memory)
    batches = []
    def check_batch(offset):
        selected = modules[offset:offset + 64]
        directory = audits / "axiom-batches" / f"{offset // 64:05d}"
        return closure_axiom_batch(selected, selected, lean, flags, env, directory, timeout, memory_budget=budget)
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        # Ordered consumption preserves exact coverage and reproducible reports,
        # although independent Lean processes may finish out of order.
        for result in pool.map(check_batch, range(0, len(modules), 64)):
            batches.append(result)
            print(f"Axiom audit: {min(len(batches) * 64, len(modules))}/{len(modules)} modules.", flush=True)
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
                        help="MiB per declaration-audit process")
    parser.add_argument("--audit-jobs", type=int, default=1,
                        help="Concurrent closure audit batches, bounded by the memory budget")
    parser.add_argument("--timeout", type=int, default=14400, help="Seconds per module")
    parser.add_argument("--fresh", action="store_true", help="Ignore this verifier's local receipts")
    parser.add_argument("--keep-going", action="store_true", help="Continue independent branches after a failure")
    parser.add_argument("--plan", action="store_true", help="Validate sources and print order without compiling")
    parser.add_argument("--audit-retry-memory", type=int, default=0)
    parser.add_argument("--no-native-producers", action="store_true",
                        help="Interpret proof producers instead of compiling fresh allowlisted native plugins")
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
            or memory_budget < largest_cap or args.timeout <= 0
            or not 1 <= args.audit_jobs <= 64
            or (args.audit_jobs > 1 and args.audit_memory > memory_budget)
            or not 0 <= args.audit_retry_memory <= max(memory_budget, args.audit_memory)):
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
    result_path = audits / "result.json"
    if not args.plan:
        # An interrupted attempt may leave reusable receipts, but no final success.
        result_path.unlink(missing_ok=True)
    policy_path = Path(__file__).resolve()
    policy_hash = hash_file(policy_path)

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
    index, index_hash = read_json_identity(index_path)
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
    native_names = set() if args.no_native_producers else selected & NATIVE_PRODUCERS.keys()
    native_dependencies = {}
    for name in order:
        ancestors = set()
        for dep in entries[name]["imports"]:
            ancestors.update(native_dependencies.get(dep, ()))
            if dep in native_names:
                ancestors.add(dep)
        native_dependencies[name] = sorted(ancestors)
        if name in native_names and any(dep in selected and dep not in native_names
                                        for dep in entries[name]["imports"]):
            raise RuntimeError(f"Native proof producer imports a non-producer project module: {name}")
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
        origin = {"format": FORMAT, "created_unix": time.time(), "nonce": uuid.uuid4().hex}
        write_json(marker, origin)
    else:
        origin = read_json(marker)
        if origin.get("format") != FORMAT or not origin.get("nonce"):
            raise RuntimeError("Unrecognized project artifact provenance")
    build.mkdir(parents=True, exist_ok=True)
    for namespace in LIBRARY_NAMESPACES:
        if (build / namespace).exists() or (build / (namespace + ".olean")).exists():
            raise RuntimeError(f"Project artifact tree shadows a library namespace: {namespace}")
    print("Hashing the pinned external import environment.", flush=True)
    external_artifacts = artifact_inventory(external_paths)
    environment = {"lean": version, "compiler_sha256": hash_file(lean),
                   "revisions": revisions, "artifacts": external_artifacts,
                   "verifier_sha256": policy_hash,
                   "import_parser_sha256": hash_file(root / "scripts/ParseImports.lean")}
    native_toolchain = native_toolchain_inventory(prefix) if native_names else {}
    native_specs = {name: native_producer_spec(name, prefix, native_toolchain)
                    for name in native_names}
    if native_names:
        environment["native_toolchain"] = native_toolchain
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
    completed, receipt_hashes, failures, running = {}, {}, {}, {}
    pending = set(order)

    def receipt_path(name):
        return module_receipt_path(audits, name)

    def artifact_values(record, force=False, check_facets=False):
        values = {}
        for artifact in record["artifacts"]:
            path = root / artifact["path"]
            value = hash_file(path) if force else hash_cache.get(path)
            if value != artifact["sha256"]:
                raise RuntimeError(f"Changed project artifact: {path}")
            values[artifact["path"]] = value
        if check_facets:
            base = build / module_path(record["module"]).with_suffix(".olean")
            actual = {str(base.with_suffix(facet).relative_to(root)) for facet in FACETS
                      if base.with_suffix(facet).exists()}
            if actual != values.keys() or len(record["artifacts"]) != len(values):
                raise RuntimeError(f"Project artifact facet inventory changed: {base}")
        native_artifact_values(record, root, native_specs.get(record["module"]),
                               hash_file if force else hash_cache.get)
        return values

    def plugins_for(name):
        return [native_plugin(completed[dep], root, native_specs[dep], hash_cache.get)
                for dep in native_dependencies[name]]

    def dependency_context(name):
        return {dep: {"key": completed[dep]["key"], "artifacts": artifact_values(completed[dep])}
                for dep in entries[name]["imports"] if dep in selected}

    def fingerprint(name, dependencies):
        plugins = plugins_for(name)
        return source_fingerprint(entries[name]["source_sha256"], environment_key,
                                  logical_flags + native_plugin_flags(plugins, root),
                                  dependencies, plugins, native_specs.get(name))

    def reusable(name, key, dependencies):
        path = receipt_path(name)
        if args.fresh or not path.is_file():
            return None
        try:
            record, receipt_hash = read_json_identity(path)
            if (record.get("format") != FORMAT or record.get("module") != name
                    or record.get("passed") is not True or record.get("exit_code") != 0
                    or record.get("source_unchanged") is not True
                    or record.get("dependencies_unchanged") is not True
                    or record.get("created_unix", 0) < origin["created_unix"]
                    or record.get("unexpected_axioms")
                    or set(record.get("reported_axioms", [])) - ALLOWED_AXIOMS):
                return None
            if record.get("source_sha256") != entries[name]["source_sha256"]:
                return None
            if record.get("external_environment") not in compatible_environments:
                return None
            plugins = plugins_for(name)
            if (record.get("native_plugins", []) != plugins
                    or (plugins and record.get("native_plugins_unchanged") is not True)):
                return None
            old_flags = record["command"][1:record["command"].index("-R")]
            expected_flags = logical_flags + native_plugin_flags(plugins, root)
            if [flag for flag in old_flags if not flag.startswith("-M")] != expected_flags:
                return None
            if set(record.get("dependencies", {})) != set(dependencies):
                return None
            if any(record["dependencies"][d]["artifacts"] != dependencies[d]["artifacts"] for d in dependencies):
                return None
            if not any(a["path"].endswith(".olean") for a in record.get("artifacts", [])):
                return None
            if record["key"] != source_fingerprint(
                    record["source_sha256"], record["external_environment"], expected_flags,
                    record["dependencies"], plugins, native_specs.get(name)):
                return None
            artifact_values(record, check_facets=True)
            if record["key"] != key:
                record["revalidated_from_key"] = record["key"]
                record["key"] = key
                record["dependencies"] = dependencies
                record["external_environment"] = environment_key
                receipt_hash = write_json(path, record, identify=True)
            return record, receipt_hash
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
        plugins = plugins_for(name)
        spec = native_specs.get(name)
        c_source = stage / (name + ".c") if spec is not None else None
        command = [str(lean), *module_flags, *native_plugin_flags(plugins, root),
                   "-R", str(sources), "-o", str(staged),
                   *(["-c", str(c_source)] if c_source is not None else []), str(source)]
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
        producer = None
        if passed and spec is not None:
            compile_command, link_command = native_commands(spec, c_source, plugins, root)
            producer = {**spec, "source_sha256": entries[name]["source_sha256"],
                        "compile_command": compile_command, "link_command": link_command,
                        "artifacts": [], "passed": False}
            if not c_source.is_file():
                passed = False
            else:
                native_env = native_compile_environment(env)
                for native_command, filename in ((compile_command, "compile.log"),
                                                  (link_command, "link.log")):
                    native_code = run_native_command(native_command, root, native_env,
                                                     stage / filename, args.timeout)
                    producer[filename.removesuffix(".log") + "_exit_code"] = native_code
                    if native_code:
                        passed = False
                        with logfile.open("a") as log:
                            log.write("\nNative producer build failure:\n")
                            log.write((stage / filename).read_text(errors="replace"))
                        print(f"Native producer compilation failed for {name}: "
                              + (stage / filename).read_text(errors="replace")[-6000:],
                              file=sys.stderr, flush=True)
                        break
                producer["passed"] = passed
        source_unchanged = hash_file(source) == entries[name]["source_sha256"]
        dependencies_unchanged = dependency_context(name) == dependencies
        plugins_unchanged = plugins_for(name) == plugins
        passed = passed and source_unchanged and dependencies_unchanged and plugins_unchanged
        record = {"format": FORMAT, "module": name, "key": key, "passed": passed,
                  "source_sha256": entries[name]["source_sha256"], "dependencies": dependencies,
                  "external_environment": environment_key, "exit_code": code,
                  "memory_limit_mib": memory_for(name),
                  "imports_mathlib": name in mathlib_dependent,
                  "seconds": round(time.monotonic() - started, 3), "command": command,
                  "reported_axioms": sorted(axioms), "unexpected_axioms": bad_axioms,
                  "source_unchanged": source_unchanged, "dependencies_unchanged": dependencies_unchanged,
                  "artifacts": [], "created_unix": time.time()}
        if plugins:
            record["native_plugins"] = plugins
            record["native_plugins_unchanged"] = plugins_unchanged
        if spec is not None:
            record["native_producer"] = producer
        if passed:
            if producer is not None:
                directory = audits / "native" / name
                if directory.resolve() != directory:
                    raise RuntimeError(f"Native producer output is redirected by a symlink: {directory}")
                directory.mkdir(parents=True, exist_ok=True)
                expected_native = {name + ".c", name + ".o", "lib" + name + ".so",
                                   "compile.log", "link.log"}
                if any(path.name not in expected_native or not path.is_file()
                       for path in directory.iterdir()):
                    raise RuntimeError(f"Unexpected file in native producer directory: {directory}")
                for filename in sorted(expected_native):
                    produced, target = stage / filename, directory / filename
                    value = hash_file(produced)
                    produced.replace(target)
                    producer["artifacts"].append({"path": str(target.relative_to(root)), "sha256": value})
                native_artifact_values(record, root, spec)
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
            if spec is not None:
                shutil.rmtree(audits / "native" / name, ignore_errors=True)
        receipt_hash = write_json(receipt_path(name), record, identify=True)
        shutil.rmtree(stage)
        if not passed:
            print(f"FAILED {name}\n{text[-6000:]}", file=sys.stderr, flush=True)
        return record, receipt_hash

    ready = ReadyModules(order, {name: entries[name]["imports"] for name in order},
                         memory_for, mathlib_dependent)

    def accept(name, record, receipt_hash):
        completed[name] = record
        receipt_hashes[name] = receipt_hash
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
                        accept(name, *previous)
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
                    record, receipt_hash = future.result()
                    if record["passed"]:
                        accept(name, record, receipt_hash)
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
        axiom_audit = closure_axiom_audit(roots, order, lean, audit_flags, env, audits, args.timeout, args.audit_jobs, max(memory_budget, args.audit_memory), args.audit_retry_memory)

    # Rehash accepted bytes without a stat cache at closeout.
    print("Rechecking source and artifact identities for closeout.", flush=True)
    changed = []
    for name, record in completed.items():
        if hash_file(source_path(name)) != entries[name]["source_sha256"]:
            changed.append(str(source_path(name)))
        try:
            artifact_values(record, force=True, check_facets=True)
            if hash_file(receipt_path(name)) != receipt_hashes[name]:
                changed.append(str(receipt_path(name)))
        except (OSError, RuntimeError) as exc:
            changed.append(str(exc))
    for path, expected in external_artifacts.items():
        if not Path(path).is_file() or hash_file(path) != expected:
            changed.append(path)
    try:
        check_native_toolchain(prefix, native_toolchain)
    except (OSError, RuntimeError) as exc:
        changed.append(str(exc))
    if hash_file(lean) != environment["compiler_sha256"]:
        changed.append(str(lean))
    for path, expected in ((index_path, index_hash), (policy_path, policy_hash)):
        if hash_file(path) != expected:
            changed.append(str(path))
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
                                  "native_producers": sorted(native_names),
                                  "audit_memory_mib": args.audit_memory, "audit_jobs": args.audit_jobs, "audit_retry_memory_mib": args.audit_retry_memory},
              "blocked_modules": sorted(pending), "changed_at_closeout": changed,
              "closure_axiom_audit": axiom_audit}
    if result["passed"]:
        result["verification_binding"] = {
            "format": FINAL_BINDING_FORMAT,
            "source_index_sha256": index_hash,
            "axiom_policy_sha256": policy_hash,
            "accepted_receipts_sha256": accepted_receipt_digest(order, receipt_hashes),
        }
    write_json(result_path, result)
    print(json.dumps(result, indent=2))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        print(f"Verification stopped: {exc}", file=sys.stderr)
        raise SystemExit(1)
