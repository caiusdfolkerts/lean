#!/usr/bin/env python3
"""Bounded real-Lean checks for the compiled dependency reader.

This compiles a few tiny proof fixtures, not any polytope enumeration.  It
checks byte-for-byte extraction equivalence, batched exact theorem equality,
and rejection of incompatible types, non-theorems, and missing artifact parts.
Run with the pinned Lean binary via --lean or with Lean on PATH.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

import verify


def run_checked(command, env, *, expected_error=None):
    began = time.monotonic()
    result = subprocess.run(command, env=env, capture_output=True, text=True, timeout=60)
    output = result.stdout + result.stderr
    if expected_error is None:
        if result.returncode:
            raise RuntimeError(f"Lean reader check failed ({result.returncode}):\n{output}")
    elif result.returncode == 0 or expected_error not in output:
        raise RuntimeError(f"Expected a closed failure containing {expected_error!r}:\n{output}")
    return time.monotonic() - began


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    executable = shutil.which(args.lean)
    if executable is None:
        parser.error("Lean was not found")
    lean = Path(executable).resolve()
    if subprocess.check_output([lean, "--githash"], text=True).strip() != verify.LEAN_COMMIT:
        raise RuntimeError("Use the exact pinned Lean compiler for the reader checks")
    source = Path(__file__).with_name("export_dependencies.lean")
    prefix = subprocess.check_output([lean, "--print-prefix"], text=True).strip()
    base_env = os.environ.copy()
    base_env["LEAN_PATH"] = str(Path(prefix) / "lib/lean")
    for key in ("LEAN_SRC_PATH", "LEAN_SYSROOT", "LEAN_PLUGIN_PATH"):
        base_env.pop(key, None)
    flags = [str(lean), "-t1", "-j1", "-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false"]
    results = {}
    with tempfile.TemporaryDirectory(prefix="lean-reader-check-") as temporary:
        root = Path(temporary)
        reader = root / "reader"
        reader.mkdir()
        results["compile_reader_seconds"] = run_checked(
            [*flags, "-R", str(source.parent), "-o", str(reader / "ExportDependencies.olean"), str(source)], base_env)
        runner = reader / "RunExport.lean"
        runner.write_text("import ExportDependencies\n")
        reader_env = dict(base_env, LEAN_PATH=str(reader) + os.pathsep + base_env["LEAN_PATH"])
        sources = {
            "A": "theorem shared : True := True.intro\ntheorem counted : 2 + 3 = 5 := rfl\n",
            "B": "theorem shared : True := True.intro\ntheorem counted : 2 + 3 = 5 := rfl\n",
            "C": "theorem shared : True := True.intro\ntheorem counted : 2 + 3 = 5 := rfl\n",
            "BadType": "theorem shared : False → False := fun h => h\n",
            "BadKind": "def shared : Nat := 1\n",
        }
        for name, body in sources.items():
            path = root / f"{name}.lean"
            path.write_text("module\npublic section\n" + body)
            run_checked([*flags, "-R", str(root), "-o", str(root / f"{name}.olean"), str(path)], base_env)

        inputs = root / "inputs.tsv"
        inputs.write_text("".join(f"project\t{name}\t{root / (name + '.olean')}\n" for name in ("A", "B", "C")))
        original, compiled = root / "source.jsonl", root / "compiled.jsonl"
        results["source_extraction_seconds"] = run_checked(
            [*flags, "--run", str(source), str(inputs), str(original)], base_env)
        results["compiled_extraction_seconds"] = run_checked(
            [*flags, "--run", str(runner), str(inputs), str(compiled)], reader_env)
        if original.read_bytes() != compiled.read_bytes():
            raise RuntimeError("Compiled reader changed the declaration export")
        results["identical_extraction_sha256"] = hashlib.sha256(compiled.read_bytes()).hexdigest()

        inputs.write_text("".join(f"{name}\t{root / (name + '.lean')}\n" for name in ("A", "B", "C")))
        run_checked([*flags, "--run", str(source), "source-imports", str(inputs), str(original)], base_env)
        run_checked([*flags, "--run", str(runner), "source-imports", str(inputs), str(compiled)], reader_env)
        if original.read_bytes() != compiled.read_bytes():
            raise RuntimeError("Compiled reader changed the source-import export")
        results["identical_header_export_sha256"] = hashlib.sha256(compiled.read_bytes()).hexdigest()

        rows = [f"compare\t{root / 'A.olean'}\t{root / (name + '.olean')}\tshared\tcounted\n"
                for name in ("B", "C")]
        expected = bytearray()
        seconds = 0.0
        for row in rows:
            inputs.write_text(row)
            seconds += run_checked([*flags, "--run", str(source), str(inputs), str(original)], base_env)
            expected.extend(original.read_bytes())
        results["separate_comparison_seconds"] = seconds
        inputs.write_text("".join(rows))
        results["separate_comparison_seconds"] = seconds
        results["batched_comparison_seconds"] = run_checked(
            [*flags, "--run", str(runner), str(inputs), str(compiled)], reader_env)
        if bytes(expected) != compiled.read_bytes():
            raise RuntimeError("Batched reader changed an exact theorem comparison")
        results["exact_comparisons"] = 4

        for name, error in (("BadType", "Incompatible repeated theorem"),
                            ("BadKind", "not a unique theorem")):
            inputs.write_text(f"compare\t{root / 'A.olean'}\t{root / (name + '.olean')}\tshared\n")
            run_checked([*flags, "--run", str(runner), str(inputs), str(compiled)], reader_env,
                        expected_error=error)
        (root / "A.olean.private").unlink()
        inputs.write_text(f"project\tA\t{root / 'A.olean'}\n")
        run_checked([*flags, "--run", str(runner), str(inputs), str(compiled)], reader_env,
                    expected_error="Incomplete ordered module facets")
        results["negative_checks"] = ["incompatible theorem type", "non-theorem collision", "missing private facet"]
    results["passed"] = True
    results["lean_commit"] = verify.LEAN_COMMIT
    results["reader_source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
