#!/usr/bin/env python3
"""Run the fixture on a separate Linux host with the pinned Elan toolchain."""
from __future__ import annotations

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import graphlib
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import time

root = Path(__file__).resolve().parent
fixture = json.loads((root / "fixture.json").read_text())
report_path = root / "benchmark-result.json"
foundational = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, cwd, limit, env=None, log=None):
    started = time.monotonic()
    proc = subprocess.run(args, cwd=cwd, timeout=limit, env=env,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if log:
        log.write_text(proc.stdout)
    proc.check_returncode()
    return round(time.monotonic() - started, 4), proc.stdout


def build_common(common, flags):
    graph = fixture["common_imports"]
    bundled = {name for deps in graph.values() for name in deps if name not in graph}
    if any(name.split(".", 1)[0] not in {"Init", "Lean", "Std"} for name in bundled):
        raise ValueError("bounded comparison requires only toolchain imports")
    order = graphlib.TopologicalSorter({m: [n for n in deps if n in graph]
                                        for m, deps in graph.items()})
    order.prepare()
    env = dict(os.environ, LEAN_PATH=str(common))
    started = time.monotonic()
    completed = 0
    tasks = {}

    def compile_module(module):
        path = Path(*module.split(".")).with_suffix(".lean")
        out = (root / "common-logs" / Path(*module.split("."))).with_suffix(".log")
        out.parent.mkdir(parents=True, exist_ok=True)
        return run([*flags, "-o", str(path.with_suffix(".olean")), str(path)],
                   common, 110, env, log=out)[0]

    with ThreadPoolExecutor(max_workers=2) as pool:
        while order.is_active():
            for module in order.get_ready():
                tasks[pool.submit(compile_module, module)] = module
            done, _ = wait(tasks, return_when=FIRST_COMPLETED)
            for job in done:
                module = tasks.pop(job)
                elapsed = job.result()
                order.done(module)
                completed += 1
                with (root / "shared-build.log").open("a") as log:
                    log.write(f"{module} {elapsed:.4f} s\n")
            if time.monotonic() - started > 560:
                raise TimeoutError("common dependency budget exceeded")
    assert completed == len(graph)
    return round(time.monotonic() - started, 4)


def main():
    if platform.system() != "Linux":
        raise SystemExit("This benchmark is for a separate Linux runner.")
    for relative, expected in fixture["sha256"].items():
        if sha(root / relative) != expected:
            raise ValueError(f"fixture hash mismatch: {relative}")
    common = root / "common"
    started = time.monotonic()
    receipt = {"host": platform.platform(), "cpu_count": os.cpu_count(),
               "fixture_sha256": sha(root / "fixture.json"), "samples": []}

    def save():
        receipt["elapsed_seconds"] = round(time.monotonic() - started, 3)
        report_path.write_text(json.dumps(receipt, indent=2) + "\n")

    try:
        _, version = run(["lean", "--version"], common, 25)
        receipt["lean"] = version.strip()
        _, lean = run(["elan", "which", "lean"], common, 25)
        flags = [lean.strip(), "-t1", "-j1", "-s65536", "-M3072",
                 "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DmaxHeartbeats=0"]
        shared_path = str(common)
        receipt["shared_build_seconds"] = build_common(common, flags)
        negative = common / 'RejectFalse.lean'
        negative.write_text('import CompactDecisionProof\nexample : (0 : Nat) = 1 := compact_decision_proof\n')
        reject = subprocess.run([*flags, negative.name], cwd=common,
            env=dict(os.environ, LEAN_PATH=str(common)), capture_output=True, text=True)
        output = reject.stdout + reject.stderr
        if reject.returncode == 0 or "error" not in output or "unknown" in output.lower():
            raise ValueError("negative decision proof did not fail for the expected reason: " + output)
        receipt["negative_test"] = output

        save()
        for group in fixture["groups"]:
            sample = dict(group, audit=None, timings={"before": [], "after": []})
            receipt["samples"].append(sample)
            location = root / "samples" / group["family"]
            stdout = {}
            for order in (("before", "after"), ("after", "before")):
                for mode in order:
                    directory = location / mode
                    env = dict(os.environ, LEAN_PATH=os.pathsep.join((str(directory), shared_path)))
                    times = {}
                    for module in group[mode]:
                        times[module] = run([*flags, "-o", module + ".olean", module + ".lean"],
                                            directory, 100, env, log=directory / (module + ".log"))[0]
                    audit_time, declarations = run([*flags, "Audit.lean"], directory, 90, env,
                                                   log=directory / "audit.log")
                    if mode in stdout and stdout[mode] != declarations:
                        raise ValueError("audit is not stable across repeats")
                    stdout[mode] = declarations
                    sample["timings"][mode].append({"module_seconds": times,
                                                    "sum_seconds": round(sum(times.values()), 4),
                                                    "audit_seconds": audit_time})
                    save()
            if stdout["before"] != stdout["after"]:
                raise ValueError("statement or axiom output differs")
            no_axioms = stdout["after"].count("does not depend on any axioms")
            with_axioms = re.findall(r"depends on axioms: \[([^\]]*)\]", stdout["after"])
            if no_axioms + len(with_axioms) != group["declarations"]:
                raise ValueError("did not observe one axiom report per declaration")
            printed_axioms = {x.strip() for item in with_axioms for x in item.split(",")}
            # pp.universes is enabled for the statement comparison. The
            # suffix is printer output, while the allowlist is by Lean name.
            axioms = {re.sub(r"\.\{[A-Za-z_0-9]+\}$", "", x) for x in printed_axioms}
            if axioms - foundational:
                raise ValueError(f"unexpected axioms: {sorted(axioms - foundational)}")
            sample["audit"] = {"comparison_equal": True, "axioms": sorted(axioms),
                               "printed_axioms": sorted(printed_axioms),
                               "stdout_sha256": hashlib.sha256(stdout["after"].encode()).hexdigest()}
            sample["median_seconds"] = {mode: statistics.median(t["sum_seconds"] for t in times)
                                         for mode, times in sample["timings"].items()}
            save()
        receipt["status"] = "pass"
    except Exception as error:
        receipt["status"] = "failed"
        receipt["error"] = str(error)
        raise
    finally:
        save()


if __name__ == "__main__":
    main()
