#!/usr/bin/env python3
"""Run the fixture on a separate Linux host with the pinned Elan toolchain."""
from __future__ import annotations

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
        receipt["dependency_seconds"] = run(
            ["lake", "exe", "cache", "get", *fixture["mathlib_imports"]],
            common, 420, log=root / "dependency-cache.log"
        )[0]
        receipt["shared_build_seconds"] = run(
            ["lake", "build", *["+" + m for m in fixture["common_targets"]]],
            common, 560, log=root / "shared-build.log"
        )[0]
        _, path = run(["lake", "env", "printenv", "LEAN_PATH"], common, 25)
        shared_path = os.pathsep.join(str((common / value).resolve())
                                      for value in path.strip().split(os.pathsep) if value)
        _, lean = run(["elan", "which", "lean"], common, 25)
        flags = [lean.strip(), "-t1", "-j1", "-s65536", "-M3072",
                 "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DmaxHeartbeats=0"]
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
            axioms = {x.strip() for item in with_axioms for x in item.split(",")}
            if axioms - foundational:
                raise ValueError(f"unexpected axioms: {sorted(axioms - foundational)}")
            sample["audit"] = {"comparison_equal": True, "axioms": sorted(axioms),
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
