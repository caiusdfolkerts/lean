#!/usr/bin/env python3
"""Build this isolated fixture, time each arm, and check statements and axioms."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from graphlib import TopologicalSorter
from hashlib import sha256
import itertools
import json
import os
from pathlib import Path
import re
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def run(command, cwd, lean_paths, label, timeout=180):
    log = ROOT / "logs" / f"{label}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    stats = log.with_suffix(".time")
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, lean_paths)))
    start = time.monotonic()
    with log.open("w") as output:
        subprocess.run(["/usr/bin/time", "-f", "%e %U %S %M", "-o", str(stats), *command],
                       cwd=cwd, env=env, timeout=timeout, stdout=output,
                       stderr=subprocess.STDOUT, check=True)
    _, user, system, rss = stats.read_text().split()
    return {"wall_seconds": round(time.monotonic() - start, 5), "user_seconds": float(user),
            "system_seconds": float(system), "peak_rss_bytes": int(rss) * 1024}, log.read_text()


def audit(text, expected):
    matches = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
    axioms = {re.sub(r"\.\{[^}]*\}$", "", k.strip()) for v in matches for k in v.split(",")}
    if not axioms <= ALLOWED or len(matches) + text.count("does not depend on any axioms") != expected:
        raise ValueError(f"incomplete or unexpected axiom report: {text}")


def main():
    common = ROOT / "common"
    fixture_path = ROOT / "fixture.json"
    fixture = json.loads(fixture_path.read_text())
    for file, digest in fixture["sha256"].items():
        if sha256((ROOT / file).read_bytes()).hexdigest() != digest:
            raise ValueError(f"hash mismatch: {file}")
    lean = subprocess.check_output(["elan", "which", "lean"], cwd=common, text=True).strip()
    version = subprocess.check_output([lean, "--version"], cwd=common, text=True).strip()
    flags = [lean, "-t1", "-j1", "-s65536", "-M4096", "-DmaxHeartbeats=0",
             "-DElab.async=false", "-Ddebug.skipKernelTC=false"]
    receipt = {"fixture_sha256": sha256(fixture_path.read_bytes()).hexdigest(),
               "commit": os.environ.get("GITHUB_SHA"), "run_id": os.environ.get("GITHUB_RUN_ID"),
               "lean": version, "cpu_count": os.cpu_count(), "groups": {}, "common": {}}
    report = ROOT / "benchmark-result.json"

    def save():
        report.write_text(json.dumps(receipt, indent=2) + "\n")

    def build(module):
        path = Path(*module.split(".")).with_suffix(".lean")
        result, _ = run([*flags, "-o", str(path.with_suffix(".olean")), str(path)],
                        common, [common], f"common/{module}")
        return result

    graph = fixture["common_imports"]
    order = TopologicalSorter({m: set(ds) & graph.keys() for m, ds in graph.items()})
    order.prepare()
    save()
    with ThreadPoolExecutor(max_workers=4) as pool:
        while order.is_active():
            batch = sorted(order.get_ready())
            for name, result in zip(batch, pool.map(build, batch), strict=True):
                receipt["common"][name] = result
                order.done(name)
            save()
    variants = ("baseline", "hoisted", "indexed")
    for group, data in fixture["groups"].items():
        timings = {v: [] for v in variants}
        receipt["groups"][group] = {"records": data, "timings": timings}
        texts = {}
        for repeat, visit in enumerate((variants, variants[::-1], variants[1:] + variants[:1])):
            for variant in visit:
                cwd = ROOT / "samples" / group / variant
                prefix = f"{group}/{variant}/{repeat}"
                elapsed, _ = run([*flags, "-o", "Probe.olean", "Probe.lean"],
                                 cwd, [cwd, common], prefix)
                timings[variant].append(elapsed)
                save()
                if repeat == 0:
                    _, texts[variant] = run([*flags, "Audit.lean"], cwd, [cwd, common],
                                            f"{group}/{variant}/audit")
                    audit(texts[variant], len(data))
        if len(set(texts.values())) != 1:
            raise ValueError(f"statement or axiom parity failed for {group}")
        entry = receipt["groups"][group]
        entry["statement_and_axiom_parity"] = True
        entry["median_seconds"] = {v: statistics.median(s["wall_seconds"] for s in ts)
                                   for v, ts in timings.items()}
        print(group, entry["median_seconds"], flush=True)
        save()
    medians = {v: sum(x["median_seconds"][v] for x in receipt["groups"].values()) for v in variants}
    receipt["sum_of_group_medians_seconds"] = medians
    # Materiality threshold set before measurement. Prefer the cheapest arm
    # only if it is at least 10% faster over the full stratified fixture.
    fastest = min(variants, key=medians.get)
    receipt["preferred"] = fastest if medians[fastest] <= 0.9 * medians["baseline"] else "baseline"
    save()


if __name__ == "__main__":
    main()
