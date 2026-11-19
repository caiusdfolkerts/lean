"""Check the locked B078 inputs and compare projection proof variants on Linux CI."""
import argparse
import graphlib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

from prepare import optimize

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "diagnostic/manifest.json"
BATCH = "Batches.B078"
IMPORT = re.compile(r"^(?:public )?(?:meta )?import (?:all )?(\S+)\s*$", re.M)
KERNEL_OPTIONS = ["-t1", "-j1", "-s65536", "-M4096", "-DmaxHeartbeats=0",
                  "-DElab.async=false", "-Ddebug.skipKernelTC=false"]


def read_json(path):
    return json.loads(path.read_text())


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def inputs():
    manifest = read_json(MANIFEST)
    assert (ROOT / "lean-toolchain").read_text().strip() == manifest["lean"]
    mathlib = next(p for p in read_json(ROOT / "lake-manifest.json")["packages"]
                   if p["name"] == "mathlib")
    assert mathlib["rev"] == manifest["mathlib"]
    for name, pinned in manifest["files"].items():
        path = ROOT / name
        assert path.stat().st_size == pinned["bytes"] and digest(path) == pinned["sha256"], name
    original = manifest["variants"]["baseline"]
    modules = original["modules"]
    source = (ROOT / modules[BATCH]).read_text()
    variants = {
        "baseline": source,
        "incidence_first": optimize(source, numeric_priority=False)[0],
        "optimized": optimize(source)[0],
    }
    external, graphs = set(), []
    for name, variant in variants.items():
        edges = {}
        for module, path in modules.items():
            data = variant if module == BATCH else (ROOT / path).read_text()
            imports = set(IMPORT.findall(data))
            edges[module] = sorted(imports & modules.keys())
            external.update(imports - modules.keys())
        graphs.append(edges)
        assert manifest["endpoint"] == BATCH
        remaining = [BATCH]
        reached = set()
        while remaining:
            module = remaining.pop()
            if module not in reached:
                reached.add(module)
                remaining.extend(edges[module])
        assert reached == modules.keys(), name
    assert all(graph == graphs[0] for graph in graphs)
    ordered = list(graphlib.TopologicalSorter(graphs[0]).static_order())
    return manifest, variants, ordered, sorted(n for n in external if n.startswith("Mathlib."))


def tail(path, n=8000):
    with path.open("rb") as stream:
        stream.seek(max(0, path.stat().st_size - n))
        return stream.read().decode(errors="replace")


class Comparison:
    def __init__(self, scratch, manifest):
        self.scratch = scratch
        self.target = manifest["theorem"]
        self.endpoint = manifest["endpoint"]
        self.target_type = manifest["type"]
        self.bin_dir = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin"
        self.lean = self.bin_dir / "lean"
        dependency_path = os.environ["LEAN_PATH"].split(os.pathsep)
        self.dependency_path = [str(Path(p).resolve()) for p in dependency_path if p]
        results = ROOT / "diagnostic-results"
        results.mkdir(exist_ok=True)
        self.path = results / "projection-speed.json"
        self.report = {
            "status": "running", "stage": "setup", "commit": os.environ["GITHUB_SHA"],
            "run_id": os.environ["GITHUB_RUN_ID"], "manifest_sha256": digest(MANIFEST),
            "mathlib": manifest["mathlib"], "target": self.target, "theorem_type": self.target_type,
            "modules": {}, "checks": {}, "exports": {}, "kernels": {},
        }
        self.save("setup")
        self.report["toolchain"] = subprocess.check_output([self.lean, "--version"], text=True).strip()
        assert re.search(r"\b4\.35\.0\b", self.report["toolchain"])
        self.report["tools"] = {t: digest(self.bin_dir / t)
                                for t in ("lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron")}

    def save(self, stage):
        self.report["stage"] = stage
        temp = self.path.with_suffix(".tmp")
        temp.write_text(json.dumps(self.report, indent=2, sort_keys=True) + "\n")
        temp.replace(self.path)

    def location(self, variant):
        return self.scratch / variant / "src", self.scratch / variant / "build"

    def measure(self, variant, label, args, output=None):
        self.save(f"{variant}.{label}")
        src, build = self.location(variant)
        _, common_build = self.location("common")
        search = ([str(common_build)] if variant == "common" else [str(build), str(common_build)])
        env = dict(os.environ, LEAN_ABORT_ON_PANIC="1",
                   LEAN_PATH=os.pathsep.join([*search, *self.dependency_path]),
                   PATH=str(self.bin_dir) + os.pathsep + os.environ["PATH"])
        times = self.scratch / "measure.time"
        log = self.scratch / "measure.log"
        command = ["/usr/bin/time", "-f", "%U %S %M", "-o", times, *args]
        start = time.monotonic()
        with log.open("wb") as err:
            if output is None:
                result = subprocess.run(command, env=env, cwd=src, stdout=err, stderr=subprocess.STDOUT)
            else:
                with output.open("wb") as out:
                    result = subprocess.run(command, env=env, cwd=src, stdout=out, stderr=err)
        elapsed = round(time.monotonic() - start, 3)
        user, system, rss = times.read_text().splitlines()[-1].split()
        return {
            "exit_code": result.returncode, "wall_seconds": elapsed, "user_seconds": float(user),
            "system_seconds": float(system), "peak_rss_bytes": int(rss) * 1024, "output_tail": tail(log),
        }

    def build(self, variant, module):
        src, build = self.location(variant)
        rel = Path(*module.split(".")).with_suffix(".lean")
        out = build / rel.with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        metric = self.measure(variant, module, [self.lean, *KERNEL_OPTIONS, "-o", out, rel])
        self.report["modules"].setdefault(variant, {})[module] = metric
        if metric["exit_code"]:
            raise RuntimeError(metric["output_tail"])
        metric["source_sha256"] = digest(src / rel)
        metric["all_olean_bytes"] = sum(p.stat().st_size for p in out.parent.glob(out.name + "*"))
        self.save(f"{variant}.{module}")
        if variant != "common":
            print(variant, module, metric, flush=True)

    def replay(self, variant):
        from lean_export_reader import AXIOMS, PRIMITIVES, export_measurements

        src, _ = self.location(variant)
        audit = src / "CheckProjection.lean"
        audit.write_text(f"module\nimport {self.endpoint}\nexample : {self.target_type} := {self.target}\n")
        checks = self.measure(variant, "exact_theorem_type", [self.lean, *KERNEL_OPTIONS, audit.name])
        self.report["checks"][variant] = checks
        if checks["exit_code"]:
            raise RuntimeError(checks["output_tail"])
        export = self.scratch / f"{variant}.ndjson"
        export_metrics = self.measure(
            variant, "export", [self.bin_dir / "leanexport", self.endpoint, "--", self.target, *PRIMITIVES],
            export,
        )
        self.report["exports"][variant] = {"phase": export_metrics}
        if export_metrics["exit_code"]:
            raise RuntimeError(export_metrics["output_tail"])
        stats = export_measurements(export, self.target)
        if set(stats["axioms"]) != set(AXIOMS):
            raise RuntimeError(f"Unexpected axiom footprint in {variant}: {stats['axioms']}")
        self.report["exports"][variant].update(stats)
        cfg = self.scratch / "nanoda.json"
        cfg.write_text(json.dumps({
            "use_stdin": False, "export_file_path": str(export), "permitted_axioms": AXIOMS,
            "unpermitted_axiom_hard_error": True, "num_threads": 1,
            "nat_extension": True, "string_extension": True,
        }))
        commands = {
            "leanchecker": [self.bin_dir / "leanchecker", "--silent", "--from-export", export],
            "nanoda": [self.bin_dir / "nanoda_bin", cfg],
            "con-ron": [self.bin_dir / "con-ron", "--jobs=1", "--verified", export],
        }
        kernels = self.report["kernels"].setdefault(variant, {})
        for label, argv in commands.items():
            metric = self.measure(variant, label, ["timeout", "--kill-after=15s", "480s", *argv])
            accepted = metric["exit_code"] == 0
            if label == "con-ron":
                accepted = accepted and bool(re.search(
                    r"^con-ron: accepted [0-9]+ declarations \(--verified\)(?: t=[0-9.]+s)?$",
                    metric["output_tail"], re.M,
                ))
            metric["accepted"] = accepted
            kernels[label] = metric
            print(variant, label, metric, flush=True)
            self.save(f"{variant}.{label}")
        export.unlink()

    def run(self, manifest, variants, ordered):
        original = manifest["variants"]["baseline"]
        for variant in ("common", *variants):
            src, build = self.location(variant)
            build.mkdir(parents=True)
            if variant == "common":
                for rel, pinned in original["paths"].items():
                    if rel == "Batches/B078.lean":
                        continue
                    dest = src / rel
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(ROOT / pinned, dest)
            else:
                dest = src / "Batches/B078.lean"
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_text(variants[variant])
        for module in ordered:
            if module != BATCH:
                self.build("common", module)
        for variant in variants:
            self.build(variant, BATCH)
        for variant in variants:
            self.replay(variant)
        accepted = all(metric["accepted"] for replay in self.report["kernels"].values()
                       for metric in replay.values())
        self.report["status"] = "pass" if accepted else "kernel_failure"
        self.save("completed")
        return accepted


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--external", action="store_true")
    parser.add_argument("--run", action="store_true")
    args = parser.parse_args()
    manifest, variants, ordered, external = inputs()
    if args.external:
        print(" ".join(external))
        return
    print(f"Verified {len(ordered) - 1} shared prerequisites and {len(variants)} B078 sources", flush=True)
    if not args.run:
        return
    with tempfile.TemporaryDirectory(prefix="projection-speed-", dir=os.environ["RUNNER_TEMP"]) as tmp:
        comparison = Comparison(Path(tmp), manifest)
        try:
            accepted = comparison.run(manifest, variants, ordered)
        except Exception as exc:
            comparison.report.update(status="failed", error=str(exc)[-8000:])
            comparison.save(comparison.report["stage"])
            raise
        if not accepted:
            raise SystemExit("At least one export was not accepted by every checker")


if __name__ == "__main__":
    main()
