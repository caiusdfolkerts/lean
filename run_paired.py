"""Validate the fixture and run an order-reversed paired benchmark on Linux."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import statistics
import subprocess
import tempfile
import time

from lean_export_reader import AXIOMS, PRIMITIVES, export_measurements
from projection_transform import HELPER, MODES, SCHEMA, endpoint_metadata, module_path, sha, transform, verify_schema
from scope import imports, local_closure

ROOT = Path(__file__).resolve().parent
OPTS = ["-t1", "-j1", "-s65536", "-M4096", "-DmaxHeartbeats=0",
        "-DElab.async=false", "-Ddebug.skipKernelTC=false"]


def validate():
    manifest = json.loads((ROOT / "fixture.json").read_text())
    for path, digest in manifest["files"].items():
        if sha((ROOT / path).read_bytes()) != digest:
            raise ValueError(f"Fixture hash mismatch: {path}")
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.35.0":
        raise ValueError("Wrong Lean pin")
    packages = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    if next(p["rev"] for p in packages if p["name"] == "mathlib") != "56a005855ea17e0b0958f73ec801ae140b0a1679":
        raise ValueError("Wrong Mathlib pin")
    verify_schema((ROOT / "source" / SCHEMA).read_text())
    source_files = sorted((ROOT / "source").rglob("*.lean"))
    graph = {".".join(p.relative_to(ROOT / "source").with_suffix("").parts): imports(p.read_text())
             for p in source_files}
    helper_imports = imports((ROOT / module_path(HELPER)).read_text())
    for batch, sample in manifest["samples"].items():
        common = sample["common"]
        endpoint = sample["endpoint"]
        known = set(graph)
        built = set()
        for module in [*common, batch, *([endpoint] if endpoint != batch else [])]:
            if not set(graph[module]) & known <= built or module in built:
                raise ValueError(f"Invalid prerequisite order: {batch}/{module}")
            built.add(module)
        scope = local_closure([endpoint, *helper_imports], graph)
        external = sorted(({dep for module in scope for dep in graph[module]}
                           | set(helper_imports)) - known)
        if built != scope or external != sample["external"]:
            raise ValueError(f"Incorrect prerequisite closure: {batch}")
        source = (ROOT / "source" / module_path(batch)).read_text()
        for mode, expected in sample["variants"].items():
            result, metadata = transform(source, batch, mode)
            if endpoint != batch:
                metadata.update(endpoint_metadata((ROOT / "source" / module_path(endpoint)).read_text(), batch))
            if sha(result.encode()) != expected or any(sample[k] != v for k, v in metadata.items()):
                raise ValueError(f"Generated source or scope mismatch: {batch}/{mode}")
    return manifest


class Benchmark:
    def __init__(self, batch, spec, scratch):
        self.batch, self.spec, self.scratch = batch, spec, scratch
        self.bin = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin"
        self.external = [str(Path(p).resolve()) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
        self.common = scratch / "common"
        self.lean = self.bin / "lean"
        self.out = ROOT / "results" / batch
        self.out.mkdir(parents=True, exist_ok=False)
        self.report = {
            "status": "running", "run_id": os.getenv("GITHUB_RUN_ID"), "commit": os.getenv("GITHUB_SHA"),
            "fixture_sha256": sha((ROOT / "fixture.json").read_bytes()), "sample": spec,
            "batch": batch, "commands": {}, "replays": {}, "builds": {},
            "toolchain": subprocess.check_output([self.lean, "--version"], text=True).strip(),
            "tools": {t: sha((self.bin / t).read_bytes()) for t in
                      ("lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron")},
        }
        if not re.search(r"\b4\.35\.0\b", self.report["toolchain"]):
            raise ValueError("Benchmark is running under the wrong toolchain")

    def save(self):
        temp = self.out / "receipt.tmp"
        temp.write_text(json.dumps(self.report, indent=2) + "\n")
        temp.replace(self.out / "receipt.json")

    def measure(self, label, args, src, builds, export=None, limit=480):
        self.report["stage"] = label
        self.save()
        env = dict(os.environ, LEAN_ABORT_ON_PANIC="1",
                   LEAN_PATH=os.pathsep.join([*map(str, builds), str(self.common), *self.external]),
                   PATH=str(self.bin) + os.pathsep + os.environ["PATH"])
        times = self.scratch / "time"
        log = self.out / (label + ".log")
        args = ["/usr/bin/time", "-f", "%U %S %M", "-o", times,
                "timeout", "--kill-after=15s", str(limit), *args]
        start = time.monotonic()
        with log.open("wb") as err:
            if export is None:
                p = subprocess.run(args, env=env, cwd=src, stdout=err, stderr=subprocess.STDOUT)
            else:
                with export.open("wb") as out:
                    p = subprocess.run(args, env=env, cwd=src, stdout=out, stderr=err)
        elapsed = time.monotonic() - start
        user, system, rss = times.read_text().splitlines()[-1].split()
        metric = {"exit_code": p.returncode, "wall_seconds": round(elapsed, 3),
                  "cpu_seconds": float(user) + float(system), "peak_rss_bytes": int(rss) * 1024}
        self.report["commands"][label] = metric
        self.save()
        if p.returncode:
            raise RuntimeError(f"{label}: {log.read_text(errors='replace')[-8000:]}")
        if not label.startswith("common."):
            print(label, metric, flush=True)
        return metric

    def build(self, label, module, src, build, *, limit=600):
        relative = module_path(module)
        output = build / relative.with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        metric = self.measure(label, [self.lean, *OPTS, "-o", output, relative],
                              src, [build] if build != self.common else [], limit=limit)
        metric["source_sha256"] = sha((src / relative).read_bytes())
        metric["olean_bytes"] = sum(p.stat().st_size for p in output.parent.glob(output.name + "*"))
        self.save()
        return metric

    def replay(self, mode, src, build):
        target = self.spec["theorem"]
        endpoint = self.spec["endpoint"]
        namespace = target.rsplit(".", 1)[0]
        audit = ["module", f"import {endpoint}", f"example : {self.spec['type']} := {target}"]
        audit.extend(f"example : {namespace}.Certifies {j} := {namespace}.{name}"
                     for name, j in self.spec["published_projections"])
        (src / "CheckProjection.lean").write_text("\n".join(audit) + "\n")
        self.measure(f"{mode}.theorems", [self.lean, *OPTS, "CheckProjection.lean"], src, [build])
        ndjson = self.scratch / (mode + ".ndjson")
        self.measure(f"{mode}.export",
                     [self.bin / "leanexport", endpoint, "--", target, *PRIMITIVES], src, [build], ndjson)
        stats = export_measurements(ndjson, target)
        if set(stats["axioms"]) - set(AXIOMS):
            raise ValueError(f"Unexpected axioms: {stats['axioms']}")
        self.report["replays"][mode] = stats
        cfg = self.scratch / "nanoda.json"
        cfg.write_text(json.dumps({
            "use_stdin": False, "export_file_path": str(ndjson), "permitted_axioms": AXIOMS,
            "unpermitted_axiom_hard_error": True, "num_threads": 1,
            "nat_extension": True, "string_extension": True,
        }))
        for name, command in {
            "leanchecker": ["leanchecker", "--silent", "--from-export", ndjson],
            "nanoda": ["nanoda_bin", cfg],
            "con-ron": ["con-ron", "--jobs=1", "--verified", ndjson],
        }.items():
            label = f"{mode}.{name}"
            self.measure(label, [self.bin / command[0], *command[1:]], src, [build], limit=660)
            if name == "con-ron" and not re.search(
                r"^con-ron: accepted [0-9]+ declarations \(--verified\)(?: t=[0-9.]+s)?$",
                (self.out / (label + ".log")).read_text(), re.M,
            ):
                raise RuntimeError(f"Verified con-ron did not explicitly accept {mode}")
        ndjson.unlink()

    def run(self):
        self.save()
        for module in self.spec["common"]:
            self.build(f"common.{module}", module, ROOT / "source", self.common)
        self.build("shared_helper", HELPER, ROOT, self.common)
        baseline = (ROOT / "source" / module_path(self.batch)).read_text()
        for trial, order in enumerate((MODES, MODES[::-1]), 1):
            for mode in order:
                src = self.scratch / f"trial{trial}" / mode / "src"
                build = src.with_name("build")
                path = src / module_path(self.batch)
                path.parent.mkdir(parents=True)
                path.write_text(transform(baseline, self.batch, mode)[0])
                metric = self.build(f"trial{trial}.{mode}", self.batch, src, build)
                self.report["builds"].setdefault(mode, []).append(metric)
                endpoint = self.spec["endpoint"]
                if endpoint != self.batch:
                    rel = module_path(endpoint)
                    (src / rel).parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(ROOT / "source" / rel, src / rel)
                    self.build(f"trial{trial}.{mode}.target_module", endpoint, src, build)
        for mode in MODES:
            src = self.scratch / "trial2" / mode / "src"
            self.replay(mode, src, src.with_name("build"))
        footprints = {tuple(sorted(stats["axioms"])) for stats in self.report["replays"].values()}
        if len(footprints) != 1:
            raise ValueError("Axiom footprints differ across variants")
        medians = {mode: statistics.median(row["wall_seconds"] for row in rows)
                   for mode, rows in self.report["builds"].items()}
        self.report["median_build_seconds"] = medians
        self.report["wall_reduction_percent"] = {
            mode: round(100 * (1 - value / medians["baseline"]), 3)
            for mode, value in medians.items()
        }
        self.report.update(status="pass", stage="complete")
        self.save()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--batch")
    mode = p.add_mutually_exclusive_group()
    mode.add_argument("--external", action="store_true")
    mode.add_argument("--run", action="store_true")
    a = p.parse_args()
    manifest = validate()
    if (a.external or a.run) and a.batch is None:
        p.error("--batch is required for --external or --run")
    if a.external:
        print(" ".join(m for m in manifest["samples"][a.batch]["external"] if m.startswith("Mathlib.")))
    elif a.run:
        with tempfile.TemporaryDirectory(prefix="projection-paired-", dir=os.environ["RUNNER_TEMP"]) as tmp:
            benchmark = Benchmark(a.batch, manifest["samples"][a.batch], Path(tmp))
            try:
                benchmark.run()
            except Exception as exc:
                benchmark.report.update(status="fail", error=str(exc))
                benchmark.save()
                raise
    else:
        print({m: (len(s["common"]), s["targets"]) for m, s in manifest["samples"].items()})


if __name__ == "__main__":
    main()
