#!/usr/bin/env python3
"""Run the paired package-module profile on one isolated GitHub Actions Linux VM."""
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import time

from quota_candidate import apply as quota_candidate

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT / "project"
OUT = ROOT / "measurement"
FLAGS = ["-t1", "-j1", "-s65536", "-DmaxHeartbeats=0",
         "-DElab.async=false", "-Ddebug.skipKernelTC=false"]
PROFILE = ["-Dprofiler=true", "-Dprofiler.threshold=25"]
LEAN_COMMIT = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"
HEADER = re.compile(r"(?m)^(?:(?:public|meta) )*import (?:all )?[\w.]+[ \t]*(?:--[^\n]*)?$")
FACETS = (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir")
AXIOM_AUDIT = r'''
open Lean in
run_cmd do
  let env ← getEnv
  if (← getOptions).getBool `debug.skipKernelTC false || env.header.trustLevel != 0 then
    throwError "Unexpected trust or kernel options"
  let some idx := env.getModuleIdx? `SUBJECT |
    throwError "Audit subject missing from the imported environment"
  let allowed := NameSet.ofList [`propext, `Classical.choice, `Quot.sound]
  let data := env.header.moduleData[idx.toNat]!
  for name in data.constNames do
    unless (env.find? name).isSome do throwError "Missing declaration: {name}"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unapproved axiom {axiomName} in {name}"
    IO.println <| "AUDIT " ++ (Json.mkObj [
      ("name", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString))]).compress
  IO.println s!"AUDIT_COUNT {data.constNames.size}"
'''


def module_path(module, extension):
    return Path(*module.split(".")).with_suffix(extension)


def hash_file(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def timed(label, command, cwd=PROJECT, env=None, limit=240):
    prefix = OUT / label
    print(label, flush=True)
    started = time.monotonic()
    with prefix.with_suffix(".log").open("wb") as log:
        process = subprocess.run(
            ["/usr/bin/time", "-f", "%e %U %S %M %F %R %x", "-o",
             str(prefix.with_suffix(".time")), "timeout", "-k", "15s", str(limit), *command],
            cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT,
        )
    if process.returncode:
        print(prefix.with_suffix(".log").read_text(errors="replace")[-5500:], flush=True)
        raise RuntimeError(f"{label}: process exit {process.returncode}")
    _, user, system, rss, major, minor, _ = prefix.with_suffix(".time").read_text().split()
    return {"wall_s": round(time.monotonic() - started, 6), "user_s": float(user),
            "system_s": float(system), "rss_kib": int(rss), "major_faults": int(major),
            "minor_faults": int(minor)}


class Profile:
    def __init__(self, env, work):
        self.env = env
        self.work = work
        self.base = PROJECT / ".lake/build/lib/lean"
        self.lean = subprocess.check_output(["elan", "which", "lean"], cwd=PROJECT, text=True).strip()

    def compile(self, module, label, output, *, source=None, overrides=None, extra=()):
        relative = module_path(module, ".lean")
        src = (PROJECT / relative) if source is None else source
        olean = output / module_path(module, ".olean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        setup = PROJECT / ".lake/build/ir" / module_path(module, ".setup.json")
        options = json.loads(setup.read_text())
        assert options["isModule"] and options["name"] == module and options.get("imports") is None
        assert not ({"debug.skipKernelTC", "Elab.async", "compiler.postponeCompile"} & options["options"].keys())
        if overrides:
            for dependency, location in overrides.items():
                if dependency not in options["importArts"]:
                    # The dependency can be outside the consumer's effective imports.
                    continue
                arts = options["importArts"][dependency]
                base = location / module_path(dependency, ".olean")
                replacements = {str(base.name).removesuffix(".olean") + suffix:
                                base.parent / (base.stem + suffix) for suffix in FACETS}
                options["importArts"][dependency] = [
                    [str(replacements[Path(path).name]) for path in group] for group in arts]
            setup = output / module_path(module, ".setup.json")
            setup.write_text(json.dumps(options))
        stats = timed(label, [self.lean, *FLAGS, *extra, str(src), "-o", str(olean),
                               "-i", str(olean.with_suffix(".ilean")),
                               "-c", str(olean.with_suffix(".c")), "--setup", str(setup), "--json"],
                      env=self.env)
        stats["facet_bytes"] = {
            suffix: olean.with_name(olean.stem + suffix).stat().st_size for suffix in FACETS}
        stats["ilean_bytes"] = olean.with_suffix(".ilean").stat().st_size
        return stats

    def alter(self, module, mode, source):
        target = self.work / "sources" / mode / module_path(module, ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source)
        for sibling in (PROJECT / module_path(module, ".lean")).parent.iterdir():
            if sibling.suffix in {".natpack", ".tablepack", ".gpack", ".gpool"} and not (target.parent / sibling.name).exists():
                (target.parent / sibling.name).symlink_to(sibling)
        return target

    def compare(self, module, label, mode, left, right):
        relative = module_path(module, ".olean")
        stats = timed(label, [self.lean, *FLAGS, "--run", str(ROOT / "CompareArtifacts.lean"),
                              mode, str(left / relative), str(right / relative)], env=self.env)
        parsed = json.loads((OUT / f"{label}.log").read_text().splitlines()[-1])
        return {"invocation": stats, **parsed}

    def audit(self, module, label, layers):
        source = self.work / "ProfileAxiomAudit.lean"
        source.write_text(
            "module\nimport Lean.Elab.BuiltinEvalCommand\n"
            "meta import Lean.Elab.Command\nmeta import Lean.Data.Json\n"
            f"meta import Lean.Util.CollectAxioms\nimport {module}\n" +
            AXIOM_AUDIT.replace("SUBJECT", module))
        env = dict(self.env, LEAN_PATH=os.pathsep.join([*(str(p) for p in layers), self.env["LEAN_PATH"]]))
        stats = timed(label, [self.lean, *FLAGS, str(source)], env=env)
        rows = {}
        count = None
        for line in (OUT / f"{label}.log").read_text().splitlines():
            if line.startswith("AUDIT "):
                row = json.loads(line.removeprefix("AUDIT "))
                assert row["name"] not in rows
                rows[row["name"]] = sorted(row["axioms"])
            elif line.startswith("AUDIT_COUNT "):
                count = int(line.split()[1])
        assert count is not None and count == len(rows)
        return rows, stats


def read_cache_roots(manifest):
    return [m for m in manifest["external_imports"] if m == "Mathlib" or m.startswith("Mathlib.")]


def verify_headers(manifest):
    modules = sorted(manifest["headers"])
    timed("source-imports", ["lean", "--deps-json", *(str(module_path(m, ".lean")) for m in modules)],
          limit=60)
    rows = json.loads((OUT / "source-imports.log").read_text())["imports"]
    assert len(rows) == len(modules)
    for module, row in zip(modules, rows):
        source = manifest["headers"][module]
        assert not row["errors"] and row["result"]["isModule"], module
        expected = [(name, "public" in modifiers.split(), "meta" in modifiers.split(), import_all)
                    for name, modifiers, import_all in source["edges"]]
        actual = [(item["module"], item.get("isExported", True),
                   item.get("isMeta", False), item.get("importAll", False))
                  for item in row["result"]["imports"]]
        if not source["prelude"]:
            assert [a[0] for a in actual[:2]] == ["Init", "Init"], module
            actual = actual[2:]
        assert actual == expected, (module, actual, expected)


def verify_sources(manifest):
    # Compare the source manifest a second time after compilation.
    for relative, digest in manifest["files"].items():
        path = PROJECT / relative
        if path.is_symlink() or hash_file(path) != digest:
            raise ValueError(f"Source identity mismatch: {relative}")


def save(result):
    temp = OUT / "result.tmp"
    temp.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    temp.replace(OUT / "result.json")


def measured_case(profile, case, record, result):
    module = case["module"]
    label = module.replace(".", "_")
    source = (PROJECT / module_path(module, ".lean")).read_text()
    directory = profile.work / label
    result.update(case)
    result["source"] = record
    result["timing"] = {}
    # Keep profiler instrumentation out of comparison estimates.
    for repeat, order in enumerate((("baseline", "header"), ("header", "baseline"),
                                    ("baseline", "header")), start=1):
        for mode in order:
            key = f"{mode}-{repeat}"
            altered = None
            if mode == "header":
                imports = list(HEADER.finditer(source))
                header = source[:imports[-1].end()] if imports else source.splitlines()[0]
                altered = profile.alter(module, "header", header + "\n")
            result["timing"][key] = profile.compile(module, f"{label}-{key}",
                                                     directory / key, source=altered)
    result["median_baseline_wall_s"] = statistics.median(
        t["wall_s"] for k, t in result["timing"].items() if k.startswith("baseline"))
    result["median_header_wall_s"] = statistics.median(
        t["wall_s"] for k, t in result["timing"].items() if k.startswith("header"))
    result["profile"] = profile.compile(module, f"{label}-profile", directory / "profile", extra=PROFILE)
    trace = OUT / f"{label}-trace.json"
    result["structured_profile"] = profile.compile(
        module, f"{label}-trace", directory / "trace",
        extra=["-Dtrace.profiler=true", "-Dtrace.profiler.threshold=20",
               f"-Dtrace.profiler.output={trace}"])
    assert trace.is_file()
    before = directory / "baseline-1"
    result["structure_comparison"] = profile.compare(
        module, f"{label}-compare-structures", "repeat", before, directory / "baseline-2")
    axioms, timing = profile.audit(module, f"{label}-audit-baseline", [before])
    assert len(axioms) == result["structure_comparison"]["public_declarations"]
    result["audit"] = {"count": len(axioms), "timing": timing,
                       "axioms": sorted({a for row in axioms.values() for a in row})}


def variant_case(profile, case, kind, result, result_set):
    module = case["module"]
    label = module.replace(".", "_")
    directory = profile.work / label
    source = (PROJECT / module_path(module, ".lean")).read_text()
    consumer = case["consumer" if kind == "quota" else "exposure_consumer"]
    edited = None
    overrides = {}
    layers = []
    if kind == "quota":
        macro = profile.alter("GraphCases", kind, quota_candidate(PROJECT / "GraphCases.lean"))
        overrides["GraphCases"] = profile.work / "quota-macro"
        if not (overrides["GraphCases"] / "GraphCases.olean").exists():
            result_set["quota_macro_build"] = profile.compile("GraphCases", "quota-macro", overrides["GraphCases"], source=macro)
        layers.append(overrides["GraphCases"])
    else:
        assert source.count("@[expose] public section") == 1
        edited = profile.alter(module, kind, source.replace("@[expose] public section", "public section"))
    result["consumer"] = consumer
    result["variants"] = {}
    for repeat, order in enumerate((("baseline", kind), (kind, "baseline"), ("baseline", kind)), start=1):
        for mode in order:
            key = f"{mode}-paired-{repeat}"
            result["variants"][key] = profile.compile(
                module, f"{label}-{key}", directory / key,
                source=edited if mode == kind else None, overrides=overrides if mode == kind else {})
    before = directory / "baseline-paired-1"
    after = directory / f"{kind}-paired-1"
    result["comparison"] = profile.compare(module, f"{label}-{kind}-compare", kind, before, after)
    result["profiles"] = {}
    for mode in ("baseline", kind):
        result["profiles"][mode] = profile.compile(
            module, f"{label}-{kind}-{mode}-profile", directory / f"{kind}-{mode}-profile",
            source=edited if mode == kind else None,
            overrides=overrides if mode == kind else {}, extra=PROFILE)
    original, _ = profile.audit(module, f"{label}-{kind}-audit-before", [before])
    changed, _ = profile.audit(module, f"{label}-{kind}-audit-after", [after, *layers])
    assert original == changed and len(original) == result["comparison"]["public_declarations"]

    reference = directory / "consumer-before"
    candidate = directory / "consumer-after"
    result["consumer_before"] = profile.compile(
        consumer, f"{label}-{kind}-consumer-before", reference, overrides={module: before})
    result["consumer_after"] = profile.compile(
        consumer, f"{label}-{kind}-consumer-after", candidate, overrides={module: after, **overrides})
    result["consumer_comparison"] = profile.compare(
        consumer, f"{label}-{kind}-consumer-compare", "quota", reference, candidate)
    original, _ = profile.audit(consumer, f"{label}-{kind}-consumer-audit-before", [reference, before])
    changed, _ = profile.audit(consumer, f"{label}-{kind}-consumer-audit-after", [candidate, after, *layers])
    assert original == changed and len(original) == result["consumer_comparison"]["public_declarations"]
    timing = result["variants"]
    before_times = [t["wall_s"] for k, t in timing.items() if k.startswith("baseline")]
    after_times = [t["wall_s"] for k, t in timing.items() if k.startswith(kind)]
    result["paired_deltas_s"] = [round(a - b, 6) for b, a in zip(before_times, after_times)]
    result["median_wall_s"] = {"baseline": statistics.median(before_times), kind: statistics.median(after_times)}
    result["audit_passed"] = True


def main():
    if platform.system() != "Linux" or os.getenv("GITHUB_ACTIONS") != "true":
        raise SystemExit("Run this only on the isolated Linux CI runner.")
    OUT.mkdir(exist_ok=False)
    work = Path(os.environ["RUNNER_TEMP"]) / "nonrat-profile-artifacts"
    work.mkdir(exist_ok=False)
    manifest = json.loads((ROOT / "fixture.json").read_text())
    result = {"status": "started", "fixture_sha256": hash_file(ROOT / "fixture.json"),
              "lean_flags": FLAGS, "samples": [], "candidate_experiments": []}
    save(result)
    try:
        verify_sources(manifest)
        for command in (["lscpu"], ["free", "-b"], ["git", "rev-parse", "HEAD"],
                        ["lean", "--version"], ["lake", "--version"]):
            timed("host-" + "-".join(command).replace("--", ""), command, limit=30)
        assert LEAN_COMMIT in (OUT / "host-lean-version.log").read_text()
        for name in ("cpu.max", "memory.max"):
            path = Path("/sys/fs/cgroup") / name
            if path.is_file():
                (OUT / name).write_text(path.read_text())
        verify_headers(manifest)
        cache_roots = read_cache_roots(manifest)
        assert cache_roots
        result["cache"] = timed("mathlib-cache", ["lake", "exe", "cache", "get", *cache_roots], limit=1500)
        assert not any((PROJECT / ".lake/build/lib/lean").rglob("*.olean"))
        targets = sorted({case[key] for case in manifest["sample"]
                          for key in ("module", "consumer", "exposure_consumer") if key in case})
        result["setup_build"] = timed("lake-bootstrap",
                                      ["lake", "build", *("+" + m for m in targets)], limit=4900)
        initialized = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=PROJECT, text=True)
        explicit_path = os.pathsep.join(str((PROJECT / p).resolve()) for p in initialized.strip().split(os.pathsep))
        profile = Profile(dict(os.environ, LEAN_PATH=explicit_path), work)
        assert explicit_path and profile.base.is_dir()
        for case in manifest["sample"]:
            sample = {}
            result["samples"].append(sample)
            try:
                measured_case(profile, case, manifest["sample_records"][case["module"]], sample)
            finally:
                save(result)
        result["status"] = "baseline_passed"
        save(result)
        for case in manifest["sample"]:
            for key, mode in (("consumer", "quota"), ("exposure_consumer", "exposure")):
                if key not in case:
                    continue
                experiment = {"module": case["module"], "mode": mode}
                result["candidate_experiments"].append(experiment)
                try:
                    variant_case(profile, case, mode, experiment, result)
                except Exception as error:
                    experiment["rejected"] = str(error)
                finally:
                    save(result)
        verify_sources(manifest)
        failures = [p for p in result["candidate_experiments"] if "rejected" in p]
        result["status"] = "baseline_passed_variant_rejected" if failures else "passed"
        if failures:
            raise RuntimeError("A bounded variant failed to reproduce or verify; inspect its logs")
    except Exception as error:
        if result["status"] != "baseline_passed_variant_rejected":
            result["status"] = "failed"
        result["error"] = str(error)
        raise
    finally:
        save(result)


if __name__ == "__main__":
    main()
