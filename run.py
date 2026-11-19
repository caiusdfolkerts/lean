"""Verify the fixture or run its bounded Lean diagnostic on a Linux runner."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import graphlib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
VARIANTS = ("original", "bulk-original", "bulk-sparse")
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IMPORT = re.compile(r"^(?:(?:public|meta) )*import (?:all )?([\w.]+)", re.M)
PRIMITIVES = ("Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble "
              "Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat "
              "List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam").split()
DECL = re.compile(rb'^\{"(axiom|thm)":')


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def graph_for(sources):
    return {name: [d for d in IMPORT.findall(path.read_text()) if d in sources]
            for name, path in sources.items()}


def closure(graph, roots):
    seen = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name)
            pending.extend(graph[name])
    return seen


def validate(m):
    for file, spec in m["files"].items():
        path = ROOT / file
        if path.stat().st_size != spec["bytes"] or sha(path) != spec["sha256"]:
            raise ValueError(f"Snapshot hash mismatch: {file}")
    sources = {name: ROOT / "source" / rel for name, rel in m["modules"].items()}
    graph = graph_for(sources)
    assert closure(graph, [m["endpoint"]]) == set(graph)
    ext = {d for path in sources.values() for d in IMPORT.findall(path.read_text()) if d not in graph}
    assert sorted(ext) == m["external_imports"]
    for variant in VARIANTS[1:]:
        changed = {name: ROOT / variant / m["modules"][name] for name in m["varied_modules"]}
        if variant == "bulk-sparse":
            changed["RootedBulk"] = ROOT / variant / "RootedBulk.lean"
            changed["RootedBulkSmoke"] = ROOT / variant / "RootedBulkSmoke.lean"
        selected = dict(sources, **changed)
        for name, path in changed.items():
            missing = set(IMPORT.findall(path.read_text())) - selected.keys() - ext
            assert not missing, (name, missing)
        list(graphlib.TopologicalSorter(graph_for(selected)).static_order())
    return graph


def audit_export(path, targets):
    prefixes = {".".join(parts[:i]) for target in [*targets, *AXIOMS]
                for parts in [target.split(".")] for i in range(1, len(parts) + 1)}
    names = {0: ""}
    axioms, found = set(), set()
    with path.open("rb") as stream:
        for line in stream:
            if b'"in":' in line[:128]:
                record = json.loads(line)
                name = record.get("str")
                if isinstance(name, dict) and name["pre"] in names and "in" in record:
                    full = ".".join(filter(None, (names[name["pre"]], name["str"])))
                    if full in prefixes:
                        names[record["in"]] = full
            match = DECL.match(line)
            if match:
                kind = match[1].decode()
                index = json.loads(line)[kind]["name"]
                if kind == "axiom":
                    axioms.add(names.get(index, f"unknown-name-{index}"))
                elif names.get(index) in targets:
                    found.add(names[index])
    if found != set(targets) or axioms - AXIOMS:
        raise ValueError(f"Unexpected export endpoints or axioms: {found}, {axioms}")
    return {"bytes": path.stat().st_size, "sha256": sha(path), "axioms": sorted(axioms),
            "targets": sorted(found)}


def run(m, graph, phase):
    if sys.platform != "linux":
        raise SystemExit("Remote execution requires Linux and GNU time")
    tmp = Path(os.environ["RUNNER_TEMP"]) / "rooted-bulk"
    results = ROOT / "results.json"
    manifest_sha = sha(ROOT / "manifest.json")
    tools = ("lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron")
    bindir = Path(subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT,
                                         text=True).strip()) / "bin"
    tool_hashes = {tool: sha(bindir / tool) for tool in tools}
    env = dict(os.environ, LEAN_ABORT_ON_PANIC="1", PATH=str(bindir) + os.pathsep + os.environ["PATH"])

    def save():
        body = (json.dumps(receipt, indent=2, sort_keys=True) + "\n").encode()
        if len(body) > 1_500_000:
            raise ValueError("Receipt exceeded its byte budget")
        partial = results.with_suffix(".tmp")
        partial.write_bytes(body)
        partial.replace(results)

    def measure(label, argv, cwd, env, seconds, export=None):
        with tempfile.TemporaryDirectory(dir=tmp) as td:
            log = Path(td) / "output"
            metric = Path(td) / "time"
            argv = ["/usr/bin/time", "-f", "%U %S %M", "-o", metric, "timeout",
                    "--kill-after=10s", str(seconds), *map(str, argv)]
            start = time.monotonic()
            with log.open("wb") as f:
                if export is None:
                    proc = subprocess.run(argv, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT)
                else:
                    with export.open("wb") as stream:
                        proc = subprocess.run(argv, cwd=cwd, env=env, stdout=stream, stderr=f)
            stat = {"exit_code": proc.returncode, "wall_seconds": round(time.monotonic() - start, 3)}
            fields = metric.read_text().splitlines()[-1].split()
            if len(fields) == 3:
                stat.update(user_seconds=float(fields[0]), system_seconds=float(fields[1]),
                            peak_rss_bytes=int(fields[2]) * 1024)
            with log.open("rb") as f:
                f.seek(max(0, log.stat().st_size - 12000))
                tail = f.read().decode(errors="replace")
            if proc.returncode or label == m["endpoint"] or phase != "build":
                stat["log_tail"] = tail
            return stat

    def ensure(stat, label):
        if stat["exit_code"] != 0:
            raise RuntimeError(f"{label} failed: {stat.get('log_tail', '')}")

    if phase != "build":
        receipt = json.loads(results.read_text())
        if receipt["manifest_sha256"] != manifest_sha or receipt["tools"] != tool_hashes:
            raise ValueError("Replay environment differs from compile environment")
        receipt.update(stage=phase)
        save()
        failures = []
        for variant in ("original", "bulk-sparse"):
            proof = tmp / (variant + ".ndjson")
            assert sha(proof) == receipt["exports"][variant]["sha256"]
            cfg = tmp / (variant + "-nanoda.json")
            cfg.write_text(json.dumps({"use_stdin": False, "export_file_path": str(proof),
                "permitted_axioms": sorted(AXIOMS), "unpermitted_axiom_hard_error": True,
                "num_threads": 2, "nat_extension": True, "string_extension": True}))
            cmd = {"lean_kernel": ["leanchecker", "--silent", "--from-export", proof],
                   "nanoda": ["nanoda_bin", cfg],
                   "con_ron": ["con-ron", "--jobs=2", "--verified", proof]}[phase]
            stat = measure(variant, [bindir / cmd[0], *cmd[1:]], tmp, env, 2700)
            receipt["replays"].setdefault(variant, {})[phase] = stat
            save()
            if stat["exit_code"]:
                failures.append(variant)
        if failures:
            receipt.update(status="failed", error=f"{phase} failed for {', '.join(failures)}")
            save()
            raise RuntimeError(receipt["error"])
        if all(set(receipt["replays"].get(v, {})) == {"lean_kernel", "nanoda", "con_ron"}
               and all(x["exit_code"] == 0 for x in receipt["replays"][v].values())
               for v in ("original", "bulk-sparse")):
            receipt.update(status="pass", stage="completed")
            save()
        return

    tmp.mkdir(exist_ok=False)
    version = subprocess.check_output([bindir / "lean", "--version"], text=True, env=env).strip()
    if not re.search(r"\bversion 4\.35\.0\b", version):
        raise RuntimeError(f"Unexpected Lean version: {version}")
    receipt = {"manifest_sha256": manifest_sha, "commit": os.getenv("GITHUB_SHA"),
               "run_id": os.getenv("GITHUB_RUN_ID"), "tools": tool_hashes, "lean_version": version,
               "cpu_affinity": len(os.sched_getaffinity(0)), "status": "running", "stage": "compile",
               "modules": {}, "exports": {}, "replays": {}, "timings": {}}
    save()
    common = closure(graph, [n for n in graph if not
                     (closure(graph, [n]) & set(m["varied_modules"]))])
    varied = set(graph) - common

    def register(label, name, stat):
        receipt["modules"].setdefault(label, {})[name] = stat
        save()
        ensure(stat, f"{label} {name}")

    def setup(label):
        work = tmp / label
        src, output = work / "source", work / "build"
        shutil.copytree(ROOT / "source", src)
        output.mkdir()
        if label in VARIANTS[1:]:
            shutil.copytree(ROOT / label, src, dirs_exist_ok=True)
        search = [str(output)]
        if label != "common":
            search.append(str(tmp / "common/build"))
        return src, output, dict(env, LEAN_PATH=os.pathsep.join(search))

    build_envs = {label: setup(label) for label in ("common", *VARIANTS)}

    def compile_module(label, name):
        src, output, leanenv = build_envs[label]
        rel = Path(name.replace(".", "/") + ".lean")
        obj = output / rel.with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        return measure(name, [bindir / "lean", "-t1", "-j1", "-s65536", "-M4096",
                              "-DmaxHeartbeats=0", "-DElab.async=false",
                              "-Ddebug.skipKernelTC=false", "-o", obj, rel], src, leanenv, 900)

    def summary(label, started):
        stats = receipt["modules"][label].values()
        return {"phase_wall_seconds": round(time.monotonic() - started, 3),
                "summed_invocation_wall_seconds": round(sum(x["wall_seconds"] for x in stats), 3),
                "summed_process_cpu_seconds": round(sum(x["user_seconds"] + x["system_seconds"]
                                                         for x in stats), 3),
                "peak_rss_bytes": max(x["peak_rss_bytes"] for x in stats)}

    try:
        started = time.monotonic()
        common_order = graphlib.TopologicalSorter({n: graph[n] for n in sorted(common)})
        common_order.prepare()
        with ThreadPoolExecutor(max_workers=3) as pool:
            queue = list(common_order.get_ready())
            jobs = {}
            while common_order.is_active():
                while queue and len(jobs) < 3:
                    name = queue.pop()
                    jobs[pool.submit(compile_module, "common", name)] = name
                done, _ = wait(jobs, return_when=FIRST_COMPLETED)
                for job in done:
                    name = jobs.pop(job)
                    register("common", name, job.result())
                    common_order.done(name)
                queue.extend(common_order.get_ready())
        receipt["timings"]["common"] = summary("common", started)
        save()

        # Alternate variants module-by-module on this host. Absolute time also
        # includes process start/imports, as in an ordinary compilation.
        register("bulk-sparse", "RootedBulk", compile_module("bulk-sparse", "RootedBulk"))
        register("smoke", "RootedBulkSmoke", compile_module("bulk-sparse", "RootedBulkSmoke"))
        ordered = [n for n in graphlib.TopologicalSorter(graph).static_order() if n in varied]
        for i, name in enumerate(ordered):
            for variant in VARIANTS[i % 3:] + VARIANTS[:i % 3]:
                register(variant, name, compile_module(variant, name))
        for variant in VARIANTS:
            stats = receipt["modules"][variant]
            wall = sum(x["wall_seconds"] for x in stats.values())
            cpu = sum(x["user_seconds"] + x["system_seconds"] for x in stats.values())
            receipt["timings"][variant] = {
                "variant_compilation_seconds": round(wall, 3),
                "variant_cpu_seconds": round(cpu, 3),
                "proof_modules_seconds": round(sum(stats[n]["wall_seconds"] for n in m["varied_modules"]), 3),
                "closure_summed_invocation_seconds": round(
                    wall + receipt["timings"]["common"]["summed_invocation_wall_seconds"], 3),
                "peak_rss_bytes": max(x["peak_rss_bytes"] for x in stats.values())}
        base = receipt["timings"]["original"]
        receipt["ratios"] = {
            variant: {
                "proof_speedup": round(base["proof_modules_seconds"] /
                                       receipt["timings"][variant]["proof_modules_seconds"], 3),
                "closure_speedup": round(base["closure_summed_invocation_seconds"] /
                                         receipt["timings"][variant]["closure_summed_invocation_seconds"], 3)}
            for variant in VARIANTS[1:]}
        save()
        for variant in ("original", "bulk-sparse"):
            receipt.update(stage=f"export_{variant}")
            save()
            src, _, leanenv = build_envs[variant]
            dest = tmp / (variant + ".ndjson")
            stat = measure("export", [bindir / "leanexport", m["endpoint"], "--",
                           *m["theorems"], *PRIMITIVES], src, leanenv, 900, export=dest)
            receipt["exports"][variant] = stat
            save()
            ensure(stat, f"{variant} export")
            receipt["exports"][variant] = dict(stat, **audit_export(dest, m["theorems"]))
            save()
        receipt.update(status="exported", stage="independent_replay")
        save()
    except Exception as exc:
        receipt.update(status="failed", error=str(exc)[-12000:])
        save()
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--phase", choices=("build", "lean_kernel", "nanoda", "con_ron"))
    args = parser.parse_args()
    manifest = json.loads((ROOT / "manifest.json").read_text())
    graph = validate(manifest)
    print(f"Verified {len(graph)} source modules and {len(manifest['files'])} file hashes", flush=True)
    if args.phase is not None:
        run(manifest, graph, args.phase)


if __name__ == "__main__":
    main()
