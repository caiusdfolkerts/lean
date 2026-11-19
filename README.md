# Rooted forest bulk diagnostic

Use this directory as the root of an isolated GitHub repository or an orphan diagnostic branch. Push to `palomar/diagnostic-rooted-bulk` to launch the included workflow. The fixture has its own pinned Lean toolchain and complete source closure. It needs only Lean core, with no Mathlib build. `python3 run.py` checks source hashes and import graphs without invoking Lean.

The workflow compiles three variants of the same three full rooted subsumed forests. `original` uses byte-identical sources from the regrouped snapshot. `bulk-original` uses the same Boolean checker in longer intervals. `bulk-sparse` uses those same intervals and a compiled theorem relating sparse list membership to the original bitmask transition. The six modified proof modules have the same boundaries and cover the same intervals in each variant. All three use the same packed data, root, leaf and disposition sources. The original classification and disposition declarations are compiled and exported under their original names. The companion smoke module exercises accepted and rejected transitions, missing coverage and wrong counters.

The workflow compares ordinary kernel-checked module builds with identical options and shared dependencies compiled once. It rotates the order of the variants across modules on the same worker. Read `timings.*.proof_modules_seconds` for the changed proof modules and `closure_summed_invocation_seconds` for the reachable fixture closure including common imports. The latter is a sum of elapsed times across processes. `variant_cpu_seconds` provides a second metric. The run records memory and per-module results. Use the two baseline ratios to distinguish batching from the sparse transition change.

Both original and sparse variants export the same six public endpoints. The workflow checks the expected names and axiom whitelist and replays both exports with Lean's kernel, NanoDa and verified con-ron. Compilation alone is a timing result. A successful verification receipt requires all six replays.

For equivalent execution on a disposable Linux worker with the pinned toolchain, set `RUNNER_TEMP` to an empty writable work area and run these stages consecutively.

```sh
python3 run.py
python3 run.py --phase build
python3 run.py --phase lean_kernel
python3 run.py --phase nanoda
python3 run.py --phase con_ron
```

The workflow saves separate compilation and verification receipts. A failing phase records its exit code and error tail. The unchanged packed data and snapshot hashes are recorded in `manifest.json`.
