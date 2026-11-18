This bundle diagnoses the strict `pinRow` mismatch without changing mathematical declarations. It is source-only and has not been compiled.

`manifest.json` records the frozen source hashes, six identical declaration texts, exact lexical contexts, comparator fields and precise remaining uncertainty. All six texts match after whitespace normalization: `Vec3`, `Twist`, `evaluateTwist`, `PairPinGraph`, `compatibilityOperator`, `pinRow`. The source `pinRow` context has only `{B E : Type}`; no finite-type hypotheses or local algebraic instances are introduced there.

Prepare a scratch project with:

```
python3 reports/clique_covered_rigidity/raw-diagnostic/prepare.py packages/clique_covered_rigidity REPORT_SCRATCH_DIRECTORY
```

The command checks exact frozen hashes, rejects input symlinks and existing output, copies the package, adds three diagnostic libraries in scratch, and prints the commands. It starts no compiler. The exact toolchain and complete canonical dependency manifest are preserved; the only diagnostic configuration change is a 4 GiB per-process memory cap. Root must review and run the returned commands in the remote bounded environment. Do not invoke the package default target or `lake update`.

The three libraries are:

- `RawChallengeDiagnostics`: actual independent Challenge values.
- `RawSourceDiagnostics`: actual substantive source values, importing `rigidity` and `import all rigidity`. This builds the real source closure, whose previous full preflight passed.
- `RawLiteralDiagnostics`: only the six declarations in their original source namespace/scope groups, using Mathlib alone. This isolates changes due to the surrounding source environment from changes due to the Challenge context.

Each emits `PALOMAR_CONSTINFO` JSON records with the declaration kind, origin, type, universe parameter names, reducibility hints, safety, mutual block list, used constants, raw expressions and expression hashes. Capture the complete build logs as artifacts. Origin differences are expected. Binder names and annotations can differ in raw/pretty output without violating the comparator; Lean's `Expr.eqv` ignores them. Compare the other `ConstantInfo` fields and implicit instance/constant arguments first.

Interpretation:

- If only regular heights differ, inspect the direct dependencies' heights and `getMaxHeight` inputs; do not mark a data definition as a comparison hole merely to suppress the difference.
- If values differ, identify the first differing constant/instance argument, then reproduce the exact source interface in the Challenge or use a fresh explicit semantic definition with an actual source-alignment proof.
- If all six complete records agree, run the native exporter/Comparator on these same snapshots to investigate export-time transformations.

The separately recorded six supporting proof-helper normalizations remain pending. They address explicit proof-bearing data fields and are not an established explanation for pure `pinRow`.

The prepared remote workflow is `clique-raw.yml` (destination `.github/workflows/clique-raw.yml`). `run_remote.py` validates all 35 frozen input files, materializes only the exact canonical manifest through pipeline policy commit `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`, obtains the official Mathlib cache, and invokes Lean directly in topological order for the three probe import closures. It starts one compiler at a time with `-j1`, disabled async elaboration, trust zero and an initial 4 GiB Lean memory limit. It never runs `lake update`, project defaults, `Solution`, or unrelated proof targets. Original source files, import-all headers, module names and complete manifest bytes are preserved.

A narrowly classified Lean memory failure permits one fresh 8 GiB attempt using the identical snapshot. The attempts have separate workspaces, bounded logs and receipts; a type error does not trigger the resource retry. Each phase log is at most 1 MiB and records total stream bytes, the full stream SHA256, truncation flag and bounded-file SHA256. The final summary cannot mark an interrupted or failed attempt as elaborated. All GitHub actions and the elan archive are pinned.

Optional `.lake/checkpoints` and `.lake/reports` persistence directories are read-only in scratch, as in the successful source phase of the official preflight. Actual source validation/assertion code runs unchanged. This prevents development checkpoint files from expanding the diagnostic workspace.

`publish-files.json` identifies exactly the files root should publish. Preparation syntax, action pins and frozen hashes were checked without running any Lean compiler. This uncompiled diagnostic preparation is not a successful proof or comparator result.
