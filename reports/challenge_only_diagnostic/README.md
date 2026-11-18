# Canonical Challenge-only remote diagnostic

Prepared for review; no remote run or publication has been performed by this worker.
This checks elaboration of the independent Challenge, whose theorem placeholders
are intentional. It does not build a Solution, run Comparator or external
kernels, establish the mathematical claims, or authorize registry intake.

The default queue contains the four Challenges from algebra_one plus singular
vector spans and three-sunlet models. Higher Specht is also snapshotted and may
be selected explicitly through the workflow's comma-separated `cases` input.
Every source digest was checked against the owning worker's supplied version.

| Case | Lean | Mathlib revision | Lines |
| --- | --- | --- | ---: |
| deformed_coinvariants | 4.36.0-rc1 | 2cabef97b63d3275776b8b060d802de6a6fa1055 | 927 |
| alternating_forms | 4.36.0-rc1 | 2cabef97b63d3275776b8b060d802de6a6fa1055 | 729 |
| barycentric_invariance | 4.35.0 | 56a005855ea17e0b0958f73ec801ae140b0a1679 | 986 |
| barycentric_invariance_relative | 4.35.0 | 56a005855ea17e0b0958f73ec801ae140b0a1679 | 688 |
| singular_vector_spans | 4.36.0-rc2 | 1626233321dc564d20355d8f9d4f22e114d68600 | 835 |
| three_sunlet_models | 4.35.0 | 56a005855ea17e0b0958f73ec801ae140b0a1679 | 738 |
| higher_specht_bases (optional) | 4.36.0-rc1 | 2cabef97b63d3275776b8b060d802de6a6fa1055 | 475 |

`cases.json` is authoritative for exact Challenge, toolchain, original manifest
and original Lakefile hashes. `original-lakefile.*` files are data only and
are never executed. The manifest and toolchain bytes are copied unchanged.

The runner uses the immutable pipeline helpers at
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7` to check each canonical root's exact
manifest closure and materialize its pinned Git revisions. An independent
workspace has only the Challenge plus canonical dependencies. Its generated
TOML names only the canonical roots and one Challenge library. Original
project defaults, local TauCeti adaptations and full verification targets
cannot enter this workspace.

No `lake update`, dependency substitution or toolchain override occurs. A
canonical-root toolchain conflict, manifest change, tracked dependency source
change or HEAD mismatch blocks the diagnostic. Extra noncanonical/Solution-only
manifest packages are rejected rather than automatically rewritten. The
current seven cases require only Mathlib/core imports; canonical TauCeti
imports are supported by building only their explicitly imported modules.

Mathlib's exact official cache is fetched first; cache failure stops the job
rather than falling back to a full mathematical project build. The final
command uses direct Lean through the generated canonical Lake environment,
with trust0, native kernel checking enabled, one Lean thread,4GiB heap limit,
and the source's own options/imports untouched. Canonical TauCeti dependency
modules may need compilation, but the submitted project's source is absent.

The workflow has `max-parallel:2`, independent hosted runners, a90-minute job
limit and40-minute cache/compile phase limits. Each artifact contains only a
receipt and a log bounded to100KiB. Receipts bind the workflow/source commit,
input hashes, exact compiler binary/version, generated config, canonical
checked-out dependency revisions, actual commands and exits, streamed output
hashes, and the resulting Challenge artifact hash. Interruptions cannot be
finalized as successes.

For publication, copy `challenge-only.yml` to
`.github/workflows/challenge-only.yml` and include the source files enumerated
in `publish-files.json` plus the repository's existing root LICENSE. The
prepared push trigger is `palomar/challenge-only-diagnostic`; the root worker
may choose the final diagnostic branch name. The workflow also supports manual
selection after it is available on the appropriate workflow branch.

Source-only validation completed: Python parsed, workflow YAML parsed, matrix
parallel cap checked, all seven supplied source hashes and exact manifests
validated. No local Lean job, canonical dependency fetch or remote end-to-end
run was launched. The first remote runs remain the integration check.
