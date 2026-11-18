# Read-only raw metadata diagnostic (prepared, not run)

This is separate from Palomar preflight. It does not replace Comparator,
Lean's kernel, NanoDa or con-ron, and must never be reported as a preflight pass.
No official workflow or verifier source is modified.

The pinned pipeline is `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.
Its `verify_submission.py execute` accepts an explicit work directory. It
retains `exports/challenge.export`, `exports/solution.export` and
`protected-comparator.json` after Comparator failure: the `stop` function
returns after writing the report, and the outer `finally` only restores
resource-accounting globals. Thus a wrapper can audit the same build in the
same remote job, without a second build or re-export. There is no supported
post-execution hook in the reusable workflow; callers cannot append steps to
a reusable-workflow job. Use a separate diagnostic job with the pinned
workflow's ordinary setup, prepare, toolchain and bubblewrap installation.

After the normal setup and prepare steps, replace only the job's execute
invocation with the wrapper invocation below. The wrapper invokes the
unmodified official CLI exactly once, then reads its retained exports.

```sh
python3 audit_retained_exports.py \
  --pipeline-root "$GITHUB_WORKSPACE/pipeline" \
  --work-dir "$RUNNER_TEMP/palomar" \
  --report "$RUNNER_TEMP/mechanical-report.json" \
  --output-dir "$RUNNER_TEMP/raw-metadata-diagnostic" \
  --audit-lean "$GITHUB_WORKSPACE/diagnostics/AuditExports.lean" \
  --execute --bwrap "$PALOMAR_BWRAP" \
  --workflow-url "$GITHUB_SERVER_URL/$GITHUB_REPOSITORY/actions/runs/$GITHUB_RUN_ID"
```

Upload only `audit-receipt.json` and `audit-bounded.log` (up to100KiB).
Do not upload/transfer exports. The wrapper checks their actual sizes before
hashing/parsing and refuses a combined size over1GiB by default. Raise that
cap only after inspecting exact sizes and remote runner resources.

Empirical memory from existing official reports: ellipsoid Comparator used
924788KiB RSS, Higher Specht940556KiB. Their export-phase disk peaks were
228.5/465.8MB and27.0/585.4MB respectively; these are phase peaks, not exact
export sizes. The diagnostic reconstructs the same two environments, then
keeps an additional visited-name set/worklist. A2GiB Lean heap cap and a
single remote process are the starting budget; this estimate is unverified.
No downloaded preflight artifact contains exports: the official workflow
uploads only the bounded mechanical JSON. Past hosted-runner exports cannot
be recovered from those artifacts.

Status: Python syntax checked. Lean diagnostic remains uncompiled pending a
small local toolchain-only slot. It imports no project or Mathlib module.
