# Current Challenge diagnostic revision03

This revision checks the owner-frozen corrected Barycentric main/scalar and symmetric-rank
Challenges listed in cases.json. Other corrected failed cases are added only
after explicit owner confirmation; unchanged passing cases are not rerun.

This is Challenge elaboration only, with intentional theorem placeholders.
It is not a Solution build, Comparator run, mathematical verification, full
preflight or registry intake. Canonical dependencies, source imports, exact
original manifests and exact toolchain files are preserved.

Current resource policy:8GiB Lean heap per standard16GiB remote runner,
one compiler per job, matrix max-parallel2,40-minute compile bound. Both the
actual .github workflow and reports/challenge_only_diagnostic/challenge-only.yml
carry this policy; the runner's command-line default is also8GiB.

Historical evidence is preserved: revision01 commit6684cf191a9441d9693ffe7e82c607149ad8ed4c,
run44325375620 used4GiB; its four source failures and two memory failures are
not overwritten. Revision02 commitb03c6d3c089e7a3d74363b252ba7e22e1043ce7e
checks four independent new candidates and two unchanged memory retries.

The pinned pipeline policy helper commit remains
14aa8d6b3c2f14a8540605e37144560b9a00e7e7. The generated workspace contains
only the Challenge and exact canonical roots/closures; original project
Lakefiles/default targets never execute. No lake update or pin override is used.
Source, compiler, manifest, actual dependency revisions, commands, exits and
bounded log hashes are bound in each receipt. Logs are bounded to100KiB.

Local preparation: source hashes and Python/YAML parsed only. No local Lean
job or remote execution has been launched by this worker. Root publishes the
ready overlay and remains responsible for subsequent verification/intake.
