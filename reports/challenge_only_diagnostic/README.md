# Current Challenge diagnostic revision04

Five explicitly owner-frozen inputs are selected in cases.json: corrected
Deformed and Alternating, newly frozen Homological, the176-line categorical
Toric Power main interface, and corrected338-line Sublattice/Rees main.
No unchanged passing case is rerun. Prior snapshots and receipts remain bound
to their immutable source commits and are not overwritten.

This is Challenge elaboration only, with intentional theorem placeholders.
It is not a Solution build, Comparator, mathematical verification, full
preflight or registry intake. The current resource policy is8GiB per standard
16GiB runner, one compiler per job, max-parallel2,40-minute compile bound.
Both workflow copies and runner defaults use8GiB. Historical4GiB results belong
to revision01 only.

Toric Power uses only the original requireTauCeti stanza, with canonical pin
1f9b4414105d86e487a4ac4c3d3397076a44d0d2 and the entire untouched upstream
manifest containing Mathlib074063781836922cb02701cd12943c9f51731afa. The runner
supports a validated direct-root subset for this case, so transitive Mathlib
is not promoted to an extra direct requirement. All manifest packages are
still validated/materialized, and BOTH canonical roots' actual checked-out
lean-toolchain files must match4.35.0. No override or local adapted TauCeti is used.
The five explicitly imported upstream TauCeti modules are built as canonical
module dependencies; no submitted project default/supporting-source build occurs.

Pinned policy helpers remain14aa8d6b3c2f14a8540605e37144560b9a00e7e7. Exact
Challenge bytes, original manifest/toolchain/config hashes, compiler, canonical
Git revisions, commands, exits and bounded100KiB logs are recorded in receipts.

Local preparation is source-only: hashes and Python/YAML parsed, no Lean build.
The Root worker owns publication and any subsequent full preflight/intake.
