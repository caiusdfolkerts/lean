# Current Challenge diagnostic revision07

Selected inputs are the owner-frozen corrected Deformed952, Alternating741,
Toric categorical176, and Sublattice main/Rees339 Challenges. Their previous
failed snapshots and receipts remain immutable. No unchanged passing case or
unfrozen repair is rerun.

This checks independent Challenge elaboration with intentional theorem
placeholders. It is not a Solution build, Comparator, mathematical verification,
full preflight or registry intake. Source toolchains and entire manifests stay
unchanged. Deformed/Alternating use4.36.0-rc1/Mathlib2cab; Sublattice uses
4.35.0/Mathlib56a. Toric uses4.35.0 and exact upstream TauCeti1f9/Mathlib074
closure, with only the original direct TauCeti requirement and no override.

Current resource policy:8GiB per standard16GiB runner, one compiler per job,
max-parallel2,40-minute compile bound. Both workflow copies and runner defaults
use8GiB. Historical4GiB belongs only to revision01. Project default targets and
local supporting libraries are absent from the generated canonical workspace.

Source, manifest, compiler, canonical Git revisions, actual commands/exits,
bounded100KiB logs and output artifact hashes are bound in receipts. Pipeline
policy helpers remain pinned14aa8d6b3c2f14a8540605e37144560b9a00e7e7.

Preparation checked exact owner-frozen source hashes and Python/YAML only;
no local compiler or dependency build. Root owns publication and verification.
