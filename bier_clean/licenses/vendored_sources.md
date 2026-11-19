# Source provenance

## Cauchy–Binet

- Upstream repository: https://github.com/chokmah-me/catalan-sun-lean
- Exact commit: `2d1890b21e946d5d61f364497b37a9fbb8790709`.
- Upstream file: `CatalanSun/CauchyBinet.lean`.
- Local file: `Bier/Forster/CauchyBinet.lean`.
- Author/copyright notice: Chokmah LLC, 2026.
- License: Creative Commons Attribution 4.0 International; full text in `vendor/CatalanSun_LICENSE`.
- Changes: namespace adapted to `Bier.Forster.CauchyBinet`, obsolete linter option removed, imports and declarations compiled with the project's pinned Lean/Mathlib. The full mathematical proof remains in the local source and is included in the transitive axiom audit.

## Convex and PL geometry

The sibling `cubical_lean` directory is an exact source/configuration match to the separately completed cubical-lower-bound project. All its local mathematical modules were independently rebuilt from source. The Bier reproduction checks all 384 recorded source/configuration hashes before using that independently checked dependency.

Its vendored foundations are:

- https://github.com/Solarys431/lean-eval-platonic-classification at `3cd00dfd965e5b9639cbf1011beea553001a290a`, Apache 2.0.
- https://github.com/qinz1yang/differential-geometry at `fd2f07fba4c6c102ba626c59153ad98da8f0d442`, Apache 2.0.

Original headers, license files, porting notes, and local dependency audits are retained in that project. These are proved Lean sources, not opaque axioms for geometric theorems.

## Pinned standard dependencies

Lean is pinned by `lean-toolchain`. Mathlib and its eight transitive packages are pinned by the exact revisions in `lake-manifest.json`. The completed cubical audit records their clean checkout revisions. The same packages are used for this project.

The user's supplied paper is included solely as the statement source for the verification; the proof-source licenses do not purport to relicense the paper.
