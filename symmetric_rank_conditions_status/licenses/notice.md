# Source provenance and license

This distribution retains the original copyright and attribution comments in the
Lean source files. The project is distributed under the Apache License, version
2.0; see `LICENSE`.

- Tau Ceti, <https://github.com/TauCetiProject/TauCeti>, revision
  `5ce4390a0a9a3277d048f680244409f42e9faeda`: monomial-order, Gröbner, and
  tableau infrastructure. Included source was adapted to the pinned Mathlib APIs.
- Tau Ceti dimension theory, revision
  `06d5bb4e3ebb737dc6538567f5c53bf8800b9362`: required integral and finite-type
  dimension arguments, adapted into the rank-stratum compilation unit with their
  original attribution.
- Ordinary Greene theorem, <https://github.com/elazarg/rsk>, revision
  `fb221a3608a2c125869bc6132354af50f38c4c2d`: Young-diagram and Greene-word
  infrastructure. Adaptations avoid redeclaring a result already provided by
  Mathlib, update API arguments and order selections, and use noncomputable definitions where
  runtime evaluation is unnecessary.
- The user's earlier manuscript-development checkpoints: symmetric definitions,
  leading-minor and symbolic-power foundations, and subsequent project proofs.
- The user's earlier homological-shifts checkpoint: integer-weight and
  ideal-integrality foundations retained in `IdealIntegralityFoundation.lean`.

Some original modules were assembled into larger compilation units while
preserving their mathematical commands and local scopes. Exact reading extracts
and authenticated source-location mappings are provided in `reading/`.
The source exporter does not establish compilation success; current compiler and
axiom-audit evidence is supplied separately in the release documentation.
