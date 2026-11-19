# Third-party proof sources

The `vendor/TauCeti` subtree contains the transitive source dependencies of the
regular-sequence Koszul exactness theorem, homogeneous Groebner-basis machinery,
alternating-matrix coordinates, complete symmetric polynomials, and internal
graded-module decomposition and quotient machinery, complementary exterior-power
wedge pairings, homogeneous polynomial substitution, local dimension and
Cohen–Macaulay regular-sequence machinery from TauCeti, at commit
`06d5bb4e3ebb737dc6538567f5c53bf8800b9362`.

These sources are distributed under the Apache License, Version 2.0, copied
as `LICENSE.TauCeti`. Their copyright headers are retained. Exact file hashes
are recorded in `TauCeti_provenance.json`.

`PaperVerification/MatrixRank.lean` is a shortened adaptation of the same
revision's `TauCeti/LinearAlgebra/Matrix/Rank.lean`. It retains the field
minor criterion and its rank consequences, and calls the field proof directly
instead of passing through the more general domain theorem.

`PaperVerification/JacobianIsolatedOrigin.lean` includes the same revision's
short monomial-induction proof of weighted scaling, specialized to evaluation
in the coefficient ring and named `weighted_eval_scaling`.

Repository: https://github.com/TauCetiProject/TauCeti

The copied source files are part of the reproducible project. Availability
of a build cache is an optimization, not an additional mathematical hypothesis.
