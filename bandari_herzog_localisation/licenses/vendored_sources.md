# Vendored proof sources

The files `CommAlg/ExteriorPower/BaseChange.lean`, `CommAlg/ExteriorPower/Product.lean`, and `CommAlg/KoszulComplex/Complex.lean` are adapted from the Mathlib pull request leanprover-community/mathlib4#34913, head commit `c7780ed427bbed31ee0c430a5594ed5ea4c7d5b5`, from the public repository `Thmoas-Guan/mathlib4_fork`. The upstream authors are Nailin Guan, Jingting Wang, Yi Yuan, and Yongle Hu; original copyright and Apache 2.0 license headers are retained. The unmerged status of that pull request is not taken as mathematical evidence: every imported proof is compiled and kernel checked against this project's pinned Lean and Mathlib. Imports are renamed into `CommAlg`; any compatibility changes are recorded in the sources.

The 11 modules below are imported from TauCetiProject/TauCeti, commit `06d5bb4e3ebb737dc6538567f5c53bf8800b9362`, under their original Apache 2.0 headers. They supply verified exterior-basis contraction formulas. Every module is compiled against this project’s pin; no upstream build status is assumed.

- `TauCeti.Algebra.Homology.HomologicalComplex.Basic`
- `TauCeti.Algebra.Homology.Homotopy`
- `TauCeti.Algebra.Homology.Linear`
- `TauCeti.Algebra.Ring.Subgroup`
- `TauCeti.LinearAlgebra.CliffordAlgebra.Contraction`
- `TauCeti.LinearAlgebra.CliffordAlgebra.Grading`
- `TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction`
- `TauCeti.LinearAlgebra.ExteriorPower.Basic`
- `TauCeti.RingTheory.Ideal.Operations`
- `TauCeti.RingTheory.KoszulComplex.Basic`
- `TauCeti.RingTheory.KoszulComplex.Basis`
