# The Hivert–Thiéry conjecture and differential normal forms

This project contains the full Lean4 formalisation of the principal coinvariant theorems and most algebraic results in my paper *The Hivert–Thiéry conjecture and differential normal forms*. I’m still working on the remaining results, which I expect to be ready in a few days.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `PaperVerification.PowerOperators`.

| Paper result | Lean statement |
| --- | --- |
| **Theorem 1.1: every clause** | `paper_theorem_1_1` |
| Theorem 1.1: the specified Artin basis | `paper_theorem_1_1_monomial_basis` |
| Theorem 1.1: graded equivalence for the full symmetric group | `paper_theorem_1_1_sufficiency` |
| Theorem 1.1: necessity at every excluded parameter, for every `n ≥ 2` | `paper_theorem_1_1_artin_necessity`, `original_artin_spanning_iff` |
| Exact exceptional parameter set | `exceptionalSet`, `nonresonant_one_iff` |
| **Theorem 2.2: every clause** | `paper_theorem_2_2` |
| Theorem 2.2 and equation (2.2): the specified weighted Artin basis | `paper_theorem_2_2_basis`, `paper_theorem_2_2_basis_apply`, `paper_theorem_2_2_monomial_basis` |
| Theorem 2.2: the complete Hilbert series | `paper_theorem_2_2_hilbert_polynomial` |
| Theorem 2.2: graded equivalence for every subgroup fixing the coefficients | `paper_theorem_2_2_graded_representation` |
| Theorem 2.2: the power-sum comparison for equal coefficients | `paper_theorem_2_2_equal_coefficient_power_sums` |
| Theorem 2.2 and equation (2.3): the original operator family | `paper_theorem_2_2_original_monomial_basis`, `paper_theorem_2_2_original_hilbert_polynomial`, `paper_theorem_2_2_original_graded_representation`, `paper_theorem_2_2_original_equal_coefficient_power_sums` |
| Original infinite tail and finite presentation | `tailHit_eq_firstTailHit`, `diagonalEquiv_original`, `diagonalEquiv_map_originalTailHit` |
| Positive-characteristic stabilizer condition used in Theorem 2.2 | `Nonresonant.isUnit_stabilizer_card` |
| **Theorem 6.2: weighted Jacobian equality on the paper’s full nonresonant range** | `PaperVerification.EulerJacobian.paper_theorem_6_2` |
| Theorem 6.2 over arbitrary characteristic-zero fields | `PaperVerification.EulerJacobian.jacobian_hit_eq_of_nonresonant` |
| **Theorem 6.3: all scalar conclusions, including equation (6.1)** | `PaperVerification.JacobianDivergence.paper_theorem_6_3_scalar` |
| Theorem 6.3: every homogeneous lift of every homogeneous Milnor basis is a basis over the actual subalgebra `ℂ[F]` | `PaperVerification.JacobianDivergence.paper_theorem_6_3_basis_lifts` |
| Theorem 6.3: equivariant decomposition (6.2), natural exact sequence, and homogeneous equivariant splitting | `PaperVerification.JacobianDivergence.paper_theorem_6_3_equivariant` |
| Theorem 6.3: canonical defect map with the paper’s ordered Hamiltonian denominator | `PaperVerification.JacobianDivergence.paperHamiltonianDefectEquiv` |
| **Proposition 6.5: all scalar conclusions, the exact exceptional set, and every integer-degree Hilbert coefficient** | `PaperVerification.VectorEuler.paper_proposition_6_5_scalar` |
| Proposition 6.5: equivariance for every linear group preserving the weights and each equation | `PaperVerification.VectorEuler.paper_proposition_6_5_equivariant` |
| Proposition 6.5: canonical equivalence from the actual polynomial degree piece to the literal defect | `PaperVerification.VectorEuler.regularDefectEquiv`, `PaperVerification.VectorEuler.regularDefectEquiv_canonical` |
