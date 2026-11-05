# The Hivert–Thiéry conjecture and differential normal forms

This project formalises the principal coinvariant results of Caius Folkerts’s *The Hivert–Thiéry conjecture and differential normal forms*: the full Hivert–Thiéry theorem, the sharp Artin-basis criterion, and the weighted tail theorem over arbitrary fields. It also proves the weighted Jacobian theorem, the complete isolated-hypersurface theorem, and the complete-intersection statement in full codimension, including the exact resonant defects and their equivariance. The source contains the supporting polynomial, grading, representation-theoretic, and commutative-algebra constructions needed for these statements.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

The [publication build record](verification/build-result.json) records the successful build, exact source and dependency hashes, and the combined audit of all eight selected theorem statements.

## Main results

Unless otherwise qualified, declaration names use the namespace `PaperVerification.PowerOperators`. The mathematical objects, proof dependencies, and correspondence with the paper are explained in [formalisation.md](formalisation.md).

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

The coinvariant quotients are formed from the actual vector-space sums of operator images. The basis statements identify each basis vector with its stated monomial class, and the representation statements supply equivalences of the actual actions that preserve every homogeneous piece. For the isolated-hypersurface theorem, the critical-point hypothesis supplies gradient regularity internally; the defect is the literal quotient `J(F)/H_t(F)` and is placed in its actual target degree `h + d`.

The recovered source, historical verification record, and completion changes are documented in [recovery.md](recovery.md).

The general normal-form results in §§3–5, including the noncommutative theorem (Theorem 5.1), and the positive-dimensional complete-intersection theorem (Theorem 6.4) are not yet formalised; I am working on these over the next few days.
