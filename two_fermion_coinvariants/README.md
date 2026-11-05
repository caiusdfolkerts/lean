# Monomial bases for two-fermion coinvariants

This project formalises the principal results of Caius Folkerts’s *Monomial bases for two-fermion coinvariants*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `PaperVerification.Fermion`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1 | `theorem_1_1`, `theorem_1_1_free_rank` |
| Theorem 1.2 | `theorem_1_2`, `theorem_1_2_free_rank` |
| Proposition 2.1 | `Newton.proposition_2_1`, `Newton.monicRectangleBasis_apply` |
| Proposition 7.1 | `paired_separated_finite_iff_over_any_ring`, `strict_separated_finite_iff_over_any_ring` |
| Theorem 7.2: local structure | `theorem_7_2`, `theorem_7_2_complex` |
| Theorem 7.2: local and global dimensions | `SeparatedPairedData.localSuper_finrank`, `SeparatedPairedData.globalSuper_finrank_sum`, `SeparatedPairedData.globalSuper_finrank_closed`, `SeparatedPairedData.localRank_sum_closed` |
| Theorem 7.2: exterior Hilbert coefficients | `SeparatedPairedData.localSuper_exterior_hilbert_coefficient`, `SeparatedPairedData.globalSuper_exterior_hilbert_coefficient`, `SeparatedPairedData.localExteriorFinrank_sum` |
| Original-data correspondence for §7 | `exists_univariate_factorization`, `SeparatedCoverOfPairedData.toSeparatedData_superIdeal`, `SeparatedCoverOfPairedData.toSeparatedData_toPairedData`, `SeparatedCoverOfPairedData.originalSuperTensorProductEquiv`, `originalSuperTensorProductEquiv_complex` |
| §8.1: invariant-generated ideals | `Coinvariants.positiveInvariantIdeal_eq_paired`, `Coinvariants.positiveInvariantIdeal_eq_strict`, `Coinvariants.positiveInvariantIdeal_eq_strict_typeA` |
| §8.1 and equation (20): bases | `Coinvariants.oppositeCoinvariantBasis`, `Coinvariants.trivialColorCoinvariantBasis`, `Coinvariants.typeACoinvariantBasis`, `Coinvariants.oppositeCoinvariantBasis_apply`, `Coinvariants.trivialColorCoinvariantBasis_apply`, `Coinvariants.typeACoinvariantBasis_apply` |
| §8.1: full Hilbert formulas | `Coinvariants.oppositeCoinvariant_full_hilbert_coefficient`, `Coinvariants.trivialColorCoinvariant_full_hilbert_coefficient`, `Coinvariants.typeACoinvariant_full_hilbert_coefficient`, `Coinvariants.typeACoinvariant_physical_basis_card` |
| §8.1: parameter fields | `Coinvariants.complex_positiveInvariantIdeal_eq_paired`, `Coinvariants.complex_positiveInvariantIdeal_eq_strict`, `Coinvariants.positive_characteristic_opposite_ideal`, `Coinvariants.positive_characteristic_trivial_color_ideal` |
| §8.1: Lentfer identifications | `Coinvariants.lentferTypeA_exponent_iff`, `Coinvariants.lentferTypeB_exponent_iff` |
| Theorem 8.1 and equation (21) | `theorem_8_1`, `TypeA.equation_21` |
| Theorem 8.1: fibers and actions | `WeightRees.fiberUnit_equivariant`, `TypeA.nonzeroFiberEquiv_intertwines`, `TypeA.TheoremEightOneClaim` |
| §8.2 and equation (22) | `TypeA.polynomialPiece_paper_module_decomposition`, `TypeA.equation_22_character`, `TypeA.equation_22_diagonal_trace` |
| §8.2: Schur decomposition | `ColorSchur.polynomialPiece_schur_decomposition`, `ColorSchur.schurCopyMultiplicity_eq_coefficient`, `ColorSchur.every_schur_summand_irreducible`, `ColorSchur.summand_equivalent_iff_label` |
| §8.3 and equation (23) | `TypeA.equation_23_character`, `TypeA.diagonal_trace_eq_eulerian` |
