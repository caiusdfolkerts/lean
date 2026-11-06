# The Wishart product inequality and spectral correlation

This project contains the full Lean4 formalisation for all principal results in my paper *The Wishart product inequality and spectral correlation*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `Wishart`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1: product inequality, selected split, finite moments, equality case | `WishartVerification.theorem_1_1` |
| Lemma 2.1: ordered-spectrum association | `WishartVerification.lemma_2_1_association`, `WishartVerification.lemma_2_1_strict_association` |
| Lemma 2.2: independent regression representation | `Wishart.map_regressionReconstruction`, `Wishart.map_regressionJointReconstruction` |
| Lemma 3.1: the full C² radial identity, real and integer shapes, including singular covariance | `FiniteOrder.lemma_3_1_real`, `FiniteOrder.lemma_3_1_integer` |
| Lemma 3.2: Gaussian determinant order | `WishartVerification.cdf_gaussian_shift_determinant_antitone`, `WishartVerification.integral_gaussian_rankOneDeterminant_rpow_strictMono` |
| Lemma 3.3: partition radial monotonicity | `WishartVerification.lemma_3_3`, `WishartVerification.strictMonoOn_radial_full_determinant` |
| Proportional shifts and Proposition 4.1: exponent monotonicity and tilted spectral domination | `WishartVerification.proportional_shift_product_inequalities`, `WishartVerification.proposition_4_1` |
| Theorem 5.1: overlapping determinant functions and all rank clauses | `theorem_5_1_complete` |
| Theorem 5.2: convex spectral gauges | `theorem_5_2_complete` |
| Theorem 5.3: convex functions of logarithmic spectra | `theorem_5_3_complete` |
| Corollary 5.4: singular integer Gaussian Gram laws | `corollary_5_4_complete` |
| Theorem 6.1: inverse-Wishart spectral association | `theorem_6_1_on_positiveOrderedSpectrum` |
| Corollary 6.2: inverse-Wishart powers and exact moments, including empty compressions | `corollary_6_2_positive_ranks`, `corollary_6_2_finite_moment_iff_positive_ranks`, `corollary_6_2_gamma_moment_effective_rank` |
| Theorem 6.3: beta-II inequalities after removing actual almost surely constant factors | `theorem_6_3_ae_constant_rank` |
| Beta-II exact moment range and gamma formula, including empty compressions | `theorem_6_3_finite_moment_iff_positive_ranks`, `theorem_6_3_gamma_moment_effective_rank` |
| Theorem 7.1: complex and quaternionic densities and singular Gram laws | `theorem_7_1` |
| Lemma 7.2: general row monotonicity with extended logarithms and zero-valued factors | `FieldGaussian.complex_row_logsubharmonic_product`, `FieldGaussian.quaternion_row_logsubharmonic_product` |
