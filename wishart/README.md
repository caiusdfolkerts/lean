# The Wishart product inequality and spectral correlation

[![Build](https://img.shields.io/github/actions/workflow/status/caiusdfolkerts/research/project-wishart.yml?branch=main&label=&style=flat)](https://github.com/caiusdfolkerts/research/actions/workflows/project-wishart.yml)

This project contains the full Lean4 formalisation for all principal results in my paper *The Wishart product inequality and spectral correlation*. I've included the paper as paper.pdf.

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

## Palomar statement of record

The independently extracted `Challenge.lean` selects all principal theorems and
substantive corollaries: Theorem 1.1, proportional shifts and Proposition 4.1,
Theorems 5.1-5.3, Corollary 5.4, Theorem 6.1, Corollary 6.2, Theorem 6.3 and
Theorem 7.1, with the full exact all-rank moment ranges and gamma identities.
`Solution.lean` imports the substantive proofs under their original names.
The 15 principal declarations are listed in `comparator.json`, alongside five
supporting theorems and two proof-valued BorelSpace interface definitions.

The real nonsingular range is the full real-shape range alpha > p-1; a
Gaussian-row representation is not inserted as a hypothesis. Real overlap
rank conditions remove actual constant/full-rank factors as in the source.
The inverse comparison is on the actual positive ordered spectrum and retains
all single, remaining and joint integrability hypotheses and the common
monotonicity direction. Zero-column determinant factors contribute exponent
zero in exact inverse and beta-II moment criteria. Beta-II rank removal tests
actual almost sure constancy. Complex and quaternion laws include actual
Lebesgue-density normalization, singular Gaussian Gram alternatives, extended
spectral boundary values and finite determinant powers.

The Challenge imports Mathlib and canonical TauCeti at the recorded support
revision. The canonical toolchain and dependency manifest were verified to
match this project's rc1 toolchain and Mathlib pin. Solution proof imports have also been normalized to the exact canonical
TauCeti paths, so private constant module identities match the Challenge.
The supplied local support files and their notices remain retained but unused. Supporting analytic and
radial lemmas remain in the proof source and are not separate Comparator
targets. Manuscript corrections and the original paper are preserved under
`verification/`.

The independent Challenge elaborates with the exact pinned canonical TauCeti
support closure and only its 20 intended theorem placeholders. Full Solution
compilation, strict dependency comparison and independent kernel checking
remain pending. This is an unchecked packaging draft.
