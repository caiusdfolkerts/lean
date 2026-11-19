# The Wishart product inequality and spectral correlation

[![Build](https://img.shields.io/github/actions/workflow/status/caiusdfolkerts/research/project-wishart.yml?branch=main&label=&style=flat)](https://github.com/caiusdfolkerts/research/actions/workflows/project-wishart.yml)

This project contains the full Lean4 formalisation for all principal results in my paper *The Wishart product inequality and spectral correlation*. The corrected manuscript is included as paper.pdf; the exact baseline manuscript with its AI assistance disclosure is preserved under verification/.

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
Theorem 7.1, including the exact all-rank moment ranges and gamma identities.
Its fifteen principal declarations and five original supporting theorems remain
selected. Ten additional complete primitive-value specifications and four genuine
constructor/Hermitian supports are comparison obligations, not additional paper
results. Seven proof-instance targets are propositions. Ten semantic definition
values are entirely fixed by the complete literal value specifications.

The real nonsingular range is the full real-shape range alpha > p-1; a
Gaussian-row representation is not inserted as a hypothesis. Real overlap
rank conditions remove actual constant/full-rank factors as in the source.
The inverse comparison uses the actual positive ordered spectrum and retains
all integrability hypotheses and the common monotonicity direction.
Zero-column determinant factors contribute exponent zero in the exact inverse
and beta-II moment criteria. Beta-II rank removal tests actual almost sure
constancy. Complex and quaternion laws include the exact Lebesgue-density
normalization, singular Gaussian-Gram alternatives, spectral boundary values
and finite determinant powers.

Challenge imports only canonical Mathlib. Its complete literal primitives fix
Frobenius norms and inner products with the exact subtype uniformity, upper-
triangular Lebesgue normalization, the complete real and inverse laws including
invalid parameters, all rectangular congruence maps, Gaussian-Gram sampling at
every integer size and scale, and the standard quaternion representation.
The exact 215-module canonical Tau Ceti closure is retained only for the proofs
under `source/TauCeti`, with unchanged upstream bytes and licence provenance
under `licenses/vendor/tauceti`. Original paper proofs and unused readable
lower-case support copies are retained. Default proof roots register the actual
canonical closure and own paper modules. Mathlib and Lean pins are unchanged.

Preparation record dated 2026-11-19, before full workflow dispatch. Later
immutable workflow reports for this exact snapshot determine its subsequent
verification outcome.

The subsequent 36b8139a full run failed at one product-Haar support instance.
The missing product translation-measurability proof is now explicit and passed
the generic canonical test 44496902908 with no placeholders. All component
measures, the exact product formula, Challenge and theorem selection are unchanged.

The subsequent 4a25cb7f full run passed that Haar instance but failed three
generic coordinate-frame rewrite proofs. This revision proves the same
compression identities entrywise and uses an explicit compression equality
in the spectral-attainment argument. All three original statements and
matrix operations are unchanged. The genuine 190-line proof model passed
run 44503460697; the revised full package still requires its own full workflow.

The earlier full snapshot built the paper proofs and Solution successfully,
then failed strict Comparator. The repair retains every original principal
result and its complete input model. It names only the measured proposition
witnesses, proves whole superclass-record equalities, and constrains every
selected mathematical definition by its complete literal value. The finite
index and identity proof replacements also have original-formula equality
checks. The current 962-line independent Challenge passed run 44487625189, including all 27
complete value equations. All 37 genuine canonical witness and whole-record
identity proofs passed 44486271637. Source/Solution replay, strict Comparator
and mandatory kernel verification were still pending at preparation.
The six genuine original-formula preservation proofs passed run 44488469049
without placeholders. This preparation record claims no registry acceptance
or completed human review.

## Paper versions and AI disclosure

`paper.pdf` is the exact corrected archival manuscript, SHA256
`ba59bf8832e2d13d233c440b9a1808a1cb979dbfec6f8ae473adaa8f068b3cf1`.
All principal theorem statements agree with the baseline, apart from the
positive-rank index in Corollary 6.2's exact moment threshold, which agrees
with the selected formal statements. Its Gaussian-section proof uses convex
sections and Brunn-Minkowski. The original baseline with its AI assistance
disclosure and the pre-disclosure original remain under `verification/`.
`verification/paper-versions.json` records their exact hashes and distinguishes
the older correction receipt from the currently included PDF. The baseline
abstract discloses assistance from GPT-6 Astra, GPT-5.6 Sol and Kimi K3;
that disclosure is preserved here and in `formalization.yaml`. No prior prompt
history or division of work among systems is reconstructed.
