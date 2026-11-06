# The Wishart product inequality and spectral correlation

This project formalises Caius Folkerts’s *The Wishart product inequality and spectral correlation*. It includes the real Wishart product theorem and equality case, the overlapping-compression and spectral extensions, inverse-Wishart and beta-II laws with exact moment ranges, and the complex and quaternionic results. The supporting probability, matrix analysis, and boundary arguments are included in the source.

[Paper](paper.pdf) · [Mathematical explanation](formalisation.md) · [Theorem correspondence](verification/theorem-scope.md) · [Recovery and completion record](recovery.md)

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source, literal statements of the main results, and an audit of every local mathematical declaration, including the vendored support library. Selected paper endpoints must be theorems with proof bodies, and their transitive axioms must be among `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

The optional command `python3 verification/verify.py` also records source hashes, dependency revisions, the build result, and the checked endpoint types in `.lake/reports/`. See [the verification contract](verification/theorem-scope.md#what-the-build-checks) for the precise trust boundary.

The [publication build](verification/build-result.json) passed on 6 November 2026: 9,589 local theorems in 298 imported modules, including the vendored support, and all 175 selected endpoints. The run checked 11,161 local declarations and kept the source and all nine dependency revisions unchanged. The [full dependency and exact-type report](verification/kernel-dependencies.json.gz) is supplied as compressed JSON.

## Main results

Declaration names below use the namespace `Wishart`, except where shown otherwise.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1: product inequality, selected split, finite moments, equality case | `WishartVerification.theorem_1_1` |
| Lemmas 2.1–2.2: ordered-spectrum association and independent regression representation | [Supporting lemmas](verification/theorem-scope.md#supporting-lemmas) |
| Lemma 3.1: the full C² radial identity, real and integer shapes, including singular covariance | `FiniteOrder.lemma_3_1_real`, `FiniteOrder.lemma_3_1_integer` |
| Lemmas 3.2–3.3: Gaussian determinant order and partition radial monotonicity | [Supporting lemmas](verification/theorem-scope.md#supporting-lemmas) |
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
| Section 7 examples: polynomial, Schur, elementary, trace and invariant-norm factors | [Example endpoints](verification/theorem-scope.md#examples-and-closure) |

The [formalisation note](formalisation.md) explains the proof mechanisms and the distinctions between the real, inverse, and other-field cases. The [scope table](verification/theorem-scope.md) also covers the overlap counterexample, closure operations, and finite moments of the final examples.

## Manuscript corrections

The included paper corrects two points found during the correspondence review. The Anderson argument on page 14 now compares opposite sections directly, so it does not assert concavity across empty sections. The exact positive-moment threshold on pages 18 and 20 sums exponents only over positive-rank compressions: a zero-column determinant is identically one. [The formalisation note](formalisation.md#manuscript-corrections) explains both changes; [the correction record](verification/manuscript-corrections.json) records their locations and hashes.

## Source organisation

`source/wishart_main.lean` is the mathematical entry point. `source/wishart/verified/` contains the paper development; `source/tau_ceti/` contains its vendored support library; `source/verification/` contains the statement and dependency checks. Original topic names are retained in `Source:` comments inside the assembled modules. [The source index](verification/source-index.md) provides navigation without maintaining a second copy of the proofs.

Original code and documentation use Apache 2.0. The paper retains its existing copyright, and third-party notices are preserved in the source and `licenses/`.
