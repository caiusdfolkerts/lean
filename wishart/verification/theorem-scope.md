# Theorem correspondence and verification

The mathematical reference is the corrected [25-page paper](../paper.pdf). This document describes the statements that the build is required to prove. [The fixed endpoint list](required-endpoints.json) and [its expected module ownership](endpoint-modules.json) are machine-readable versions of the acceptance selection. The audit checks all local mathematical declarations, not only those endpoints.

## Real Wishart results

| Paper assertion | Endpoint | Scope retained |
| --- | --- | --- |
| Theorem 1.1 | `WishartVerification.theorem_1_1` | Actual density-defined Wishart measure, every real shape $\alpha>p-1$, arbitrary positive definite covariance, every finite principal partition, nonnegative real powers, finite subproduct moments, every selected split, full product inequality, and equality exactly for independent active blocks. |
| Random-matrix formulation | `WishartVerification.theorem_1_1_of_hasLaw` | Any measurable random matrix with the specified law. |
| Lemma 3.1, real shape | `Wishart.FiniteOrder.lemma_3_1_real` | $C\succeq0$, exactly $N>\operatorname{rank}C$, arbitrary mean direction, actual range-Wishart/Gaussian independence, local $C^2$ regularity, and polynomial bounds only for the first two derivatives and the value on the cone. |
| Lemma 3.1, integer shape | `Wishart.FiniteOrder.lemma_3_1_integer` | Every integer $N\ge1$, actual Gram matrix of $N-1$ Gaussian rows, arbitrary positive semidefinite covariance including zero, arbitrary mean direction, and the same local $C^2$ test class. |
| Proportional shifts | `WishartVerification.proportional_shift_product_inequalities` | Shifts $c_i\Sigma_{I_i,I_i}$ with $c_i\ge0$, including zero shift. |
| Proposition 4.1 | `WishartVerification.proposition_4_1` | Coordinatewise exponent monotonicity of the moment ratio and increasing-expectation domination of the selected whitened eigenvalues under the full tilt. |
| Theorem 5.1 | `Wishart.theorem_5_1_complete` | Arbitrary full-column-rank overlapping compressions; geometric determinant functions; selected and full-product rank tests; full-rank and final-pair exceptions; unrestricted monotone outer functions for the finite-moment pair case; disjoint principal blocks including empty determinant blocks. |
| Theorem 5.2 | `Wishart.theorem_5_2_complete` | Continuous nonzero convex homogeneous Loewner-increasing invariant gauges; geometric outer functions; selected $\alpha\ge q+1$ and product $\alpha\ge k_{(3)}+1$ tests, with the stated pair and full-rank exceptions. |
| Theorem 5.3 | `Wishart.theorem_5_3_complete` | Every finite convex symmetric coordinatewise increasing logarithmic spectral profile; selected rank test, largest-two-ranks product test, full-rank factors, and the paper’s distinct two-block and at-least-three-block ranges. |
| Corollary 5.4 | `Wishart.corollary_5_4_complete` | Actual positive-integer Gaussian Gram laws with positive definite covariance, including singular Gram matrices; geometric boundary values, almost surely constant factors, unrestricted final pairs, and finite nonnegative determinant-power moments. |
| Complete Section 5 package | `Wishart.real_section_five` | Conjunction of the full interfaces above. |

These statements use normalized compressions where the paper requires them. A shift by the compressed covariance is different from a scalar shift before whitening. Positive definiteness of the covariance is retained in the paper’s normalized principal results; singular Gram matrices are included without conflating them with singular covariance matrices. The radial support theory also treats the singular residual covariances that occur inside the proofs.

The two radial-mean endpoints prove absolute integrability of the test and its generator, ordinary first and second derivatives for $t>0$, the displayed differential equation, a finite right derivative at zero with the same limit of $F'(t)$, and monotonicity when the expected generator is nonnegative. The [independent radial statement gates](../source/verification/statements_radial_c2.lean) spell out the open neighborhood and the three polynomial bounds without using a regularity predicate or an assumed radial identity. Their bilinear Hessian bound is proved equivalent to the operator-norm bound by `WishartAudit.hessian_polynomial_bound_iff_bilinear_bound`. The real-law gate also verifies that its factor has exactly the covariance rank, is injective, has $LL^T=C$, and defines a probability law.

The proof extends a local test without changing its first two derivatives on the cone, proves support-restricted Stein and parameter-integration identities, and uses scalar regression with rectangular covariance transport at real shape. Covariance regularization gives the integer statement at singular covariance. Global smoothness of all orders and higher-derivative growth are not hypotheses of these endpoints.

The principal and shift formulas are checked in [statements_principal](../source/verification/statements_principal.lean) and [statements_extensions](../source/verification/statements_extensions.lean). Section 5’s complete target propositions are in [real_clauses01](../source/wishart/verified/real_clauses01.lean); they are explicit propositions whose conclusions are subsequently proved.

## Supporting lemmas

The radial mean lemma is described above, and the complex/quaternion row lemma is described below. The remaining numbered lemmas have the following concrete endpoints.

| Paper assertion | Endpoint | Scope retained |
| --- | --- | --- |
| Lemma 2.1, association | `WishartVerification.lemma_2_1_association` in [core03](../source/wishart/verified/core03.lean) | The normalized ordered-chamber Lebesgue density, positive finite normalizer, positive Vandermonde exponent, and measurable nonnegative increasing functions. The comparison uses extended nonnegative integrals, so finiteness of the observables is not an extra premise. The permitted coordinate set and nonnegative weights also cover the paper's interval and positive weights. |
| Lemma 2.1, strictness | `WishartVerification.lemma_2_1_strict_association` in [core04](../source/wishart/verified/core04.lean) | Strict increase in the last coordinate with the lower coordinates fixed, and exactly the finite second moments stated in the paper. Strict increase in every coordinate is not required. |
| Lemma 2.2 | `Wishart.map_regressionReconstruction` and `Wishart.map_regressionJointReconstruction` in [core01](../source/wishart/verified/core01.lean) | Every admissible real shape, positive definite residual covariance, and arbitrary cross matrix. The source is the explicit product of the selected Wishart law, independent Gaussian rows, and the reduced-shape residual Wishart law. The joint selected-block/full-matrix identity supplies the conditional representation and its independence assertions. |
| Lemma 3.2 | `WishartVerification.cdf_gaussian_shift_determinant_antitone` and `WishartVerification.integral_gaussian_rankOneDeterminant_rpow_strictMono` in [core02](../source/wishart/verified/core02.lean) | Stochastic monotonicity for arbitrary positive semidefinite background and covariance. Positive powers are strictly increasing when the background is positive definite and the mean direction is nonzero; the formal strict result even permits singular covariance. Gaussian power integrability is proved separately. |
| Lemma 3.3 | `WishartVerification.lemma_3_3` and `WishartVerification.strictMonoOn_radial_full_determinant` in [lemma_3_3](../source/wishart/verified/lemma_3_3.lean) | Exactly $N>m$, positive definite covariance, any positive semidefinite offset, every principal partition, all nonnegative real powers, and arbitrary mean direction. Product integrability is a conclusion. The single full block has the strict comparison stated in the proof when its power is positive and its mean direction is nonzero. |

The [literal partition gates](../source/verification/statements_radial_partition.lean), `WishartAudit.lemma_3_3_literal` and `WishartAudit.lemma_3_3_single_block_strict_literal`, display the actual principal submatrices and independent Wishart/Gaussian product measure. Proper blocks satisfy the generator's dimension bound automatically. A full single block uses the one-determinant comparison, which preserves the admissible shapes $m<N<m+1$ as well.

## Inverse-Wishart and beta-II

| Paper assertion | Endpoint | Scope retained |
| --- | --- | --- |
| Theorem 6.1 | `Wishart.theorem_6_1` | Actual inverse-Wishart law; arbitrary overlaps; nonnegative measurable spectral functions with a common increasing or decreasing direction; the finite relevant integrals specified by the theorem. |
| Natural positive spectral domain | `Wishart.theorem_6_1_on_positiveOrderedSpectrum` | Functions stated on the ordered positive eigenvalue domain. |
| Corollary 6.2 inequality | `Wishart.corollary_6_2_positive_ranks` | Nonnegative powers under the effective-rank moment condition, or arbitrary nonpositive powers with nonnegative shifts, including zero. |
| Corollary 6.2 exact finiteness | `Wishart.corollary_6_2_finite_moment_iff_positive_ranks` | Necessity and sufficiency of $2\sum_{k_i>0}\nu_i<\beta-p+1$. |
| Corollary 6.2 gamma formula | `Wishart.corollary_6_2_gamma_moment_effective_rank` | Exact unshifted compression moment, including the rank-zero exception. |
| Rank-zero correction | `Wishart.Audit.inverse_rank_zero_moment_threshold_edge_case` | Explicit failure of the uncorrected all-exponent threshold when a compression has zero columns. |
| Beta-II density and mixture | `WishartVerification.Audit.betaII_density_eighteen_normalized`, `WishartVerification.Audit.betaII_actual_hierarchy_and_independent_congruence` | The concrete density is normalized and agrees with both the conditional Wishart hierarchy and the independent congruence mixture. The historical declaration suffix `eighteen` is retained; the current paper numbers the beta-II density (19). |
| Theorem 6.3 | `Wishart.theorem_6_3_ae_constant_rank` | Actual-law almost-sure constant-factor removal, full-rank removal, and the permutation-invariant rank test. |
| Beta-II disjoint principal blocks | `Wishart.theorem_6_3_disjoint_principal_blocks_allow_empty` | Every admissible shape pair, including empty principal determinant factors. |
| Beta-II exact finiteness | `Wishart.theorem_6_3_finite_moment_iff_positive_ranks` | The same necessary and sufficient effective-rank threshold. |
| Beta-II gamma formula | `Wishart.theorem_6_3_gamma_moment_effective_rank` | The exact Wishart/inverse-Wishart gamma product with the unrestricted rank-zero moment domain. |

The normalization conclusions matter: normalizing an infinite extended integral by its inverse could otherwise produce the zero measure. The acceptance statements require positive finite normalizers and probability mass, rather than assuming those properties or accepting a comparison under a potentially vacuous measure.

The exact moment statements distinguish finite real integrals from extended nonnegative integrals. Finiteness is proved where claimed; general profile comparisons remain extended inequalities. Empty determinants are one and contribute no positive-tail restriction. The [inverse gates](../source/verification/statements_inverse.lean), [beta-II law gates](../source/verification/statements_beta_ii.lean), and [beta-II moment gates](../source/verification/statements_beta_ii_moments.lean) state these distinctions explicitly.

## Complex and quaternionic fields

`Wishart.theorem_7_1` combines six conclusions: complex and quaternionic normalization, complex and quaternionic spectral comparison, and finite nonnegative determinant-power moments over both fields. The individual endpoints are `theorem_7_1_complex_normalization`, `theorem_7_1_quaternion_normalization`, `theorem_7_1_complex`, `theorem_7_1_quaternion`, `theorem_7_1_complex_finite_powers`, and `theorem_7_1_quaternion_finite_powers`.

Both concrete laws are included: the normalized density for every real shape $\alpha>p-1$, and the actual Gaussian Gram image for every integer row count $n\ge1$. Covariance is positive definite as in the printed theorem. A Gram matrix may be singular. Compression matrices have full column rank and may overlap arbitrarily. There is no additional rank restriction. Shifts are nonnegative, logarithmic profiles are finite convex symmetric and coordinatewise increasing, and their boundary values are obtained by decreasing positive scalar regularization. The comparisons include every selected split and every finite subfamily.

The [field statement gates](../source/verification/statements_field.lean) also fix the definitions on which these claims depend: covariance whitening, determinant/eigenvalue correspondence, quaternionic positive cones and full column rank, the complex representation of quaternionic rank, real Gaussian component variance $1/b$, covariance factors, Gram pushforwards, and the literal density exponents and normalization. The `_of_hasLaw` theorems transport the canonical-law results to arbitrary random matrices with those laws.

### Lemma 7.2 with zero-valued factors

`Wishart.FieldGaussian.complex_row_logsubharmonic_product` and `Wishart.FieldGaussian.quaternion_row_logsubharmonic_product` in [field_row_logsubharmonic](../source/wishart/verified/field_row_logsubharmonic.lean) prove the full abstract row lemma. The factors are nonnegative and continuous only on the positive semidefinite cone, with polynomial upper bounds there. The Gaussian law is the actual image of a standard row under an arbitrary rectangular covariance factor, so singular covariance is included. Compressions and positive semidefinite offsets are arbitrary, and factors may vanish or be identically zero. Integrability of the product and monotonicity of its expectation are conclusions.

The extended logarithmic hypothesis is represented by a nonnegative defect: on a ball where $\log f\le M$, put $D_M=M-\log f$, with $D_M=+\infty$ at a zero. Its average is at most its value at the center. This is the extended logarithmic submean inequality, without an undefined difference of infinite integrals. [extended_log_submean](../source/wishart/verified/extended_log_submean.lean) proves that the inequality passes to $\max(f,\varepsilon)$, then proves the ordinary submean inequality for finite products by decreasing positive truncations. Polynomial bounds supply the integrable Gaussian envelope; unit-scalar invariance supplies radiality.

The [literal row-lemma gates](../source/verification/statements_row_logsubharmonic.lean), `WishartAudit.lemma_7_2_complex_literal` and `WishartAudit.lemma_7_2_quaternion_literal`, state the defect integral explicitly. They assume neither product subharmonicity, an integrable dominating function, nor the desired expectation comparison. These general endpoints are separate from the spectral specializations used by Theorem 7.1.

## Examples and closure

The explicit real overlap obstruction is developed in [overlap_obstruction](../source/wishart/verified/overlap_obstruction.lean). Its covariance is calculated under the actual $W_2(\alpha,I)$ law, with moments obtained from the Bartlett coordinates. The negative parameter range and the rational example $\alpha=3/2$, $a=1/4$ explain why an unrestricted three-factor real split is false. The public endpoints `Wishart.OverlapObstruction.covariance_rank_one_overlap`, `covariance_rank_one_overlap_neg`, and `covariance_rank_one_overlap_three_halves` give the general identity, negative range, and exact rational value; `rank_one_overlap_split_fails` states the strict failure of the proposed split. The displayed conditional-mean identity is proved by `conditional_mean_rank_one_overlap_bartlett` for the sigma algebra generated by the selected matrix entry, and `bartlett_realizes_wishart` identifies that realization's actual Wishart law. Integrability and the individual and joint moment formulas are proved separately.

| Final-section assertion | Endpoint families |
| --- | --- |
| Unnormalized determinant powers and geometric determinant functions | `Wishart.complex_unnormalizedDeterminantPower_comparison`, `quaternion_unnormalizedDeterminantPower_comparison`, `complex_geometricDeterminant_comparison`, `quaternion_geometricDeterminant_comparison` |
| Polynomial, elementary, Schur-positive, trace-power and invariant-norm comparisons | The paired `Wishart.complex_*_comparison` and `Wishart.quaternion_*_comparison` endpoints in [field_residual08](../source/wishart/verified/field_residual08.lean) and [field_residual09](../source/wishart/verified/field_residual09.lean) |
| Products, nonnegative sums and geometric outer composition | `Wishart.Spectral.productProfile_properties`, `nonnegativeSumProfile_properties`, `nonnegativeSum_zero_or_profile`, `outerCompositionProfile_properties`, and their three `spectralBoundaryValue_*` identities |
| Polynomial and symmetric-norm moment envelopes | The four theorems in [spectral_example_moments](../source/wishart/verified/spectral_example_moments.lean) |
| Probability mass, trace moments and shifted compression eigenvalue moments under actual field laws | The nine theorems in [field_spectral_moments](../source/wishart/verified/field_spectral_moments.lean) |
| All finite moments and finite joint moments for uncomposed polynomial, trace-power and invariant-norm-power examples | The twelve paired complex/quaternionic theorems in [field_example_finite_moments](../source/wishart/verified/field_example_finite_moments.lean) |

The zero-sum alternative in the closure result and the singular spectral boundary identities are included. The finite-moment conclusions concern the uncomposed examples specified by the paper; arbitrary convex logarithmic profiles need not have finite expectation.

## What the build checks

The default Lake target includes every mathematical module and all statement gates. [complete.lean](../source/verification/complete.lean) imports local modules with proof bodies available and determines declaration ownership from the imported module tables. It does not infer ownership from a convenient namespace prefix.

The audit enumerates every local declaration, including vendored TauCeti declarations, and rejects local mathematical axioms and unapproved transitive axioms. Every selected endpoint must exist in its expected module as an actual theorem with a proof body, and its type and proof must be closed. Unsafe or partial declarations on traversable theorem dependency paths are rejected. The permitted foundational axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

For each selected theorem, the audit exports its exact type as a lossless expression DAG, decodes that serialization, and compares it structurally with the checked type before writing the report. The endpoint list and ownership table are fixed data. [generate_audit.py](generate_audit.py) refreshes explicit imports and those selections; generating the configuration is not a verification result.

The local source is compiled with kernel checking enabled. The audit additionally examines the imported checked environment; it is not an independent implementation of Lean’s kernel. For external Lean/Mathlib library bodies that are unavailable in the imported environment, dependency inspection stops at the library’s recorded axiom summary, and the report identifies that boundary. Thus the ordinary trust in the pinned Lean compiler, standard library, Mathlib, and their compiled artifacts remains explicit. The exact-type serializer itself is audit infrastructure and supplies no mathematical axioms.

`lake build` writes the current dependency report under `.lake/reports/audit/`. The optional [verification runner](verify.py) reruns the audit, verifies all nine dependency checkouts against the pinned manifest, records compiler identity, checks that source and configuration are unchanged during the build, and writes `.lake/reports/build-result.json`. It starts with `passed: false` and records success only after the build and every acceptance condition pass. Failed or interrupted attempts remain unsuccessful records. The [publication receipt](build-result.json) records the successful 6 November 2026 run: 298 imported local modules, 11,161 declarations, 9,589 theorems, and all 175 selected endpoints. It links the unmodified full receipt, exact-type dependency report, and build log as lossless gzip files, with compressed and uncompressed hashes. Source edits require a new run.

The verification layers answer different questions. Compilation checks the proof terms. The axiom and ownership audit checks what those terms depend on. Literal statement gates and the paper correspondence review check that the proved propositions express the intended mathematics. A filename containing `Verified`, a static search without `sorry`, or a successful cache download establishes none of these by itself.
