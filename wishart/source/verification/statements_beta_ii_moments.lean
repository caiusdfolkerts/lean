module

public import wishart.verified.real_tail01

@[expose] public section

/-!
# Literal beta-II moment targets, including zero-column compressions

The integrands and gamma constants are written out independently of the
product and moment abbreviations. The assignments below check these literal
statements against the proved declarations.
-/

noncomputable section

open Matrix MeasureTheory TauCeti TauCeti.Probability
open scoped Classical BigOperators ENNReal Matrix

namespace WishartVerification.Audit

/-- The sum excludes precisely the exponents of empty determinants. -/
theorem betaII_joint_moment_exact_positive_rank_sum {p d : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i) :
    Integrable (fun X : WishartVerification.SymmetricMatrix p =>
      ∏ i, ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det ^ ν i)
        (Wishart.matrixBetaIIMeasure α β Omega) ↔
      2 * (∑ i ∈ Finset.univ.filter (fun i => 0 < k i), ν i) < β - p + 1 := by
  change Integrable (Wishart.compressionDeterminantProduct k B ν Finset.univ)
      (Wishart.matrixBetaIIMeasure α β Omega) ↔ _
  exact Wishart.theorem_6_3_finite_moment_iff_positive_ranks hOmega hα hβ k B hB ν hν

/-- The same exact criterion in the literal extended-expectation form.
The conversion from Bochner integrability uses proved almost-sure
nonnegativity of the actual compressed determinants. -/
theorem betaII_joint_lintegral_finite_iff_positive_rank_sum {p d : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i) :
    (∫⁻ X : WishartVerification.SymmetricMatrix p,
      ENNReal.ofReal (∏ i,
        ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det ^ ν i)
          ∂Wishart.matrixBetaIIMeasure α β Omega) < ⊤ ↔
      2 * (∑ i ∈ Finset.univ.filter (fun i => 0 < k i), ν i) < β - p + 1 := by
  have hnonneg : ∀ᵐ X : WishartVerification.SymmetricMatrix p
      ∂Wishart.matrixBetaIIMeasure α β Omega,
      0 ≤ ∏ i, ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det ^ ν i := by
    filter_upwards [Wishart.ae_posDef_matrixBetaIIMeasure α β Omega] with X hX
    exact Finset.prod_nonneg (fun i _ ↦ Real.rpow_nonneg
      (Wishart.compressionScale_posDef hX (B i) (hB i)).det_pos.le _)
  constructor
  · intro hfinite
    apply (betaII_joint_moment_exact_positive_rank_sum hOmega hα hβ k B hB ν hν).mp
    have hm : Measurable (fun X : WishartVerification.SymmetricMatrix p =>
        ∏ i, ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det ^ ν i) :=
      Wishart.measurable_compressionDeterminantProduct k B ν Finset.univ
    exact ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnonneg).mpr hfinite⟩
  · intro hthreshold
    have hI := (betaII_joint_moment_exact_positive_rank_sum
      hOmega hα hβ k B hB ν hν).mpr hthreshold
    exact (hasFiniteIntegral_iff_ofReal hnonneg).mp hI.2

/-- When every compression has positive rank, the corrected criterion is
literally the unrestricted-overlap condition printed after Theorem 6.3. -/
theorem betaII_joint_moment_exact_nonempty_compressions {p d : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i) :
    Integrable (fun X : WishartVerification.SymmetricMatrix p =>
      ∏ i, ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det ^ ν i)
        (Wishart.matrixBetaIIMeasure α β Omega) ↔
      2 * (∑ i, ν i) < β - p + 1 := by
  change Integrable (Wishart.compressionDeterminantProduct k B ν Finset.univ)
      (Wishart.matrixBetaIIMeasure α β Omega) ↔ _
  exact Wishart.theorem_6_3_finite_moment_iff hOmega hα hβ k B hB ν hν (fun i _ ↦ hk i)

/-- The full marginal formula retains both actual multivariate gamma ratios.
There is no restriction on the exponent in the zero-column branch. -/
theorem betaII_gamma_moment_all_ranks {p k : ℕ} {α β r : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (hr : k = 0 ∨ (0 ≤ r ∧ 2 * r < β - p + 1)) :
    Integrable (fun X : WishartVerification.SymmetricMatrix p =>
      (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r)
        (Wishart.matrixBetaIIMeasure α β Omega) ∧
    (∫ X : WishartVerification.SymmetricMatrix p,
      (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r
        ∂Wishart.matrixBetaIIMeasure α β Omega) =
      (Bᵀ * Omega * B).det ^ r *
        (multivariateGamma k (α / 2 + r) / multivariateGamma k (α / 2)) *
          (multivariateGamma k ((β - p + k) / 2 - r) /
            multivariateGamma k ((β - p + k) / 2)) := by
  refine ⟨Wishart.integrable_compression_det_rpow_matrixBetaII_effective_rank
    hOmega hα hβ B hB hr, ?_⟩
  simpa only [Wishart.compressionScale] using
    Wishart.theorem_6_3_gamma_moment_effective_rank hOmega hα hβ B hB hr

/-- This separate replay root states the zero-column case for every real
exponent, with no inferred finite-moment inequality as a premise. -/
theorem betaII_zero_column_moment_every_real_exponent {p : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (B : Matrix (Fin p) (Fin 0) ℝ) (r : ℝ) :
    Integrable (fun X : WishartVerification.SymmetricMatrix p =>
      (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r)
        (Wishart.matrixBetaIIMeasure α β Omega) ∧
    (∫ X : WishartVerification.SymmetricMatrix p,
      (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r
        ∂Wishart.matrixBetaIIMeasure α β Omega) = 1 :=
  Wishart.theorem_6_3_zero_column_moment hOmega hα hβ B r

/-- A concrete counterexample to carrying the unmodified sum in equation
(18) over to beta-II when zero-column full-column-rank matrices are allowed.
Here `p = α = β = 1`, `Omega = I`, `B` has zero columns, and its exponent is
one. The actual determinant factor has expectation one although `2 < 1`
fails. This corrects that literal endpoint; it is not a refutation of the
positive-rank theorem. -/
theorem betaII_rank_zero_moment_threshold_edge_case :
    (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧
    ((1 : ℕ) : ℝ) - 1 < (1 : ℝ) ∧
    ((1 : ℕ) : ℝ) - 1 < (1 : ℝ) ∧
    IsProbabilityMeasure
      (Wishart.matrixBetaIIMeasure 1 1 (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
    Wishart.Audit.rankZeroCompression.rank = 0 ∧
    (∀ X : Wishart.Audit.ScalarSymmetricMatrix, Wishart.Audit.rankZeroFactor X = 1) ∧
    Integrable Wishart.Audit.rankZeroFactor
      (Wishart.matrixBetaIIMeasure 1 1 (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
    (∫ X, Wishart.Audit.rankZeroFactor X
      ∂Wishart.matrixBetaIIMeasure 1 1 (1 : Matrix (Fin 1) (Fin 1) ℝ)) = 1 ∧
    ¬ (2 * (∑ _i : Fin 1, (1 : ℝ)) < (1 : ℝ) - (1 : ℕ) + 1) := by
  have hshape : ((1 : ℕ) : ℝ) - 1 < (1 : ℝ) := by norm_num
  have hm := betaII_zero_column_moment_every_real_exponent
    (p := 1) (α := 1) (β := 1)
    (Omega := (1 : Matrix (Fin 1) (Fin 1) ℝ))
    Matrix.PosDef.one hshape hshape Wishart.Audit.rankZeroCompression 1
  refine ⟨Matrix.PosDef.one, hshape, hshape,
    Wishart.isProbabilityMeasure_matrixBetaIIMeasure Matrix.PosDef.one hshape hshape,
    Wishart.Audit.rankZeroCompression_fullColumnRank,
    Wishart.Audit.rankZeroFactor_eq_one, hm.1, hm.2, ?_⟩
  norm_num



end WishartVerification.Audit
