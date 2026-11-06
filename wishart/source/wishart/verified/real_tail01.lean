module

public import wishart.verified.real_clauses01

/- Complete real moment-domain and constancy correspondences. -/

@[expose] public section

section CanonicalSource0
/- Source: Wishart/InverseEffectiveRanks.lean -/



/-!
# Exact inverse-Wishart threshold with zero-column compressions

The exponent of an empty determinant is discarded explicitly. For positive
compression ranks this is exactly Corollary 6.2; allowing zero ranks yields
the same exact criterion with the sum restricted to positive-rank factors.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal Matrix

noncomputable section

namespace Wishart

def positiveRankExponent {d : ℕ} (k : Fin d → ℕ) (ν : Fin d → ℝ) (i : Fin d) : ℝ :=
  if 0 < k i then ν i else 0

theorem inverseDeterminantProduct_positiveRankExponent {p d : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (c ν : Fin d → ℝ)
    (J : Finset (Fin d)) :
    inverseDeterminantProduct Omega k B c (positiveRankExponent k ν) J =
      inverseDeterminantProduct Omega k B c ν J := by
  funext Y
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hk : 0 < k i
  · simp only [positiveRankExponent, if_pos hk]
  · have hz : k i = 0 := Nat.eq_zero_of_not_pos hk
    letI : IsEmpty (Fin (k i)) := by rw [hz]; infer_instance
    have hdet : inverseCompressionDeterminant Omega (B i) (c i) Y = 1 := Matrix.det_isEmpty
    simp only [positiveRankExponent, if_neg hk, hdet, Real.one_rpow]

/-- The exact criterion under the convention permitting zero-column full
column rank matrices. No positive-rank hypothesis is imposed. -/
theorem corollary_6_2_finite_moment_iff_positive_ranks {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i) :
    Integrable (inverseDeterminantProduct Omega k B c ν Finset.univ)
      (inverseWishartMeasure β Omega) ↔
      2 * (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < k i), ν i) < β - p + 1 := by
  have hnonneg (i : Fin d) : 0 ≤ positiveRankExponent k ν i := by
    unfold positiveRankExponent
    split_ifs <;> first | exact hν i | exact le_rfl
  have hactive (i : Fin d) (hi : 0 < positiveRankExponent k ν i) : 0 < k i := by
    by_contra hk
    simp only [positiveRankExponent, if_neg hk] at hi
    exact (lt_irrefl 0 hi)
  have h := corollary_6_2_finite_moment_iff hOmega hβ k B hB c
    (positiveRankExponent k ν) hc hnonneg hactive
  rw [inverseDeterminantProduct_positiveRankExponent] at h
  simpa only [positiveRankExponent, Finset.sum_filter] using h

theorem positiveRankExponent_eq_of_positive {d : ℕ} (k : Fin d → ℕ)
    (ν : Fin d → ℝ) (hk : ∀ i, 0 < k i) : positiveRankExponent k ν = ν := by
  funext i
  simp only [positiveRankExponent, if_pos (hk i)]

/-- The full common-sign product inequalities also retain zero-column
compressions, with the exact positive-rank sum in the finite-moment range. -/
theorem corollary_6_2_positive_ranks {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hrange : ((∀ i, 0 ≤ ν i) ∧
      2 * (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < k i), ν i) < β - p + 1) ∨
        (∀ i, ν i ≤ 0)) :
    (∀ J : Finset (Fin d), Integrable (inverseDeterminantProduct Omega k B c ν J)
      (inverseWishartMeasure β Omega)) ∧
    (∏ i, inverseDeterminantMoment β Omega k B c ν {i}) ≤
      inverseDeterminantMoment β Omega k B c ν Finset.univ ∧
    ∀ j : Fin d,
      (∏ i, inverseDeterminantMoment β Omega k B c ν {i}) ≤
        inverseDeterminantMoment β Omega k B c ν {j} *
          inverseDeterminantMoment β Omega k B c ν (Finset.univ.erase j) ∧
      inverseDeterminantMoment β Omega k B c ν {j} *
          inverseDeterminantMoment β Omega k B c ν (Finset.univ.erase j) ≤
        inverseDeterminantMoment β Omega k B c ν Finset.univ := by
  have hnew : ((∀ i, 0 ≤ positiveRankExponent k ν i) ∧
      2 * (∑ i, positiveRankExponent k ν i) < β - p + 1) ∨
        (∀ i, positiveRankExponent k ν i ≤ 0) := by
    rcases hrange with ⟨hν, hsum⟩ | hν
    · refine Or.inl ⟨?_, ?_⟩
      · intro i
        unfold positiveRankExponent
        split_ifs <;> first | exact hν i | exact le_rfl
      · simpa only [positiveRankExponent, Finset.sum_filter] using hsum
    · apply Or.inr
      intro i
      unfold positiveRankExponent
      split_ifs <;> first | exact hν i | exact le_rfl
  have h := corollary_6_2 hOmega hβ k B hB c (positiveRankExponent k ν) hc hnew
  simpa only [inverseDeterminantMoment, inverseDeterminantProduct_positiveRankExponent] using h

end Wishart
end
end CanonicalSource0

section CanonicalSource1
/- Source: Wishart/InverseRankZeroAudit.lean -/



/-!
# The zero-column convention in Corollary 6.2

The manuscript does not explicitly state `k_i ≥ 1`. If a full-column-rank
matrix is allowed to have zero columns, its compressed determinant is the
empty determinant, hence identically one. Its exponent cannot contribute to
a necessary moment threshold. This file records the precise edge case for
the literal unrestricted-dimension reading; it does not refute the intended
positive-rank version of the corollary.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability
open scoped Matrix

noncomputable section

namespace Wishart.Audit

abbrev ScalarSymmetricMatrix := selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℝ)

def rankZeroCompression : Matrix (Fin 1) (Fin 0) ℝ := 0

def rankZeroFactor (Y : ScalarSymmetricMatrix) : ℝ :=
  (rankZeroCompressionᵀ * (Y : Matrix (Fin 1) (Fin 1) ℝ) * rankZeroCompression).det ^ (1 : ℝ)

theorem rankZeroCompression_fullColumnRank : rankZeroCompression.rank = 0 := by
  exact Matrix.rank_zero

theorem rankZeroFactor_eq_one (Y : ScalarSymmetricMatrix) : rankZeroFactor Y = 1 := by
  simp only [rankZeroFactor, Matrix.det_isEmpty, Real.one_rpow]

/-- Every defining property of the zero-column edge case, including its
actual inverse-Wishart expectation and the failure of the unmodified sum
threshold. The law is `IW₁(1,I)`, the sole exponent is `1`, and the sole
compression has zero columns and full column rank. -/
theorem inverse_rank_zero_moment_threshold_edge_case :
    (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ∧
    ((1 : ℕ) : ℝ) - 1 < (1 : ℝ) ∧
    rankZeroCompression.rank = 0 ∧
    (∀ Y : ScalarSymmetricMatrix, rankZeroFactor Y = 1) ∧
    Integrable rankZeroFactor
      (inverseWishartMeasure 1 (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
    (∫ Y, rankZeroFactor Y
      ∂inverseWishartMeasure 1 (1 : Matrix (Fin 1) (Fin 1) ℝ)) = 1 ∧
    ¬ (2 * (∑ _i : Fin 1, (1 : ℝ)) < (1 : ℝ) - (1 : ℕ) + 1) := by
  letI : IsProbabilityMeasure
      (inverseWishartMeasure (1 : ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    isProbabilityMeasure_inverseWishartMeasure
      (n := (1 : ℝ)) (S := (1 : Matrix (Fin 1) (Fin 1) ℝ))
      Matrix.PosDef.one (by norm_num)
  have hfun : rankZeroFactor = fun _ : ScalarSymmetricMatrix ↦ (1 : ℝ) :=
    funext rankZeroFactor_eq_one
  refine ⟨Matrix.PosDef.one, by norm_num, rankZeroCompression_fullColumnRank,
    rankZeroFactor_eq_one, ?_, ?_, ?_⟩
  · rw [hfun]
    exact integrable_const 1
  · rw [hfun]
    simp
  · norm_num

end Wishart.Audit
end
end CanonicalSource1

section CanonicalSource2
/- Source: Wishart/InverseGammaEffectiveRanks.lean -/



noncomputable section

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

/-- The marginal gamma formula on the full corrected finite-moment range.
For a zero-column compression the determinant and both multivariate gamma
factors equal one, so no condition on the real exponent is needed. -/
theorem corollary_6_2_gamma_moment_effective_rank {p k : ℕ} {β r : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (hr : k = 0 ∨ 2 * r < β - p + 1) :
    (∫ Y : SymmetricMatrix p, (Bᵀ * (Y : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r
      ∂inverseWishartMeasure β Omega) =
      (compressionScale Omega B).det ^ r * (2 : ℝ) ^ (-(k : ℝ) * r) *
        (multivariateGamma k ((β - p + k) / 2 - r) /
          multivariateGamma k ((β - p + k) / 2)) := by
  rcases hr with hk | hr
  · subst k
    letI := isProbabilityMeasure_inverseWishartMeasure hOmega hβ
    simp [Matrix.det_isEmpty, multivariateGamma_zero]
  · exact corollary_6_2_gamma_moment hOmega hβ B hB hr

end Wishart
end
end CanonicalSource2

section CanonicalSource3
/- Source: Wishart/MatrixBetaIIEffectiveRanks.lean -/



/-!
# The beta-II exact threshold with all zero-dimensional conventions explicit

The unrestricted dimension version sums the powers only over positive-rank
compressions. The intended positive-rank statement is recovered literally.
The marginal gamma formula also retains every real exponent of a zero-column
compression: its determinant and both dimension-zero gamma ratios equal one.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal Matrix

noncomputable section

namespace Wishart

theorem compressionDeterminantProduct_positiveRankExponent {p d : ℕ}
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (ν : Fin d → ℝ) (J : Finset (Fin d)) :
    compressionDeterminantProduct k B (positiveRankExponent k ν) J =
      compressionDeterminantProduct k B ν J := by
  funext Y
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hk : 0 < k i
  · simp only [positiveRankExponent, if_pos hk]
  · have hz : k i = 0 := Nat.eq_zero_of_not_pos hk
    letI : IsEmpty (Fin (k i)) := by rw [hz]; infer_instance
    simp only [positiveRankExponent, if_neg hk, Matrix.det_isEmpty, Real.one_rpow]

theorem theorem_6_3_finite_moment_iff_positive_ranks {p d : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (ν : Fin d → ℝ) (hν : ∀ i, 0 ≤ ν i) :
    Integrable (compressionDeterminantProduct k B ν Finset.univ)
      (matrixBetaIIMeasure α β Omega) ↔
      2 * (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < k i), ν i) < β - p + 1 := by
  have hnonneg (i : Fin d) : 0 ≤ positiveRankExponent k ν i := by
    unfold positiveRankExponent
    split_ifs <;> first | exact hν i | exact le_rfl
  have hactive (i : Fin d) (hi : 0 < positiveRankExponent k ν i) : 0 < k i := by
    by_contra hk
    simp only [positiveRankExponent, if_neg hk] at hi
    exact (lt_irrefl 0 hi)
  have h := theorem_6_3_finite_moment_iff hOmega hα hβ k B hB
    (positiveRankExponent k ν) hnonneg hactive
  rw [compressionDeterminantProduct_positiveRankExponent] at h
  simpa only [positiveRankExponent, Finset.sum_filter] using h

/-- Empty compressed determinants are identically one. Their moment exists
and equals one for every real exponent, without a tail restriction. -/
theorem theorem_6_3_zero_column_moment {p : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (B : Matrix (Fin p) (Fin 0) ℝ) (r : ℝ) :
    Integrable (fun X : SymmetricMatrix p =>
      (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r)
        (matrixBetaIIMeasure α β Omega) ∧
    (∫ X : SymmetricMatrix p,
      (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r
        ∂matrixBetaIIMeasure α β Omega) = 1 := by
  letI := isProbabilityMeasure_matrixBetaIIMeasure hOmega hα hβ
  constructor
  · simpa only [Matrix.det_isEmpty, Real.one_rpow] using
      (integrable_const (μ := matrixBetaIIMeasure α β Omega) (1 : ℝ))
  · simp [Matrix.det_isEmpty]

theorem integrable_compression_det_rpow_matrixBetaII_effective_rank
    {p k : ℕ} {α β r : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ}
    (hOmega : Omega.PosDef) (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (hr : k = 0 ∨ (0 ≤ r ∧ 2 * r < β - p + 1)) :
    Integrable (fun X : SymmetricMatrix p =>
      (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r)
        (matrixBetaIIMeasure α β Omega) := by
  rcases hr with hk | ⟨hr, hthreshold⟩
  · subst k
    exact (theorem_6_3_zero_column_moment hOmega hα hβ B r).1
  · exact integrable_compression_det_rpow_matrixBetaII hOmega hα hβ B hB hr hthreshold

/-- The printed beta-II gamma formula on the corrected all-rank domain.
Positive ranks retain exactly the printed nonnegative moment range; rank zero
permits every real exponent and both gamma ratios reduce to one. -/
theorem theorem_6_3_gamma_moment_effective_rank {p k : ℕ} {α β r : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (hr : k = 0 ∨ (0 ≤ r ∧ 2 * r < β - p + 1)) :
    (∫ X : SymmetricMatrix p, (Bᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r
      ∂matrixBetaIIMeasure α β Omega) =
      (compressionScale Omega B).det ^ r *
        (multivariateGamma k (α / 2 + r) / multivariateGamma k (α / 2)) *
          (multivariateGamma k ((β - p + k) / 2 - r) /
            multivariateGamma k ((β - p + k) / 2)) := by
  rcases hr with hk | ⟨hr, hthreshold⟩
  · subst k
    rw [(theorem_6_3_zero_column_moment hOmega hα hβ B r).2]
    simp [Matrix.det_isEmpty, multivariateGamma_zero]
  · exact theorem_6_3_gamma_moment hOmega hα hβ B hB hr hthreshold

end Wishart
end
end CanonicalSource3

section CanonicalSource4
/- Source: Wishart/MatrixBetaIIConstancy.lean -/



/-!
# The beta-II rank test uses actual almost-sure constancy

The density in (19) is strictly positive throughout the positive definite
cone. Its null sets there therefore agree with symmetric Lebesgue null sets.
Continuity of the geometric determinant factors identifies the manuscript's
almost-sure constant factors with the pointwise constant factors used in the
conditional Wishart rank test. No support or constancy premise is added.
-/

noncomputable section

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open WishartVerification.MomentAssembly
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace Wishart

theorem matrixBetaIIPDF_pos_iff {p : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (X : SymmetricMatrix p) :
    0 < matrixBetaIIPDF α β Omega X ↔
      (X : Matrix (Fin p) (Fin p) ℝ).PosDef := by
  by_cases hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef
  · have hpos : 0 < matrixBetaIIPDFReal α β Omega X := by
      rw [matrixBetaIIPDFReal_of_posDef α β Omega hX]
      exact mul_pos (mul_pos (matrixBetaIIConstant_pos hOmega hα hβ)
        (Real.rpow_pos_of_pos hX.det_pos _))
        (Real.rpow_pos_of_pos (hOmega.add hX).det_pos _)
    simpa only [matrixBetaIIPDF, ENNReal.ofReal_pos, hX, iff_true] using hpos
  · simp only [matrixBetaIIPDF, matrixBetaIIPDFReal_of_not_posDef α β Omega hX,
      ENNReal.ofReal_zero, lt_self_iff_false, hX]

theorem ae_matrixBetaII_iff_ae_restrict_posDef {p : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (P : SymmetricMatrix p → Prop) :
    (∀ᵐ X ∂matrixBetaIIMeasure α β Omega, P X) ↔
      ∀ᵐ X ∂(symmetricLebesgue p).restrict
        {X : SymmetricMatrix p | (X : Matrix (Fin p) (Fin p) ℝ).PosDef}, P X := by
  rw [matrixBetaIIMeasure,
    ae_withDensity_iff_ae_restrict (measurable_matrixBetaIIPDF α β Omega)]
  have hset : {X : SymmetricMatrix p | matrixBetaIIPDF α β Omega X ≠ 0} =
      {X : SymmetricMatrix p | (X : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
    ext X
    exact (pos_iff_ne_zero).symm.trans (matrixBetaIIPDF_pos_iff hOmega hα hβ X)
  rw [hset]

theorem eqOn_posDef_of_ae_eq_matrixBetaII {p : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    {f g : SymmetricMatrix p → ℝ}
    (hf : ContinuousOn f {X | (X : Matrix (Fin p) (Fin p) ℝ).PosDef})
    (hg : ContinuousOn g {X | (X : Matrix (Fin p) (Fin p) ℝ).PosDef})
    (hfg : f =ᵐ[matrixBetaIIMeasure α β Omega] g) :
    Set.EqOn f g {X | (X : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  have hae := (ae_matrixBetaII_iff_ae_restrict_posDef hOmega hα hβ
    (fun X ↦ f X = g X)).mp hfg
  exact Measure.eqOn_open_of_ae_eq hae (isOpen_setOfPred_posDefMatrix p) hf hg

theorem betaIIGeometricFamily_constantFactor_iff_ae_constant {p d : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) (i : Fin d) :
    (betaIIGeometricFamily k B hB f hf).ConstantFactor Omega i ↔
      ∃ c : ℝ, ∀ᵐ X : SymmetricMatrix p ∂matrixBetaIIMeasure α β Omega,
        f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det = c := by
  let F := betaIIGeometricFamily k B hB f hf
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, (ae_posDef_matrixBetaIIMeasure α β Omega).mono ?_⟩
    intro X hX
    simpa only [betaIIGeometricFamily_factor] using hc X hX
  · rintro ⟨c, hc⟩
    have hfc : F.factor Omega i =ᵐ[matrixBetaIIMeasure α β Omega] fun _ ↦ c := by
      filter_upwards [hc] with X hX
      simpa only [F, betaIIGeometricFamily_factor] using hX
    exact ⟨c, eqOn_posDef_of_ae_eq_matrixBetaII hOmega hα hβ
      (F.continuousOn_factor_posDef Omega hOmega i) continuousOn_const hfc⟩

theorem betaIIGeometricFamily_activeProper_eq_filter_not_ae_constant
    {p d : ℕ} {α β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ}
    (hOmega : Omega.PosDef) (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i)) :
    (betaIIGeometricFamily k B hB f hf).activeProper Omega =
      Finset.univ.filter (fun i ↦ k i < p ∧
        ¬ ∃ c : ℝ, ∀ᵐ X : SymmetricMatrix p ∂matrixBetaIIMeasure α β Omega,
          f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det = c) := by
  ext i
  simp only [GeometricCompressionFamily.activeProper, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change (k i < p ∧ ¬ (betaIIGeometricFamily k B hB f hf).ConstantFactor Omega i) ↔ _
  rw [betaIIGeometricFamily_constantFactor_iff_ae_constant hOmega hα hβ k B hB f hf i]

/-- The exact beta-II product statement with the retained factors defined by
their actual almost-sure behavior under the density (19). -/
theorem theorem_6_3_ae_constant_rank {p d : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, GeometricallyLogConvex (f i))
    (hsize : orderedRankThreshold k (Finset.univ.filter (fun i ↦ k i < p ∧
      ¬ ∃ c : ℝ, ∀ᵐ X : SymmetricMatrix p ∂matrixBetaIIMeasure α β Omega,
        f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det = c)) p α)
    (J : Finset (Fin d)) :
    (∏ i ∈ J, ∫⁻ X : SymmetricMatrix p,
      ENNReal.ofReal (f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det)
        ∂matrixBetaIIMeasure α β Omega) ≤
      ∫⁻ X : SymmetricMatrix p,
        ENNReal.ofReal (∏ i ∈ J, f i ((B i)ᵀ * (X : Matrix (Fin p) (Fin p) ℝ) * B i).det)
          ∂matrixBetaIIMeasure α β Omega := by
  apply theorem_6_3 hOmega hα hβ k B hB f hf _ J
  rwa [betaIIGeometricFamily_activeProper_eq_filter_not_ae_constant
    hOmega hα hβ k B hB f hf]

/-- Empty principal blocks contribute the constant factor `f i 1`, so they
are removed by the same genuine constant-factor rank test. No nonemptiness
hypothesis on the original block family is needed. -/
theorem theorem_6_3_disjoint_principal_blocks_allow_empty {p d : ℕ} {α β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hα : (p : ℝ) - 1 < α) (hβ : (p : ℝ) - 1 < β)
    (I : Fin d → Finset (Fin p))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (I i) (I j)))
    (f : Fin d → ℝ → ℝ) (hf : ∀ i, GeometricallyLogConvex (f i))
    (J : Finset (Fin d)) :
    (∏ i ∈ J, ∫⁻ X : SymmetricMatrix p,
      ENNReal.ofReal (f i (principalMinor (I i) X))
        ∂matrixBetaIIMeasure α β Omega) ≤
      ∫⁻ X : SymmetricMatrix p,
        ENNReal.ofReal (∏ i ∈ J, f i (principalMinor (I i) X))
          ∂matrixBetaIIMeasure α β Omega := by
  let F := betaIIGeometricFamily (fun i ↦ Fintype.card (I i))
    (fun i ↦ principalSelectionMatrix (I i))
    (fun i ↦ principalSelectionMatrix_rank (I i)) f hf
  have hactive_nonempty (l : Fin d) (hl : l ∈ F.activeProper Omega) :
      (I l).Nonempty := by
    have hnot : ¬ F.ConstantFactor Omega l := (Finset.mem_filter.mp hl).2.2
    by_contra hempty
    have hIl : I l = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hnot
    refine ⟨f l 1, ?_⟩
    intro X hX
    dsimp only [F]
    rw [betaIIGeometricFamily_factor, principalSelectionMatrix_det, hIl]
    simp only [principalMinor, Matrix.det_isEmpty]
  have hsize : orderedRankThreshold (fun i ↦ Fintype.card (I i))
      (F.activeProper Omega) p α := by
    apply (orderedRankThreshold_iff _ _ _ _).mpr
    intro i hi j hj l hl hij hil hjl hrij hril
    obtain ⟨a, hal⟩ := hactive_nonempty l hl
    have hai : a ∉ I i := fun hai ↦
      Finset.disjoint_left.mp (hdisjoint hil.symm) hal hai
    have haj : a ∉ I j := fun haj ↦
      Finset.disjoint_left.mp (hdisjoint hjl.symm) hal haj
    have ha : a ∉ I i ∪ I j := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hai, haj⟩
    have hcard := Finset.card_le_card (Finset.subset_univ (insert a (I i ∪ I j)))
    have hnat : (I i).card + (I j).card + 1 ≤ p := by
      simpa only [Finset.card_insert_of_notMem ha,
        Finset.card_union_of_disjoint (hdisjoint hij), Finset.card_univ,
        Fintype.card_fin] using hcard
    have hreal : (Fintype.card (I i) : ℝ) + Fintype.card (I j) + 1 ≤ p := by
      simp only [Fintype.card_coe]
      exact_mod_cast hnat
    exact (min_le_left _ _).trans (by linarith)
  have h := theorem_6_3 hOmega hα hβ (fun i ↦ Fintype.card (I i))
    (fun i ↦ principalSelectionMatrix (I i))
    (fun i ↦ principalSelectionMatrix_rank (I i)) f hf hsize J
  simpa only [principalSelectionMatrix_det] using h

end Wishart
end
end CanonicalSource4
