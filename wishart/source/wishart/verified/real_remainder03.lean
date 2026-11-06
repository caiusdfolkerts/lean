module

public import wishart.verified.real_remainder02
public import tau_ceti.probability.distributions.wishart.inverse.moments

/- Generated ordinary proof stage. See audit/staged_real_remainder/RealRemainder03/manifest.json. -/

@[expose] public section

section CanonicalSource20
/- Source: Wishart/InverseDeterminantMoments.lean -/



/-!
# Exact determinant moments and shifted inverse-Wishart moments

The determinant gamma ratio is obtained from an equality of tilted Wishart
measures. Positive shifted moments retain the exact scalar threshold
`2*s < β-p+1`; negative shifted powers have moments of every finite order.
These are marginal statements used below to prove joint moment finiteness.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

theorem det_symmetricInv_rpow {p : ℕ} (X : SymmetricMatrix p) (r : ℝ) :
    (symmetricInv X : Matrix (Fin p) (Fin p) ℝ).det ^ r =
      (X : Matrix (Fin p) (Fin p) ℝ).det ^ (-r) := by
  rw [coe_symmetricInv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    ← Real.rpow_neg_eq_inv_rpow]

theorem integrable_det_rpow_inverseWishart {p : ℕ} {β r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hβ : (p : ℝ) - 1 < β) (hr : 2 * r < β - p + 1) :
    Integrable (fun Y : SymmetricMatrix p => (Y : Matrix (Fin p) (Fin p) ℝ).det ^ r)
      (inverseWishartMeasure β S) := by
  rw [inverseWishartMeasure_def]
  have hm : Measurable (fun Y : SymmetricMatrix p =>
      (Y : Matrix (Fin p) (Fin p) ℝ).det ^ r) :=
    (show Measurable (fun Y : SymmetricMatrix p =>
      (Y : Matrix (Fin p) (Fin p) ℝ).det) by fun_prop).pow_const r
  apply (integrable_map_measure hm.aestronglyMeasurable
    measurable_symmetricInv.aemeasurable).mpr
  apply (integrable_det_rpow_wishart hS.inv hβ (r := -r) (by linarith)).congr
  exact Filter.Eventually.of_forall fun X => (det_symmetricInv_rpow X r).symm

theorem integral_det_rpow_inverseWishart {p : ℕ} {β r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hβ : (p : ℝ) - 1 < β) (hr : 2 * r < β - p + 1) :
    (∫ Y : SymmetricMatrix p, (Y : Matrix (Fin p) (Fin p) ℝ).det ^ r
      ∂inverseWishartMeasure β S) =
      S.det ^ r * (2 : ℝ) ^ (-(p : ℝ) * r) *
        (multivariateGamma p (β / 2 - r) / multivariateGamma p (β / 2)) := by
  rw [inverseWishartMeasure_def,
    integral_map_of_stronglyMeasurable measurable_symmetricInv (by fun_prop)]
  simp_rw [det_symmetricInv_rpow]
  rw [integral_det_rpow_wishart hS.inv hβ (r := -r) (by linarith),
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← Real.rpow_neg_eq_inv_rpow, neg_neg]
  congr 1
  · rw [mul_comm]
    congr 1
    ring

theorem allFiniteMoments_det_nonpos_rpow_inverseWishart {p : ℕ} {β r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hβ : (p : ℝ) - 1 < β) (hr : r ≤ 0) :
    HasAllFiniteMoments (fun Y : SymmetricMatrix p =>
      (Y : Matrix (Fin p) (Fin p) ℝ).det ^ r) (inverseWishartMeasure β S) := by
  letI := isProbabilityMeasure_nonsingularWishartMeasure hS.inv hβ
  have hdet : HasAllFiniteMoments (fun X : SymmetricMatrix p =>
      (X : Matrix (Fin p) (Fin p) ℝ).det) (nonsingularWishartMeasure β S⁻¹) :=
    HasAllFiniteMoments.det _ (fun i j => allFiniteMoments_wishart_entry i j)
  apply HasAllFiniteMoments.of_comp_measurePreserving
    (show MeasurePreserving symmetricInv (nonsingularWishartMeasure β S⁻¹)
      (inverseWishartMeasure β S) from
        ⟨measurable_symmetricInv, (inverseWishartMeasure_def β S).symm⟩)
    (by fun_prop)
  apply (hdet.rpow (neg_nonneg.mpr hr)).congr_ae
  exact Filter.Eventually.of_forall fun X => (det_symmetricInv_rpow X r).symm

def inverseShiftedDeterminant {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (c : ℝ) (Y : SymmetricMatrix p) : ℝ :=
  ((Y : Matrix (Fin p) (Fin p) ℝ) + c • S).det

@[fun_prop] theorem measurable_inverseShiftedDeterminant {p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) :
    Measurable (inverseShiftedDeterminant S c) := by
  unfold inverseShiftedDeterminant
  fun_prop

theorem inverseShiftedDeterminant_pos {p : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosSemidef) {c : ℝ} (hc : 0 ≤ c) {Y : SymmetricMatrix p}
    (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    0 < inverseShiftedDeterminant S c Y :=
  (hY.add_posSemidef (hS.smul hc)).det_pos

theorem inverseShiftedDeterminant_inv_identity {p : ℕ} {c : ℝ}
    (X : SymmetricMatrix p) (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    inverseShiftedDeterminant (1 : Matrix (Fin p) (Fin p) ℝ) c (symmetricInv X) =
      (X : Matrix (Fin p) (Fin p) ℝ).det⁻¹ *
        ((1 : Matrix (Fin p) (Fin p) ℝ) + c • (X : Matrix (Fin p) (Fin p) ℝ)).det := by
  have hmatrix : (X : Matrix (Fin p) (Fin p) ℝ)⁻¹ + c • 1 =
      (X : Matrix (Fin p) (Fin p) ℝ)⁻¹ * (1 + c • (X : Matrix (Fin p) (Fin p) ℝ)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hX.det_pos.ne')]
  rw [inverseShiftedDeterminant, coe_symmetricInv, hmatrix,
    Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

theorem integrable_inverseShiftedDeterminant_identity_rpow {p : ℕ} {β c s : ℝ}
    (hβ : (p : ℝ) - 1 < β) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hthreshold : 2 * s < β - p + 1) :
    Integrable (fun Y : SymmetricMatrix p =>
      inverseShiftedDeterminant (1 : Matrix (Fin p) (Fin p) ℝ) c Y ^ s)
      (inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ)) := by
  have hshape : (p : ℝ) - 1 < β + 2 * (-s) := by linarith
  letI := isProbabilityMeasure_nonsingularWishartMeasure
    (Matrix.PosDef.one : (1 : Matrix (Fin p) (Fin p) ℝ).PosDef) hshape
  have hpoly : HasAllFiniteMoments (fun X : SymmetricMatrix p =>
      ((1 : Matrix (Fin p) (Fin p) ℝ) + c • (X : Matrix (Fin p) (Fin p) ℝ)).det)
      (nonsingularWishartMeasure (β + 2 * (-s)) (1 : Matrix (Fin p) (Fin p) ℝ)) := by
    apply HasAllFiniteMoments.det
    intro i j
    exact (HasAllFiniteMoments.const ((1 : Matrix (Fin p) (Fin p) ℝ) i j)).add
      ((allFiniteMoments_wishart_entry i j).const_mul c)
  have hweighted := integrable_wishart_det_rpow_mul Matrix.PosDef.one hβ hshape
    (hpoly.rpow hs).integrable
  rw [inverseWishartMeasure_def, inv_one]
  apply (integrable_map_measure (by fun_prop) measurable_symmetricInv.aemeasurable).mpr
  apply hweighted.congr
  filter_upwards [ae_posDef_nonsingularWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ)]
    with X hX
  dsimp only [Function.comp_apply]
  rw [inverseShiftedDeterminant_inv_identity X hX,
    Real.mul_rpow (inv_nonneg.mpr hX.det_pos.le)
      (Matrix.PosDef.one.add_posSemidef (hX.posSemidef.smul hc)).det_pos.le,
    ← Real.rpow_neg_eq_inv_rpow]

theorem inverseShiftedDeterminant_congruence {p : ℕ}
    (A S : Matrix (Fin p) (Fin p) ℝ) (hAS : A * Aᵀ = S)
    (c : ℝ) (Y : SymmetricMatrix p) :
    inverseShiftedDeterminant S c (Matrix.symmetricCongruenceLinearMap A Y) =
      S.det * inverseShiftedDeterminant (1 : Matrix (Fin p) (Fin p) ℝ) c Y := by
  have hmatrix : A * (Y : Matrix (Fin p) (Fin p) ℝ) * Aᵀ + c • S =
      A * ((Y : Matrix (Fin p) (Fin p) ℝ) + c • 1) * Aᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hAS]
  have hdet : A.det * A.det = S.det := by
    simpa only [Matrix.det_mul, Matrix.det_transpose] using congrArg Matrix.det hAS
  rw [inverseShiftedDeterminant, Matrix.coe_symmetricCongruenceLinearMap_apply,
    hmatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    inverseShiftedDeterminant, ← hdet]
  ring

theorem integrable_inverseShiftedDeterminant_rpow {p : ℕ} {β c s : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hβ : (p : ℝ) - 1 < β) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hthreshold : 2 * s < β - p + 1) :
    Integrable (fun Y : SymmetricMatrix p => inverseShiftedDeterminant S c Y ^ s)
      (inverseWishartMeasure β S) := by
  let A := CFC.sqrt S
  have hAA : A * Aᵀ = S := by
    rw [matrix_sqrt_transpose]
    exact CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  have hmap : (inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ)).map
      (Matrix.symmetricCongruenceLinearMap A) = inverseWishartMeasure β S := by
    rw [map_symmetricCongruenceLinearMap_inverseWishartMeasure_of_det_ne_zero _ _ A
      (sqrt_det_ne_zero_of_posDef hS), Matrix.mul_one, hAA]
  rw [← hmap]
  apply (integrable_map_measure (by fun_prop)
    (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable).mpr
  apply ((integrable_inverseShiftedDeterminant_identity_rpow hβ hc hs hthreshold).const_mul
    (S.det ^ s)).congr
  filter_upwards [ae_posDef_inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ)] with Y hY
  dsimp only [Function.comp_apply]
  rw [inverseShiftedDeterminant_congruence A S hAA c Y,
    Real.mul_rpow hS.det_pos.le (inverseShiftedDeterminant_pos Matrix.PosSemidef.one hc hY).le]

theorem allFiniteMoments_inverseShiftedDeterminant_nonpos_rpow {p : ℕ} {β c r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hβ : (p : ℝ) - 1 < β) (hc : 0 ≤ c) (hr : r ≤ 0) :
    HasAllFiniteMoments (fun Y : SymmetricMatrix p => inverseShiftedDeterminant S c Y ^ r)
      (inverseWishartMeasure β S) := by
  intro q hq
  apply (allFiniteMoments_det_nonpos_rpow_inverseWishart hS hβ hr q hq).mono'
  · exact ((measurable_inverseShiftedDeterminant S c).pow_const r).aestronglyMeasurable
  filter_upwards [ae_posDef_inverseWishartMeasure β S] with Y hY
  let T : SymmetricMatrix p :=
    Y + c • ⟨S, Matrix.isHermitian_iff_isSelfAdjoint.mp hS.isHermitian⟩
  have hYT : ((T : Matrix (Fin p) (Fin p) ℝ) - Y).PosSemidef := by
    simpa only [T, Submodule.coe_add, Submodule.coe_smul, add_sub_cancel_left] using
      hS.posSemidef.smul hc
  have hd := det_le_of_posSemidef_sub Y T hY.posSemidef hYT
  change (Y : Matrix (Fin p) (Fin p) ℝ).det ≤ inverseShiftedDeterminant S c Y at hd
  rw [Real.norm_eq_abs, abs_of_nonneg
    (Real.rpow_nonneg (inverseShiftedDeterminant_pos hS.posSemidef hc hY).le r)]
  exact Real.rpow_le_rpow_of_nonpos hY.det_pos hd hr

theorem integral_compression_det_rpow_inverseWishart {p k : ℕ} {β r : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef) (hβ : (p : ℝ) - 1 < β)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (hr : 2 * r < β - p + 1) :
    (∫ Y : SymmetricMatrix p, (Bᵀ * (Y : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r
      ∂inverseWishartMeasure β S) =
      (compressionScale S B).det ^ r * (2 : ℝ) ^ (-(k : ℝ) * r) *
        (multivariateGamma k ((β - p + k) / 2 - r) /
          multivariateGamma k ((β - p + k) / 2)) := by
  have hG := compressionScale_posDef hS B hB
  have hshape : (k : ℝ) - 1 < β - p + k := by linarith
  have hthreshold : 2 * r < (β - p + k) - k + 1 := by linarith
  have hm := integral_det_rpow_inverseWishart hG hshape hthreshold
  rw [← map_compression_inverseWishartMeasure hS hβ B hB,
    integral_map_of_stronglyMeasurable
      (LinearMap.continuous_of_finiteDimensional _).measurable (by fun_prop)] at hm
  simpa only [Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.transpose_transpose] using hm

end Wishart
end
end CanonicalSource20

section CanonicalSource21
/- Source: Wishart/InverseProductMoments.lean -/



/-!
# Joint inverse-Wishart determinant moments

Weighted AM–GM uses the sum of the exponents exactly. It does not replace the
sharp threshold by an equal-exponent Hölder bound. Negative powers are handled
by their moments of every finite order, without any additional degree bound.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace WishartVerification

theorem integrable_rpow_product_of_sum_moments
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (J : Finset ι) (D : ι → Ω → ℝ) (ν : ι → ℝ)
    (hDm : ∀ i ∈ J, Measurable (D i))
    (hD0 : ∀ᵐ x ∂μ, ∀ i ∈ J, 0 ≤ D i x)
    (hν : ∀ i ∈ J, 0 ≤ ν i)
    (hI : ∀ i ∈ J, Integrable (fun x => D i x ^ (∑ j ∈ J, ν j)) μ) :
    Integrable (fun x => ∏ i ∈ J, D i x ^ ν i) μ := by
  classical
  let s := ∑ i ∈ J, ν i
  have hs0 : 0 ≤ s := Finset.sum_nonneg hν
  by_cases hs : s = 0
  · have hνzero : ∀ i ∈ J, ν i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hν).mp hs
    have hfun : (fun x => ∏ i ∈ J, D i x ^ ν i) = fun _ => (1 : ℝ) := by
      funext x
      apply Finset.prod_eq_one
      intro i hi
      rw [hνzero i hi, Real.rpow_zero]
    rw [hfun]
    exact integrable_const _
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
  have hboundI : Integrable (fun x => ∑ i ∈ J, (ν i / s) * D i x ^ s) μ :=
    integrable_finsetSum J (fun i hi => (hI i hi).const_mul (ν i / s))
  apply hboundI.mono'
  · exact (Finset.measurable_prod _ (fun i hi => (hDm i hi).pow_const _)).aestronglyMeasurable
  filter_upwards [hD0] with x hx
  have hweights : ∑ i ∈ J, ν i / s = 1 := by
    rw [← Finset.sum_div]
    exact div_self hs
  have hAMGM := Real.geom_mean_le_arith_mean_weighted J
    (fun i => ν i / s) (fun i => D i x ^ s)
    (fun i hi => div_nonneg (hν i hi) hs0) hweights
    (fun i hi => Real.rpow_nonneg (hx i hi) s)
  have heq : (∏ i ∈ J, (D i x ^ s) ^ (ν i / s)) =
      ∏ i ∈ J, D i x ^ ν i := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hx i hi)]
    congr 1
    field_simp
  rw [heq] at hAMGM
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg
    (fun i hi => Real.rpow_nonneg (hx i hi) (ν i)))]
  exact hAMGM

end WishartVerification

namespace Wishart

def inverseCompressionDeterminant {p k : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin k) ℝ)
    (c : ℝ) (Y : SymmetricMatrix p) : ℝ :=
  (Bᵀ * (Y : Matrix (Fin p) (Fin p) ℝ) * B + c • compressionScale S B).det

@[fun_prop] theorem measurable_inverseCompressionDeterminant {p k : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin k) ℝ) (c : ℝ) :
    Measurable (inverseCompressionDeterminant S B c) := by
  unfold inverseCompressionDeterminant
  fun_prop

theorem inverseCompressionDeterminant_eq_comp {p k : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin k) ℝ) (c : ℝ) :
    inverseCompressionDeterminant S B c =
      inverseShiftedDeterminant (compressionScale S B) c ∘
        Matrix.symmetricCongruenceLinearMap Bᵀ := by
  funext Y
  simp only [inverseCompressionDeterminant, inverseShiftedDeterminant, Function.comp_apply,
    Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.transpose_transpose]

theorem inverseCompressionDeterminant_pos {p k : ℕ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) {c : ℝ} (hc : 0 ≤ c)
    {Y : SymmetricMatrix p} (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    0 < inverseCompressionDeterminant S B c Y :=
  ((compressionScale_posDef hY B hB).add_posSemidef
    ((compressionScale_posDef hS B hB).posSemidef.smul hc)).det_pos

theorem integrable_inverseCompressionDeterminant_rpow {p k : ℕ} {β c s : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hβ : (p : ℝ) - 1 < β) (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hthreshold : 2 * s < β - p + 1) :
    Integrable (fun Y : SymmetricMatrix p => inverseCompressionDeterminant S B c Y ^ s)
      (inverseWishartMeasure β S) := by
  have hI := integrable_inverseShiftedDeterminant_rpow
    (compressionScale_posDef hS B hB) (β := β - p + k) (by linarith) hc hs (by linarith)
  have hmap := map_compression_inverseWishartMeasure hS hβ B hB
  rw [← hmap] at hI
  have h := (integrable_map_measure (by fun_prop)
    (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable).mp hI
  apply h.congr
  apply Filter.Eventually.of_forall
  intro Y
  rw [inverseCompressionDeterminant_eq_comp]
  rfl

theorem allFiniteMoments_inverseCompressionDeterminant_nonpos_rpow
    {p k : ℕ} {β c r : ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosDef) (hβ : (p : ℝ) - 1 < β)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) (hc : 0 ≤ c) (hr : r ≤ 0) :
    HasAllFiniteMoments
      (fun Y : SymmetricMatrix p => inverseCompressionDeterminant S B c Y ^ r)
      (inverseWishartMeasure β S) := by
  have h := (allFiniteMoments_inverseShiftedDeterminant_nonpos_rpow
    (compressionScale_posDef hS B hB) (β := β - p + k) (by linarith) hc hr).comp_measurePreserving
    (show MeasurePreserving (Matrix.symmetricCongruenceLinearMap Bᵀ)
      (inverseWishartMeasure β S) (inverseWishartMeasure (β - p + k) (compressionScale S B)) from
        ⟨(LinearMap.continuous_of_finiteDimensional _).measurable,
          map_compression_inverseWishartMeasure hS hβ B hB⟩)
  apply h.congr_ae
  apply Filter.Eventually.of_forall
  intro Y
  rw [inverseCompressionDeterminant_eq_comp]
  rfl

def inverseDeterminantProduct {p d : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (c ν : Fin d → ℝ)
    (J : Finset (Fin d)) (Y : SymmetricMatrix p) : ℝ :=
  ∏ i ∈ J, inverseCompressionDeterminant S (B i) (c i) Y ^ ν i

@[fun_prop] theorem measurable_inverseDeterminantProduct {p d : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (c ν : Fin d → ℝ)
    (J : Finset (Fin d)) : Measurable (inverseDeterminantProduct S k B c ν J) := by
  unfold inverseDeterminantProduct
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_inverseCompressionDeterminant S (B i) (c i)).pow_const _)

theorem integrable_inverseDeterminantProduct_nonneg {p d : ℕ} {β : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (J : Finset (Fin d))
    (hν : ∀ i ∈ J, 0 ≤ ν i) (hthreshold : 2 * (∑ i ∈ J, ν i) < β - p + 1) :
    Integrable (inverseDeterminantProduct S k B c ν J) (inverseWishartMeasure β S) := by
  letI := isProbabilityMeasure_inverseWishartMeasure hS hβ
  apply integrable_rpow_product_of_sum_moments J
    (fun i => inverseCompressionDeterminant S (B i) (c i)) ν
  · intro i hi
    fun_prop
  · filter_upwards [ae_posDef_inverseWishartMeasure β S] with Y hY i hi
    exact (inverseCompressionDeterminant_pos hS (B i) (hB i) (hc i) hY).le
  · exact hν
  · intro i hi
    exact integrable_inverseCompressionDeterminant_rpow hS hβ (B i) (hB i) (hc i)
      (Finset.sum_nonneg hν) hthreshold

theorem allFiniteMoments_inverseDeterminantProduct_nonpos {p d : ℕ} {β : ℝ}
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (J : Finset (Fin d))
    (hν : ∀ i ∈ J, ν i ≤ 0) :
    HasAllFiniteMoments (inverseDeterminantProduct S k B c ν J) (inverseWishartMeasure β S) := by
  letI := isProbabilityMeasure_inverseWishartMeasure hS hβ
  exact HasAllFiniteMoments.finset_prod J _ (fun i hi =>
    allFiniteMoments_inverseCompressionDeterminant_nonpos_rpow
      hS hβ (B i) (hB i) (hc i) (hν i hi))

end Wishart
end
end CanonicalSource21

section CanonicalSource22
/- Source: Wishart/InverseDeterminantSpectralTests.lean -/



/-!
# The literal shifted determinant factors as inverse spectral tests

The scalar scale factor is retained exactly. The spectral function is defined
on every coordinate vector and agrees with the determinant power on the actual
positive-definite support. Negative powers need monotonicity only on positive
ordered spectra, where the shifted eigenvalues are strictly positive.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

open Spectral

theorem inverseCompressionDeterminant_normalized {p k : ℕ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (c : ℝ) (Y : SymmetricMatrix p) :
    inverseCompressionDeterminant Omega B c Y =
      (compressionScale Omega B).det *
        inverseShiftedDeterminant (1 : Matrix (Fin k) (Fin k) ℝ) c
          (normalizedCompression Omega B Y) := by
  have hT : CFC.sqrt (compressionScale Omega B) * (CFC.sqrt (compressionScale Omega B))ᵀ =
      compressionScale Omega B := by
    rw [matrix_sqrt_transpose]
    exact CFC.sqrt_mul_sqrt_self _ (compressionScale_posDef hOmega B hB).posSemidef.nonneg
  rw [inverseCompressionDeterminant_eq_comp, Function.comp_apply,
    ← unnormalize_normalizedCompression hOmega B hB Y,
    inverseShiftedDeterminant_congruence _ _ hT]

theorem shiftedSpectralDetPower_ascendingSpectrum {k : ℕ} {c : ℝ}
    (hc : 0 ≤ c) (r : ℝ) (Y : SymmetricMatrix k)
    (hY : (Y : Matrix (Fin k) (Fin k) ℝ).PosDef) :
    shiftedSpectralDetPower c r (ascendingSpectrum Y) =
      inverseShiftedDeterminant (1 : Matrix (Fin k) (Fin k) ℝ) c Y ^ r := by
  obtain ⟨O, hO⟩ := exists_conjugate_diagonal_ascendingSpectrum Y
  have h := shiftedMatrixDetPower_conjugate_diagonal O hc r (ascendingSpectrum Y)
    (ascendingSpectrum_mem_positiveOrderedSpectrum Y hY).2
  rw [hO] at h
  exact h.symm

theorem shiftedSpectralDetPower_antitoneOn_positive {k : ℕ} {c r : ℝ}
    (hc : 0 ≤ c) (hr : r ≤ 0) :
    AntitoneOn (shiftedSpectralDetPower (ι := Fin k) c r) (positiveOrderedSpectrum k) := by
  intro x hx y hy hxy
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Real.rpow_nonneg (le_max_right _ _) _
  · intro i hi
    have hxpos := add_pos_of_pos_of_nonneg (hx.2 i) hc
    have hypos := add_pos_of_pos_of_nonneg (hy.2 i) hc
    have hsum : x i + c ≤ y i + c := by linarith [hxy i]
    simpa only [max_eq_left hxpos.le, max_eq_left hypos.le] using
      Real.rpow_le_rpow_of_nonpos hxpos hsum hr

def inverseDeterminantSpectralTest {p k : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin k) ℝ)
    (c r : ℝ) (lam : Fin k → ℝ) : ℝ :=
  (compressionScale Omega B).det ^ r * shiftedSpectralDetPower c r lam

@[fun_prop] theorem measurable_inverseDeterminantSpectralTest {p k : ℕ}
    (Omega : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin p) (Fin k) ℝ) (c r : ℝ) :
    Measurable (inverseDeterminantSpectralTest Omega B c r) :=
  (shiftedSpectralDetPower_measurable c r).const_mul _

theorem inverseDeterminantSpectralTest_nonneg {p k : ℕ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) (c r : ℝ) (lam : Fin k → ℝ) :
    0 ≤ inverseDeterminantSpectralTest Omega B c r lam :=
  mul_nonneg (Real.rpow_nonneg (compressionScale_posDef hOmega B hB).det_pos.le _)
    (shiftedSpectralDetPower_nonneg c r lam)

theorem inverseDeterminantSpectralTest_mono {p k : ℕ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    MonotoneOn (inverseDeterminantSpectralTest Omega B c r) (positiveOrderedSpectrum k) := by
  intro x hx y hy hxy
  exact mul_le_mul_of_nonneg_left (shiftedSpectralDetPower_monotone c r hr hxy)
    (Real.rpow_nonneg (compressionScale_posDef hOmega B hB).det_pos.le _)

theorem inverseDeterminantSpectralTest_antitone {p k : ℕ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) {c r : ℝ} (hc : 0 ≤ c) (hr : r ≤ 0) :
    AntitoneOn (inverseDeterminantSpectralTest Omega B c r) (positiveOrderedSpectrum k) := by
  intro x hx y hy hxy
  exact mul_le_mul_of_nonneg_left
    (shiftedSpectralDetPower_antitoneOn_positive hc hr hx hy hxy)
    (Real.rpow_nonneg (compressionScale_posDef hOmega B hB).det_pos.le _)

theorem inverseDeterminantSpectralTest_factor_eq {p k : ℕ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) {c : ℝ} (hc : 0 ≤ c)
    (r : ℝ) {Y : SymmetricMatrix p} (hY : (Y : Matrix (Fin p) (Fin p) ℝ).PosDef) :
    inverseCompressionFactor Omega B (inverseDeterminantSpectralTest Omega B c r) Y =
      inverseCompressionDeterminant Omega B c Y ^ r := by
  unfold inverseCompressionFactor inverseDeterminantSpectralTest
  rw [shiftedSpectralDetPower_ascendingSpectrum hc r _ (normalizedCompression_posDef hOmega B hB hY),
    inverseCompressionDeterminant_normalized hOmega B hB c Y,
    Real.mul_rpow (compressionScale_posDef hOmega B hB).det_pos.le
      (inverseShiftedDeterminant_pos Matrix.PosSemidef.one hc
        (normalizedCompression_posDef hOmega B hB hY)).le]

theorem ae_inverseDeterminantSpectralProduct_eq {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (J : Finset (Fin d)) :
    inverseCompressionProduct Omega k B
      (fun i => inverseDeterminantSpectralTest Omega (B i) (c i) (ν i)) J =ᵐ[
        inverseWishartMeasure β Omega] inverseDeterminantProduct Omega k B c ν J := by
  filter_upwards [ae_posDef_inverseWishartMeasure β Omega] with Y hY
  apply Finset.prod_congr rfl
  intro i hi
  exact inverseDeterminantSpectralTest_factor_eq hOmega (B i) (hB i) (hc i) (ν i) hY

def inverseDeterminantMoment {p d : ℕ} (β : ℝ)
    (Omega : Matrix (Fin p) (Fin p) ℝ) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (c ν : Fin d → ℝ)
    (J : Finset (Fin d)) : ℝ :=
  ∫ Y, inverseDeterminantProduct Omega k B c ν J Y ∂inverseWishartMeasure β Omega

theorem inverseDeterminantMoment_eq_spectral {p d : ℕ} (β : ℝ)
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (J : Finset (Fin d)) :
    inverseDeterminantMoment β Omega k B c ν J =
      inverseCompressionMoment β Omega k B
        (fun i => inverseDeterminantSpectralTest Omega (B i) (c i) (ν i)) J :=
  integral_congr_ae (ae_inverseDeterminantSpectralProduct_eq hOmega k B hB c ν hc J).symm

end Wishart
end
end CanonicalSource22

section CanonicalSource23
/- Source: Wishart/InverseMomentSharpnessAlgebra.lean -/



/-!
# Rank-one growth and the scalar sharp moment obstruction

A fixed positive-definite baseline plus `(t-1) vvᵀ` has determinant bounded
below by a positive multiple of `t` on `t ≥ 2`, provided `v ≠ 0`.
Products therefore have lower growth of degree exactly the sum of their
active powers. The final probabilistic obstruction is the proved sharp
inverse-gamma moment threshold, not an assumed asymptotic density formula.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

theorem det_add_smul_vecMulVec {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsUnit A.det)
    (v : Fin k → ℝ) (t : ℝ) :
    (A + t • Matrix.vecMulVec v v).det =
      A.det * (1 + t * (v ⬝ᵥ (A⁻¹ *ᵥ v))) := by
  have hfactor : A + t • Matrix.vecMulVec v v =
      A * (1 + Matrix.vecMulVec (A⁻¹ *ᵥ (t • v)) v) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec,
      Matrix.smul_vecMulVec]
  rw [hfactor, Matrix.det_mul, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem exists_det_rankOne_linear_lower {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosDef)
    {v : Fin k → ℝ} (hv : v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
      c * t ≤ (A + (t - 1) • Matrix.vecMulVec v v).det := by
  let q := v ⬝ᵥ (A⁻¹ *ᵥ v)
  have hq : 0 < q := by
    simpa only [q, star_trivial] using hA.inv.dotProduct_mulVec_pos hv
  refine ⟨A.det * q / 2, div_pos (mul_pos hA.det_pos hq) two_pos, ?_⟩
  intro t ht
  rw [det_add_smul_vecMulVec hA.det_pos.ne'.isUnit]
  change A.det * q / 2 * t ≤ A.det * (1 + (t - 1) * q)
  have hscalar : q / 2 * t ≤ 1 + (t - 1) * q := by nlinarith
  have h := mul_le_mul_of_nonneg_left hscalar hA.det_pos.le
  nlinarith

theorem exists_det_rankOne_rpow_lower {k : ℕ}
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosDef)
    {v : Fin k → ℝ} {r : ℝ} (hr : 0 ≤ r) (hv : 0 < r → v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
      c * t ^ r ≤ (A + (t - 1) • Matrix.vecMulVec v v).det ^ r := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    exact ⟨1, one_pos, fun t ht => by simp⟩
  obtain ⟨c, hc, hbound⟩ := exists_det_rankOne_linear_lower hA (hv hr)
  refine ⟨c ^ r, Real.rpow_pos_of_pos hc r, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := by linarith
  rw [← Real.mul_rpow hc.le ht0]
  exact Real.rpow_le_rpow (mul_nonneg hc.le ht0) (hbound t ht) hr.le

theorem exists_det_rankOne_product_lower {ι : Type*} [Fintype ι]
    (k : ι → ℕ) (A : ∀ i, Matrix (Fin (k i)) (Fin (k i)) ℝ)
    (v : ∀ i, Fin (k i) → ℝ) (r : ι → ℝ)
    (hA : ∀ i, (A i).PosDef) (hr : ∀ i, 0 ≤ r i)
    (hv : ∀ i, 0 < r i → v i ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
      c * t ^ (∑ i, r i) ≤
        ∏ i, (A i + (t - 1) • Matrix.vecMulVec (v i) (v i)).det ^ r i := by
  choose c hc hbound using fun i => exists_det_rankOne_rpow_lower (hA i) (hr i) (hv i)
  refine ⟨∏ i, c i, Finset.prod_pos (fun i _ => hc i), ?_⟩
  intro t ht
  have htpos : 0 < t := by linarith
  rw [Real.rpow_sum_of_pos htpos, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact mul_nonneg (hc i).le (Real.rpow_nonneg htpos.le _)
  · intro i hi
    exact hbound i t ht

/-- A tail lower bound by an integrable observable forces the corresponding
nonnegative power to be integrable; the bounded interval is handled explicitly. -/
theorem integrable_rpow_of_tail_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {x F : Ω → ℝ} (hxm : Measurable x) (hx0 : ∀ᵐ ω ∂μ, 0 ≤ x ω)
    (hF : Integrable F μ) {s c : ℝ} (hs : 0 ≤ s) (hc : 0 < c)
    (hbound : ∀ᵐ ω ∂μ, 2 ≤ x ω → c * x ω ^ s ≤ F ω) :
    Integrable (fun ω => x ω ^ s) μ := by
  have hI : Integrable (fun ω => (2 : ℝ) ^ s + c⁻¹ * |F ω|) μ :=
    (integrable_const _).add (hF.abs.const_mul _)
  apply hI.mono' (hxm.pow_const s).aestronglyMeasurable
  filter_upwards [hx0, hbound] with ω hx hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx s)]
  by_cases hsmall : x ω ≤ 2
  · exact (Real.rpow_le_rpow hx hsmall hs).trans
      (le_add_of_nonneg_right (mul_nonneg (inv_pos.mpr hc).le (abs_nonneg _)))
  · have hlarge := hω (lt_of_not_ge hsmall).le
    have hscaled := mul_le_mul_of_nonneg_left hlarge (inv_pos.mpr hc).le
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at hscaled
    exact hscaled.trans ((mul_le_mul_of_nonneg_left (le_abs_self _) (inv_pos.mpr hc).le).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg zero_le_two s)))

theorem scalar_inverseWishart_rpow_integrable_iff {β s : ℝ} (hβ : 0 < β) :
    Integrable (fun Y : SymmetricMatrix 1 =>
      ((Y : Matrix (Fin 1) (Fin 1) ℝ) 0 0) ^ s)
      (inverseWishartMeasure β (1 : Matrix (Fin 1) (Fin 1) ℝ)) ↔ s < β / 2 := by
  have hmap := map_coe_apply_inverseWishartMeasure_one
    (p := 1) (n := β) (by simpa using hβ) (0 : Fin 1)
  norm_num only [Nat.cast_one, sub_self, sub_add_cancel, sub_zero] at hmap
  have hI := integrable_map_measure
    (μ := inverseWishartMeasure β (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (f := fun Y : SymmetricMatrix 1 => (Y : Matrix (Fin 1) (Fin 1) ℝ) 0 0)
    (g := fun x : ℝ => x ^ s) (by fun_prop)
    (selfAdjoint.measurable_coe_apply (0 : Fin 1) 0).aemeasurable
  rw [hmap] at hI
  exact hI.symm.trans (integrable_rpow_inverseGammaMeasure_iff (by linarith) (by norm_num) s)

end Wishart
end
end CanonicalSource23

section CanonicalSource24
/- Source: Wishart/InverseScalarRegression.lean -/



/-!
# Haar-randomized scalar inverse regression

The scalar selected block has law `IW₁(β-m,I)`. Independent orthogonal
conjugation preserves the entire reconstructed matrix law. The coefficient
of the selected scalar is an explicit nonzero rank-one direction; all its
finitely many nontrivial compressed projections are nonzero almost surely.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

open Spectral

def scalarIdentitySym : SymmetricMatrix 1 :=
  ⟨(1 : Matrix (Fin 1) (Fin 1) ℝ), Matrix.isHermitian_one⟩

@[simp] theorem coe_scalarIdentitySym :
    (scalarIdentitySym : Matrix (Fin 1) (Fin 1) ℝ) = 1 := rfl

def scalarInverseRegressionDirection {m : ℕ} (H : Matrix (Fin 1) (Fin m) ℝ) :
    Fin (1 + m) → ℝ :=
  fun j => Matrix.fromCols (1 : Matrix (Fin 1) (Fin 1) ℝ) H 0 (finSumFinEquiv.symm j)

@[fun_prop] theorem measurable_scalarInverseRegressionDirection {m : ℕ} :
    Measurable (@scalarInverseRegressionDirection m) := by
  apply measurable_pi_lambda
  intro j
  cases hj : finSumFinEquiv.symm j with
  | inl i =>
    simpa only [scalarInverseRegressionDirection, hj, Matrix.fromCols_apply_inl] using
      (measurable_const : Measurable (fun _ : Matrix (Fin 1) (Fin m) ℝ =>
        (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 i))
  | inr i =>
    simpa only [scalarInverseRegressionDirection, hj, Matrix.fromCols_apply_inr,
      Function.comp_def] using
      ((measurable_pi_apply i).comp (measurable_pi_apply (0 : Fin 1)))

theorem scalarInverseRegressionDirection_ne_zero {m : ℕ}
    (H : Matrix (Fin 1) (Fin m) ℝ) : scalarInverseRegressionDirection H ≠ 0 := by
  intro hz
  have h := congrFun hz (Fin.castAdd m (0 : Fin 1))
  simpa [scalarInverseRegressionDirection] using h

theorem inverseRegressionAffine_scalar_update {m : ℕ}
    (S : SymmetricMatrix 1) (R : SymmetricMatrix m) (H : Matrix (Fin 1) (Fin m) ℝ) :
    (inverseRegressionAffine S R H : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) =
      (inverseRegressionAffine scalarIdentitySym R H :
        Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) +
      ((S : Matrix (Fin 1) (Fin 1) ℝ) 0 0 - 1) •
        Matrix.vecMulVec (scalarInverseRegressionDirection H) (scalarInverseRegressionDirection H) := by
  ext i j
  simp only [inverseRegressionAffine, inverseRegressionBlock_eq_affine,
    Matrix.submatrix_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_one, coe_scalarIdentitySym, Matrix.one_apply_eq,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, scalarInverseRegressionDirection]
  ring

theorem congruence_rankOne_update {p k : ℕ}
    (C : Matrix (Fin k) (Fin p) ℝ) (M : Matrix (Fin p) (Fin p) ℝ)
    (u : Fin p → ℝ) (t : ℝ) :
    C * (M + t • Matrix.vecMulVec u u) * Cᵀ =
      C * M * Cᵀ + t • Matrix.vecMulVec (C *ᵥ u) (C *ᵥ u) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

theorem map_conjugate_identity_inverseWishart {p : ℕ} (β : ℝ) (O : Orth p) :
    (inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ)).map (conjugate O) =
      inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ) := by
  unfold conjugate
  rw [map_symmetricCongruenceLinearMap_inverseWishartMeasure_of_det_ne_zero β 1
    (O : Matrix (Fin p) (Fin p) ℝ) (Matrix.UnitaryGroup.det_isUnit O).ne_zero,
    Matrix.mul_one, orth_mul_transpose]

theorem map_haar_conjugate_identity_inverseWishart {p : ℕ} {β : ℝ}
    (hβ : (p : ℝ) - 1 < β) :
    ((haarProb (Orth p)).prod
      (inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ))).map
        (fun z => conjugate z.1 z.2) =
      inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ) := by
  letI := isProbabilityMeasure_inverseWishartMeasure Matrix.PosDef.one hβ
  have horbit (X : SymmetricMatrix p) : ∃ O : Orth p, conjugate O X = X := by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp [conjugate, Matrix.coe_symmetricCongruenceLinearMap_apply]
  have h := map_prod_orbit_representative (haarProb (Orth p))
    (inverseWishartMeasure β (1 : Matrix (Fin p) (Fin p) ℝ))
    conjugate id id (continuous_conjugate p).measurable measurable_id measurable_id
    conjugate_mul (map_conjugate_identity_inverseWishart β) horbit
  simpa only [Measure.map_id, id_eq] using h

def randomizedInverseRegression {q m : ℕ}
    (A : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)
    (z : Orth (q + m) × (SymmetricMatrix q × InverseRegressionNoise q m)) :
    SymmetricMatrix (q + m) :=
  Matrix.symmetricCongruenceLinearMap A (conjugate z.1 (inverseRegressionReconstruction z.2))

@[fun_prop] theorem measurable_randomizedInverseRegression {q m : ℕ}
    (A : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) :
    Measurable (randomizedInverseRegression A) :=
  (LinearMap.continuous_of_finiteDimensional _).measurable.comp
    ((continuous_conjugate (q + m)).measurable.comp
      (measurable_fst.prodMk (measurable_inverseRegressionReconstruction.comp measurable_snd)))

theorem map_randomizedInverseRegression {q m : ℕ} {β : ℝ}
    (hβ : ((q + m : ℕ) : ℝ) - 1 < β)
    (A : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) (hA : A.det ≠ 0) :
    ((haarProb (Orth (q + m))).prod (inverseRegressionSource β q m)).map
      (randomizedInverseRegression A) = inverseWishartMeasure β (A * Aᵀ) := by
  letI := inverseRegressionSource_isProbability hβ
  let f : SymmetricMatrix (q + m) → SymmetricMatrix (q + m) :=
    Matrix.symmetricCongruenceLinearMap A
  let g : Orth (q + m) × SymmetricMatrix (q + m) → SymmetricMatrix (q + m) :=
    Function.uncurry conjugate
  let h : Orth (q + m) × (SymmetricMatrix q × InverseRegressionNoise q m) →
      Orth (q + m) × SymmetricMatrix (q + m) :=
    Prod.map id inverseRegressionReconstruction
  have hf : Measurable f := (LinearMap.continuous_of_finiteDimensional _).measurable
  have hg : Measurable g := (continuous_conjugate (q + m)).measurable
  have hh : Measurable h := measurable_id.prodMap measurable_inverseRegressionReconstruction
  have hbuild : randomizedInverseRegression A = f ∘ (g ∘ h) := by
    funext z
    rfl
  have hnoise : ((haarProb (Orth (q + m))).prod (inverseRegressionSource β q m)).map h =
      (haarProb (Orth (q + m))).prod
        (inverseWishartMeasure β (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)) := by
    change Measure.map (Prod.map id inverseRegressionReconstruction) _ = _
    rw [← Measure.map_prod_map _ _ measurable_id measurable_inverseRegressionReconstruction,
      Measure.map_id, map_inverseRegressionReconstruction hβ]
  have hrotate : ((haarProb (Orth (q + m))).prod
      (inverseWishartMeasure β (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ))).map g =
        inverseWishartMeasure β (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ) :=
    map_haar_conjugate_identity_inverseWishart hβ
  rw [hbuild, ← Measure.map_map hf (hg.comp hh), ← Measure.map_map hg hh,
    hnoise, hrotate]
  change (inverseWishartMeasure β (1 : Matrix (Fin (q + m)) (Fin (q + m)) ℝ)).map
    (Matrix.symmetricCongruenceLinearMap A) = _
  rw [map_symmetricCongruenceLinearMap_inverseWishartMeasure_of_det_ne_zero _ _ A hA,
    Matrix.mul_one]

theorem haar_compression_rotated_direction_ne_zero {p k : ℕ}
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B ≠ 0)
    (u : Fin p → ℝ) (hu : u ≠ 0) :
    ∀ᵐ O : Orth p ∂haarProb (Orth p), Bᵀ *ᵥ ((O : Matrix (Fin p) (Fin p) ℝ) *ᵥ u) ≠ 0 := by
  have hentry : ∃ a b, B a b ≠ 0 := by
    by_contra! h
    exact hB (Matrix.ext h)
  obtain ⟨a, b, hab⟩ := hentry
  let v : Vec p := WithLp.toLp 2 (fun i => B i b)
  let w : Vec p := WithLp.toLp 2 u
  have hv : v ≠ 0 := by
    intro hz
    have h := congrArg (fun z : Vec p => z a) hz
    exact hab (by simpa [v] using h)
  have hw : w ≠ 0 := by
    intro hz
    apply hu
    ext i
    exact congrArg (fun z : Vec p => z i) hz
  filter_upwards [haar_inner_ne_zero hv hw] with O hO
  intro hzero
  apply hO
  have hz := congrFun hzero b
  simpa only [v, w, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toEuclideanCLM_toLp, PiLp.toLp_apply, star_trivial,
    Matrix.mulVec, Matrix.transpose_apply, Pi.zero_apply, dotProduct_comm] using hz

theorem transpose_mul_compression_ne_zero {p k : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.det ≠ 0)
    (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k) (hk : 0 < k) :
    Aᵀ * B ≠ 0 := by
  intro hz
  have hBzero : B = 0 := by
    have h := congrArg (fun M : Matrix (Fin p) (Fin k) ℝ => (Aᵀ)⁻¹ * M) hz
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (by simpa using hA)), Matrix.one_mul, Matrix.mul_zero] at h
    exact h
  rw [hBzero, Matrix.rank_zero] at hB
  omega

end Wishart
end
end CanonicalSource24

section CanonicalSource25
/- Source: Wishart/InverseMomentSharpness.lean -/



/-!
# Necessity of the exact joint inverse-Wishart moment threshold

Condition on a Haar frame and all inverse-regression noise. The baseline is
the actual full conditional matrix at scalar selected block `S = 1`, so every
full-rank compressed baseline is positive definite. Its rank-one increment
has nonzero projection on every active compression almost surely. Fubini and
the scalar inverse-gamma threshold then force the exact sum-of-powers bound.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace WishartVerification

/-- Fubini for a measurable family avoiding one fixed value.  Keeping this
measure-theoretic step abstract avoids repeatedly unfolding the concrete
matrix and Gaussian product-space instances. -/
theorem ae_ae_ne_of_forall_ae {U V E : Type*}
    [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace E]
    [MeasurableSingletonClass E]
    (μ : Measure U) (ν : Measure V) [SFinite μ] [SFinite ν]
    (f : U × V → E) (hf : Measurable f) (z : E)
    (h : ∀ v, ∀ᵐ u ∂μ, f (u, v) ≠ z) :
    ∀ᵐ u ∂μ, ∀ᵐ v ∂ν, f (u, v) ≠ z := by
  have hs : MeasurableSet {p : V × U | f (p.2, p.1) ≠ z} :=
    (((hf.comp measurable_swap) (measurableSet_singleton z)).compl)
  exact (Measure.ae_ae_comm (μ := ν) (ν := μ)
    (p := fun v u => f (u, v) ≠ z) hs).mp (ae_of_all ν h)

end WishartVerification

namespace Wishart

open Spectral

def inverseNoiseDirection {m : ℕ} (w : InverseRegressionNoise 1 m) : Fin (1 + m) → ℝ :=
  scalarInverseRegressionDirection (inverseRegressionCoefficient w.1 w.2)

@[fun_prop] theorem measurable_inverseNoiseDirection {m : ℕ} :
    Measurable (@inverseNoiseDirection m) :=
  measurable_scalarInverseRegressionDirection.comp measurable_inverseRegressionCoefficient

theorem inverseNoiseDirection_ne_zero {m : ℕ} (w : InverseRegressionNoise 1 m) :
    inverseNoiseDirection w ≠ 0 := scalarInverseRegressionDirection_ne_zero _

def inverseRotatedProjection {m k : ℕ}
    (A : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ)
    (B : Matrix (Fin (1 + m)) (Fin k) ℝ)
    (O : Orth (1 + m)) (w : InverseRegressionNoise 1 m) : Fin k → ℝ :=
  Bᵀ *ᵥ (A *ᵥ ((O : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) *ᵥ inverseNoiseDirection w))

@[fun_prop] theorem measurable_inverseRotatedProjection {m k : ℕ}
    (A : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ)
    (B : Matrix (Fin (1 + m)) (Fin k) ℝ) :
    Measurable (fun z : Orth (1 + m) × InverseRegressionNoise 1 m =>
      inverseRotatedProjection A B z.1 z.2) := by
  unfold inverseRotatedProjection
  fun_prop

theorem haar_inverseRotatedProjection_ne_zero {m k : ℕ}
    (A : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) (hA : A.det ≠ 0)
    (B : Matrix (Fin (1 + m)) (Fin k) ℝ) (hB : B.rank = k) (hk : 0 < k)
    (w : InverseRegressionNoise 1 m) :
    ∀ᵐ O : Orth (1 + m) ∂haarProb (Orth (1 + m)),
      inverseRotatedProjection (m := m) (k := k) A B O w ≠ 0 := by
  have h := haar_compression_rotated_direction_ne_zero (Aᵀ * B)
    (transpose_mul_compression_ne_zero A hA B hB hk)
    (inverseNoiseDirection w) (inverseNoiseDirection_ne_zero w)
  filter_upwards [h] with O hO
  intro hz
  apply hO
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mulVec_mulVec]
  exact hz

theorem ae_inverseRotatedProjection_ne_zero_of_finite {m k : ℕ}
    (ν : Measure (InverseRegressionNoise 1 m)) [IsFiniteMeasure ν]
    (A : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) (hA : A.det ≠ 0)
    (B : Matrix (Fin (1 + m)) (Fin k) ℝ) (hB : B.rank = k) (hk : 0 < k) :
    ∀ᵐ O : Orth (1 + m) ∂haarProb (Orth (1 + m)),
      ∀ᵐ w : InverseRegressionNoise 1 m ∂ν,
        inverseRotatedProjection (m := m) (k := k) A B O w ≠ (0 : Fin k → ℝ) := by
  exact ae_ae_ne_of_forall_ae (haarProb (Orth (1 + m))) ν
    (fun z : Orth (1 + m) × InverseRegressionNoise 1 m =>
      inverseRotatedProjection (m := m) (k := k) A B z.1 z.2)
    (measurable_inverseRotatedProjection A B) (0 : Fin k → ℝ)
    (haar_inverseRotatedProjection_ne_zero A hA B hB hk)

theorem ae_inverseRotatedProjection_ne_zero {m k : ℕ} {β : ℝ}
    (hβ : ((1 + m : ℕ) : ℝ) - 1 < β)
    (A : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) (hA : A.det ≠ 0)
    (B : Matrix (Fin (1 + m)) (Fin k) ℝ) (hB : B.rank = k) (hk : 0 < k) :
    ∀ᵐ O : Orth (1 + m) ∂haarProb (Orth (1 + m)),
      ∀ᵐ w : InverseRegressionNoise 1 m
        ∂(inverseRegressionNoiseMeasure β 1 m : Measure (InverseRegressionNoise 1 m)),
        inverseRotatedProjection (m := m) (k := k) A B O w ≠ (0 : Fin k → ℝ) := by
  letI : IsProbabilityMeasure (inverseRegressionNoiseMeasure β 1 m) :=
    inverseRegressionNoiseMeasure_isProbability (q := 1) (m := m) hβ
  exact ae_inverseRotatedProjection_ne_zero_of_finite
    (inverseRegressionNoiseMeasure β 1 m) A hA B hB hk

theorem inverseCompressionDeterminant_scalar_update {m k : ℕ}
    (Omega A : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ)
    (B : Matrix (Fin (1 + m)) (Fin k) ℝ) (c : ℝ)
    (O : Orth (1 + m)) (w : InverseRegressionNoise 1 m) (S : SymmetricMatrix 1) :
    inverseCompressionDeterminant Omega B c (randomizedInverseRegression A (O, (S, w))) =
      (Bᵀ * (randomizedInverseRegression A (O, (scalarIdentitySym, w)) :
          Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) * B + c • compressionScale Omega B +
        ((S : Matrix (Fin 1) (Fin 1) ℝ) 0 0 - 1) •
          Matrix.vecMulVec (inverseRotatedProjection A B O w)
            (inverseRotatedProjection A B O w)).det := by
  let C := Bᵀ * A * (O : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ)
  have hcompress (T : SymmetricMatrix 1) :
      Bᵀ * (randomizedInverseRegression A (O, (T, w)) :
          Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) * B =
        C * (inverseRegressionReconstruction (T, w) :
          Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) * Cᵀ := by
    simp only [C, randomizedInverseRegression, conjugate,
      Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  have hv : C *ᵥ inverseNoiseDirection w = inverseRotatedProjection A B O w := by
    simp only [C, inverseRotatedProjection, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [inverseCompressionDeterminant, hcompress S,
    show (inverseRegressionReconstruction (S, w) :
        Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) =
      (inverseRegressionReconstruction (scalarIdentitySym, w) :
        Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) +
        ((S : Matrix (Fin 1) (Fin 1) ℝ) 0 0 - 1) •
          Matrix.vecMulVec (inverseNoiseDirection w) (inverseNoiseDirection w) from
      inverseRegressionAffine_scalar_update S (symmetricInv w.1) _,
    congruence_rankOne_update, hv, ← hcompress scalarIdentitySym]
  congr 1
  abel

theorem randomizedInverseRegression_baseline_posDef {m : ℕ}
    (A : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) (hA : A.det ≠ 0)
    (O : Orth (1 + m)) (w : InverseRegressionNoise 1 m)
    (hw : (w.1 : Matrix (Fin m) (Fin m) ℝ).PosDef) :
    (randomizedInverseRegression A (O, (scalarIdentitySym, w)) :
      Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ).PosDef := by
  have hR : (symmetricInv w.1 : Matrix (Fin m) (Fin m) ℝ).PosDef := by
    simpa only [coe_symmetricInv] using hw.inv
  have hbase : (inverseRegressionReconstruction (scalarIdentitySym, w) :
      Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ).PosDef :=
    inverseRegressionAffine_posDef Matrix.PosDef.one hR _
  have hO : Function.Injective (O : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ).vecMul :=
    Matrix.vecMul_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.UnitaryGroup.det_isUnit O))
  have hAi : Function.Injective A.vecMul :=
    Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hA.isUnit)
  simpa only [randomizedInverseRegression, conjugate,
    Matrix.coe_symmetricCongruenceLinearMap_apply, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hbase.mul_mul_conjTranspose_same hO).mul_mul_conjTranspose_same hAi

theorem inverseDeterminantProduct_integrable_implies_sum_lt_succ
    {m d : ℕ} {β : ℝ} {Omega : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ}
    (hOmega : Omega.PosDef) (hβ : ((1 + m : ℕ) : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin (1 + m)) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (c ν : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (hactive : ∀ i, 0 < ν i → 0 < k i)
    (hI : Integrable (inverseDeterminantProduct Omega k B c ν Finset.univ)
      (inverseWishartMeasure β Omega)) :
    2 * (∑ i, ν i) < β - (1 + m : ℕ) + 1 := by
  have hscalar : 0 < β - m := by push_cast at hβ; linarith
  letI : IsProbabilityMeasure
      (inverseWishartMeasure (β - m) (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    isProbabilityMeasure_inverseWishartMeasure
      (n := β - m) (S := (1 : Matrix (Fin 1) (Fin 1) ℝ)) Matrix.PosDef.one
      (by simpa only [Nat.cast_one, sub_self] using hscalar)
  letI : IsProbabilityMeasure (inverseRegressionNoiseMeasure β 1 m) :=
    inverseRegressionNoiseMeasure_isProbability (q := 1) (m := m) hβ
  letI : IsProbabilityMeasure (inverseRegressionSource β 1 m) :=
    inverseRegressionSource_isProbability (q := 1) (m := m) hβ
  let A := CFC.sqrt Omega
  have hA : A.det ≠ 0 := sqrt_det_ne_zero_of_posDef hOmega
  have hAA : A * Aᵀ = Omega := by
    rw [matrix_sqrt_transpose]
    exact CFC.sqrt_mul_sqrt_self _ hOmega.posSemidef.nonneg
  have hmap := map_randomizedInverseRegression hβ A hA
  rw [hAA] at hmap
  have hIrot : Integrable (fun z => inverseDeterminantProduct Omega k B c ν Finset.univ
      (randomizedInverseRegression A z))
      ((haarProb (Orth (1 + m))).prod (inverseRegressionSource β 1 m)) := by
    rw [← hmap] at hI
    exact (integrable_map_measure
      (measurable_inverseDeterminantProduct Omega k B c ν Finset.univ).aestronglyMeasurable
      (measurable_randomizedInverseRegression A).aemeasurable).mp hI
  have hconditional : ∀ᵐ O : Orth (1 + m) ∂haarProb (Orth (1 + m)),
      ∀ᵐ w ∂inverseRegressionNoiseMeasure β 1 m,
        Integrable (fun S : SymmetricMatrix 1 =>
          inverseDeterminantProduct Omega k B c ν Finset.univ
            (randomizedInverseRegression A (O, (S, w))))
          (inverseWishartMeasure (β - m) (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    filter_upwards [hIrot.prod_right_ae] with O hO
    exact hO.prod_left_ae
  have hprojections : ∀ᵐ O : Orth (1 + m) ∂haarProb (Orth (1 + m)),
      ∀ᵐ w ∂inverseRegressionNoiseMeasure β 1 m,
        ∀ i, 0 < ν i → inverseRotatedProjection A (B i) O w ≠ 0 := by
    have hi (i : Fin d) : ∀ᵐ O : Orth (1 + m) ∂haarProb (Orth (1 + m)),
        ∀ᵐ w ∂inverseRegressionNoiseMeasure β 1 m,
          0 < ν i → inverseRotatedProjection A (B i) O w ≠ 0 := by
      by_cases hpos : 0 < ν i
      · filter_upwards [ae_inverseRotatedProjection_ne_zero hβ A hA (B i) (hB i)
          (hactive i hpos)] with O hO
        exact hO.mono (fun w hw hνi => hw)
      · exact ae_of_all _ (fun O => ae_of_all _ (fun w => fun h => (hpos h).elim))
    filter_upwards [ae_all_iff.mpr hi] with O hO
    exact ae_all_iff.mpr hO
  have hV : ∀ᵐ w ∂inverseRegressionNoiseMeasure β 1 m,
      (w.1 : Matrix (Fin m) (Fin m) ℝ).PosDef :=
    Measure.quasiMeasurePreserving_fst.ae
      (ae_posDef_nonsingularWishartMeasure β (1 : Matrix (Fin m) (Fin m) ℝ))
  obtain ⟨O, hOI, hOP⟩ := (hconditional.and hprojections).exists
  obtain ⟨w, hwI, hwP, hwV⟩ := (hOI.and (hOP.and hV)).exists
  let M := randomizedInverseRegression A (O, (scalarIdentitySym, w))
  have hM : (M : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ).PosDef :=
    randomizedInverseRegression_baseline_posDef A hA O w hwV
  let D := fun i => (B i)ᵀ * (M : Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ) * B i +
    c i • compressionScale Omega (B i)
  have hD (i : Fin d) : (D i).PosDef :=
    (compressionScale_posDef hM (B i) (hB i)).add_posSemidef
      ((compressionScale_posDef hOmega (B i) (hB i)).posSemidef.smul (hc i))
  obtain ⟨a, ha, habound⟩ := exists_det_rankOne_product_lower k D
    (fun i => inverseRotatedProjection A (B i) O w) ν hD hν hwP
  have hmoment : Integrable (fun S : SymmetricMatrix 1 =>
      ((S : Matrix (Fin 1) (Fin 1) ℝ) 0 0) ^ (∑ i, ν i))
      (inverseWishartMeasure (β - m) (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    have hxm : Measurable (fun S : SymmetricMatrix 1 =>
        (S : Matrix (Fin 1) (Fin 1) ℝ) 0 0) := by fun_prop
    have hx0 : ∀ᵐ S : SymmetricMatrix 1 ∂inverseWishartMeasure (β - m)
        (1 : Matrix (Fin 1) (Fin 1) ℝ), 0 ≤ (S : Matrix (Fin 1) (Fin 1) ℝ) 0 0 := by
      filter_upwards [ae_posDef_inverseWishartMeasure (β - m)
        (1 : Matrix (Fin 1) (Fin 1) ℝ)] with S hS
      exact hS.diag_pos.le
    apply integrable_rpow_of_tail_lower_bound hxm hx0 hwI
      (Finset.sum_nonneg (fun i _ => hν i)) ha
    apply ae_of_all
    intro S hS
    have h := habound ((S : Matrix (Fin 1) (Fin 1) ℝ) 0 0) hS
    simpa only [inverseDeterminantProduct, inverseCompressionDeterminant_scalar_update, D, M] using h

  have hsum := (scalar_inverseWishart_rpow_integrable_iff hscalar).mp hmoment
  push_cast
  linarith

/-- Necessity includes all zero exponents and all ambient dimensions. The
positive-rank condition is required only for factors with positive exponent;
zero-column determinants are identically one and cannot contribute a tail. -/
theorem inverseDeterminantProduct_integrable_implies_sum_lt
    {p d : ℕ} {β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ}
    (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (c ν : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (hactive : ∀ i, 0 < ν i → 0 < k i)
    (hI : Integrable (inverseDeterminantProduct Omega k B c ν Finset.univ)
      (inverseWishartMeasure β Omega)) :
    2 * (∑ i, ν i) < β - p + 1 := by
  by_cases hp : p = 0
  · subst p
    have hk (i : Fin d) : k i = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← hB i]
      simpa using (B i).rank_le_height
    have hzero (i : Fin d) : ν i = 0 := by
      apply le_antisymm _ (hν i)
      by_contra! hpos
      have hbad : (0 : ℕ) < 0 := by simpa only [hk i] using hactive i hpos
      exact (Nat.lt_irrefl 0) hbad
    simp only [hzero, Finset.sum_const_zero, mul_zero, Nat.cast_zero, sub_zero]
    simpa only [Nat.cast_zero, zero_sub] using (show 0 < β + 1 by linarith)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ p by omega)
  exact inverseDeterminantProduct_integrable_implies_sum_lt_succ
    hOmega hβ k B hB c ν hc hν hactive hI

theorem integrable_inverseDeterminantProduct_iff
    {p d : ℕ} {β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ}
    (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (c ν : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (hactive : ∀ i, 0 < ν i → 0 < k i) :
    Integrable (inverseDeterminantProduct Omega k B c ν Finset.univ)
      (inverseWishartMeasure β Omega) ↔ 2 * (∑ i, ν i) < β - p + 1 := by
  constructor
  · exact inverseDeterminantProduct_integrable_implies_sum_lt
      hOmega hβ k B hB c ν hc hν hactive
  · intro hthreshold
    exact integrable_inverseDeterminantProduct_nonneg hOmega hβ k B hB c ν hc Finset.univ
      (fun i _ => hν i) hthreshold

end Wishart
end
end CanonicalSource25

section CanonicalSource26
/- Source: Wishart/InverseCorollary.lean -/



/-!
# Corollary 6.2

The factors below are literally `det(Bᵀ Y B + c Bᵀ Ω B)^ν`. The common-sign
product inequalities, every displayed moment's finiteness, the exact positive
joint-moment threshold, and the unshifted multivariate-gamma formula are
separate declarations corresponding to the four claims of the corollary.
-/

open Matrix MeasureTheory TauCeti TauCeti.Probability WishartVerification
open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Wishart

theorem inverseDeterminantProduct_integrable_common_sign
    {p d : ℕ} {β : ℝ} {Omega : Matrix (Fin p) (Fin p) ℝ}
    (hOmega : Omega.PosDef) (hβ : (p : ℝ) - 1 < β)
    (k : Fin d → ℕ) (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ)
    (hB : ∀ i, (B i).rank = k i) (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hrange : ((∀ i, 0 ≤ ν i) ∧ 2 * (∑ i, ν i) < β - p + 1) ∨ (∀ i, ν i ≤ 0))
    (J : Finset (Fin d)) :
    Integrable (inverseDeterminantProduct Omega k B c ν J) (inverseWishartMeasure β Omega) := by
  rcases hrange with ⟨hν, hsum⟩ | hν
  · have hsubset : (∑ i ∈ J, ν i) ≤ ∑ i, ν i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) (fun i hi hnot => hν i)
    exact integrable_inverseDeterminantProduct_nonneg hOmega hβ k B hB c ν hc J
      (fun i hi => hν i) (by linarith)
  · exact (allFiniteMoments_inverseDeterminantProduct_nonpos hOmega hβ k B hB c ν hc J
      (fun i hi => hν i)).integrable

/-- Corollary 6.2's full product and every selected split, with all the
displayed expectations proved finite under the stated common-sign range. -/
theorem corollary_6_2 {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hrange : ((∀ i, 0 ≤ ν i) ∧ 2 * (∑ i, ν i) < β - p + 1) ∨ (∀ i, ν i ≤ 0)) :
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
  have hI := inverseDeterminantProduct_integrable_common_sign
    hOmega hβ k B hB c ν hc hrange
  refine ⟨hI, ?_⟩
  let Φ := fun i => inverseDeterminantSpectralTest Omega (B i) (c i) (ν i)
  have hΦm (i : Fin d) : Measurable (Φ i) := by fun_prop
  have hΦ0 (i : Fin d) (x : Fin (k i) → ℝ) : 0 ≤ Φ i x :=
    inverseDeterminantSpectralTest_nonneg hOmega (B i) (hB i) (c i) (ν i) x
  have hdir : CommonSpectralMonotonicity k Φ := by
    rcases hrange with ⟨hν, hsum⟩ | hν
    · exact Or.inl (fun i => inverseDeterminantSpectralTest_mono hOmega (B i) (hB i) (c i) (hν i))
    · exact Or.inr (fun i => inverseDeterminantSpectralTest_antitone hOmega (B i) (hB i) (hc i) (hν i))
  have hIspectral (J : Finset (Fin d)) : Integrable (inverseCompressionProduct Omega k B Φ J)
      (inverseWishartMeasure β Omega) :=
    (hI J).congr (ae_inverseDeterminantSpectralProduct_eq hOmega k B hB c ν hc J).symm
  have h := theorem_6_1 hOmega hβ k B hB Φ hΦm hΦ0 hdir
    (fun i => (hIspectral {i}).congr (Filter.Eventually.of_forall
      (inverseCompressionProduct_singleton Omega k B Φ i)))
    (fun j => hIspectral (Finset.univ.erase j)) (hIspectral Finset.univ)
  simpa only [Φ, ← inverseDeterminantMoment_eq_spectral β hOmega k B hB c ν hc] using h

/-- The exact joint threshold, including zero powers. Positive rank is needed
only for active factors. This states the positive-rank interpretation explicitly;
zero-column factors require the effective-exponent version. -/
theorem corollary_6_2_finite_moment_iff {p d : ℕ} {β : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (k : Fin d → ℕ)
    (B : ∀ i, Matrix (Fin p) (Fin (k i)) ℝ) (hB : ∀ i, (B i).rank = k i)
    (c ν : Fin d → ℝ) (hc : ∀ i, 0 ≤ c i) (hν : ∀ i, 0 ≤ ν i)
    (hactive : ∀ i, 0 < ν i → 0 < k i) :
    Integrable (inverseDeterminantProduct Omega k B c ν Finset.univ)
      (inverseWishartMeasure β Omega) ↔ 2 * (∑ i, ν i) < β - p + 1 :=
  integrable_inverseDeterminantProduct_iff hOmega hβ k B hB c ν hc hν hactive

/-- Exact unshifted marginal constant in Corollary 6.2, for every real degree
and real power in its finite-moment range. -/
theorem corollary_6_2_gamma_moment {p k : ℕ} {β r : ℝ}
    {Omega : Matrix (Fin p) (Fin p) ℝ} (hOmega : Omega.PosDef)
    (hβ : (p : ℝ) - 1 < β) (B : Matrix (Fin p) (Fin k) ℝ) (hB : B.rank = k)
    (hr : 2 * r < β - p + 1) :
    (∫ Y : SymmetricMatrix p, (Bᵀ * (Y : Matrix (Fin p) (Fin p) ℝ) * B).det ^ r
      ∂inverseWishartMeasure β Omega) =
      (compressionScale Omega B).det ^ r * (2 : ℝ) ^ (-(k : ℝ) * r) *
        (multivariateGamma k ((β - p + k) / 2 - r) /
          multivariateGamma k ((β - p + k) / 2)) :=
  integral_compression_det_rpow_inverseWishart hOmega hβ B hB hr

end Wishart
end
end CanonicalSource26

section CanonicalSource27
/- Source: Wishart/PositiveTemperatePowers.lean -/



/-!
# Powers of positive functions with polynomial derivative bounds

The lower bound is proved for the concrete smooth extensions. It is used only
at a fixed regularization parameter; no uniform derivative bound as that
parameter tends to zero is claimed.
-/

noncomputable section

namespace WishartVerification

set_option backward.isDefEq.respectTransparency false in
theorem hasTemperateGrowth_rpow_of_pos_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : f.HasTemperateGrowth)
    {δ : ℝ} (hδ : 0 < δ) (hlower : ∀ x, δ ≤ f x) (r : ℝ) :
    (fun x => f x ^ r).HasTemperateGrowth := by
  have hscaled : (fun x => f x / δ).HasTemperateGrowth := by
    simpa only [div_eq_mul_inv, Pi.mul_def] using
      hf.mul (Function.HasTemperateGrowth.const δ⁻¹)
  have hhalf (x : E) : (1 : ℝ) / 2 < f x / δ := by
    have h := (one_le_div hδ).mpr (hlower x)
    linarith
  have hpow := (Function.HasTemperateGrowth.const (δ ^ r)).mul
    (hasTemperateGrowth_rpow_of_half_lt hscaled hhalf r)
  convert hpow using 1
  funext x
  simp only [Pi.mul_apply]
  rw [← Real.mul_rpow hδ.le (div_nonneg (hδ.le.trans (hlower x)) hδ.le)]
  congr 1
  field_simp

theorem smoothPositivePower_pos {a : ℝ} (ha : 0 < a) (r x : ℝ) :
    0 < smoothPositivePower a r x := by
  unfold smoothPositivePower
  apply mul_pos (Real.rpow_pos_of_pos (half_pos ha) _)
  apply Real.rpow_pos_of_pos
  exact lt_of_lt_of_le zero_lt_one (one_le_smoothPositiveClamp _)

theorem smoothPositivePower_lower {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 ≤ r)
    (x : ℝ) : (a / 2) ^ r ≤ smoothPositivePower a r x := by
  unfold smoothPositivePower
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.one_le_rpow (one_le_smoothPositiveClamp _) hr)
    (Real.rpow_pos_of_pos (half_pos ha) _).le

theorem smoothRegularizedDetPower_pos {p : ℕ} {k : Type*} [Fintype k] [DecidableEq k]
    {ε : ℝ} (hε : 0 < ε) (η : ℝ) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (X : SymmetricMatrix p) :
    0 < smoothRegularizedDetPower ε η B M X :=
  smoothPositivePower_pos (by positivity) η _

theorem smoothRegularizedDetPower_lower {p : ℕ} {k : Type*} [Fintype k] [DecidableEq k]
    {ε : ℝ} (hε : 0 < ε) {η : ℝ} (hη : 0 ≤ η) (B : Matrix k k ℝ)
    (M : Matrix (Fin p) k ℝ) (X : SymmetricMatrix p) :
    (ε ^ Fintype.card k / 2 / 2) ^ η ≤ smoothRegularizedDetPower ε η B M X :=
  smoothPositivePower_lower (by positivity) hη _

end WishartVerification
end
end CanonicalSource27

section CanonicalSource28
/- Source: Wishart/ScalarGeneratorChainRule.lean -/



/-!
# Scalar composition for the actual radial generator

Both first and second directional derivatives are genuine Fréchet derivatives.
This is the composition rule used for convex functions of logarithmic spectra.
-/

noncomputable section

open Filter Topology Matrix
open scoped BigOperators

namespace WishartVerification

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {g : E → ℝ} {φ : ℝ → ℝ} {x : E}

theorem fderiv_scalar_comp_apply (hg : DifferentiableAt ℝ g x)
    (hφ : DifferentiableAt ℝ φ (g x)) (H : E) :
    fderiv ℝ (fun y => φ (g y)) x H = deriv φ (g x) * fderiv ℝ g x H := by
  have hd := (hφ.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun T : E →L[ℝ] ℝ => T H) hd

theorem second_fderiv_scalar_comp_apply
    (hg : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y)
    (hφ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ (g y))
    (hφ' : DifferentiableAt ℝ (deriv φ) (g x))
    (H K : E) (hgH : DifferentiableAt ℝ (fun y => fderiv ℝ g y H) x) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => φ (g z)) y H) x K =
      deriv φ (g x) * fderiv ℝ (fun y => fderiv ℝ g y H) x K +
        deriv (deriv φ) (g x) * fderiv ℝ g x H * fderiv ℝ g x K := by
  have hgx : DifferentiableAt ℝ g x := mem_of_mem_nhds hg
  have heq : (fun y => fderiv ℝ (fun z => φ (g z)) y H) =ᶠ[𝓝 x]
      (fun y => deriv φ (g y) * fderiv ℝ g y H) := by
    filter_upwards [hg, hφ] with y hgy hφy
    exact fderiv_scalar_comp_apply hgy hφy H
  have hd := (hφ'.hasDerivAt.comp_hasFDerivAt x hgx.hasFDerivAt).mul hgH.hasFDerivAt
  rw [heq.fderiv_eq]
  simpa only [Function.comp_def, Pi.mul_def, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm,
    add_comm] using congrArg (fun T : E →L[ℝ] ℝ => T K) hd.fderiv

end Derivatives

variable {p : ℕ} {g : SymmetricMatrix p → ℝ} {φ : ℝ → ℝ}

theorem symmetricDirectionalGenerator_scalar_comp {X : SymmetricMatrix p}
    (hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ g Y)
    (hφ : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ φ (g Y))
    (hφ' : DifferentiableAt ℝ (deriv φ) (g X))
    (hgD : ∀ H, DifferentiableAt ℝ (fun Y => fderiv ℝ g Y H) X)
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    symmetricDirectionalGenerator N v (fun Y => φ (g Y)) X =
      deriv φ (g X) * symmetricDirectionalGenerator N v g X +
        deriv (deriv φ) (g X) * symmetricCarreDuChamp g X v := by
  have hgX : DifferentiableAt ℝ g X := mem_of_mem_nhds hg
  have hφX : DifferentiableAt ℝ φ (g X) := mem_of_mem_nhds hφ
  simp only [symmetricDirectionalGenerator, symmetricCarreDuChamp,
    fderiv_scalar_comp_apply hgX hφX,
    second_fderiv_scalar_comp_apply hg hφ hφ' _ _ (hgD _),
    mul_add, Finset.sum_add_distrib]
  have hterm₁ (i j : Fin p) :
      (X : Matrix (Fin p) (Fin p) ℝ) i j *
          (deriv φ (g X) *
            fderiv ℝ (fun Y => fderiv ℝ g Y (symmetricRankDirection v (coordinateVector i))) X
              (symmetricRankDirection v (coordinateVector j))) =
        deriv φ (g X) *
          ((X : Matrix (Fin p) (Fin p) ℝ) i j *
            fderiv ℝ (fun Y => fderiv ℝ g Y (symmetricRankDirection v (coordinateVector i))) X
              (symmetricRankDirection v (coordinateVector j))) := by ring
  have hterm (i j : Fin p) :
      (X : Matrix (Fin p) (Fin p) ℝ) i j *
          (deriv (deriv φ) (g X) * fderiv ℝ g X (symmetricRankDirection v (coordinateVector i)) *
            fderiv ℝ g X (symmetricRankDirection v (coordinateVector j))) =
        deriv (deriv φ) (g X) *
          ((X : Matrix (Fin p) (Fin p) ℝ) i j *
            fderiv ℝ g X (symmetricRankDirection v (coordinateVector i)) *
            fderiv ℝ g X (symmetricRankDirection v (coordinateVector j))) := by ring
  simp only [hterm₁, hterm, ← Finset.mul_sum]
  ring

theorem symmetricDirectionalGenerator_convex_comp_nonneg {X : SymmetricMatrix p}
    (hX : (X : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
    (hg : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ g Y)
    (hφ : ∀ᶠ Y in 𝓝 X, DifferentiableAt ℝ φ (g Y))
    (hφ' : DifferentiableAt ℝ (deriv φ) (g X))
    (hgD : ∀ H, DifferentiableAt ℝ (fun Y => fderiv ℝ g Y H) X)
    (hfirst : 0 ≤ deriv φ (g X)) (hsecond : 0 ≤ deriv (deriv φ) (g X))
    (N : ℝ) (v : EuclideanSpace ℝ (Fin p))
    (hgen : 0 ≤ symmetricDirectionalGenerator N v g X) :
    0 ≤ symmetricDirectionalGenerator N v (fun Y => φ (g Y)) X := by
  rw [symmetricDirectionalGenerator_scalar_comp hg hφ hφ' hgD]
  exact add_nonneg (mul_nonneg hfirst hgen)
    (mul_nonneg hsecond (symmetricCarreDuChamp_nonneg g hX v))

end WishartVerification
end
end CanonicalSource28

section CanonicalSource29
/- Source: Wishart/PositiveQuadraticVariance.lean -/



/-!
# A weighted variance inequality for a positive semidefinite matrix

This finite algebraic identity supplies the nonnegative Hessian term in
log-sum-exp composition of the radial generator.
-/

noncomputable section

open Matrix
open scoped BigOperators

namespace WishartVerification

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

def matrixQuadratic (V : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (V *ᵥ x)

theorem matrixQuadratic_sub (V : Matrix n n ℝ) (x y : n → ℝ) :
    matrixQuadratic V (x - y) = matrixQuadratic V x + matrixQuadratic V y -
      x ⬝ᵥ (V *ᵥ y) - y ⬝ᵥ (V *ᵥ x) := by
  simp only [matrixQuadratic, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
  ring

theorem matrixQuadratic_weighted_sum (V : Matrix n n ℝ)
    (w : ι → ℝ) (a : ι → n → ℝ) :
    matrixQuadratic V (∑ i, w i • a i) =
      ∑ i, ∑ j, w i * w j * (a i ⬝ᵥ (V *ᵥ a j)) := by
  simp only [matrixQuadratic, Matrix.mulVec_sum, sum_dotProduct, dotProduct_sum,
    Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem matrixQuadratic_weighted_variance (V : Matrix n n ℝ)
    (w : ι → ℝ) (a : ι → n → ℝ) :
    (∑ i, ∑ j, w i * w j * matrixQuadratic V (a i - a j)) =
      2 * ((∑ i, w i) * (∑ i, w i * matrixQuadratic V (a i)) -
        matrixQuadratic V (∑ i, w i • a i)) := by
  have hfirst : (∑ i, ∑ j, w i * w j * matrixQuadratic V (a i)) =
      (∑ i, w i) * (∑ i, w i * matrixQuadratic V (a i)) := by
    have hterm (i j : ι) : w i * w j * matrixQuadratic V (a i) =
        w j * (w i * matrixQuadratic V (a i)) := by ring
    simp only [hterm, ← Finset.sum_mul, ← Finset.mul_sum]
  have hsecond : (∑ i, ∑ j, w i * w j * matrixQuadratic V (a j)) =
      (∑ i, w i) * (∑ i, w i * matrixQuadratic V (a i)) := by
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  have hcross : (∑ i, ∑ j, w i * w j * (a j ⬝ᵥ (V *ᵥ a i))) =
      ∑ i, ∑ j, w i * w j * (a i ⬝ᵥ (V *ᵥ a j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [matrixQuadratic_sub, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hfirst, hsecond, hcross]
  simp only [← matrixQuadratic_weighted_sum]
  ring

/-- The inequality holds also for zero total weight and singular covariance;
there is no division by the total weight or by a matrix determinant. -/
theorem matrixQuadratic_weighted_sum_le {V : Matrix n n ℝ} (hV : V.PosSemidef)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a : ι → n → ℝ) :
    matrixQuadratic V (∑ i, w i • a i) ≤
      (∑ i, w i) * (∑ i, w i * matrixQuadratic V (a i)) := by
  have hn : 0 ≤ ∑ i, ∑ j, w i * w j * matrixQuadratic V (a i - a j) := by
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    apply mul_nonneg (mul_nonneg (hw i) (hw j))
    simpa only [matrixQuadratic, star_trivial] using
      hV.dotProduct_mulVec_nonneg (a i - a j)
  rw [matrixQuadratic_weighted_variance] at hn
  linarith

end WishartVerification
end
end CanonicalSource29
