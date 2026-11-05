module

public import Ellipsoid.SupportGeometry
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Pointwise Topology InnerProductSpace RealInnerProductSpace

namespace EllipsoidVerification

theorem hasFDerivAt_euclideanNorm {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (fun z : Space n => ‖z‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have h' : HasFDerivAt (fun z : Space n => ‖z‖)
      ((1 / (2 * ‖x‖)) • 2 • innerSL ℝ x) x := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using h
  apply h'.congr_fderiv
  ext y
  simp only [two_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [norm_ne_zero_iff.mpr hx] <;> ring

theorem hasFDerivAt_axisSupport {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {x : Space n} (hx : x ≠ 0) :
    HasFDerivAt (axisSupport a) (innerSL ℝ (supportPoint a x)) x := by
  have h := (hasFDerivAt_euclideanNorm (axisMap_ne_zero (fun i => (ha i).ne') hx)).comp x
    (axisCLM a).hasFDerivAt
  have h' : HasFDerivAt (axisSupport a)
      ((‖axisMap a x‖⁻¹ • innerSL ℝ (axisMap a x)).comp (axisCLM a)) x := h
  apply h'.congr_fderiv
  ext y
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, axisCLM_apply, smul_eq_mul, supportPoint,
    ← axisMap_inner, real_inner_smul_left, axisSupport]

theorem supportPoint_smul_pos {n : ℕ} (a : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (x : Space n) : supportPoint a (r • x) = supportPoint a x := by
  simp only [supportPoint, axisSupport_smul, abs_of_pos hr, axisMap_smul, _root_.mul_inv_rev,
    smul_smul]
  congr 1
  congr 1
  field_simp [hr.ne']

theorem normalOffset_smul_nonneg {n : ℕ} (a : Fin n → ℝ) (t : ℝ)
    {r : ℝ} (hr : 0 ≤ r) (x : Space n) :
    normalOffset a t (r • x) = r • normalOffset a t x := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp
  · rw [normalOffset, norm_smul, Real.norm_of_nonneg hr.le,
      supportPoint_smul_pos a hr, normalOffset, smul_add, smul_smul, smul_smul, smul_smul]
    congr 1 <;> congr 1 <;> ring

theorem normalized_mem_unitSphere {n : ℕ} {x : Space n} (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Space n) 1 := by
  simp [Metric.mem_sphere, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    norm_ne_zero_iff.mpr hx]

/-- The homogeneous normal-offset parametrization is onto the whole ambient
space. The proof maximizes the dual support ratio on the actual unit sphere
and applies Fermat's theorem; it does not presume a boundary parametrization. -/
theorem normalOffset_surjective {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {t : ℝ} (ht : 0 ≤ t) : Function.Surjective (normalOffset a t) := by
  intro z
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  let g : Space n → ℝ := fun u => ⟪z, u⟫_ℝ / (axisSupport a u + t)
  have hu0 (u : Space n) (hu : u ∈ Metric.sphere (0 : Space n) 1) : u ≠ 0 := by
    intro h
    simpa [h] using hu
  have hden (u : Space n) (hu : u ∈ Metric.sphere (0 : Space n) 1) :
      0 < axisSupport a u + t := add_pos_of_pos_of_nonneg (axisSupport_pos ha (hu0 u hu)) ht
  have hg : ContinuousOn g (Metric.sphere (0 : Space n) 1) := by
    apply ((innerSL ℝ z).continuous.continuousOn).div
      ((continuous_axisSupport a).add continuous_const).continuousOn
    exact fun u hu => (hden u hu).ne'
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : Space n) 1).exists_isMaxOn
    ⟨‖z‖⁻¹ • z, normalized_mem_unitSphere hz⟩ hg
  have hun : ‖u‖ = 1 := by simpa using hu
  let c := g u
  have hc : 0 < c := by
    have hv := hmax (normalized_mem_unitSphere hz)
    have hip : 0 < ⟪z, ‖z‖⁻¹ • z⟫_ℝ := by
      rw [inner_smul_right, real_inner_self_eq_norm_sq]
      positivity
    exact (div_pos hip (hden _ (normalized_mem_unitSphere hz))).trans_le hv
  have hsupport (x : Space n) : ⟪z, x⟫_ℝ ≤ c * (axisSupport a x + t * ‖x‖) := by
    by_cases hx : x = 0
    · simp [hx]
    have hnx := norm_pos_iff.mpr hx
    have hm := (div_le_iff₀ (hden _ (normalized_mem_unitSphere hx))).mp
      (hmax (normalized_mem_unitSphere hx))
    have hmul := mul_le_mul_of_nonneg_left hm hnx.le
    simp only [inner_smul_right, axisSupport_smul,
      abs_of_pos (inv_pos.mpr hnx)] at hmul
    convert hmul using 1 <;> field_simp [hnx.ne'] <;> ring
  let f : Space n → ℝ := fun x => c * (axisSupport a x + t * ‖x‖) - ⟪z, x⟫_ℝ
  have hfu : f u = 0 := by
    dsimp [f, c, g]
    rw [hun, mul_one, div_mul_cancel₀ _ (hden u hu).ne', sub_self]
  have hmin : IsLocalMin f u := by
    apply (show IsMinOn f Set.univ u from fun x hx => ?_).isLocalMin (by simp)
    rw [hfu]
    exact sub_nonneg.mpr (hsupport x)
  have hderiv := (((hasFDerivAt_axisSupport ha (hu0 u hu)).add
    ((hasFDerivAt_euclideanNorm (hu0 u hu)).const_mul t)).const_mul c).sub
      (innerSL ℝ z).hasFDerivAt
  have hzero := hmin.hasFDerivAt_eq_zero hderiv
  have hgrad : c • (supportPoint a u + t • u) = z := by
    let w := c • (supportPoint a u + t • u) - z
    have hw := congrArg (fun L : Space n →L[ℝ] ℝ => L w) hzero
    have hnorm : ‖w‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      change ⟪c • (supportPoint a u + t • u) - z, w⟫_ℝ = 0
      simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply,
        innerSL_apply_apply, smul_eq_mul, hun, inv_one, one_mul,
        inner_sub_left, real_inner_smul_left, inner_add_left] using hw
    have hnorm0 : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  refine ⟨c • u, ?_⟩
  rw [normalOffset_smul_nonneg a t hc.le, normalOffset, hun, one_smul]
  exact hgrad

/-- The image is the literal Minkowski parallel body, including radius zero. -/
theorem normalOffset_image_unitBall {n : ℕ} {a : Fin n → ℝ} (ha : ∀ i, 0 < a i)
    {t : ℝ} (ht : 0 ≤ t) :
    normalOffset a t '' Metric.closedBall (0 : Space n) 1 = parallelBody (axisBody a) t := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    exact normalOffset_mem_parallelBody a ht hx
  · intro z hz
    obtain ⟨x, rfl⟩ := normalOffset_surjective ha ht z
    refine ⟨x, ?_, rfl⟩
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨v, hv, w, hw, heq⟩ := hz
    have hh : ⟪x, normalOffset a t x⟫_ℝ ≤ axisSupport a x + t * ‖x‖ := by
      rw [← heq, inner_add_right]
      have hs := inner_le_axisSupport a x hv
      have hn : ‖w‖ ≤ t := by simpa using hw
      have hi := (real_inner_le_norm x w).trans
        (mul_le_mul_of_nonneg_left hn (norm_nonneg x))
      nlinarith
    rw [inner_normalOffset_self] at hh
    have hp := add_pos_of_pos_of_nonneg (axisSupport_pos ha hx)
      (mul_nonneg ht (norm_nonneg x))
    have hn : ‖x‖ ≤ 1 := le_of_mul_le_mul_right (by simpa using hh) hp
    simpa using hn

end EllipsoidVerification
