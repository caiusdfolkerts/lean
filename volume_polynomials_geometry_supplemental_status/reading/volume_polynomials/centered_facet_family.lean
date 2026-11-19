module

public import VolumePolynomials.FiniteFacetFamily
public import VolumePolynomials.HalfspacePyramids
public import VolumePolynomials.BodyOperations
public import Mathlib.Tactic.Positivity

@[expose] public section
set_option autoImplicit false

/-!
# Centered finite facet families and their genuine lower-dimensional bodies

The height coefficients are supports of the original summands. Containing the
origin makes each one nonnegative; interior of the total makes every positive
weighted height positive. The lower-dimensional bodies are actual projected
exposed faces in the kernels of the facet functionals.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise BigOperators

namespace VolumePolynomials.PolytopeGeometry

open OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem support_nonneg_of_zero_mem {A : Set E} (hA : IsCompact A)
    (h0 : (0 : E) ∈ A) (l : E →L[ℝ] ℝ) :
    0 ≤ SupportGeometry.support A l := by
  first
  | simpa only [map_zero] using SupportGeometry.le_support hA l h0

theorem support_pos_of_zero_mem_interior {A : Set E} (hA : IsCompact A)
    (h0 : (0 : E) ∈ interior A) (l : E →L[ℝ] ℝ) (hl : l ≠ 0) :
    0 < SupportGeometry.support A l := by
  first
  | obtain ⟨v, hv⟩ := LinearFrame.exists_unit_value l hl
    have hv0 : v ≠ 0 := by intro h; simpa [h] using hv
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
    let t : ℝ := ε / (2 * ‖v‖)
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hn)
    have htv : t • v ∈ A := by
      apply hball
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have heq : t * ‖v‖ = ε / 2 := by dsimp [t]; field_simp
      rw [heq]
      linarith
    have h := SupportGeometry.le_support hA l htv
    simp only [map_smul, smul_eq_mul, hv, mul_one] at h
    exact ht.trans_le h

theorem exposed_eq_support_level {A : Set E} (hA : IsCompact A) (hne : A.Nonempty)
    (l : E →L[ℝ] ℝ) :
    l.toExposed A = {x | x ∈ A ∧ l x = SupportGeometry.support A l} := by
  first
  | ext x
    constructor
    · intro hx
      exact ⟨hx.1, le_antisymm (SupportGeometry.le_support hA l hx.1)
        (SupportGeometry.support_le hne l hx.2)⟩
    · rintro ⟨hx, heq⟩
      refine ⟨hx, ?_⟩
      intro y hy
      rw [heq]
      exact SupportGeometry.le_support hA l hy

namespace FixedFacets

variable {ι : Type*} [Fintype ι] {A : ι → Set E} (D : FixedFacets A)

def heightCoefficient (i : Fin D.count) (j : ι) : ℝ :=
  SupportGeometry.support (A j) (D.normal i)

def height (t : ι → ℝ) (i : Fin D.count) : ℝ :=
  ∑ j, t j * D.heightCoefficient i j

theorem heightCoefficient_nonneg (hA : ∀ j, IsCompact (A j))
    (h0 : ∀ j, (0 : E) ∈ A j) (i : Fin D.count) (j : ι) :
    0 ≤ D.heightCoefficient i j :=
  support_nonneg_of_zero_mem (hA j) (h0 j) (D.normal i)

theorem height_eq_support (hA : ∀ j, IsCompact (A j))
    (hne : ∀ j, (A j).Nonempty) (t : ι → ℝ) (ht : ∀ j, 0 < t j) (i : Fin D.count) :
    D.height t i = SupportGeometry.support (∑ j, t j • A j) (D.normal i) :=
  (support_positive_sum A hA hne t ht (D.normal i)).symm

theorem height_one_pos (hA : ∀ j, IsCompact (A j))
    (h0 : ∀ j, (0 : E) ∈ A j) (hint : (0 : E) ∈ interior (∑ j, A j))
    (i : Fin D.count) : 0 < ∑ j, D.heightCoefficient i j := by
  first
  | have hcompact : IsCompact (∑ j, A j) :=
      Finset.sum_induction A IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton (fun j _ => hA j)
    have h := support_pos_of_zero_mem_interior hcompact hint (D.normal i) (D.normal_ne_zero i)
    rw [SupportGeometry.support_sum Finset.univ A (fun j _ => hA j)
      (fun j _ => ⟨0, h0 j⟩)] at h
    exact h

theorem height_pos (hA : ∀ j, IsCompact (A j))
    (h0 : ∀ j, (0 : E) ∈ A j) (hint : (0 : E) ∈ interior (∑ j, A j))
    (t : ι → ℝ) (ht : ∀ j, 0 < t j) (i : Fin D.count) : 0 < D.height t i := by
  first
  | have hn : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ D.heightCoefficient i j :=
      fun j _ => D.heightCoefficient_nonneg hA h0 i j
    obtain ⟨j, hj, hjpos⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp (D.height_one_pos hA h0 hint i)
    apply (Finset.sum_pos_iff_of_nonneg (fun j _ =>
      mul_nonneg (ht j).le (D.heightCoefficient_nonneg hA h0 i j))).mpr
    exact ⟨j, hj, mul_pos (ht j) hjpos⟩

def normalized (t : ι → ℝ) (i : Fin D.count) : E →L[ℝ] ℝ :=
  (D.height t i)⁻¹ • D.normal i

theorem normalized_le_one_iff (t : ι → ℝ) (i : Fin D.count)
    (hi : 0 < D.height t i) (x : E) :
    D.normalized t i x ≤ 1 ↔ D.normal i x ≤ D.height t i := by
  first
  | change (D.height t i)⁻¹ * D.normal i x ≤ 1 ↔ _
    rw [mul_comm, ← div_eq_mul_inv, div_le_one hi]

theorem normalized_eq_one_iff (t : ι → ℝ) (i : Fin D.count)
    (hi : 0 < D.height t i) (x : E) :
    D.normalized t i x = 1 ↔ D.normal i x = D.height t i := by
  first
  | change (D.height t i)⁻¹ * D.normal i x = 1 ↔ _
    rw [mul_comm, ← div_eq_mul_inv, div_eq_one_iff_eq hi.ne']

theorem normalized_body (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (hheight : ∀ i, 0 < D.height t i) :
    HalfspacePyramids.body (D.normalized t) = ∑ j, t j • A j := by
  first
  | rw [D.body_eq t ht]
    ext x
    change (∀ i, D.normalized t i x ≤ 1) ↔ _
    simp_rw [D.normalized_le_one_iff t _ (hheight _) x]
    rfl

theorem normalized_injective (t : ι → ℝ) (hheight : ∀ i, 0 < D.height t i) :
    Function.Injective (D.normalized t) := by
  first
  | intro i j hij
    apply D.positive_ray_injective i j (div_pos (hheight i) (hheight j))
    have h := congrArg (fun L : E →L[ℝ] ℝ => D.height t i • L) hij
    simpa only [normalized, smul_smul, mul_inv_cancel₀ (hheight i).ne', one_smul,
      ← div_eq_mul_inv] using h

theorem normalized_face (hA : ∀ j, IsCompact (A j))
    (hne : ∀ j, (A j).Nonempty) (t : ι → ℝ) (ht : ∀ j, 0 < t j)
    (hheight : ∀ i, 0 < D.height t i) (i : Fin D.count) :
    HalfspacePyramids.face (D.normalized t) i =
      (D.normal i).toExposed (∑ j, t j • A j) := by
  first
  | have hc : IsCompact (∑ j, t j • A j) :=
      Finset.sum_induction _ IsCompact (fun _ _ ha hb => ha.add hb)
        isCompact_singleton (fun j _ => (hA j).image (continuous_const.smul continuous_id))
    have hn : (∑ j, t j • A j).Nonempty :=
      PolytopeFaces.nonempty_sum Finset.univ _ (fun j _ => (hne j).image (fun x => t j • x))
    rw [exposed_eq_support_level hc hn, ← D.height_eq_support hA hne t ht i]
    ext x
    change (x ∈ HalfspacePyramids.body (D.normalized t) ∧ D.normalized t i x = 1) ↔ _
    rw [D.normalized_body t ht hheight, D.normalized_eq_one_iff t i (hheight i) x]
    rfl

end FixedFacets

section KernelBody

variable [FiniteDimensional ℝ E]

def kernelBody (K : ConvexBody E) (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    ConvexBody (LinearMap.ker l.toLinearMap) where
  carrier := LinearFrame.kernelPart l v hv '' l.toExposed (K : Set E)
  convex' := (ContinuousLinearMap.toExposed.isExposed.convex K.convex).linear_image
    (LinearFrame.kernelPart l v hv)
  isCompact' := (ContinuousLinearMap.toExposed.isExposed.isCompact K.isCompact).image
    (LinearFrame.kernelPart l v hv).continuous_of_finiteDimensional
  nonempty' := (PolytopeFaces.exposed_nonempty l K.isCompact K.nonempty).image _

theorem kernelBody_isFiniteHull (K : ConvexBody E) (hK : IsFiniteHull (K : Set E))
    (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1) :
    IsFiniteHull (kernelBody K l v hv : Set (LinearMap.ker l.toLinearMap)) :=
  (hK.exposed l).linear_image (LinearFrame.kernelPart l v hv)

theorem image_exposed_positive_sum {ι : Type*} [Fintype ι]
    (K : ι → ConvexBody E) (l : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (t : ι → ℝ) (ht : ∀ j, 0 < t j) :
    Prod.snd '' (LinearFrame.continuousEquiv l v hv ''
      l.toExposed (∑ j, t j • (K j : Set E))) =
        (↑(∑ j, t j • kernelBody (K j) l v hv) : Set (LinearMap.ker l.toLinearMap)) := by
  first
  | rw [Set.image_image]
    change LinearFrame.kernelPart l v hv '' l.toExposed (∑ j, t j • (K j : Set E)) = _
    rw [PolytopeFaces.exposed_weighted_sum l Finset.univ _ t (fun j _ => ht j),
      image_weighted_sum, coe_sum_body]
    apply Finset.sum_congr rfl
    intro j hj
    rfl

end KernelBody
end VolumePolynomials.PolytopeGeometry
