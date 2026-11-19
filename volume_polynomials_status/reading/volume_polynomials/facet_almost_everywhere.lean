module

public import VolumePolynomials.PolytopeRadialGeometry
public import VolumePolynomials.LinearFrame
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section
set_option autoImplicit false

/-! # Null exceptional sets in the actual facet Haar measure

Distinct normalized facet functionals cut a proper affine subspace of the
chosen facet coordinates. Thus almost every point of each old facet satisfies
all the other defining inequalities strictly. This is a statement in the
lower-dimensional Haar measure, not merely an ambient null-set assertion.
-/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.FacetAlmostEverywhere

open HalfspacePyramids LinearFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def facetCut (l m : E →L[ℝ] ℝ) (v : E) :
    AffineSubspace ℝ (LinearMap.ker l.toLinearMap) where
  carrier := {y | m (v + y.val) = 1}
  smul_vsub_vadd_mem' c p₁ p₂ p₃ h₁ h₂ h₃ := by
    first
    | change m (v + (c • (p₁.val - p₂.val) + p₃.val)) = 1
      change m (v + p₁.val) = 1 at h₁
      change m (v + p₂.val) = 1 at h₂
      change m (v + p₃.val) = 1 at h₃
      simp only [map_add] at h₁ h₂ h₃
      have he : m p₁.val = m p₂.val := by linarith
      simpa only [map_add, map_smul, map_sub, smul_eq_mul, he, sub_self,
        mul_zero, zero_add] using h₃

theorem facetCut_ne_top (l m : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (hlm : l ≠ m) : facetCut l m v ≠ ⊤ := by
  first
  | intro htop
    have hall : ∀ y : LinearMap.ker l.toLinearMap, m (v + y.val) = 1 := by
      first
      | intro y
        have hy : y ∈ facetCut l m v := by rw [htop]; trivial
        exact hy
    have hmv : m v = 1 := by simpa using hall 0
    have hker : ∀ y : LinearMap.ker l.toLinearMap, m y.val = 0 := by
      first
      | intro y
        have h := hall y
        rw [map_add, hmv] at h
        linarith
    apply hlm
    ext x
    have h := hker (kernelPart l v hv x)
    rw [kernelPart_coe, map_sub, map_smul, smul_eq_mul, hmv, mul_one] at h
    exact (sub_eq_zero.mp h).symm

section FiniteDimensional

variable [FiniteDimensional ℝ E]

theorem measure_facetCut_eq_zero (l m : E →L[ℝ] ℝ) (v : E) (hv : l v = 1)
    (hlm : l ≠ m)
    [MeasurableSpace (LinearMap.ker l.toLinearMap)]
    [BorelSpace (LinearMap.ker l.toLinearMap)]
    (μ : Measure (LinearMap.ker l.toLinearMap))
    [Measure.IsAddHaarMeasure μ] :
    μ {y : LinearMap.ker l.toLinearMap | m (v + y.val) = 1} = 0 :=
  Measure.addHaar_affineSubspace μ (facetCut l m v) (facetCut_ne_top l m v hv hlm)

variable {ι : Type*} [Fintype ι]

def facetBase (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E) :
    Set (LinearMap.ker (l i).toLinearMap) :=
  {y | v + y.val ∈ body l}

theorem facetBase_eq_image (l : ι → E →L[ℝ] ℝ) (i : ι) (v : E)
    (hv : l i v = 1) :
    facetBase l i v = Prod.snd '' (continuousEquiv (l i) v hv '' face l i) := by
  first
  | ext y
    constructor
    · intro hy
      refine ⟨continuousEquiv (l i) v hv (v + y.val), ?_, ?_⟩
      · exact ⟨v + y.val, ⟨hy, by simp [map_add, hv, y.property]⟩, rfl⟩
      · apply Subtype.ext
        change v + y.val - l i (v + y.val) • v = y.val
        have hy0 : l i y.val = 0 := y.property
        simp only [map_add, hv, hy0, add_zero, one_smul]
        abel
    · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
      change v + (x - l i x • v) ∈ body l
      have he : v + (x - v) = x := by abel
      simpa only [hx.2, one_smul, he] using hx.1

theorem facetBase_compact (l : ι → E →L[ℝ] ℝ)
    (hC : IsCompact (body l)) (i : ι) (v : E) (hv : l i v = 1) :
    IsCompact (facetBase l i v) := by
  first
  | rw [facetBase_eq_image l i v hv]
    exact ((face_compact l hC i).image (continuousEquiv (l i) v hv).continuous).image
      continuous_snd

theorem facetBase_point_mem_face (l : ι → E →L[ℝ] ℝ)
    (i : ι) (v : E) (hv : l i v = 1)
    {y : LinearMap.ker (l i).toLinearMap} (hy : y ∈ facetBase l i v) :
    v + y.val ∈ face l i :=
  ⟨hy, by simp [map_add, hv, y.property]⟩

/-- Exceptional intersections with other facets have zero measure in the
actual kernel coordinates, including redundant and lower-dimensional facets. -/
theorem ae_strict_other_facets
    (l : ι → E →L[ℝ] ℝ) (hl : Function.Injective l)
    (hC : IsCompact (body l)) (i : ι) (v : E) (hv : l i v = 1)
    [MeasurableSpace (LinearMap.ker (l i).toLinearMap)]
    [BorelSpace (LinearMap.ker (l i).toLinearMap)]
    (μ : Measure (LinearMap.ker (l i).toLinearMap)) [Measure.IsAddHaarMeasure μ] :
    ∀ᵐ y ∂μ.restrict (facetBase l i v), ∀ j, j ≠ i → l j (v + y.val) < 1 := by
  first
  | have hall : ∀ j, ∀ᵐ y ∂μ, j ≠ i → l j (v + y.val) ≠ 1 := by
      first
      | intro j
        by_cases hji : j = i
        · exact Filter.Eventually.of_forall fun _ h => (h hji).elim
        · have hnull := measure_facetCut_eq_zero (l i) (l j) v hv
            (fun h => hji (hl h).symm) μ
          have hne : ∀ᵐ y ∂μ, l j (v + y.val) ≠ 1 := by
            first
            | rw [ae_iff]
              simpa only [not_not] using hnull
          exact hne.mono fun _ h _ => h
    have hne : ∀ᵐ y ∂μ, ∀ j, j ≠ i → l j (v + y.val) ≠ 1 :=
      Filter.eventually_all.mpr hall
    filter_upwards [ae_restrict_mem (facetBase_compact l hC i v hv).measurableSet,
      ae_restrict_of_ae hne] with y hy hyne
    intro j hji
    exact lt_of_le_of_ne (hy j) (hyne j hji)

end FiniteDimensional
end VolumePolynomials.FacetAlmostEverywhere
