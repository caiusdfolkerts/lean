module

public import VolumePolynomials.PlanarCornerInequality
public import VolumePolynomials.PolytopeFirstVariation
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section
set_option autoImplicit false

/-! # First variation as a literal planar mixed-area formula -/

noncomputable section
open Set Filter MeasureTheory Module
open scoped BigOperators Pointwise Topology

namespace VolumePolynomials.PlanarMixedForm

open PlanarExtrusion OAI.Paper092

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem area_add_smul (hdim : finrank ℝ E = 2) (P A : ConvexBody E)
    {r : ℝ} (hr : 0 ≤ r) :
    μ.real (P + r • A : ConvexBody E) = μ.real (P : Set E) +
      r * (2 * mixedArea μ A P) + r ^ 2 * μ.real (A : Set E) := by
  first
  | rw [area_add μ hdim, mixedArea_smul_right μ _ _ hr,
      haar_real_smul_body μ A hr, hdim, mixedArea_symm μ P A]
    ring

theorem hasDerivWithinAt_area_add_smul (hdim : finrank ℝ E = 2)
    (P A : ConvexBody E) :
    HasDerivWithinAt (fun t : ℝ => μ.real (P + t • A : ConvexBody E))
      (2 * mixedArea μ A P) (Ioi 0) 0 := by
  first
  | have hp : HasDerivAt (fun t : ℝ => μ.real (P : Set E) +
        t * (2 * mixedArea μ A P) + t ^ 2 * μ.real (A : Set E))
        (2 * mixedArea μ A P) 0 := by
      convert ((hasDerivAt_const (0 : ℝ) (μ.real (P : Set E))).add
        ((hasDerivAt_id (0 : ℝ)).mul_const (2 * mixedArea μ A P))).add
        (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (μ.real (A : Set E))) using 1 <;> norm_num
      all_goals rfl
    exact hp.hasDerivWithinAt.congr
      (fun t ht => area_add_smul μ hdim P A ht.le) (area_add_smul μ hdim P A le_rfl)

end VolumePolynomials.PlanarMixedForm

namespace VolumePolynomials.PlanarEdges

open PlanarExtrusion PlanarMixedForm OAI.Paper092 PolytopeFirstVariation

theorem mixedArea_facet_formula {ι : Type*} [Fintype ι]
    (P : ConvexBody Plane) (l : ι → Plane →L[ℝ] ℝ)
    (hl : Function.Injective l) (hbody : HalfspacePyramids.body l = (P : Set Plane))
    (v : ι → Plane) (hv : ∀ i, l i (v i) = 1) (A : ConvexBody Plane) :
    2 * mixedArea volume A P =
      ∑ i, canonicalFacetWeight l i (v i) (hv i) *
        SupportGeometry.support (A : Set Plane) (l i) := by
  first
  | have hcompact : IsCompact (HalfspacePyramids.body l) := by rw [hbody]; exact P.isCompact
    have hd := first_variation l hl hcompact v hv A.isCompact A.convex A.nonempty
    rw [hbody] at hd
    have hp := hasDerivWithinAt_area_add_smul volume PlanarCorner.plane_finrank P A
    have h₁ := (hasDerivWithinAt_iff_tendsto_slope'
      (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hp
    have h₂ := (hasDerivWithinAt_iff_tendsto_slope'
      (self_notMem_Ioi : (0 : ℝ) ∉ Ioi 0)).mp hd
    exact tendsto_nhds_unique h₁ h₂

end VolumePolynomials.PlanarEdges
