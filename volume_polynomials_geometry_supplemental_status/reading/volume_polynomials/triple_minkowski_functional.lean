module

public import VolumePolynomials.GeneralInteractionBody
public import VolumePolynomials.MinkowskiFunctional
public import VolumePolynomials.MixedVolumeMonotonicity

@[expose] public section

set_option autoImplicit false

/-! # Actual mixed volume as a monotone Minkowski functional -/

noncomputable section
open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

def mixedVolumeFunctional {n : ℕ} (K : Fin n → ConvexBody E)
    (hdim : finrank ℝ E = n + 1) : MinkowskiFunctional E where
  toFun A := mixedVolume μ (Fin.cons A K)
  continuous_toFun := by
    first
    | apply (continuous_mixedVolume μ (n + 1)).comp
      apply continuous_pi
      intro i
      refine Fin.cases continuous_id (fun _ => continuous_const) i
  monotone h := by
    first
    | letI : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
      exact mixedVolume_mono_first_all μ K hdim _ _ h
  map_add A B := by
    first
    | simpa only [Fin.update_cons_zero] using mixedVolume_add μ (Fin.cons A K) 0 A B
  map_nonneg_smul r hr A := by
    first
    | simpa only [Fin.update_cons_zero] using mixedVolume_smul μ (Fin.cons A K) 0 A hr

namespace PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner

theorem triple_add_first (A D B C : ConvexBody Plane) :
    triple (A + D) B C = triple A B C + triple D B C := by
  first
  | simp only [triple, mapBody_add, mixed3_add_first]

theorem triple_smul_first (A B C : ConvexBody Plane) {r : ℝ} (hr : 0 ≤ r) :
    triple (r • A) B C = r * triple A B C := by
  first
  | simp only [triple, mapBody_smul, mixed3_smul_first _ _ _ hr]

theorem triple_mono_first {A D : ConvexBody Plane} (B C : ConvexBody Plane)
    (hAD : A ≤ D) : triple A B C ≤ triple D B C := by
  first
  | exact mixedVolume_mono_first_all volume ![mapBody embedYZ B, mapBody embedXZ C]
      space_finrank (mapBody embedXY A) (mapBody embedXY D) (by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, hAD hx, rfl⟩)

theorem continuous_triple_first (B C : ConvexBody Plane) :
    Continuous (fun A : ConvexBody Plane => triple A B C) := by
  first
  | apply (continuous_mixedVolume volume 3).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_mapBody embedXY
    · exact continuous_const
    · exact continuous_const

/-- This is exactly the functional averaged in (6.4): its value is the
ordinary squarefree cubic coefficient for the three coordinate-plane bodies. -/
def tripleFunctional (B C : ConvexBody Plane) : MinkowskiFunctional Plane where
  toFun A := 6 * triple A B C
  continuous_toFun := continuous_const.mul (continuous_triple_first B C)
  monotone h := mul_le_mul_of_nonneg_left (triple_mono_first B C h) (by norm_num)
  map_add A D := by rw [triple_add_first]; ring
  map_nonneg_smul r hr A := by rw [triple_smul_first _ _ _ hr]; ring

@[simp] theorem tripleFunctional_apply (B C A : ConvexBody Plane) :
    tripleFunctional B C A = 6 * triple A B C := rfl

end PlanarInteraction
end VolumePolynomials
