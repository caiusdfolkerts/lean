module

public import VolumePolynomials.ShapeProjectionEvaluation

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace VolumePolynomials.Holonomy

open ShapeConditions

/-- Every calibrated realization of the finite rational conditions has exactly
the forced planar shape, in all three coordinate planes. The hypotheses here
are literal ordinary volumes, and every equality-case input is derived below. -/
theorem calibrated_conditions_force_shape (lam a : ℝ) (K : Fin 9 → Body 3)
    (hK : IsCalibratedTuple K)
    (hcond : OrdinaryConditions lam a (volumeFunction K)) :
    ∃ (hlam₀ : 0 < lam) (hlam₁ : lam < 1), ∃ a₀ b₀ c₀ : Plane,
      (K bodyA : Set ThreeSpace) =
        embedXY a₀ +ᵥ embedXY '' (forcedBody lam hlam₀.le hlam₁ : Set Plane) ∧
      (K bodyB : Set ThreeSpace) =
        embedXZ b₀ +ᵥ embedXZ ''
          (transport01 '' (forcedBody lam hlam₀.le hlam₁ : Set Plane)) ∧
      (K bodyC : Set ThreeSpace) =
        embedYZ c₀ +ᵥ embedYZ ''
          (transport12 '' (transport01 '' (forcedBody lam hlam₀.le hlam₁ : Set Plane))) ∧
      a = volume.real (forcedBody lam hlam₀.le hlam₁ : Set Plane) := by
  first
  | haveI : (volume : Measure Plane).IsAddHaarMeasure := by
      change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
      exact Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
    rcases hcond with ⟨hseg, ⟨hframe, hv0, hv1, hv2, hw0, hw1, hw2,
      hz0, hz1, hz2, hvwz, hplaneA, hplaneB, hplaneC,
      hAB, hABsum, hBC, hBCsum, hAD, hADsum, ha⟩,
      ⟨hlam₀, hlam₁, hApos, hBpos, hCpos, hVApos, hWBpos, hZApos⟩⟩
    rw [hK.extrusion_axisA] at hApos ha
    rw [hK.extrusion_axisB] at hBpos
    rw [hK.extrusion_VA, hK.extrusion_VB] at hAB
    rw [hK.extrusion_VAB, hK.extrusion_VA] at hABsum
    rw [hK.extrusion_WB, hK.extrusion_WC] at hBC
    rw [hK.extrusion_WBC, hK.extrusion_WB] at hBCsum
    rw [hK.extrusion_ZA, hK.extrusion_ZD lam hlam₀.le] at hAD
    rw [hK.extrusion_ZAD lam hlam₀.le, hK.extrusion_ZA] at hADsum
    obtain ⟨a₀, b₀, c₀, hA, hB, hC⟩ := projected_comparisons_force_shape lam hlam₀.le hlam₁
      (planarA K) (planarB K) (planarC K)
      (planarA K).isCompact (planarA K).convex
      (planarB K).isCompact (planarB K).convex
      (planarC K).isCompact (planarC K).convex
      hApos hAB.symm hABsum hBpos hBC.symm hBCsum hAD.symm hADsum
    refine ⟨hlam₀, hlam₁, a₀, b₀, c₀, ?_, ?_, ?_, ?_⟩
    · rw [hK.placeA, hA, linear_image_vadd]
    · rw [hK.placeB, hB, linear_image_vadd]
    · rw [hK.placeC, hC, linear_image_vadd]
    · rw [ha, hA]
      simp only [Measure.real, measure_vadd]


end VolumePolynomials.Holonomy
