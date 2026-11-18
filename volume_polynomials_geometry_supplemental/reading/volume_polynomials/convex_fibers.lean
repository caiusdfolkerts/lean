module

public import VolumePolynomials.MinkowskiAverages
public import VolumePolynomials.ConvexFibersBasic

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Fibers of compact convex sets and their planar average

The fibers are literal sections of a compact convex subset of a product.
Only nonempty fibers over the actual projection enter the averaging measure.
-/

open Set Metric MeasureTheory Module
open scoped Pointwise



namespace VolumePolynomials.MinkowskiAverages

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]

open ConvexFibers

theorem uniformAverage_eq_setAverage (Z : Set U) (f : U → ℝ) :
    uniformAverage Z f = ⨍ y in Z, f y := by
  first
  | rw [uniformAverage, setAverage_eq, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem rootVolume_sq_of_finrank_two (hdim : finrank ℝ E = 2) (K : ConvexBody E) :
    rootVolume K ^ 2 = volume.real (K : Set E) := by
  first
  | have hn : finrank ℝ E ≠ 0 := by omega
    have h := Real.rpow_inv_natCast_pow (x := volume.real (K : Set E)) measureReal_nonneg hn
    simpa only [rootVolume, hdim] using h

/-- The geometric assertion of Lemma 6.1 for an arbitrary compact convex
total set, with an actual Minkowski average. It preserves support values,
widths, and every other continuous monotone Minkowski functional. -/
theorem planar_average_area (hdim : finrank ℝ E = 2) (hbase : 0 < finrank ℝ U)
    (C : ConvexBody (E × U)) (hvol : 0 < volume.real (projection C)) :
    ∃ A : ConvexBody E,
      (∀ φ : MinkowskiFunctional E,
        φ A = uniformAverage (projection C) (fun y => φ (fiberBody C y))) ∧
      (berwaldConstant (finrank ℝ U))⁻¹ *
          uniformAverage (projection C) (fun y => volume.real (fiberBody C y : Set E)) ≤
        volume.real (A : Set E) := by
  first
  | obtain ⟨R, hR⟩ := fibers_uniformly_bounded C
    have hn : finrank ℝ E ≠ 0 := by omega
    have hZ := projection_compact C
    have hK := fiberBody_concave C
    obtain ⟨A, hA, hφ, hroot⟩ := exists_average_body hn hZ hvol hK hR
    refine ⟨A, ?_, ?_⟩
    · intro φ
      rw [uniformAverage_eq_setAverage]
      exact hφ φ
    · let f : U → ℝ := fun y => rootVolume (fiberBody C y)
      have hf : ConcaveOn ℝ (projection C) f := rootVolume_fiber_concave hn hK
      have hfn : ∀ y ∈ projection C, 0 ≤ f y := fun y _ => rootVolume_nonnegative _
      have hfb : BddAbove (f '' projection C) := by
        first
        | apply (((boundedBodies_compact (E := E) R).image continuous_rootVolume).bddAbove).mono
          rintro _ ⟨y, hy, rfl⟩
          exact ⟨fiberBody C y, hR y hy, rfl⟩
      have hB := sharp_berwald_second_moment hbase hZ hvol hf hfn hfb
      have hmean0 : 0 ≤ uniformAverage (projection C) f := by
        first
        | unfold uniformAverage
          apply div_nonneg _ hvol.le
          apply integral_nonneg_of_ae
          filter_upwards [ae_restrict_mem hZ.measurableSet] with y hy
          exact hfn y hy
      have hmean : uniformAverage (projection C) f ≤ rootVolume A := by
        first
        | rw [uniformAverage_eq_setAverage]
          exact hroot
      have hmean2 : uniformAverage (projection C) f ^ 2 ≤ volume.real (A : Set E) := by
        first
        | rw [← rootVolume_sq_of_finrank_two hdim A]
          nlinarith [rootVolume_nonnegative A]
      have hsecond : uniformAverage (projection C) (fun y => f y ^ 2) =
          uniformAverage (projection C) (fun y => volume.real (fiberBody C y : Set E)) := by
        first
        | congr 1
          funext y
          exact rootVolume_sq_of_finrank_two hdim _
      have hc : 0 < berwaldConstant (finrank ℝ U) := by
        first
        | unfold berwaldConstant
          positivity
      rw [hsecond] at hB
      have hfinal := hB.trans (mul_le_mul_of_nonneg_left hmean2 hc.le)
      have hh := mul_le_mul_of_nonneg_left hfinal (inv_pos.mpr hc).le
      simpa only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using hh

end VolumePolynomials.MinkowskiAverages
