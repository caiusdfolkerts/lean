module

public import VolumePolynomials.ConvexFibersBasic
public import VolumePolynomials.BodyOperations
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section
noncomputable section

/-!
# Fubini for the higher-dimensional lift

The quotient Jacobian and the actual fiber of the weighted Minkowski sum
are identified explicitly. The lower-dimensional summands are embedded at
quotient coordinate zero. The formula includes scalar zero when the
quotient dimension is positive.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.FiberVolume

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

open ConvexFibers

def embedBody (D : ConvexBody E) : ConvexBody (E × U) :=
  mapBody (ContinuousLinearMap.inl ℝ E U) D

theorem coe_embedBody (D : ConvexBody E) :
    (embedBody (U := U) D : Set (E × U)) = (D : Set E) ×ˢ {0} := by
  first
  | ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
    · rintro ⟨hp, hp0⟩
      exact ⟨p.1, hp, Prod.ext rfl hp0.symm⟩

theorem scaled_sum_fiber (C : ConvexBody (E × U)) (D : ConvexBody E)
    {t : ℝ} (ht : t ≠ 0) (y : U) :
    fiberSet (t • C + embedBody D) (t • y) = t • fiberSet C y + (D : Set E) := by
  first
  | ext x
    constructor
    · rintro ⟨_, ⟨⟨u, z⟩, huz, rfl⟩, _, ⟨v, hv, rfl⟩, hsum⟩
      have hy := congrArg Prod.snd hsum
      change t • z + (0 : U) = t • y at hy
      rw [add_zero] at hy
      have hzy : z = y := (smul_right_injective U ht) hy
      subst z
      exact ⟨t • u, ⟨u, huz, rfl⟩, v, hv, congrArg Prod.fst hsum⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, v, hv, huv⟩
      refine ⟨t • (u, y), ⟨(u, y), hu, rfl⟩,
        (v, 0), ⟨v, hv, rfl⟩, ?_⟩
      exact Prod.ext huv (by simp)

section Measure

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]
  [MeasureSpace E] [BorelSpace E] [MeasureSpace U] [BorelSpace U]
  [Measure.IsAddHaarMeasure (volume : Measure E)]
  [Measure.IsAddHaarMeasure (volume : Measure U)]

theorem realVolume_eq_integral_fibers (C : ConvexBody (E × U)) :
    volume.real (C : Set (E × U)) = ∫ y : U, volume.real (fiberSet C y) := by
  first
  | let f : E × U → ℝ := (C : Set (E × U)).indicator (fun _ => 1)
    have hf : Integrable f (volume : Measure (E × U)) :=
      (integrableOn_const C.isCompact.measure_ne_top).integrable_indicator C.isCompact.measurableSet
    have htotal : (∫ p : E × U, f p) = volume.real (C : Set (E × U)) := by
      first
      | rw [integral_indicator C.isCompact.measurableSet, setIntegral_const]
        simp only [smul_eq_mul, mul_one]
    have hfiber (y : U) : (∫ x : E, f (x, y)) = volume.real (fiberSet C y) := by
      first
      | change (∫ x : E, (fiberSet C y).indicator (fun _ => (1 : ℝ)) x) = _
        rw [integral_indicator (fiberSet_compact C y).measurableSet, setIntegral_const]
        simp only [smul_eq_mul, mul_one]
    have h := integral_prod_symm f (by simpa only [Measure.volume_eq_prod] using hf)
    simpa only [← Measure.volume_eq_prod, htotal, hfiber] using h

theorem integrable_fiber_realVolume (C : ConvexBody (E × U)) :
    Integrable (fun y : U => volume.real (fiberSet C y)) := by
  first
  | let f : E × U → ℝ := (C : Set (E × U)).indicator (fun _ => 1)
    have hf : Integrable f ((volume : Measure E).prod (volume : Measure U)) := by
      rw [← Measure.volume_eq_prod]
      exact (integrableOn_const C.isCompact.measure_ne_top).integrable_indicator C.isCompact.measurableSet
    have hfiber (y : U) : (∫ x : E, f (x, y)) = volume.real (fiberSet C y) := by
      change (∫ x : E, (fiberSet C y).indicator (fun _ => (1 : ℝ)) x) = _
      rw [integral_indicator (fiberSet_compact C y).measurableSet, setIntegral_const]
      simp only [smul_eq_mul, mul_one]
    simpa only [hfiber] using hf.integral_prod_right

theorem scaled_sum_fiber_volume (C : ConvexBody (E × U)) (D : ConvexBody E)
    {t : ℝ} (ht : t ≠ 0) (y : U) :
    volume.real (fiberSet (t • C + embedBody D) (t • y)) =
      (projection C).indicator (fun z => volume.real
        ((t • fiberBody C z + D : ConvexBody E) : Set E)) y := by
  first
  | classical
    rw [scaled_sum_fiber C D ht y]
    by_cases hy : y ∈ projection C
    · rw [Set.indicator_of_mem hy]
      simp only [ConvexBody.coe_add, ConvexBody.coe_smul, coe_fiberBody C hy]
    · rw [Set.indicator_of_notMem hy]
      have he : fiberSet C y = ∅ := not_nonempty_iff_eq_empty.mp
        (fun h => hy ((fiberSet_nonempty_iff C y).mp h))
      simp only [he, Set.smul_set_empty, Set.empty_add, measureReal_empty]

/-- Formula (6.4), with all lower-dimensional summands collected into `D`.
This version is independent of any polynomial coefficient calculation. -/
theorem realVolume_scaled_sum_of_pos (C : ConvexBody (E × U)) (D : ConvexBody E)
    {t : ℝ} (ht : 0 < t) :
    volume.real ((t • C + embedBody D : ConvexBody (E × U)) : Set (E × U)) =
      t ^ finrank ℝ U * ∫ y in projection C,
        volume.real ((t • fiberBody C y + D : ConvexBody E) : Set E) := by
  first
  | let f : U → ℝ := fun y => volume.real (fiberSet (t • C + embedBody D) y)
    have hchange := Measure.integral_comp_smul_of_nonneg volume f t (hR := ht.le)
    have hleft : (∫ y : U, f (t • y)) =
        ∫ y in projection C, volume.real ((t • fiberBody C y + D : ConvexBody E) : Set E) := by
      first
      | simp only [f, scaled_sum_fiber_volume C D ht.ne']
        exact integral_indicator (projection_compact C).measurableSet
    rw [hleft, smul_eq_mul] at hchange
    rw [realVolume_eq_integral_fibers]
    change (∫ y, f y) = t ^ finrank ℝ U * _
    rw [hchange, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]

theorem realVolume_embedBody [Nontrivial U] (D : ConvexBody E) :
    volume.real (embedBody (U := U) D : Set (E × U)) = 0 := by
  first
  | rw [coe_embedBody, measureReal_def, Measure.volume_eq_prod, Measure.prod_prod]
    simp only [measure_singleton, mul_zero, ENNReal.toReal_zero]

theorem realVolume_scaled_sum (hk : 0 < finrank ℝ U)
    (C : ConvexBody (E × U)) (D : ConvexBody E) {t : ℝ} (ht : 0 ≤ t) :
    volume.real ((t • C + embedBody D : ConvexBody (E × U)) : Set (E × U)) =
      t ^ finrank ℝ U * ∫ y in projection C,
        volume.real ((t • fiberBody C y + D : ConvexBody E) : Set E) := by
  first
  | rcases ht.eq_or_lt with rfl | ht
    · letI : Nontrivial U := finrank_pos_iff.mp hk
      have hz : ((0 : ℝ) • C + embedBody D : ConvexBody (E × U)) = embedBody D := by
        rw [body_zero_smul]
        exact zero_add (embedBody (U := U) D)
      rw [hz, realVolume_embedBody, zero_pow hk.ne', zero_mul]
    · exact realVolume_scaled_sum_of_pos C D ht

end Measure

end VolumePolynomials.FiberVolume
