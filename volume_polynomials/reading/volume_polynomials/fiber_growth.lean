module

public import VolumePolynomials.FiberVolume
public import VolumePolynomials.RealizationCone
public import VolumePolynomials.LinearFrame
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
noncomputable section

/-!
# Volume growth along a fixed subspace

An embedded `k`-dimensional summand changes only the fibers. Fubini gives
upper growth of order `t^k`, and the contained translate in each nonempty
fiber gives a matching lower bound whenever the summand and quotient
projection have positive volume. Both bounds are literal measure bounds.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.FiberGrowth

open ConvexFibers FiberVolume

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def projectionBody (C : ConvexBody (E × U)) : ConvexBody U :=
  mapBody (ContinuousLinearMap.snd ℝ E U) C

theorem coe_projectionBody (C : ConvexBody (E × U)) :
    (projectionBody C : Set U) = projection C := rfl

theorem embedded_sum_fiber (A : ConvexBody E) (C : ConvexBody (E × U)) (y : U) :
    fiberSet (embedBody A + C) y = (A : Set E) + fiberSet C y := by
  first
  | ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, ⟨b, z⟩, hbz, heq⟩
      have hz : z = y := by simpa using congrArg Prod.snd heq
      subst z
      exact ⟨a, ha, b, hbz, congrArg Prod.fst heq⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨(a, 0), ⟨a, ha, rfl⟩, (b, y), hb, Prod.ext hab (zero_add _)⟩

theorem embedded_sum_fiber_of_notMem (A : ConvexBody E) (C : ConvexBody (E × U))
    {y : U} (hy : y ∉ projection C) : fiberSet (embedBody A + C) y = ∅ := by
  first
  | have he : fiberSet C y = ∅ := Set.not_nonempty_iff_eq_empty.mp
      (fun h => hy ((fiberSet_nonempty_iff C y).mp h))
    rw [embedded_sum_fiber, he, Set.add_empty]

theorem embedded_sum_fiber_of_mem (A : ConvexBody E) (C : ConvexBody (E × U))
    {y : U} (hy : y ∈ projection C) :
    fiberSet (embedBody A + C) y = (A + fiberBody C y : ConvexBody E) := by
  first
  | rw [embedded_sum_fiber, ConvexBody.coe_add, coe_fiberBody C hy]

theorem map_snd_embedBody (A : ConvexBody E) :
    mapBody (ContinuousLinearMap.snd ℝ E U) (embedBody A) = 0 := by
  first
  | apply ConvexBody.ext
    ext y
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      rfl
    · intro hy
      have hy0 : y = 0 := hy
      subst y
      obtain ⟨a, ha⟩ := A.nonempty
      exact ⟨(a, 0), ⟨a, ha, rfl⟩, rfl⟩

section Coordinates

variable {k q : ℕ}

theorem upper_bound (A : Body k) (C : ConvexBody (Space k × Space q))
    {t : ℝ} (ht : 1 ≤ t) :
    volume.real ((embedBody (t • A) + C : ConvexBody (Space k × Space q)) : Set (Space k × Space q)) ≤
      t ^ k * volume.real ((embedBody A + C : ConvexBody (Space k × Space q)) : Set (Space k × Space q)) := by
  first
  | have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hpoint (y : Space q) :
        volume.real (fiberSet (embedBody (t • A) + C) y) ≤
          t ^ k * volume.real (fiberSet (embedBody A + C) y) := by
      by_cases hy : y ∈ projection C
      · rw [embedded_sum_fiber_of_mem _ _ hy, embedded_sum_fiber_of_mem _ _ hy]
        have hw : ∀ i : Fin 2, 0 ≤ (![t, 1] : Fin 2 → ℝ) i := by
          intro i
          fin_cases i <;> first | exact ht0 | exact zero_le_one
        have hb : ∀ i : Fin 2, (![t, 1] : Fin 2 → ℝ) i ≤ t := by
          intro i
          fin_cases i <;> first | exact le_rfl | exact ht
        have h := volumeFunction_le (![A, fiberBody C y] : Fin 2 → Body k) ![t, 1] hw ht0 hb
        simpa only [volumeFunction, weightedSum, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, bodyVolume] using h
      · rw [embedded_sum_fiber_of_notMem _ _ hy, embedded_sum_fiber_of_notMem _ _ hy,
          measureReal_empty, mul_zero]
    rw [realVolume_eq_integral_fibers, realVolume_eq_integral_fibers, ← integral_const_mul]
    exact integral_mono (integrable_fiber_realVolume _)
      ((integrable_fiber_realVolume _).const_mul _) hpoint

theorem lower_bound (A : Body k) (C : ConvexBody (Space k × Space q))
    {t : ℝ} (ht : 0 ≤ t) :
    t ^ k * bodyVolume A * bodyVolume (projectionBody C) ≤
      volume.real ((embedBody (t • A) + C : ConvexBody (Space k × Space q)) : Set (Space k × Space q)) := by
  first
  | let g : Space q → ℝ := (projection C).indicator (fun _ => t ^ k * bodyVolume A)
    have hg : Integrable g :=
      (integrableOn_const (projection_compact C).measure_ne_top).integrable_indicator
        (projection_compact C).measurableSet
    have hpoint (y : Space q) : g y ≤ volume.real (fiberSet (embedBody (t • A) + C) y) := by
      by_cases hy : y ∈ projection C
      · dsimp only [g]
        rw [Set.indicator_of_mem hy, embedded_sum_fiber_of_mem _ _ hy]
        obtain ⟨p, hp⟩ := (fiberBody C y).nonempty
        have hsub : translateBody p (t • A) ≤ t • A + fiberBody C y := by
          rintro x ⟨u, hu, v, hv, rfl⟩
          have hup : u = p := hu
          subst u
          exact ⟨v, hv, p, hp, add_comm _ _⟩
        have h := bodyVolume_mono hsub
        rwa [bodyVolume_translate, bodyVolume_smul _ ht] at h
      · dsimp only [g]
        rw [Set.indicator_of_notMem hy, embedded_sum_fiber_of_notMem _ _ hy, measureReal_empty]
    have hgint : (∫ y : Space q, g y) = t ^ k * bodyVolume A * bodyVolume (projectionBody C) := by
      dsimp only [g]
      rw [integral_indicator (projection_compact C).measurableSet, setIntegral_const]
      simp only [smul_eq_mul, bodyVolume, coe_projectionBody]
      ring
    rw [realVolume_eq_integral_fibers, ← hgint]
    exact integral_mono hg (integrable_fiber_realVolume _) hpoint

end Coordinates
end VolumePolynomials.FiberGrowth
