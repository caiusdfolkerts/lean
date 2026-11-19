module

public import VolumePolynomials.PyramidVolume
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false

/-! # Fubini formula for a fixed cone clipped by a moving compact set

The radial integration coordinates are over a fixed old facet. Consequently
no continuity of a moving radial function is needed for first variation.
-/

noncomputable section
open Set MeasureTheory Module
open scoped ENNReal Pointwise

namespace VolumePolynomials.ClippedConeVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialMap (p : ℝ × E) : ℝ × E := (p.1, p.1 • p.2)

theorem continuous_radialMap : Continuous (radialMap (E := E)) := by
  first
  | unfold radialMap
    fun_prop

def clippedCone (R : ℝ) (A : Set E) (K : Set (ℝ × E)) : Set (ℝ × E) :=
  (radialMap '' (Icc (0 : ℝ) R ×ˢ A)) ∩ K

theorem clippedCone_compact {R : ℝ} {A : Set E} (hA : IsCompact A)
    {K : Set (ℝ × E)} (hK : IsClosed K) : IsCompact (clippedCone R A K) :=
  ((isCompact_Icc.prod hA).image continuous_radialMap).inter_right hK

theorem clippedCone_fiber (R : ℝ) (A : Set E) (K : Set (ℝ × E)) (r : ℝ) :
    Prod.mk r ⁻¹' clippedCone R A K =
      if r ∈ Icc (0 : ℝ) R then
        r • {x : E | x ∈ A ∧ radialMap (r, x) ∈ K} else ∅ := by
  first
  | classical
    by_cases hr : r ∈ Icc (0 : ℝ) R
    · rw [if_pos hr]
      ext y
      constructor
      · rintro ⟨⟨⟨s, x⟩, ⟨hs, hx⟩, heq⟩, hyK⟩
        have hsr : s = r := congrArg Prod.fst heq
        subst s
        have hxy : r • x = y := congrArg Prod.snd heq
        refine ⟨x, ⟨hx, ?_⟩, hxy⟩
        simpa only [radialMap, hxy] using hyK
      · rintro ⟨x, ⟨hxA, hxK⟩, rfl⟩
        exact ⟨⟨(r, x), ⟨hr, hxA⟩, rfl⟩, hxK⟩
    · rw [if_neg hr]
      apply eq_empty_iff_forall_notMem.mpr
      rintro y ⟨⟨⟨s, x⟩, ⟨hs, hx⟩, heq⟩, hyK⟩
      have hsr : s = r := congrArg Prod.fst heq
      exact hr (hsr ▸ hs)

def radialWeight (k : ℕ) (K : Set (ℝ × E)) : ℝ × E → ℝ≥0∞ :=
  (radialMap ⁻¹' K).indicator (fun p => ENNReal.ofReal (p.1 ^ k))

section Measure

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem measurable_radialWeight (k : ℕ) {K : Set (ℝ × E)}
    (hK : MeasurableSet K) : Measurable (radialWeight k K) := by
  first
  | apply Measurable.indicator (by fun_prop)
    exact hK.preimage continuous_radialMap.measurable

theorem clippedCone_fiber_measure (R : ℝ) (A : Set E) (K : Set (ℝ × E)) (r : ℝ) :
    volume (Prod.mk r ⁻¹' clippedCone R A K) =
      (Icc (0 : ℝ) R).indicator
        (fun s => ENNReal.ofReal (s ^ finrank ℝ E) *
          volume {x : E | x ∈ A ∧ radialMap (s, x) ∈ K}) r := by
  first
  | classical
    rw [clippedCone_fiber]
    by_cases hr : r ∈ Icc (0 : ℝ) R
    · rw [if_pos hr, Set.indicator_of_mem hr,
        Measure.addHaar_smul_of_nonneg volume hr.1]
    · simp only [if_neg hr, measure_empty, Set.indicator_of_notMem hr]

theorem lintegral_radialWeight (k : ℕ) (A : Set E) {K : Set (ℝ × E)}
    (hK : MeasurableSet K) (r : ℝ) :
    (∫⁻ x in A, radialWeight k K (r, x)) =
      ENNReal.ofReal (r ^ k) * volume {x : E | x ∈ A ∧ radialMap (r, x) ∈ K} := by
  first
  | have hm : MeasurableSet {x : E | radialMap (r, x) ∈ K} :=
      hK.preimage (continuous_radialMap.comp (continuous_const.prodMk continuous_id)).measurable
    have heq : (fun x : E => radialWeight k K (r, x)) =
        {x : E | radialMap (r, x) ∈ K}.indicator (fun _ => ENNReal.ofReal (r ^ k)) := rfl
    rw [heq, lintegral_indicator_const hm, Measure.restrict_apply hm]
    congr 2
    ext x
    simp only [mem_inter_iff, mem_setOf_eq, and_comm]

/-- The genuine volume of the clipped cone as an integral over the fixed base
and a fixed interval. The moving set occurs only in a measurable indicator. -/
theorem volume_clippedCone {R : ℝ} {A : Set E} (hA : IsCompact A)
    {K : Set (ℝ × E)} (hK : IsClosed K) :
    volume (clippedCone R A K) =
      ∫⁻ x in A, ∫⁻ r in Icc (0 : ℝ) R, radialWeight (finrank ℝ E) K (r, x) := by
  first
  | calc
      volume (clippedCone R A K) =
          ∫⁻ r : ℝ, volume (Prod.mk r ⁻¹' clippedCone R A K) :=
        Measure.prod_apply (clippedCone_compact hA hK).measurableSet
      _ = ∫⁻ r : ℝ, (Icc (0 : ℝ) R).indicator
          (fun s => ENNReal.ofReal (s ^ finrank ℝ E) *
            volume {x : E | x ∈ A ∧ radialMap (s, x) ∈ K}) r :=
        lintegral_congr (clippedCone_fiber_measure R A K)
      _ = ∫⁻ r in Icc (0 : ℝ) R, ENNReal.ofReal (r ^ finrank ℝ E) *
          volume {x : E | x ∈ A ∧ radialMap (r, x) ∈ K} :=
        lintegral_indicator measurableSet_Icc _
      _ = ∫⁻ r in Icc (0 : ℝ) R, ∫⁻ x in A, radialWeight (finrank ℝ E) K (r, x) := by
        first
        | apply lintegral_congr
          intro r
          exact (lintegral_radialWeight _ A hK.measurableSet r).symm
      _ = _ := lintegral_lintegral_swap (measurable_radialWeight _ hK.measurableSet).aemeasurable

end Measure
end VolumePolynomials.ClippedConeVolume
