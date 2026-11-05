module

public import VolumePolynomials.PowerLayerCake

public import VolumePolynomials.BerwaldLevelSets
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Measurability and the actual moment identities

A bounded concave function is allowed to be discontinuous on the boundary
of its convex domain. Its interior continuity and the null frontier give
the required almost-everywhere measurability. The moment identities below
are actual Lebesgue integrals, obtained from Mathlib's layer-cake theorem.
-/

open Set MeasureTheory Filter

namespace VolumePolynomials.BerwaldMoments



section ConvexDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open BerwaldLevelSets

theorem convex_ae_eq_interior {Z : Set E} (hZ : Convex ℝ Z) :
    Z =ᵐ[volume] interior Z := by
  first
  | filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hZ.addHaar_frontier volume)] with x hx
    apply propext
    exact ⟨fun hxZ => (mem_interior_iff_notMem_frontier hxZ).mpr hx,
      fun hxZ => interior_subset hxZ⟩

theorem concave_aestronglyMeasurable {Z : Set E} {f : E → ℝ}
    (hf : ConcaveOn ℝ Z f) : AEStronglyMeasurable f (volume.restrict Z) := by
  first
  | rw [Measure.restrict_congr_set (convex_ae_eq_interior hf.1)]
    exact hf.continuousOn_interior.aestronglyMeasurable isOpen_interior.measurableSet

theorem bounded_concave_integrable_signed {Z : Set E} {f : E → ℝ}
    (hZ : IsCompact Z) (hf : ConcaveOn ℝ Z f) {C : ℝ}
    (hb : ∀ x ∈ Z, ‖f x‖ ≤ C) : IntegrableOn f Z := by
  first
  | letI : IsFiniteMeasure (volume.restrict Z) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hZ.measure_lt_top⟩
    apply (integrable_const C).mono' (concave_aestronglyMeasurable hf)
    filter_upwards [ae_restrict_mem hZ.measurableSet] with x hx
    exact hb x hx

/-- Boundary values require no continuity hypothesis. -/
theorem bounded_concave_integrable {Z : Set E} {f : E → ℝ}
    (hZ : IsCompact Z) (hf : ConcaveOn ℝ Z f) {M : ℝ}
    (hn : ∀ x ∈ Z, 0 ≤ f x) (hb : ∀ x ∈ Z, f x ≤ M) :
    IntegrableOn f Z := by
  first
  | letI : IsFiniteMeasure (volume.restrict Z) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hZ.measure_lt_top⟩
    apply Integrable.of_mem_Icc 0 M (concave_aestronglyMeasurable hf).aemeasurable
    filter_upwards [ae_restrict_mem hZ.measurableSet] with x hx
    exact ⟨hn x hx, hb x hx⟩

theorem concave_pow_integrable {Z : Set E} {f : E → ℝ}
    (hZ : IsCompact Z) (hf : ConcaveOn ℝ Z f) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ x ∈ Z, 0 ≤ f x) (hb : ∀ x ∈ Z, f x ≤ M) (p : ℕ) :
    IntegrableOn (fun x => f x ^ p) Z := by
  first
  | letI : IsFiniteMeasure (volume.restrict Z) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hZ.measure_lt_top⟩
    apply Integrable.of_mem_Icc 0 (M ^ p)
      ((concave_aestronglyMeasurable hf).aemeasurable.pow_const p)
    filter_upwards [ae_restrict_mem hZ.measurableSet] with x hx
    exact ⟨pow_nonneg (hn x hx) p, pow_le_pow_left₀ (hn x hx) (hb x hx) p⟩

def tail (Z : Set E) (f : E → ℝ) (t : ℝ) : ℝ :=
  volume.real (superlevel Z f t) / volume.real Z

theorem tail_nonnegative (Z : Set E) (f : E → ℝ) (t : ℝ) : 0 ≤ tail Z f t :=
  div_nonneg measureReal_nonneg measureReal_nonneg

theorem tail_antitone {Z : Set E} (hZ : IsCompact Z) (f : E → ℝ) :
    Antitone (tail Z f) := by
  first
  | intro s t hst
    apply div_le_div_of_nonneg_right _ measureReal_nonneg
    exact measureReal_mono (fun _ hx => ⟨hx.1, hst.trans hx.2⟩)
      (ne_top_of_le_ne_top hZ.measure_ne_top
        (measure_mono (superlevel_subset Z f s)))

theorem tail_le_one {Z : Set E} (hZ : IsCompact Z) (f : E → ℝ) (t : ℝ) :
    tail Z f t ≤ 1 := by
  first
  | by_cases hz : volume.real Z = 0
    · simp [tail, hz]
    · apply (div_le_one (lt_of_le_of_ne measureReal_nonneg (Ne.symm hz))).mpr
      exact measureReal_mono (superlevel_subset Z f t) hZ.measure_ne_top

theorem tail_zero_of_sup_lt {Z : Set E} {f : E → ℝ}
    (hb : BddAbove (f '' Z)) {t : ℝ} (ht : sSup (f '' Z) < t) : tail Z f t = 0 := by
  first
  | have he : superlevel Z f t = ∅ := by
      first
      | apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact not_le_of_gt ht (hx.2.trans (le_csSup hb ⟨x, hx.1, rfl⟩))
    simp only [tail, he, measureReal_empty, zero_div]

def clippedTail (Z : Set E) (f : E → ℝ) (t : ℝ) : ℝ :=
  if t < sSup (f '' Z) then tail Z f t else 0

theorem clippedTail_ae_eq_tail {Z : Set E} {f : E → ℝ}
    (hb : BddAbove (f '' Z)) : clippedTail Z f =ᵐ[volume] tail Z f := by
  first
  | filter_upwards [volume.ae_ne (sSup (f '' Z))] with t ht
    by_cases hlt : t < sSup (f '' Z)
    · simp only [clippedTail, if_pos hlt]
    · rw [clippedTail, if_neg hlt]
      exact (tail_zero_of_sup_lt hb (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm ht))).symm

theorem clippedTail_nonnegative (Z : Set E) (f : E → ℝ) (t : ℝ) :
    0 ≤ clippedTail Z f t := by
  first
  | unfold clippedTail
    split_ifs
    · exact tail_nonnegative Z f t
    · exact le_rfl

theorem clippedTail_antitone {Z : Set E} (hZ : IsCompact Z) (f : E → ℝ) :
    Antitone (clippedTail Z f) := by
  first
  | intro s t hst
    by_cases ht : t < sSup (f '' Z)
    · simp only [clippedTail, if_pos ht, if_pos (hst.trans_lt ht)]
      exact tail_antitone hZ f hst
    · rw [clippedTail, if_neg ht]
      exact clippedTail_nonnegative Z f s

theorem clippedTail_integrableOn {Z : Set E} (hZ : IsCompact Z) (f : E → ℝ)
    (a b : ℝ) : IntegrableOn (clippedTail Z f) (Icc a b) :=
  ((clippedTail_antitone hZ f).antitoneOn (Icc a b)).integrableOn_isCompact isCompact_Icc

theorem clippedTail_first_moment_integrableOn {Z : Set E} (hZ : IsCompact Z)
    (f : E → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t => t * clippedTail Z f t) (Icc 0 a) := by
  first
  | apply (clippedTail_integrableOn hZ f 0 a).bdd_mul (c := a)
      continuous_id.measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2

theorem moment_identity {Z : Set E} {f : E → ℝ}
    (hZ : IsCompact Z) (hf : ConcaveOn ℝ Z f) (hn : ∀ x ∈ Z, 0 ≤ f x)
    (hb : BddAbove (f '' Z)) (p : ℕ) :
    (∫ x in Z, f x ^ (p + 1)) / volume.real Z =
      (p + 1 : ℝ) * ∫ t in Ioi 0, t ^ p * clippedTail Z f t := by
  first
  | letI : IsFiniteMeasure (volume.restrict Z) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hZ.measure_lt_top⟩
    have hn' : 0 ≤ᵐ[volume.restrict Z] f := by
      first
      | filter_upwards [ae_restrict_mem hZ.measurableSet] with x hx
        exact hn x hx
    have ht (t : ℝ) : (volume.restrict Z).real {x | t ≤ f x} =
        volume.real (superlevel Z f t) := by
      first
      | unfold Measure.real
        rw [Measure.restrict_apply' hZ.measurableSet]
        apply congrArg (fun S : Set E => (volume S).toReal)
        ext x
        simp only [mem_inter_iff, mem_setOf_eq, superlevel, and_comm]
    rw [power_layer_cake (concave_aestronglyMeasurable hf).aemeasurable hn' p]
    simp only [ht]
    rw [mul_div_assoc, ← integral_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (clippedTail_ae_eq_tail hb)] with t ht'
    rw [ht', tail, mul_div_assoc]

/-- A finite upper integration limit is justified by the actual support of
the survival function, including a possible positive plateau at its maximum. -/
theorem moment_identity_bounded {Z : Set E} {f : E → ℝ}
    (hZ : IsCompact Z) (hf : ConcaveOn ℝ Z f) (hn : ∀ x ∈ Z, 0 ≤ f x)
    (hb : BddAbove (f '' Z)) {a : ℝ} (ha : sSup (f '' Z) ≤ a) (p : ℕ) :
    (∫ x in Z, f x ^ (p + 1)) / volume.real Z =
      (p + 1 : ℝ) * ∫ t in Icc 0 a, t ^ p * clippedTail Z f t := by
  first
  | rw [moment_identity hZ hf hn hb p, integral_Icc_eq_integral_Ioc]
    congr 1
    apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      nullMeasurableSet_Ioi Ioc_subset_Ioi_self
    exact Eventually.of_forall fun t ht => by
      have hta : a < t := by
        first
        | have ht0 := ht.1
          simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and] at ht
          exact lt_of_not_ge (ht.2 ht0)
      simp only [clippedTail, if_neg (not_lt.mpr (ha.trans hta.le)), mul_zero]

end ConvexDomain

end VolumePolynomials.BerwaldMoments
