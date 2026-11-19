module

public import mixed_volume.general.automaton_words
public import mixed_volume.general.series_support

/-! The actual word-indexed state zonoids and the exact Minkowski-summand
criterion.  Every alphabet size, state size, real probability row, and finite
word is retained; the converse quantifies over arbitrary compact convex bodies. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace MixedVolume.AutomatonZonoids

open VolumePolynomials AutomatonWords IndexedSeries Set MeasureTheory
open scoped Pointwise BigOperators

variable {s m : ℕ}

def baseBody (hs : 0 < s) : ConvexBody Plane :=
  IndexedSeries.segmentSeriesBody generator (generator_summable hs)

theorem state_summable (A : Data s m) (hs : 0 < s) (j : Fin m) :
    Summable (fun w : Word s => ‖A.weight w j • generator w‖) := by
  apply IndexedSeries.summable_weighted_of_bounded generator (generator_summable hs)
    (fun w => A.weight w j) 2
  intro w
  rw [abs_of_pos (A.weight_pos w j)]
  exact A.weight_le_two w j

def stateBody (A : Data s m) (hs : 0 < s) (j : Fin m) : ConvexBody Plane :=
  IndexedSeries.segmentSeriesBody (fun w => A.weight w j • generator w) (state_summable A hs j)

theorem initial_summable (A : Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (hp : ProbabilityRow p) :
    Summable (fun w : Word s => ‖(1 + A.acceptance p w) • generator w‖) := by
  apply IndexedSeries.summable_weighted_of_bounded generator (generator_summable hs)
    (fun w => 1 + A.acceptance p w) 2
  intro w
  have h₀ := A.acceptance_nonneg p hp w
  have h₁ := A.acceptance_le_one p hp w
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 + A.acceptance p w)]
  linarith

def initialBody (A : Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (hp : ProbabilityRow p) : ConvexBody Plane :=
  IndexedSeries.segmentSeriesBody (fun w => (1 + A.acceptance p w) • generator w)
    (initial_summable A hs p hp)

/-- The acceptance probabilities are the literal segment weights of the
finite Minkowski combination of state bodies. -/
theorem initialBody_eq_combination (A : Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (hp : ProbabilityRow p) :
    initialBody A hs p hp = ∑ j, p j • stateBody A hs j := by
  have hsum : Summable (fun w : Word s => ‖(∑ j, p j * A.weight w j) • generator w‖) := by
    simpa only [A.probability_weight p hp] using initial_summable A hs p hp
  have h := SeriesSupport.weighted_combination generator (fun j w => A.weight w j) p
    (fun j w => (A.weight_pos w j).le) hp.1 (state_summable A hs) hsum
  simpa only [A.probability_weight p hp, initialBody, stateBody] using h.symm

/-- Equation (3), with the common stationary row and its actual state bodies. -/
theorem stationary_body (A : Data s m) (hs : 0 < s) :
    (∑ j, A.stationary j • stateBody A hs j) = (1 + A.gamma) • baseBody hs := by
  rw [← initialBody_eq_combination A hs A.stationary A.stationary_probability]
  apply ConvexBody.ext
  change IndexedSeries.segmentSeries (fun w => (1 + A.acceptance A.stationary w) • generator w) =
    (1 + A.gamma) • IndexedSeries.segmentSeries generator
  have hw : (fun w : Word s => (1 + A.acceptance A.stationary w) • generator w) =
      fun w => (1 + A.gamma) • generator w := by
    funext w
    rw [Data.acceptance, A.stationary_value]
  rw [hw]
  exact IndexedSeries.segmentSeries_smul generator (generator_summable hs) _

/-- At a word's own normal, precisely that word's positive generating segment
survives in the exposed face. -/
theorem weighted_faceHeight (hs : 0 < s) (c : Word s → ℝ)
    (hc : ∀ w, 0 < c w) (hcs : Summable fun w => ‖c w • generator w‖) (w : Word s) :
    ExposedLengths.faceHeight (tagNormal w)
      (IndexedSeries.segmentSeriesBody (fun v => c v • generator v) hcs) = c w * rho s ^ w.length := by
  have hz : tagNormal w (c w • generator w) = 0 := by
    rw [map_smul, tagNormal_generator]
    simp
  have hn (v : Word s) (hvw : v ≠ w) : tagNormal w (c v • generator v) ≠ 0 := by
    rw [map_smul, smul_eq_mul]
    exact mul_ne_zero (hc v).ne' (tagNormal_generator_ne hs w v hvw)
  obtain ⟨p, hp⟩ := IndexedSeries.exposed_face_eq_centered_segment (tagNormal w)
    (fun v => c v • generator v) hcs w hz hn
  have heq : ExposedLengths.exposedBody (tagNormal w)
      (IndexedSeries.segmentSeriesBody (fun v => c v • generator v) hcs) =
      translateBody p (PlanarCorner.segmentBody (c w • generator w)) := by
    apply ConvexBody.ext
    change (tagNormal w).toExposed (IndexedSeries.segmentSeries (fun v => c v • generator v)) = _
    rw [hp, coe_translateBody]
    change {x | ∃ t : Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      x = p + (t : ℝ) • (c w • generator w)} =
        p +ᵥ PlanarExtrusion.centeredSegment (c w • generator w)
    rw [← VolumePolynomials.centeredSegment_eq_planar]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(t : ℝ) • (c w • generator w), ⟨t, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  rw [ExposedLengths.faceHeight, heq, PlanarCorner.height_translate,
    ExposedLengths.height_segmentBody]
  simp only [generator, Prod.smul_snd, smul_eq_mul, mul_one]
  exact abs_of_pos (mul_pos (hc w) (pow_pos (rho_pos hs) _))

theorem base_faceHeight (hs : 0 < s) (w : Word s) :
    ExposedLengths.faceHeight (tagNormal w) (baseBody hs) = rho s ^ w.length := by
  have hsum : Summable (fun v : Word s => ‖(1 : ℝ) • generator v‖) := by
    simpa only [one_smul] using generator_summable hs
  simpa only [one_smul, one_mul, baseBody] using
    weighted_faceHeight hs (fun _ => 1) (fun _ => by norm_num) hsum w

theorem initial_faceHeight (A : Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (hp : ProbabilityRow p) (w : Word s) :
    ExposedLengths.faceHeight (tagNormal w) (initialBody A hs p hp) =
      (1 + A.acceptance p w) * rho s ^ w.length :=
  weighted_faceHeight hs _ (fun v => by linarith [A.acceptance_nonneg p hp v])
    (initial_summable A hs p hp) w

theorem deficit_summable (A : Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (hp : ProbabilityRow p) (theta : ℝ)
    (htheta : theta < 1) (hcut : A.UniversalCutpoint p theta) :
    Summable (fun w : Word s => ‖(theta - A.acceptance p w) • generator w‖) := by
  apply IndexedSeries.summable_weighted_of_bounded generator (generator_summable hs)
    (fun w => theta - A.acceptance p w) 1
  intro w
  have h₀ := A.acceptance_nonneg p hp w
  have h₁ := hcut w
  rw [abs_of_nonneg (sub_nonneg.mpr h₁)]
  linarith

def deficitBody (A : Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (hp : ProbabilityRow p) (theta : ℝ)
    (htheta : theta < 1) (hcut : A.UniversalCutpoint p theta) : ConvexBody Plane :=
  IndexedSeries.segmentSeriesBody (fun w => (theta - A.acceptance p w) • generator w)
    (deficit_summable A hs p hp theta htheta hcut)

theorem deficit_equation (A : Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (hp : ProbabilityRow p) (theta : ℝ)
    (htheta : theta < 1) (hcut : A.UniversalCutpoint p theta) :
    deficitBody A hs p hp theta htheta hcut + initialBody A hs p hp =
      (1 + theta) • baseBody hs := by
  have hsum : Summable (fun w : Word s =>
      ‖((theta - A.acceptance p w) + (1 + A.acceptance p w)) • generator w‖) := by
    have heq (w : Word s) :
        (theta - A.acceptance p w) + (1 + A.acceptance p w) = 1 + theta := by ring
    simpa only [heq, norm_smul] using (generator_summable hs).mul_left ‖1 + theta‖
  have hadd := IndexedSeries.segmentSeries_add generator
    (fun w => theta - A.acceptance p w) (fun w => 1 + A.acceptance p w)
    (fun w => sub_nonneg.mpr (hcut w))
    (fun w => by linarith [A.acceptance_nonneg p hp w])
    (deficit_summable A hs p hp theta htheta hcut) (initial_summable A hs p hp) hsum
  apply ConvexBody.ext
  change IndexedSeries.segmentSeries (fun w => (theta - A.acceptance p w) • generator w) +
    IndexedSeries.segmentSeries (fun w => (1 + A.acceptance p w) • generator w) =
      (1 + theta) • IndexedSeries.segmentSeries generator
  rw [← hadd]
  have h : (fun w : Word s =>
      ((theta - A.acceptance p w) + (1 + A.acceptance p w)) • generator w) =
      fun w => (1 + theta) • generator w := by
    funext w
    congr 1
    ring
  rw [h]
  exact IndexedSeries.segmentSeries_smul generator (generator_summable hs) _

/-- Paper Lemma 2.2, including its arbitrary compact-convex-body converse and
translation freedom.  No generating-measure or recurrence hypothesis is placed
on the competing summand. -/
theorem summand_iff_universalCutpoint (A : Data s m) (hs : 0 < s)
    (p : Fin m → ℝ) (hp : ProbabilityRow p) (theta : ℝ)
    (htheta₀ : 0 < theta) (htheta₁ : theta < 1) :
    (∃ (D : ConvexBody Plane) (q : Plane),
      D + (∑ j, p j • stateBody A hs j) = translateBody q ((1 + theta) • baseBody hs)) ↔
      A.UniversalCutpoint p theta := by
  constructor
  · rintro ⟨D, q, hD⟩ w
    rw [← initialBody_eq_combination A hs p hp] at hD
    have h := congrArg (ExposedLengths.faceHeight (tagNormal w)) hD
    rw [ExposedLengths.faceHeight_add, initial_faceHeight,
      ExposedLengths.faceHeight_translate, ExposedLengths.faceHeight_smul _ _ (by linarith),
      base_faceHeight] at h
    have hnonneg := ExposedLengths.faceHeight_nonneg (tagNormal w) D
    have hpos := pow_pos (rho_pos hs) w.length
    nlinarith
  · intro hcut
    refine ⟨deficitBody A hs p hp theta htheta₁ hcut, 0, ?_⟩
    rw [translateBody_zero, ← initialBody_eq_combination A hs p hp]
    exact deficit_equation A hs p hp theta htheta₁ hcut

end MixedVolume.AutomatonZonoids

end
