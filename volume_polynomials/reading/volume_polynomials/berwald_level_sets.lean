module

public import VolumePolynomials.BerwaldComparison
public import Mathlib.Analysis.Convex.Measure
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Actual superlevel sets of concave functions

Brunn--Minkowski gives concavity of the normalized dimension root of their
volumes. Superlevel sets need not be closed: convexity supplies their null
measurability, and compact containment supplies finiteness.
-/

open Set MeasureTheory Module
open scoped Pointwise

namespace VolumePolynomials.BerwaldLevelSets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def superlevel (Z : Set E) (f : E → ℝ) (t : ℝ) : Set E := {x | x ∈ Z ∧ t ≤ f x}

theorem superlevel_subset (Z : Set E) (f : E → ℝ) (t : ℝ) : superlevel Z f t ⊆ Z :=
  fun _ h => h.1

theorem superlevel_convex {Z : Set E} {f : E → ℝ} (hf : ConcaveOn ℝ Z f) (t : ℝ) :
    Convex ℝ (superlevel Z f t) := by
  first
  | intro x hx y hy a b ha hb hab
    refine ⟨hf.1 hx.1 hy.1 ha hb hab, ?_⟩
    have h := hf.2 hx.1 hy.1 ha hb hab
    change a * f x + b * f y ≤ f (a • x + b • y) at h
    have hleft := mul_le_mul_of_nonneg_left hx.2 ha
    have hright := mul_le_mul_of_nonneg_left hy.2 hb
    have ht : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
    linarith

theorem superlevel_minkowski_subset {Z : Set E} {f : E → ℝ} (hf : ConcaveOn ℝ Z f)
    (s t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • superlevel Z f s + b • superlevel Z f t ⊆ superlevel Z f (a * s + b * t) := by
  first
  | rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨hf.1 hx.1 hy.1 ha hb hab, ?_⟩
    exact (add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
      (mul_le_mul_of_nonneg_left hy.2 hb)).trans (hf.2 hx.1 hy.1 ha hb hab)

theorem superlevel_zero {Z : Set E} {f : E → ℝ} (hf : ∀ x ∈ Z, 0 ≤ f x) :
    superlevel Z f 0 = Z := by
  first
  | ext x
    exact ⟨fun h => h.1, fun hx => ⟨hx, hf x hx⟩⟩

theorem superlevel_nonempty_of_lt_sup {Z : Set E} {f : E → ℝ}
    (hZ : Z.Nonempty) {t : ℝ} (ht : t < sSup (f '' Z)) :
    (superlevel Z f t).Nonempty := by
  first
  | obtain ⟨v, ⟨x, hx, rfl⟩, htx⟩ := exists_lt_of_lt_csSup (hZ.image f) ht
    exact ⟨x, hx, htx.le⟩

def rootTail (Z : Set E) (f : E → ℝ) (t : ℝ) : ℝ :=
  volume.real (superlevel Z f t) ^ ((finrank ℝ E : ℝ)⁻¹) /
    volume.real Z ^ ((finrank ℝ E : ℝ)⁻¹)

theorem rootTail_nonnegative (Z : Set E) (f : E → ℝ) (t : ℝ) :
    0 ≤ rootTail Z f t := by
  first
  | exact div_nonneg (Real.rpow_nonneg (measureReal_nonneg) _)
      (Real.rpow_nonneg measureReal_nonneg _)

theorem rootTail_zero {Z : Set E} {f : E → ℝ}
    (hvol : 0 < volume.real Z) (hf : ∀ x ∈ Z, 0 ≤ f x) : rootTail Z f 0 = 1 := by
  first
  | unfold rootTail
    rw [superlevel_zero hf, div_self (Real.rpow_pos_of_pos hvol _).ne']

theorem rootTail_pow {Z : Set E} {f : E → ℝ} (hdim : finrank ℝ E ≠ 0) (t : ℝ) :
    rootTail Z f t ^ finrank ℝ E = volume.real (superlevel Z f t) / volume.real Z := by
  first
  | unfold rootTail
    rw [div_pow, Real.rpow_inv_natCast_pow measureReal_nonneg hdim,
      Real.rpow_inv_natCast_pow measureReal_nonneg hdim]

/-- The geometric concavity input to the scalar Berwald comparison. -/
theorem rootTail_concave {Z : Set E} {f : E → ℝ}
    (hdim : finrank ℝ E ≠ 0) (hZ : IsCompact Z) (hne : Z.Nonempty)
    (hvol : 0 < volume.real Z) (hf : ConcaveOn ℝ Z f) :
    ConcaveOn ℝ (Iio (sSup (f '' Z))) (rootTail Z f) := by
  first
  | refine ⟨convex_Iio _, ?_⟩
    intro s hs t ht a b ha hb hab
    have hsne := superlevel_nonempty_of_lt_sup hne hs
    have htne := superlevel_nonempty_of_lt_sup hne ht
    have hsubset := superlevel_minkowski_subset hf s t ha hb hab
    have hbound : volume (a • superlevel Z f s + b • superlevel Z f t) ≠ ⊤ :=
      ne_top_of_le_ne_top hZ.measure_ne_top
        (measure_mono (hsubset.trans (superlevel_subset Z f _)))
    have hbm := TauCeti.mul_volume_real_rpow_add_mul_volume_real_rpow_le hdim
      hsne ((superlevel_convex hf s).nullMeasurableSet volume)
      htne ((superlevel_convex hf t).nullMeasurableSet volume) ha hb hbound
    have hmono := Real.rpow_le_rpow (measureReal_nonneg (μ := volume)
      (s := a • superlevel Z f s + b • superlevel Z f t))
      (measureReal_mono hsubset
        (ne_top_of_le_ne_top hZ.measure_ne_top (measure_mono (superlevel_subset Z f _))))
      (inv_nonneg.mpr (Nat.cast_nonneg (finrank ℝ E)))
    have hden : 0 < volume.real Z ^ ((finrank ℝ E : ℝ)⁻¹) :=
      Real.rpow_pos_of_pos hvol _
    have h := div_le_div_of_nonneg_right (hbm.trans hmono) hden.le
    simpa only [rootTail, smul_eq_mul, add_div, mul_div_assoc] using h

theorem rootTail_concave_nonnegative {Z : Set E} {f : E → ℝ}
    (hdim : finrank ℝ E ≠ 0) (hZ : IsCompact Z) (hne : Z.Nonempty)
    (hvol : 0 < volume.real Z) (hf : ConcaveOn ℝ Z f) :
    ConcaveOn ℝ (Ico 0 (sSup (f '' Z))) (rootTail Z f) :=
  (rootTail_concave hdim hZ hne hvol hf).subset (fun _ h => h.2) (convex_Ico _ _)

end VolumePolynomials.BerwaldLevelSets
