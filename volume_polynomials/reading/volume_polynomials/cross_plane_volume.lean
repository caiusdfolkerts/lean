module

public import VolumePolynomials.PlanarExtrusion
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Tactic.FunProp

@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Volumes of sums in two transverse planes

The two planar sets share the first coordinate axis. A fiber of their sum
is the sum of the two corresponding compact intervals. Tonelli therefore
expresses the three-dimensional volume as area times transverse width in
each of the two directions. All measures here are actual Lebesgue measures.
-/

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace VolumePolynomials.CrossPlaneVolume

open PlanarExtrusion

abbrev Plane := ℝ × ℝ
abbrev ThreeSpace := ℝ × (ℝ × ℝ)

def firstPlane : Plane →L[ℝ] ThreeSpace where
  toFun p := (p.1, (p.2, 0))
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  cont := by fun_prop

def secondPlane : Plane →L[ℝ] ThreeSpace where
  toFun p := (p.1, (0, p.2))
  map_add' p q := by ext <;> simp
  map_smul' r p := by ext <;> simp
  cont := by fun_prop

def planeSum (A B : Set Plane) : Set ThreeSpace := firstPlane '' A + secondPlane '' B

theorem planeSum_compact {A B : Set Plane} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact (planeSum A B) :=
  (hA.image firstPlane.continuous).add (hB.image secondPlane.continuous)

theorem fiber_planeSum (A B : Set Plane) (y z : ℝ) :
    fiber (planeSum A B) (y, z) = fiber A y + fiber B z := by
  first
  | ext x
    constructor
    · rintro ⟨a, ⟨⟨u, v⟩, huv, rfl⟩, b, ⟨⟨r, s⟩, hrs, rfl⟩, heq⟩
      have hv : v = y := by
        first
        | simpa [firstPlane, secondPlane] using
            (congrArg (fun p : ThreeSpace => p.2.1) heq)
      have hs : s = z := by
        first
        | simpa [firstPlane, secondPlane] using
            (congrArg (fun p : ThreeSpace => p.2.2) heq)
      subst v
      subst s
      exact ⟨u, huv, r, hrs, by
        simpa [firstPlane, secondPlane] using congrArg Prod.fst heq⟩
    · rintro ⟨u, hu, v, hv, huv⟩
      refine ⟨firstPlane (u, y), ⟨(u, y), hu, rfl⟩,
        secondPlane (v, z), ⟨(v, z), hv, rfl⟩, ?_⟩
      ext <;> simp [firstPlane, secondPlane, huv]

theorem length_add_nonempty_intervals {I J : Set ℝ}
    (hI : IsCompact I) (hJ : IsCompact J) (hcI : Convex ℝ I) (hcJ : Convex ℝ J)
    (hneI : I.Nonempty) (hneJ : J.Nonempty) :
    volume (I + J) = volume I + volume J := by
  first
  | have hreprI : I = Icc (sInf I) (sSup I) :=
      eq_Icc_of_connected_compact ⟨hneI, Real.convex_iff_isPreconnected.mp hcI⟩ hI
    have hreprJ : J = Icc (sInf J) (sSup J) :=
      eq_Icc_of_connected_compact ⟨hneJ, Real.convex_iff_isPreconnected.mp hcJ⟩ hJ
    have hi : sInf I ≤ sSup I := csInf_le_csSup hneI hI.bddBelow hI.bddAbove
    have hj : sInf J ≤ sSup J := csInf_le_csSup hneJ hJ.bddBelow hJ.bddAbove
    rw [hreprI, hreprJ, Icc_add_Icc hi hj, Real.volume_Icc, Real.volume_Icc,
      Real.volume_Icc]
    rw [show sSup I + sSup J - (sInf I + sInf J) =
      (sSup I - sInf I) + (sSup J - sInf J) by ring]
    exact ENNReal.ofReal_add (sub_nonneg.mpr hi) (sub_nonneg.mpr hj)

theorem fiber_measure_planeSum {A B : Set Plane}
    (hA : IsCompact A) (hB : IsCompact B) (hcA : Convex ℝ A) (hcB : Convex ℝ B)
    (y z : ℝ) :
    volume (fiber (planeSum A B) (y, z)) =
      volume (fiber A y) * (projection B).indicator (fun _ => (1 : ℝ≥0∞)) z +
      (projection A).indicator (fun _ => (1 : ℝ≥0∞)) y * volume (fiber B z) := by
  first
  | classical
    rw [fiber_planeSum]
    by_cases hy : y ∈ projection A
    · by_cases hz : z ∈ projection B
      · simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hz, mul_one, one_mul]
        exact length_add_nonempty_intervals (fiber_compact hA y) (fiber_compact hB z)
          (fiber_convex hcA y) (fiber_convex hcB z)
          ((fiber_nonempty_iff A y).mpr hy) ((fiber_nonempty_iff B z).mpr hz)
      · have hempty : fiber B z = ∅ := Set.not_nonempty_iff_eq_empty.mp
          (fun h => hz ((fiber_nonempty_iff B z).mp h))
        simp [hempty, Set.indicator_of_notMem hz]
    · have hempty : fiber A y = ∅ := Set.not_nonempty_iff_eq_empty.mp
        (fun h => hy ((fiber_nonempty_iff A y).mp h))
      simp [hempty, Set.indicator_of_notMem hy]

/-- The exact product-volume identity, including empty and degenerate sets. -/
theorem volume_planeSum {A B : Set Plane}
    (hA : IsCompact A) (hB : IsCompact B) (hcA : Convex ℝ A) (hcB : Convex ℝ B) :
    volume (planeSum A B) =
      volume A * volume (projection B) + volume (projection A) * volume B := by
  first
  | have ha : Measurable (fun y => volume (fiber A y)) :=
      measurable_measure_prodMk_right hA.measurableSet
    have hb : Measurable (fun z => volume (fiber B z)) :=
      measurable_measure_prodMk_right hB.measurableSet
    have hpA : IsCompact (projection A) := hA.image continuous_snd
    have hpB : IsCompact (projection B) := hB.image continuous_snd
    have hia : Measurable ((projection A).indicator (fun _ => (1 : ℝ≥0∞))) :=
      measurable_const.indicator hpA.measurableSet
    have hib : Measurable ((projection B).indicator (fun _ => (1 : ℝ≥0∞))) :=
      measurable_const.indicator hpB.measurableSet
    have hvolA : (∫⁻ y : ℝ, volume (fiber A y)) = volume A :=
      (Measure.prod_apply_symm hA.measurableSet).symm
    have hvolB : (∫⁻ z : ℝ, volume (fiber B z)) = volume B :=
      (Measure.prod_apply_symm hB.measurableSet).symm
    calc
      volume (planeSum A B) = ∫⁻ p : Plane, volume (fiber (planeSum A B) p) :=
        Measure.prod_apply_symm (planeSum_compact hA hB).measurableSet
      _ = ∫⁻ p : Plane,
          volume (fiber A p.1) * (projection B).indicator (fun _ => (1 : ℝ≥0∞)) p.2 +
          (projection A).indicator (fun _ => (1 : ℝ≥0∞)) p.1 * volume (fiber B p.2) :=
        lintegral_congr (fun p => fiber_measure_planeSum hA hB hcA hcB p.1 p.2)
      _ = (∫⁻ p : Plane,
          volume (fiber A p.1) * (projection B).indicator (fun _ => (1 : ℝ≥0∞)) p.2) +
          ∫⁻ p : Plane,
          (projection A).indicator (fun _ => (1 : ℝ≥0∞)) p.1 * volume (fiber B p.2) :=
        lintegral_add_left ((ha.comp measurable_fst).mul (hib.comp measurable_snd)) _
      _ = (∫⁻ y, volume (fiber A y)) *
          (∫⁻ z, (projection B).indicator (fun _ => (1 : ℝ≥0∞)) z) +
          (∫⁻ y, (projection A).indicator (fun _ => (1 : ℝ≥0∞)) y) *
          ∫⁻ z, volume (fiber B z) := by
        rw [Measure.volume_eq_prod, lintegral_prod_mul ha.aemeasurable hib.aemeasurable,
          lintegral_prod_mul hia.aemeasurable hb.aemeasurable]
      _ = volume A * volume (projection B) + volume (projection A) * volume B := by
        rw [hvolA, hvolB,
          lintegral_indicator_const hpA.measurableSet,
          lintegral_indicator_const hpB.measurableSet, one_mul, one_mul]

theorem realVolume_planeSum {A B : Set Plane}
    (hA : IsCompact A) (hB : IsCompact B) (hcA : Convex ℝ A) (hcB : Convex ℝ B) :
    volume.real (planeSum A B) =
      volume.real A * volume.real (projection B) + volume.real (projection A) * volume.real B := by
  first
  | have hpA : IsCompact (projection A) := hA.image continuous_snd
    have hpB : IsCompact (projection B) := hB.image continuous_snd
    have h := congrArg ENNReal.toReal (volume_planeSum hA hB hcA hcB)
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top hA.measure_ne_top hpB.measure_ne_top)
        (ENNReal.mul_ne_top hpA.measure_ne_top hB.measure_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_mul] at h
    exact h

theorem projection_smul (r : ℝ) (A : Set Plane) :
    projection (r • A) = r • projection A := by
  first
  | ext y
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, hpy⟩
      exact ⟨q.2, ⟨q, hq, rfl⟩, hpy⟩
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨r • p, ⟨p, hp, rfl⟩, rfl⟩

theorem realVolume_smul_plane (A : Set Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (r • A) = r ^ 2 * volume.real A := by
  first
  | haveI : (volume : Measure Plane).IsAddHaarMeasure := by
      change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
      infer_instance
    simp only [measureReal_def,
      Measure.addHaar_smul_of_nonneg (volume : Measure Plane) hr A,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr _)]
    simp

theorem realVolume_smul_line (A : Set ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (r • A) = r * volume.real A := by
  first
  | simp only [measureReal_def, Measure.addHaar_smul_of_nonneg volume hr A,
      Module.finrank_self, pow_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr]

/-- Repeated coefficients for two transverse planar summands, derived from
the volume of every nonnegative weighted sum. -/
theorem realVolume_planeSum_smul {A B : Set Plane}
    (hA : IsCompact A) (hB : IsCompact B) (hcA : Convex ℝ A) (hcB : Convex ℝ B)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    volume.real (planeSum (s • A) (t • B)) =
      (volume.real A * volume.real (projection B)) * s ^ 2 * t +
      (volume.real (projection A) * volume.real B) * s * t ^ 2 := by
  first
  | rw [realVolume_planeSum (hA.smul s) (hB.smul t) (hcA.smul s) (hcB.smul t),
      projection_smul, projection_smul,
      realVolume_smul_plane A hs, realVolume_smul_plane B ht,
      realVolume_smul_line (projection A) hs, realVolume_smul_line (projection B) ht]
    ring

/-- The cyclic-product cancellation used when all three planes share a line.
The two angular factors occur once on each side. This algebraic lemma is
kept separate from the geometric task of deriving its six coefficients. -/
theorem cyclic_product
    (A₀ A₁ A₂ w₀ w₁ w₂ a b : ℝ) :
    (A₀ * w₁) * (|a| * A₁ * w₂) * (|b| * w₀ * A₂) =
      (|b| * A₀ * w₂) * (w₀ * A₁) * (|a| * w₁ * A₂) := by
  first
  | ring

end VolumePolynomials.CrossPlaneVolume
