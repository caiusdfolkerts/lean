module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Extrusion from interval fibers and product Lebesgue measure

The statements here use actual compact convex subsets of `ℝ × E`. The first
factor carries Lebesgue measure and the second carries a locally finite Borel
measure on a second-countable real normed space. The plane is obtained by
`E = ℝ`. No mixed-volume functional or extrusion axiom is assumed. Empty and
lower-dimensional sets are permitted.
-/

noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal

namespace VolumePolynomials.PlanarExtrusion

variable {E : Type*} [NormedAddCommGroup E]

/-- A horizontal segment of length `t` when `0 ≤ t`. -/
def horizontal (t : ℝ) : Set (ℝ × E) := Icc 0 t ×ˢ {0}

/-- The horizontal fiber at height `y`. -/
def fiber (C : Set (ℝ × E)) (y : E) : Set ℝ := (fun x : ℝ => (x, y)) ⁻¹' C

/-- Projection to the vertical coordinate. -/
def projection (C : Set (ℝ × E)) : Set E := Prod.snd '' C

theorem horizontal_compact (t : ℝ) : IsCompact (horizontal (E := E) t) :=
  isCompact_Icc.prod (isCompact_singleton (x := (0 : E)))

theorem fiber_nonempty_iff (C : Set (ℝ × E)) (y : E) :
    (fiber C y).Nonempty ↔ y ∈ projection C := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(x, y), hx, rfl⟩
  · rintro ⟨⟨x, z⟩, hx, hz⟩
    change z = y at hz
    subst z
    exact ⟨x, hx⟩

theorem fiber_compact {C : Set (ℝ × E)} (hC : IsCompact C) (y : E) :
    IsCompact (fiber C y) := by
  have heq : fiber C y = Prod.fst '' (C ∩ {p : ℝ × E | p.2 = y}) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, y), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨hab, hb⟩, ha⟩
      change b = y at hb
      change a = x at ha
      subst a
      subst b
      exact hab
  rw [heq]
  exact (hC.inter_right (isClosed_eq continuous_snd continuous_const)).image continuous_fst

theorem fiber_convex [NormedSpace ℝ E] {C : Set (ℝ × E)} (hC : Convex ℝ C) (y : E) :
    Convex ℝ (fiber C y) := by
  intro x hx z hz a b ha hb hab
  have h := hC hx hz ha hb hab
  change (a * x + b * z, y) ∈ C
  convert h using 1
  ext
  · simp [smul_eq_mul]
  · simp [← add_smul, hab]

/-- Minkowski addition by a horizontal segment acts independently in each fiber. -/
theorem fiber_add_horizontal (C : Set (ℝ × E)) (t : ℝ) (y : E) :
    fiber (C + horizontal t) y = fiber C y + Icc 0 t := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, hab, ⟨u, v⟩, ⟨hu, hv⟩, heq⟩
    change v = 0 at hv
    subst v
    have hb : b = y := by simpa using congrArg Prod.snd heq
    subst b
    refine ⟨a, hab, u, hu, ?_⟩
    simpa using congrArg Prod.fst heq
  · rintro ⟨a, ha, u, hu, hau⟩
    refine ⟨(a, y), ha, (u, 0), ⟨hu, rfl⟩, ?_⟩
    ext <;> simp [hau]

/-- Exact one-dimensional length increment, including point intervals. -/
theorem length_add_interval {K : Set ℝ} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    volume (K + Icc 0 t) = volume K + ENNReal.ofReal t := by
  have hI : K = Icc (sInf K) (sSup K) :=
    eq_Icc_of_connected_compact ⟨hne, Real.convex_iff_isPreconnected.mp hc⟩ hK
  have hab : sInf K ≤ sSup K := csInf_le_csSup hne hK.bddBelow hK.bddAbove
  rw [hI, Icc_add_Icc hab ht, Real.volume_Icc, Real.volume_Icc]
  simp only [add_zero]
  rw [show sSup K + t - sInf K = (sSup K - sInf K) + t by ring,
    ENNReal.ofReal_add (sub_nonneg.mpr hab) ht]

/-- The measurable indicator records exactly which fibers are nonempty. -/
theorem fiber_measure_increment [NormedSpace ℝ E] {C : Set (ℝ × E)}
    (hC : IsCompact C) (hc : Convex ℝ C) {t : ℝ} (ht : 0 ≤ t) (y : E) :
    volume (fiber (C + horizontal t) y) = volume (fiber C y) +
      (projection C).indicator (fun _ => ENNReal.ofReal t) y := by
  classical
  rw [fiber_add_horizontal]
  by_cases hy : y ∈ projection C
  · rw [Set.indicator_of_mem hy]
    exact length_add_interval (fiber_compact hC y) (fiber_convex hc y)
      ((fiber_nonempty_iff C y).mpr hy) ht
  · have hempty : fiber C y = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ((fiber_nonempty_iff C y).mp ⟨x, hx⟩)
    simp [hempty, Set.indicator_of_notMem hy]

section Measure

variable [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
  [SecondCountableTopology E] [IsLocallyFiniteMeasure (volume : Measure E)]

/-- Product extrusion, proved with actual product measure and Tonelli's theorem. -/
theorem volume_add_horizontal {C : Set (ℝ × E)}
    (hC : IsCompact C) (hc : Convex ℝ C) {t : ℝ} (ht : 0 ≤ t) :
    volume (C + horizontal t) = volume C + ENNReal.ofReal t * volume (projection C) := by
  have hsum : IsCompact (C + horizontal t) := hC.add (horizontal_compact t)
  have hp : IsCompact (projection C) := hC.image continuous_snd
  calc
    volume (C + horizontal t) = ∫⁻ y, volume (fiber (C + horizontal t) y) :=
      Measure.prod_apply_symm hsum.measurableSet
    _ = ∫⁻ y, volume (fiber C y) +
        (projection C).indicator (fun _ => ENNReal.ofReal t) y :=
      lintegral_congr (fun y => fiber_measure_increment hC hc ht y)
    _ = (∫⁻ y, volume (fiber C y)) +
        ∫⁻ y, (projection C).indicator (fun _ => ENNReal.ofReal t) y :=
      lintegral_add_left (measurable_measure_prodMk_right hC.measurableSet) _
    _ = volume C + ENNReal.ofReal t * volume (projection C) := by
      rw [lintegral_indicator_const hp.measurableSet]
      congr 1
      exact (Measure.prod_apply_symm hC.measurableSet).symm

/-- The real-valued volume identity, with finiteness justified by compactness. -/
theorem realVolume_add_horizontal {C : Set (ℝ × E)}
    (hC : IsCompact C) (hc : Convex ℝ C) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (C + horizontal t) = volume.real C + t * volume.real (projection C) := by
  change (volume (C + horizontal t)).toReal =
    (volume C).toReal + t * (volume (projection C)).toReal
  have hp : IsCompact (projection C) := hC.image continuous_snd
  have h := congrArg ENNReal.toReal (volume_add_horizontal hC hc ht)
  rw [ENNReal.toReal_add hC.measure_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp.measure_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht] at h
  exact h

end Measure

/-- The planar specialization of the product extrusion theorem. -/
theorem area_add_horizontal {C : Set (ℝ × ℝ)}
    (hC : IsCompact C) (hc : Convex ℝ C) {t : ℝ} (ht : 0 ≤ t) :
    volume.real (C + horizontal t) = volume.real C + t * volume.real (projection C) :=
  realVolume_add_horizontal hC hc ht

end VolumePolynomials.PlanarExtrusion
