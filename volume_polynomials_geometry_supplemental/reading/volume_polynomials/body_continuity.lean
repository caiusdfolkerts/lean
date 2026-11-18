module
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Lebesgue-volume continuity for actual convex bodies

The proof uses separating linear functionals to show that Hausdorff convergence
preserves membership of every interior point eventually. Exterior points are
handled by positive distance. The exceptional frontier has Haar measure zero,
so dominated convergence proves continuity, including lower-dimensional limits.
-/

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology Pointwise

namespace VolumePolynomials
namespace BodySupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def support (K : ConvexBody E) (f : E →L[ℝ] ℝ) : ℝ := sSup (f '' (K : Set E))

theorem le_support (K : ConvexBody E) (f : E →L[ℝ] ℝ) {x : E} (hx : x ∈ K) :
    f x ≤ support K f :=
  le_csSup (K.isCompact.image f.continuous).bddAbove (mem_image_of_mem f hx)

theorem support_le (K : ConvexBody E) (f : E →L[ℝ] ℝ) {a : ℝ}
    (ha : ∀ x ∈ K, f x ≤ a) : support K f ≤ a :=
  csSup_le (K.nonempty.image f) (by rintro _ ⟨x, hx, rfl⟩; exact ha x hx)

theorem exists_support (K : ConvexBody E) (f : E →L[ℝ] ℝ) :
    ∃ x ∈ K, f x = support K f :=
  (K.isCompact.image f.continuous).sSup_mem (K.nonempty.image f)

theorem mem_iff_le_support (K : ConvexBody E) {x : E} :
    x ∈ K ↔ ∀ f : E →L[ℝ] ℝ, f x ≤ support K f := by
  refine ⟨fun hx f => le_support K f hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point K.convex K.isClosed hx
  exact (hux.trans_le ((h f).trans (support_le K f fun y hy => (hu y hy).le))).false

theorem support_le_add_norm_mul_dist (K L : ConvexBody E) (f : E →L[ℝ] ℝ) :
    support K f ≤ support L f + ‖f‖ * dist K L := by
  obtain ⟨x, hx, hfx⟩ := exists_support K f
  obtain ⟨y, hy, hxy⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty x
  have hd : dist x y ≤ dist K L := by
    rw [← hxy]
    exact infDist_le_hausdorffDist_of_mem hx ConvexBody.hausdorffEDist_ne_top
  have hf : f x - f y ≤ ‖f‖ * dist x y := by
    calc
      f x - f y = f (x - y) := (map_sub f x y).symm
      _ ≤ ‖f (x - y)‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖x - y‖ := f.le_opNorm _
      _ = ‖f‖ * dist x y := by rw [dist_eq_norm]
  have hfy := le_support L f hy
  have hmul := mul_le_mul_of_nonneg_left hd (norm_nonneg f)
  rw [← hfx]
  linarith

theorem support_margin_of_closedBall_subset (K : ConvexBody E) {x : E} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ (K : Set E)) (f : E →L[ℝ] ℝ) :
    f x + r * ‖f‖ ≤ support K f := by
  have hnorm : ‖f‖ ≤ (support K f - f x) / r := by
    apply ContinuousLinearMap.opNorm_bound_of_ball_bound hr (support K f - f x) f
    intro z hz
    have hzp : x + z ∈ K := hball (by
      simpa [mem_closedBall, dist_eq_norm] using hz)
    have hzm : x - z ∈ K := hball (by
      simpa [mem_closedBall, dist_eq_norm] using hz)
    have hp := le_support K f hzp
    have hm := le_support K f hzm
    rw [map_add] at hp
    rw [map_sub] at hm
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hm := (le_div_iff₀ hr).mp hnorm
  nlinarith

theorem mem_of_dist_lt_of_closedBall_subset (K L : ConvexBody E) {x : E} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ (K : Set E)) (hKL : dist K L < r) :
    x ∈ L := by
  apply (mem_iff_le_support L).mpr
  intro f
  have h1 := support_margin_of_closedBall_subset K hr hball f
  have h2 := support_le_add_norm_mul_dist K L f
  have h3 := mul_le_mul_of_nonneg_left hKL.le (norm_nonneg f)
  nlinarith

theorem eventually_mem_of_mem_interior {ι : Type*} {l : Filter ι}
    {K : ConvexBody E} {L : ι → ConvexBody E} (hL : Tendsto L l (𝓝 K))
    {x : E} (hx : x ∈ interior (K : Set E)) : ∀ᶠ i in l, x ∈ L i := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hevent : ∀ᶠ i in l, dist K (L i) < r := by
    have := hL.eventually (Metric.ball_mem_nhds K hr)
    simpa only [mem_ball, dist_comm] using this
  filter_upwards [hevent] with i hi
  exact mem_of_dist_lt_of_closedBall_subset K (L i) hr hball hi

theorem eventually_notMem_of_notMem {ι : Type*} {l : Filter ι}
    {K : ConvexBody E} {L : ι → ConvexBody E} (hL : Tendsto L l (𝓝 K))
    {x : E} (hx : x ∉ K) : ∀ᶠ i in l, x ∉ L i := by
  have hr : 0 < infDist x (K : Set E) :=
    (K.isClosed.notMem_iff_infDist_pos K.nonempty).mp hx
  have hevent := hL.eventually (Metric.ball_mem_nhds K hr)
  filter_upwards [hevent] with i hi hxi
  have hd : infDist x (K : Set E) ≤ dist (L i) K :=
    infDist_le_hausdorffDist_of_mem hxi ConvexBody.hausdorffEDist_ne_top
  exact (not_lt_of_ge hd) hi

end BodySupport

section MeasureContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem tendsto_convexBody_measure {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {K : ConvexBody E} {L : ι → ConvexBody E} (hL : Tendsto L l (𝓝 K)) :
    Tendsto (fun i => μ (L i : Set E)) l (𝓝 (μ (K : Set E))) := by
  apply tendsto_measure_of_ae_tendsto_indicator l K.isCompact.measurableSet
    (fun i => (L i).isCompact.measurableSet)
    (isClosed_cthickening (E := (K : Set E)) (δ := 1)).measurableSet
    K.isBounded.cthickening.measure_lt_top.ne
  · have hevent := hL.eventually (Metric.ball_mem_nhds K zero_lt_one)
    filter_upwards [hevent] with i hi x hx
    obtain ⟨y, hy, hxy⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty x
    apply mem_cthickening_of_dist_le x y 1 (K : Set E) hy
    rw [← hxy]
    exact (infDist_le_hausdorffDist_of_mem hx ConvexBody.hausdorffEDist_ne_top).trans hi.le
  · have hnull := K.convex.addHaar_frontier μ
    have hae : ∀ᵐ x ∂μ, x ∉ frontier (K : Set E) := by
      exact measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [hae] with x hx
    by_cases hxK : x ∈ K
    · have hxi : x ∈ interior (K : Set E) := (mem_interior_iff_notMem_frontier hxK).mpr hx
      filter_upwards [BodySupport.eventually_mem_of_mem_interior hL hxi] with i hi
      exact iff_of_true hi hxK
    · filter_upwards [BodySupport.eventually_notMem_of_notMem hL hxK] with i hi
      exact iff_of_false hi hxK

theorem continuous_convexBody_measure :
    Continuous (fun K : ConvexBody E => μ (K : Set E)) := by
  rw [continuous_iff_continuousAt]
  intro K
  exact tendsto_convexBody_measure μ tendsto_id

theorem continuous_convexBody_realMeasure :
    Continuous (fun K : ConvexBody E => μ.real (K : Set E)) := by
  rw [continuous_iff_continuousAt]
  intro K
  have hfinite : μ (K : Set E) ≠ ⊤ := K.isCompact.measure_lt_top.ne
  exact (ENNReal.tendsto_toReal hfinite).comp
    ((continuous_convexBody_measure μ).tendsto K)

end MeasureContinuity
end VolumePolynomials
