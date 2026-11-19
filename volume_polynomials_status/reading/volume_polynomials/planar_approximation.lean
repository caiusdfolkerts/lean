module

public import VolumePolynomials.FiniteInteractionBody
public import VolumePolynomials.FiniteBodyApproximation
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences

@[expose] public section

set_option autoImplicit false

/-! # Polygon approximation with the four coordinate supports fixed

Adding four attained support points to an inscribed finite net preserves both
projection widths exactly. Thus the approximation used in the interaction
argument never changes the normalization of either input body.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology Pointwise BigOperators

namespace VolumePolynomials

theorem continuous_mapBody {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) :
    Continuous (mapBody L) := by
  first
  | apply isometry_bodyToNonemptyCompacts.comp_continuous_iff.mp
    change Continuous (fun K : ConvexBody E =>
      (bodyToNonemptyCompacts K).map L L.continuous)
    exact (Continuous.nonemptyCompacts_map L.continuous).comp continuous_bodyToNonemptyCompacts

namespace PlanarInteraction

open PlanarExtrusion PlanarMixedForm PlanarCorner PlanarEdges OAI.Paper092 PolytopeGeometry

theorem continuous_mixedArea_pair :
    Continuous (fun p : ConvexBody Plane × ConvexBody Plane => mixedArea volume p.1 p.2) := by
  first
  | apply (continuous_mixedVolume volume 2).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

theorem continuous_width : Continuous (width : ConvexBody Plane → ℝ) := by
  first
  | have hp : Continuous (fun P : ConvexBody Plane => (P, unitY)) :=
      continuous_id.prodMk continuous_const
    have hm : Continuous (fun P : ConvexBody Plane => mixedArea volume P unitY) :=
      Continuous.comp'
        (f := fun P : ConvexBody Plane => (P, unitY))
        (g := fun p : ConvexBody Plane × ConvexBody Plane => mixedArea volume p.1 p.2)
        continuous_mixedArea_pair hp
    have h : Continuous (fun P : ConvexBody Plane => (2 : ℝ) * mixedArea volume P unitY) :=
      continuous_const.mul hm
    simpa only [twice_mixedArea_unitY] using h

theorem continuous_height : Continuous (height : ConvexBody Plane → ℝ) := by
  first
  | have hp : Continuous (fun P : ConvexBody Plane => (P, unitX)) :=
      continuous_id.prodMk continuous_const
    have hm : Continuous (fun P : ConvexBody Plane => mixedArea volume P unitX) :=
      Continuous.comp'
        (f := fun P : ConvexBody Plane => (P, unitX))
        (g := fun p : ConvexBody Plane × ConvexBody Plane => mixedArea volume p.1 p.2)
        continuous_mixedArea_pair hp
    have h : Continuous (fun P : ConvexBody Plane => (2 : ℝ) * mixedArea volume P unitX) :=
      continuous_const.mul hm
    simpa only [twice_mixedArea_unitX] using h

theorem continuous_triple (A : ConvexBody Plane) :
    Continuous (fun p : ConvexBody Plane × ConvexBody Plane => triple A p.1 p.2) := by
  first
  | apply (continuous_mixedVolume volume 3).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact (continuous_mapBody embedYZ).comp continuous_fst
    · exact (continuous_mapBody embedXZ).comp continuous_snd

theorem continuous_mixedArea_right (A : ConvexBody Plane) :
    Continuous (fun Q : ConvexBody Plane => mixedArea volume A Q) := by
  first
  | have hp : Continuous (fun Q : ConvexBody Plane => (A, Q)) :=
      continuous_const.prodMk continuous_id
    exact Continuous.comp'
      (f := fun Q : ConvexBody Plane => (A, Q))
      (g := fun p : ConvexBody Plane × ConvexBody Plane => mixedArea volume p.1 p.2)
      continuous_mixedArea_pair hp

theorem exists_inscribed_polygon_preserving_axes (K : ConvexBody Plane)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ConvexBody Plane, IsFiniteHull (P : Set Plane) ∧ P ≤ K ∧
      width P = width K ∧ height P = height K ∧ dist P K < ε := by
  first
  | classical
    have hp : ∀ i : Fin 4, ∃ p ∈ K,
        axisNormals i p = SupportGeometry.support (K : Set Plane) (axisNormals i) := by
      first
      | intro i
        exact BodySupport.exists_support K (axisNormals i)
    choose p hpK hps using hp
    obtain ⟨S, hSK, hS, hcover⟩ := Metric.finite_approx_of_totallyBounded
      K.isCompact.totallyBounded (ε / 2) (half_pos hε)
    let V : Set Plane := S ∪ Set.range p
    have hV : V.Finite := hS.union (Set.finite_range p)
    have hVne : V.Nonempty := ⟨p 0, Or.inr ⟨0, rfl⟩⟩
    let P := finiteHullBody V hV hVne
    have hPK : P ≤ K := by
      first
      | apply convexHull_min _ K.convex
        rintro x (hx | ⟨i, rfl⟩)
        · exact hSK hx
        · exact hpK i
    have hpP (i : Fin 4) : p i ∈ P := subset_convexHull ℝ V (Or.inr ⟨i, rfl⟩)
    have hs (i : Fin 4) : SupportGeometry.support (P : Set Plane) (axisNormals i) =
        SupportGeometry.support (K : Set Plane) (axisNormals i) := by
      first
      | apply le_antisymm
        · exact SupportGeometry.support_le P.nonempty _
            (fun x hx => SupportGeometry.le_support K.isCompact _ (hPK hx))
        · rw [← hps i]
          exact SupportGeometry.le_support P.isCompact _ (hpP i)
    have hw : width P = width K := by
      first
      | rw [← support_axisX_sum, ← support_axisX_sum]
        exact congrArg₂ (· + ·) (hs 0) (hs 1)
    have hh : height P = height K := by
      first
      | rw [← support_axisY_sum, ← support_axisY_sum]
        exact congrArg₂ (· + ·) (hs 2) (hs 3)
    refine ⟨P, finiteHullBody_isFiniteHull V hV hVne, hPK, hw, hh, ?_⟩
    have hd : dist P K ≤ ε / 2 := by
      first
      | change hausdorffDist (P : Set Plane) (K : Set Plane) ≤ ε / 2
        apply hausdorffDist_le_of_mem_dist (half_pos hε).le
        · intro x hx
          exact ⟨x, hPK hx, by simpa using (half_pos hε).le⟩
        · intro x hx
          obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
          exact ⟨y, subset_convexHull ℝ V (Or.inl hy), (Metric.mem_ball.mp hxy).le⟩
    exact hd.trans_lt (half_lt_self hε)

theorem exists_unit_polygon_sequence (K : ConvexBody Plane)
    (hKa : 0 < volume.real (K : Set Plane)) (hKw : width K = 1) (hKh : height K = 1) :
    ∃ P : ℕ → ConvexBody Plane,
      (∀ n, IsFiniteHull (P n : Set Plane) ∧ P n ≤ K ∧
        width (P n) = 1 ∧ height (P n) = 1 ∧ 0 < volume.real (P n : Set Plane)) ∧
      Tendsto P atTop (𝓝 K) := by
  first
  | have hp (n : ℕ) := exists_inscribed_polygon_preserving_axes K
      (show 0 < 1 / ((n : ℝ) + 1) by positivity)
    choose P hpoly hPK hw hh hd using hp
    have ht : Tendsto P atTop (𝓝 K) := by
      first
      | rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun n => dist_nonneg) (fun n => (hd n).le)
          tendsto_one_div_add_atTop_nhds_zero_nat
    have ha : Tendsto (fun n => volume.real (P n : Set Plane)) atTop
        (𝓝 (volume.real (K : Set Plane))) :=
      (continuous_convexBody_realMeasure volume).continuousAt.tendsto.comp ht
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ha.eventually (Ioi_mem_nhds hKa))
    refine ⟨fun n => P (n + N), ?_, ht.comp (tendsto_add_atTop_nat N)⟩
    intro n
    exact ⟨hpoly _, hPK _, (hw _).trans hKw, (hh _).trans hKh,
      hN _ (Nat.le_add_left N n)⟩

/-- Every centered body with unit widths is in one fixed compact box. This
uses the actual coordinate extrema, not a choice of a bounding rectangle
which need not have a vertex in the body. -/
theorem unit_body_subset_box (K : ConvexBody Plane) (h0 : (0 : Plane) ∈ K)
    (hw : width K = 1) (hh : height K = 1) :
    (K : Set Plane) ⊆ Icc (-1, -1) (1, 1) := by
  first
  | intro p hp
    have hpos (i : Fin 4) : 0 ≤ SupportGeometry.support (K : Set Plane) (axisNormals i) := by
      first
      | simpa only [map_zero] using SupportGeometry.le_support K.isCompact (axisNormals i) h0
    have hx := support_axisX_sum K
    have hy := support_axisY_sum K
    rw [hw] at hx
    rw [hh] at hy
    have hpx := SupportGeometry.le_support K.isCompact (axisNormals 0) hp
    have hnx := SupportGeometry.le_support K.isCompact (axisNormals 1) hp
    have hpy := SupportGeometry.le_support K.isCompact (axisNormals 3) hp
    have hny := SupportGeometry.le_support K.isCompact (axisNormals 2) hp
    have h0' := hpos 0
    have h1' := hpos 1
    have h2' := hpos 2
    have h3' := hpos 3
    simp only [axisNormals, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      normal_apply, one_mul, zero_mul, neg_one_mul, sub_zero, zero_sub] at hpx hnx hpy hny h0' h1' h2' h3'
    change (-1 ≤ p.1 ∧ -1 ≤ p.2) ∧ (p.1 ≤ 1 ∧ p.2 ≤ 1)
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

def centeredUnitBodies : Set (ConvexBody Plane) :=
  {Q | (0 : Plane) ∈ Q ∧ width Q = 1 ∧ height Q = 1}

theorem isCompact_centeredUnitBodies : IsCompact centeredUnitBodies := by
  first
  | have hbox := isCompact_bodies_in_compact (E := Plane)
      (isCompact_Icc : IsCompact (Icc ((-1, -1) : Plane) (1, 1)))
    have hw := isClosed_eq continuous_width (continuous_const : Continuous (fun _ : ConvexBody Plane => (1 : ℝ)))
    have hh := isClosed_eq continuous_height (continuous_const : Continuous (fun _ : ConvexBody Plane => (1 : ℝ)))
    have h := (hbox.inter_right hw).inter_right hh
    convert h using 1
    ext Q
    constructor
    · rintro ⟨h0, hqw, hqh⟩
      exact ⟨⟨⟨h0, unit_body_subset_box Q h0 hqw hqh⟩, hqw⟩, hqh⟩
    · rintro ⟨⟨⟨h0, _⟩, hqw⟩, hqh⟩
      exact ⟨h0, hqw, hqh⟩

end PlanarInteraction
end VolumePolynomials
