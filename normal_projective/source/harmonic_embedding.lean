module

public import planar_geometry
public import triangular_disk
public import dirichlet

import face_graph
import boundary_corners
import planar_tools
import punctured_convex
import interval_chain
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Util.CollectAxioms
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson.Basic
import Lean.Data.Json.Printer

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit/final"


/-! # Geometric harmonic embeddings of finite triangular disks

This module develops the nondegeneracy, nonoverlap, and faithful incidence of
the harmonic drawing. Its inputs are actual geometric triangulations, positive
edge weights, and harmonic equations. No embedding conclusion is assumed.
-/

@[expose] public section

noncomputable section

/-! ## HarmonicMap -/

/-!
# Nondegeneracy of every face of the actual harmonic drawing

The boundary triangle gives one nondegenerate face. The proved adjacency
lemma propagates this property across the connected actual face graph.
-/

namespace NormalProjective.Planar

open Set Finset

theorem edgeHeight_zero_on_line {a b z : ℂ}
    (hz : z ∈ affineSpan ℝ ({a,b} : Set ℂ)) : edgeHeight a b z = 0 := by
  obtain ⟨r,rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hz
  rw [edgeHeight_eq_linear]
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  rw [map_add,map_smul,map_sub]
  have hb := edgeHeight_zero_on_segment (right_mem_segment ℝ a b)
  rw [edgeHeight_eq_linear] at hb
  rw [sub_eq_zero.mp hb]
  simp

theorem affineIndependent_triple_of_height_ne_zero {a b c : ℂ}
    (hc : edgeHeight a b c ≠ 0) : AffineIndependent ℝ ![a,b,c] := by
  have hab : a ≠ b := by intro h; apply hc; simp [h,edgeHeight,edgeNormalize]
  exact affineIndependent_of_ne_of_mem_of_mem_of_notMem hab
    (left_mem_affineSpan_pair ℝ a b) (right_mem_affineSpan_pair ℝ a b)
    (fun h => hc (edgeHeight_zero_on_line h))

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem face_independent_of_height_ne_zero (q : V → ℂ) {a b x : V}
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b)
    (hx : edgeHeight (q a) (q b) (q x) ≠ 0) :
    AffineIndependent ℝ (fun v : ({a,b,x} : Finset V) => q v) := by
  let f : ({a,b,x} : Finset V) → Fin 3 := fun v =>
    if (v : V) = a then 0 else if (v : V) = b then 1 else 2
  have hv (v : ({a,b,x} : Finset V)) : (v : V) = a ∨ (v : V) = b ∨ (v : V) = x := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using v.property
  have hf : Function.Injective f := by
    intro u v heq
    apply Subtype.ext
    rcases hv u with hu | hu | hu <;> rcases hv v with hv | hv | hv
    all_goals simp_all [f,hab.symm,hxa.symm,hxb.symm]
  have hp : (fun v : ({a,b,x} : Finset V) => q v) = ![q a,q b,q x] ∘ f := by
    funext v
    rcases hv v with hv | hv | hv <;> simp [Function.comp_def,f,hv,hab,hab.symm,hxa,hxb]
  rw [hp]
  exact (affineIndependent_triple_of_height_ne_zero hx).comp_embedding ⟨f,hf⟩

theorem height_ne_zero_of_face_independent (q : V → ℂ) {s : Finset V}
    (hs : AffineIndependent ℝ (fun v : s => q v))
    {a b x : V} (ha : a ∈ s) (hb : b ∈ s) (hx : x ∈ s)
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    edgeHeight (q a) (q b) (q x) ≠ 0 := by
  intro hzero
  have habq : q a ≠ q b := by
    intro h
    exact hab (congrArg Subtype.val (hs.injective (a₁ := ⟨a,ha⟩) (a₂ := ⟨b,hb⟩) h))
  have hline := mem_line_of_edgeHeight_zero habq hzero
  let a' : s := ⟨a,ha⟩
  let b' : s := ⟨b,hb⟩
  let x' : s := ⟨x,hx⟩
  have hmem : q x ∈ affineSpan ℝ ((fun v : s => q v) '' ({a',b'} : Set s)) := by
    simpa [a',b'] using hline
  have hm := (hs.mem_affineSpan_iff x' ({a',b'} : Set s)).mp hmem
  simp only [mem_insert_iff,mem_singleton_iff] at hm
  rcases hm with h | h
  · exact hxa (congrArg Subtype.val h)
  · exact hxb (congrArg Subtype.val h)

namespace TriangularDisk

variable (D : TriangularDisk V)

def IsHarmonicDrawing (w : V → V → ℝ) (q : V → ℂ) : Prop :=
  (∀ j, q (D.corner j) = basePoint j) ∧
    ∀ v, v ∉ D.boundary →
      Dirichlet.Harmonic w (fun v => (q v).re) v ∧
      Dirichlet.Harmonic w (fun v => (q v).im) v

theorem IsHarmonicDrawing.coordinate_harmonic {w : V → V → ℝ} {q : V → ℂ}
    (hq : D.IsHarmonicDrawing w q) {v : V} (hv : v ∉ D.boundary) (j : Fin 3) :
    Dirichlet.Harmonic w (fun v => triangleCoordinate j (q v)) v := by
  have h := hq.2 v hv
  fin_cases j
  · have heq : (fun u => triangleCoordinate 0 (q u)) =
        (fun u => (-1) * (q u).re + (-1) * (q u).im + 1) := by
      funext u
      change 1 - (q u).re - (q u).im =
        (-1) * (q u).re + (-1) * (q u).im + 1
      ring
    change Dirichlet.Harmonic w (fun u => triangleCoordinate 0 (q u)) v
    rw [heq]
    exact Dirichlet.harmonic_affine h.1 h.2 (-1) (-1) 1
  · simpa [triangleCoordinate] using h.1
  · simpa [triangleCoordinate] using h.2

theorem IsHarmonicDrawing.height_harmonic {w : V → V → ℝ} {q : V → ℂ}
    (hq : D.IsHarmonicDrawing w q) {v : V} (hv : v ∉ D.boundary) (a b : ℂ) :
    Dirichlet.Harmonic w (fun v => edgeHeight a b (q v)) v := by
  have h := hq.2 v hv
  have heq : (fun v => edgeHeight a b (q v)) =
      (fun v => ((b-a)⁻¹).im * (q v).re + ((b-a)⁻¹).re * (q v).im -
        (((b-a)⁻¹).im * a.re + ((b-a)⁻¹).re * a.im)) := by
    funext v
    simp only [edgeHeight,edgeNormalize,AffineMap.coe_mk,Complex.mul_im,Complex.sub_re,Complex.sub_im]
    ring
  rw [heq]
  exact Dirichlet.harmonic_affine h.1 h.2 _ _ _

theorem IsHarmonicDrawing.third_coordinate_pos {w : V → V → ℝ} {q : V → ℂ}
    (hq : D.IsHarmonicDrawing w q)
    (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    {v : V} (hv0 : v ≠ D.corner 0) (hv1 : v ≠ D.corner 1) :
    0 < (q v).im := by
  by_cases hv : v ∈ D.boundary
  · obtain ⟨j,rfl⟩ := hv
    fin_cases j <;> simp_all [basePoint,hq.1]
  · have hi := D.interior_of_harmonic w hw he q hq.1
      (fun i hi j => IsHarmonicDrawing.coordinate_harmonic D hq hi j) v hv
    have hcoord : 0 < triangleCoordinate 2 (q v) := by
      change 0 < (q v).im
      have hsub : baseTriangle ⊆ {z : ℂ | 0 ≤ z.im} := by
        intro z hz
        exact hz 2
      have hh := interior_mono hsub hi
      simpa only [Complex.interior_setOfPred_le_im,mem_setOf_eq] using hh
    simpa [triangleCoordinate] using hcoord

theorem harmonic_face_independent
    (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
    (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
    (q : V → ℂ) (hq : D.IsHarmonicDrawing w q) :
    ∀ s ∈ D.faces, AffineIndependent ℝ (fun v : s => q v) := by
  classical
  have hab : D.corner 0 ≠ D.corner 1 := D.corner.injective.ne (by decide)
  obtain ⟨_,s,hs,ha,hb⟩ := D.boundary_edge 0 1 (by decide : (0 : Fin 3) ≠ 1)
  obtain ⟨x,hxa,hxb,hsx⟩ := triangle_eq_insert_pair (D.face_card s hs) hab ha hb
  have hxq : 0 < edgeHeight (q (D.corner 0)) (q (D.corner 1)) (q x) := by
    rw [hq.1,hq.1]
    simpa [edgeHeight,edgeNormalize,basePoint] using IsHarmonicDrawing.third_coordinate_pos D hq hw he hxa hxb
  have hstart : AffineIndependent ℝ (fun v : s => q v) := by
    rw [hsx]
    exact face_independent_of_height_ne_zero q hab hxa hxb hxq.ne'
  letI : Nonempty D.toTriangulation.Face := ⟨⟨s,hs⟩⟩
  have hconn := D.toTriangulation.faceGraph_connected (D.domain_eq.symm ▸ baseTriangle_convex)
  have hstep : ∀ (u v : D.toTriangulation.Face), D.toTriangulation.faceGraph.Adj u v →
      AffineIndependent ℝ (fun x : u.val => q x) →
      AffineIndependent ℝ (fun x : v.val => q x) := by
    intro u v huv hu
    obtain ⟨a,b,x,y,hab,hxy,hxa,hxb,hya,hyb,hux,hvy⟩ := adjacent_triangles_decompose
      (D.face_card u.val u.property) (D.face_card v.val v.property)
      (fun h => huv.1 (Subtype.ext h)) huv.2
    have hs' : ({a,b,x} : Finset V) ∈ D.faces := hux ▸ u.property
    have ht' : ({a,b,y} : Finset V) ∈ D.faces := hvy ▸ v.property
    have hxne := height_ne_zero_of_face_independent q hu
      (by simp [hux]) (by simp [hux]) (by simp [hux]) hab hxa hxb
    have habq : q a ≠ q b := by intro h; simpa [h,edgeHeight,edgeNormalize] using hxne
    have hhy : edgeHeight (q a) (q b) (q y) ≠ 0 := by
      rcases lt_or_gt_of_ne hxne with hxn | hxp
      · have hp := D.harmonic_height_negative_across_edge w hw he hoff
          (fun z => -edgeHeight (q a) (q b) (q z))
          (fun z hz => Dirichlet.harmonic_neg (IsHarmonicDrawing.height_harmonic D hq hz _ _))
          hs' ht' hab hxy hxa hxb hya hyb
          (by simp [edgeHeight,edgeNormalize])
          (by rw [edgeHeight_zero_on_segment (right_mem_segment ℝ (q a) (q b)), neg_zero])
          (neg_pos.mpr hxn)
        intro heq
        simpa [heq] using hp
      · exact (D.harmonic_height_negative_across_edge w hw he hoff
          (fun z => edgeHeight (q a) (q b) (q z))
          (fun z hz => IsHarmonicDrawing.height_harmonic D hq hz _ _) hs' ht' hab hxy hxa hxb hya hyb
          (by simp [edgeHeight,edgeNormalize])
          (edgeHeight_zero_on_segment (right_mem_segment ℝ (q a) (q b))) hxp).ne
    rw [hvy]
    exact face_independent_of_height_ne_zero q hab hya hyb hhy
  intro t ht
  obtain ⟨p⟩ := hconn ⟨s,hs⟩ ⟨t,ht⟩
  have hwalk : ∀ {u v : D.toTriangulation.Face},
      D.toTriangulation.faceGraph.Walk u v →
      AffineIndependent ℝ (fun x : u.val => q x) →
      AffineIndependent ℝ (fun x : v.val => q x) := by
    intro u v p
    induction p with
    | nil => exact id
    | cons huv p ih => exact fun hu => ih (hstep _ _ huv hu)
  exact hwalk p hstart

end TriangularDisk

end NormalProjective.Planar

/-! ## DrawingBoundary -/

/-! Boundary labels detected from the actual harmonic coordinates. -/

namespace NormalProjective.Planar

open Set Finset

theorem triangleCoordinate_combo (j : Fin 3) (a b : ℂ) (r s : ℝ) (hrs : r+s=1) :
    triangleCoordinate j (r • a+s • b) =
      r * triangleCoordinate j a+s * triangleCoordinate j b := by
  fin_cases j <;> simp [triangleCoordinate,Complex.real_smul]
  · nlinarith
  all_goals ring

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TriangularDisk

variable (D : TriangularDisk V) (w : V → V → ℝ)
  (hw : ∀ i j, 0 ≤ w i j)
  (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
  (q : V → ℂ) (hq : D.IsHarmonicDrawing w q)

include hw he hq in
theorem drawing_coordinates_nonnegative (v : V) (j : Fin 3) :
    0 ≤ triangleCoordinate j (q v) :=
  D.coordinates_nonneg_of_harmonic w hw he q hq.1
    (fun v hv j => IsHarmonicDrawing.coordinate_harmonic D hq hv j) v j

include hw he hq in
theorem drawing_coordinates_positive {v : V} (hv : v ∉ D.boundary) (j : Fin 3) :
    0 < triangleCoordinate j (q v) := by
  apply Dirichlet.strict_minimum_of_accessible D.toTriangulation.graph D.graph_connected
    D.boundary w hw he (fun v => triangleCoordinate j (q v))
    (fun v hv => IsHarmonicDrawing.coordinate_harmonic D hq hv j) 0 _ (D.corner j) ⟨j,rfl⟩ _ v hv
    (D.corner_accessible j v hv)
  · rintro b ⟨k,rfl⟩
    rw [hq.1,coordinate_basePoint]
    split_ifs <;> norm_num
  · rw [hq.1,coordinate_basePoint]
    simp

include hw he hq in
theorem drawing_coordinate_zero_iff (v : V) (j : Fin 3) :
    triangleCoordinate j (q v) = 0 ↔ ∃ k : Fin 3, k ≠ j ∧ v = D.corner k := by
  constructor
  · intro hz
    by_cases hv : v ∈ D.boundary
    · obtain ⟨k,rfl⟩ := hv
      refine ⟨k,?_,rfl⟩
      intro hkj
      subst k
      rw [hq.1,coordinate_basePoint] at hz
      norm_num at hz
    · exact False.elim ((D.drawing_coordinates_positive w hw he q hq hv j).ne' hz)
  · rintro ⟨k,hkj,rfl⟩
    rw [hq.1,coordinate_basePoint]
    simp [hkj.symm]

include hw he hq in
theorem open_image_edge_zero_coordinate {a b : V} {z : ℂ}
    (hz : z ∈ openSegment ℝ (q a) (q b)) (j : Fin 3)
    (hzj : triangleCoordinate j z = 0) :
    triangleCoordinate j (q a) = 0 ∧ triangleCoordinate j (q b) = 0 := by
  obtain ⟨r,s,hr,hs,hrs,rfl⟩ := hz
  rw [triangleCoordinate_combo j _ _ r s hrs] at hzj
  have ha := D.drawing_coordinates_nonnegative w hw he q hq a j
  have hb := D.drawing_coordinates_nonnegative w hw he q hq b j
  have hra : r * triangleCoordinate j (q a) = 0 := by
    have := mul_nonneg hs.le hb
    have := mul_nonneg hr.le ha
    linarith
  have hsb : s * triangleCoordinate j (q b) = 0 := by
    have := mul_nonneg hs.le hb
    have := mul_nonneg hr.le ha
    linarith
  exact ⟨(mul_eq_zero.mp hra).resolve_left hr.ne',
    (mul_eq_zero.mp hsb).resolve_left hs.ne'⟩

include hw he hq in
theorem strict_coordinate_open_edge_interior {a b : V} {z : ℂ}
    (hab : a ≠ b) (hz : z ∈ openSegment ℝ (q a) (q b))
    (hzpos : ∀ j, 0 < triangleCoordinate j z) : a ∉ D.boundary ∨ b ∉ D.boundary := by
  by_contra! h
  obtain ⟨i,rfl⟩ := h.1
  obtain ⟨j,rfl⟩ := h.2
  have hij : i ≠ j := fun h => hab (congrArg D.corner h)
  have hex : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals decide
  obtain ⟨k,hki,hkj⟩ := hex
  obtain ⟨r,s,hr,hs,hrs,rfl⟩ := hz
  have h := hzpos k
  rw [triangleCoordinate_combo k _ _ r s hrs,hq.1,hq.1,coordinate_basePoint,
    coordinate_basePoint] at h
  simp [hki,hkj] at h

include hw he hq in
theorem open_edge_at_right_boundary {a b : V} {c : ℝ}
    (hab : a ≠ b) (hz : horizontalPoint c (1-c) ∈ openSegment ℝ (q a) (q b)) :
    ({a,b} : Finset V) = {D.corner 1,D.corner 2} := by
  have hzero : triangleCoordinate 0 (horizontalPoint c (1-c)) = 0 := by
    simp [triangleCoordinate,horizontalPoint]
  have hends := D.open_image_edge_zero_coordinate w hw he q hq hz 0 hzero
  obtain ⟨i,hi,rfl⟩ := (D.drawing_coordinate_zero_iff w hw he q hq a 0).mp hends.1
  obtain ⟨j,hj,rfl⟩ := (D.drawing_coordinate_zero_iff w hw he q hq b 0).mp hends.2
  have hij : i ≠ j := fun h => hab (congrArg D.corner h)
  fin_cases i <;> fin_cases j <;> simp_all [Finset.pair_comm]

include hw he hq in
theorem generic_slice_height_range (c : ℝ) (hgeneric : ∀ v, (q v).im ≠ c)
    {s : D.toTriangulation.Face} (hne : (horizontalSlice (simplex q s.val) c).Nonempty) :
    0 < c ∧ c < 1 := by
  obtain ⟨x,hx⟩ := hne
  have hsub : simplex q s.val ⊆ baseTriangle :=
    D.toTriangulation.drawing_cell_subset q baseTriangle_convex
      (fun v => D.drawing_coordinates_nonnegative w hw he q hq v) s
  have hz := hsub hx
  have hc : 0 ≤ c := by simpa [triangleCoordinate,horizontalPoint] using hz 2
  have hx0 : 0 ≤ x := by simpa [triangleCoordinate,horizontalPoint] using hz 1
  have hxc : 0 ≤ 1-x-c := by simpa [triangleCoordinate,horizontalPoint] using hz 0
  have hc0 : c ≠ 0 := by
    intro h
    exact hgeneric (D.corner 0) (by simp [hq.1,basePoint,h])
  have hc1 : c ≠ 1 := by
    intro h
    exact hgeneric (D.corner 2) (by simp [hq.1,basePoint,h])
  exact ⟨lt_of_le_of_ne hc hc0.symm,lt_of_le_of_ne (by linarith) hc1⟩

end TriangularDisk

end NormalProjective.Planar

/-! ## EdgeIncidence -/

/-!
# Edge incidence derived from actual planar geometry

An edge in the interior of the triangular disk belongs to exactly two
triangles, one on either side. A boundary edge belongs to one. These are proved
from the convex-hull intersection and covering conditions.
-/

namespace NormalProjective.Planar

open Set Finset Filter
open scoped Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

theorem edge_midpoint_ne_left {a b : V} (hab : a ≠ b) :
    (1/2 : ℝ) • (T.point a + T.point b) ≠ T.point a := by
  intro h
  apply hab
  apply T.point_injective
  have : T.point b = T.point a := by
    apply Complex.ext
    · have hr := congrArg Complex.re h
      simp only [Complex.smul_re, Complex.add_re, smul_eq_mul] at hr
      linarith
    · have hi := congrArg Complex.im h
      simp only [Complex.smul_im, Complex.add_im, smul_eq_mul] at hi
      linarith
  exact this.symm

theorem edge_midpoint_ne_right {a b : V} (hab : a ≠ b) :
    (1/2 : ℝ) • (T.point a + T.point b) ≠ T.point b := by
  simpa [add_comm] using T.edge_midpoint_ne_left hab.symm

theorem edge_midpoint_mem_segment (a b : V) :
    (1/2 : ℝ) • (T.point a + T.point b) ∈ segment ℝ (T.point a) (T.point b) := by
  exact ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,by module⟩

theorem edge_midpoint_mem_cell_iff {a b : V} (hab : T.graph.Adj a b)
    (s : T.Face) :
    (1/2 : ℝ) • (T.point a + T.point b) ∈ T.cell s ↔ a ∈ s.val ∧ b ∈ s.val := by
  let m := (1/2 : ℝ) • (T.point a + T.point b)
  constructor
  · intro hm
    obtain ⟨habne,u,hu,ha,hb⟩ := hab
    have hmab : m ∈ simplex T.point ({a,b} : Finset V) := by
      rw [simplex_pair]
      exact T.edge_midpoint_mem_segment a b
    have hinter := T.subface_intersection hu s.property
      (Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩)
      (by intro v hv; exact hv : s.val ⊆ s.val)
    have hmi : m ∈ simplex T.point (({a,b} : Finset V) ∩ s.val) := by
      rw [← hinter]
      exact ⟨hmab,hm⟩
    constructor
    · by_contra ha'
      have hsub : ({a,b} : Finset V) ∩ s.val ⊆ {b} := by
        intro v hv
        simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton] at hv ⊢
        rcases hv.1 with rfl | hvb
        · exact False.elim (ha' hv.2)
        · exact hvb
      have hm' : m ∈ simplex T.point ({b} : Finset V) :=
        convexHull_mono (Set.image_mono hsub) hmi
      have heq : m = T.point b := by simpa [simplex] using hm'
      exact T.edge_midpoint_ne_right habne heq
    · by_contra hb'
      have hsub : ({a,b} : Finset V) ∩ s.val ⊆ {a} := by
        intro v hv
        simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton] at hv ⊢
        rcases hv.1 with hva | rfl
        · exact hva
        · exact False.elim (hb' hv.2)
      have hm' : m ∈ simplex T.point ({a} : Finset V) :=
        convexHull_mono (Set.image_mono hsub) hmi
      have heq : m = T.point a := by simpa [simplex] using hm'
      exact T.edge_midpoint_ne_left habne heq
  · rintro ⟨ha,hb⟩
    have hsub : segment ℝ (T.point a) (T.point b) ⊆ T.cell s :=
      (convex_convexHull ℝ _).segment_subset (T.point_mem_cell s ha) (T.point_mem_cell s hb)
    exact hsub (T.edge_midpoint_mem_segment a b)

theorem edgeHeight_nonneg_on_triangle {a b x z : ℂ}
    (hx : 0 ≤ edgeHeight a b x)
    (hz : z ∈ convexHull ℝ ({a,b,x} : Set ℂ)) : 0 ≤ edgeHeight a b z := by
  let L := edgeHeightLinear a b
  have hsub : convexHull ℝ ({a,b,x} : Set ℂ) ⊆ {z | L a ≤ L z} := by
    apply convexHull_min
    · intro y hy
      simp only [mem_insert_iff,mem_singleton_iff] at hy
      rcases hy with hya | hyb | hyx
      · subst y
        change L a ≤ L a
        exact le_rfl
      · subst y
        change L a ≤ L b
        have hb := edgeHeight_zero_on_segment (right_mem_segment ℝ a b)
        rw [edgeHeight_eq_linear] at hb
        exact (sub_eq_zero.mp hb).ge
      · subst y
        change L a ≤ L x
        simpa only [L, edgeHeight_eq_linear, sub_nonneg] using hx
    · exact convex_halfSpace_ge L.toLinearMap.isLinear (L a)
  rw [edgeHeight_eq_linear]
  exact sub_nonneg.mpr (hsub hz)

end Triangulation

namespace TriangularDisk

variable (D : TriangularDisk V)

theorem edge_midpoint_interior {a b : V} (hab : D.toTriangulation.graph.Adj a b)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary) :
    (1/2 : ℝ) • (D.point a + D.point b) ∈ interior baseTriangle := by
  apply mem_interior_baseTriangle_of_coordinates
  intro j
  have ha := D.source_coordinates_nonnegative a j
  have hb := D.source_coordinates_nonnegative b j
  have heq : triangleCoordinate j ((1/2 : ℝ) • (D.point a + D.point b)) =
      (1/2 : ℝ) * triangleCoordinate j (D.point a) +
        (1/2 : ℝ) * triangleCoordinate j (D.point b) := by
    fin_cases j <;> simp [triangleCoordinate,Complex.real_smul] <;> ring
  rw [heq]
  rcases hi with hi | hi
  · have h := D.interior_vertex a hi j
    linarith
  · have h := D.interior_vertex b hi j
    linarith

/-- The finite closed cover supplies a face on the opposite side of every
interior edge. -/
theorem exists_opposite_face {a b x : V}
    (hs : ({a,b,x} : Finset V) ∈ D.faces)
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary)
    (hx : 0 < edgeHeight (D.point a) (D.point b) (D.point x)) :
    ∃ y, y ≠ a ∧ y ≠ b ∧ y ≠ x ∧ ({a,b,y} : Finset V) ∈ D.faces ∧
      edgeHeight (D.point a) (D.point b) (D.point y) < 0 := by
  classical
  let m := (1/2 : ℝ) • (D.point a + D.point b)
  have habG : D.toTriangulation.graph.Adj a b := ⟨hab,_,hs,by simp,by simp⟩
  let bad : Set ℂ := ⋃ s : {s : D.toTriangulation.Face // ¬ (a ∈ s.val ∧ b ∈ s.val)},
    D.toTriangulation.cell s.val
  have hbad : IsClosed bad := isClosed_iUnion_of_finite (fun s =>
    (D.toTriangulation.cell_isCompact s.val).isClosed)
  have hmnot : m ∉ bad := by
    intro hm
    obtain ⟨s,hms⟩ := mem_iUnion.mp hm
    exact s.property ((D.toTriangulation.edge_midpoint_mem_cell_iff habG s.val).mp hms)
  have hm : m ∈ interior baseTriangle := D.edge_midpoint_interior habG hi
  let z : ℝ → ℂ := fun t => m - (t : ℂ) * Complex.I * (D.point b-D.point a)
  have hz0 : z 0 = m := by simp [z]
  have hznear : ∀ᶠ t in 𝓝 (0 : ℝ), z t ∈ interior baseTriangle ∩ badᶜ := by
    have hzcont : Continuous z := by fun_prop
    exact hzcont.continuousAt ((isOpen_interior.inter hbad.isOpen_compl).mem_nhds
      (by simpa [hz0] using And.intro hm hmnot))
  obtain ⟨t,ht0,ht⟩ := hznear.exists_gt
  have hzt : z t ∈ D.toTriangulation.domain := by
    rw [D.domain_eq]
    exact interior_subset ht.1
  obtain ⟨f,hf⟩ := mem_iUnion.mp hzt
  have habf : a ∈ f.val ∧ b ∈ f.val := by
    by_contra h
    exact ht.2 (mem_iUnion.mpr ⟨⟨f,h⟩,hf⟩)
  obtain ⟨y,hya,hyb,hfy⟩ := triangle_eq_insert_pair (D.face_card f.val f.property) hab habf.1 habf.2
  have hzy : z t ∈ convexHull ℝ ({D.point a,D.point b,D.point y} : Set ℂ) := by
    simpa [Triangulation.cell,simplex,hfy] using hf
  have hheight : edgeHeight (D.point a) (D.point b) (z t) = -t := by
    have habq := D.point_injective.ne hab
    change (((D.point b-D.point a)⁻¹)*(z t-D.point a)).im = -t
    have hn : ((D.point b-D.point a)⁻¹)*(z t-D.point a) = (1/2 : ℂ)-(t : ℂ)*Complex.I := by
      dsimp [z,m]
      norm_num [Complex.ofReal_div]
      field_simp [sub_ne_zero.mpr habq.symm]
      ring
    rw [hn]
    simp
  have hyneg : edgeHeight (D.point a) (D.point b) (D.point y) < 0 := by
    by_contra hy
    have hznonneg := Triangulation.edgeHeight_nonneg_on_triangle (le_of_not_gt hy) hzy
    rw [hheight] at hznonneg
    linarith
  have hyx : y ≠ x := by intro h; subst y; exact hx.not_ge hyneg.le
  exact ⟨y,hya,hyb,hyx,hfy ▸ f.property,hyneg⟩

end TriangularDisk

end NormalProjective.Planar

/-! ## IncidentFaces -/

/-! Exact one-face/two-face incidence, derived from the planar carriers. -/

namespace NormalProjective.Planar

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

def IncidentFace (a b : V) := {s : T.Face // a ∈ s.val ∧ b ∈ s.val}

instance (a b : V) : Fintype (T.IncidentFace a b) := by
  classical
  unfold IncidentFace
  infer_instance

def edgeThird {a b : V} (hab : a ≠ b) (s : T.IncidentFace a b) : V :=
  Classical.choose (triangle_eq_insert_pair (T.face_card s.val.val s.val.property)
    hab s.property.1 s.property.2)

theorem edgeThird_spec {a b : V} (hab : a ≠ b) (s : T.IncidentFace a b) :
    T.edgeThird hab s ≠ a ∧ T.edgeThird hab s ≠ b ∧
      s.val.val = {a,b,T.edgeThird hab s} :=
  Classical.choose_spec (triangle_eq_insert_pair (T.face_card s.val.val s.val.property)
    hab s.property.1 s.property.2)

theorem edgeThird_height_ne_zero {a b : V} (hab : a ≠ b) (s : T.IncidentFace a b) :
    edgeHeight (T.point a) (T.point b) (T.point (T.edgeThird hab s)) ≠ 0 := by
  have hs := T.edgeThird_spec hab s
  apply T.face_third_height_ne_zero s.val.property s.property.1 s.property.2
    (by rw [hs.2.2]; simp) hab hs.1 hs.2.1

theorem edgeThird_injective {a b : V} (hab : a ≠ b) :
    Function.Injective (T.edgeThird hab) := by
  intro s t h
  apply Subtype.ext
  apply Subtype.ext
  rw [(T.edgeThird_spec hab s).2.2,(T.edgeThird_spec hab t).2.2,h]

def incidentSide {a b : V} (hab : a ≠ b) (s : T.IncidentFace a b) : Bool :=
  decide (0 < edgeHeight (T.point a) (T.point b) (T.point (T.edgeThird hab s)))

/-- Opposite source faces lie on opposite sides of their common edge.
This uses the actual simplicial intersection and the public triangle-side lemma. -/
theorem source_adjacent_third_height_neg {a b x y : V}
    (hs : ({a,b,x} : Finset V) ∈ T.faces)
    (ht : ({a,b,y} : Finset V) ∈ T.faces)
    (hab : a ≠ b) (hxy : x ≠ y)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b)
    (hx : 0 < edgeHeight (T.point a) (T.point b) (T.point x)) :
    edgeHeight (T.point a) (T.point b) (T.point y) < 0 := by
  have hint : ({a,b,x} ∩ {a,b,y} : Finset V) = {a,b} := by
    ext v
    simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · intro hv
      rcases hv.1 with ha | hb | hxv
      · exact Or.inl ha
      · exact Or.inr hb
      · rcases hv.2 with ha | hb | hyv
        · exact Or.inl ha
        · exact Or.inr hb
        · exact False.elim (hxy (hxv.symm.trans hyv))
    · intro hv
      rcases hv with ha | hb
      · exact ⟨Or.inl ha,Or.inl ha⟩
      · exact ⟨Or.inr (Or.inl hb),Or.inr (Or.inl hb)⟩
  apply third_vertex_negative_of_triangle_intersection (T.point_injective.ne hab) hx
  · exact T.face_third_height_ne_zero ht (by simp) (by simp) (by simp) hab hya hyb
  · have hh := T.intersection _ hs _ ht
    rw [hint,T.simplex_pair] at hh
    simpa [simplex] using hh.le

theorem incidentSide_injective {a b : V} (hab : a ≠ b) :
    Function.Injective (T.incidentSide hab) := by
  intro s t hside
  by_contra hst
  have hxy := (T.edgeThird_injective hab).ne hst
  have hs := T.edgeThird_spec hab s
  have ht := T.edgeThird_spec hab t
  have hsf : ({a,b,T.edgeThird hab s} : Finset V) ∈ T.faces := hs.2.2 ▸ s.val.property
  have htf : ({a,b,T.edgeThird hab t} : Finset V) ∈ T.faces := ht.2.2 ▸ t.val.property
  rcases lt_or_gt_of_ne (T.edgeThird_height_ne_zero hab s) with hxneg | hxpos
  · have hsf' : ({b,a,T.edgeThird hab s} : Finset V) ∈ T.faces := by
      simpa only [Finset.insert_comm] using hsf
    have htf' : ({b,a,T.edgeThird hab t} : Finset V) ∈ T.faces := by
      simpa only [Finset.insert_comm] using htf
    have hxpos' : 0 < edgeHeight (T.point b) (T.point a) (T.point (T.edgeThird hab s)) := by
      rw [edgeHeight_swap (T.point_injective.ne hab)]
      exact neg_pos.mpr hxneg
    have hyneg := T.source_adjacent_third_height_neg hsf' htf' hab.symm hxy
      hs.2.1 hs.1 ht.2.1 ht.1 hxpos'
    rw [edgeHeight_swap (T.point_injective.ne hab)] at hyneg
    have hypos : 0 < edgeHeight (T.point a) (T.point b) (T.point (T.edgeThird hab t)) := by
      linarith
    simp [incidentSide,hxneg.not_gt,hypos] at hside
  · have hyneg := T.source_adjacent_third_height_neg hsf htf hab hxy hs.1 hs.2.1 ht.1 ht.2.1 hxpos
    simp [incidentSide,hxpos,hyneg.not_gt] at hside

theorem incidentFace_card_le_two {a b : V} (hab : a ≠ b) :
    Fintype.card (T.IncidentFace a b) ≤ 2 := by
  simpa using Fintype.card_le_of_injective _ (T.incidentSide_injective hab)

theorem incidentFace_nonempty {a b : V} (hab : T.graph.Adj a b) :
    Nonempty (T.IncidentFace a b) := by
  obtain ⟨_,s,hs,ha,hb⟩ := hab
  exact ⟨⟨⟨s,hs⟩,ha,hb⟩⟩

end Triangulation

namespace TriangularDisk

variable (D : TriangularDisk V)

theorem incidentFace_card_eq_two {a b : V} (hab : D.toTriangulation.graph.Adj a b)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary) :
    Fintype.card (D.toTriangulation.IncidentFace a b) = 2 := by
  classical
  obtain ⟨s⟩ := D.toTriangulation.incidentFace_nonempty hab
  let x := D.toTriangulation.edgeThird hab.1 s
  have hs := D.toTriangulation.edgeThird_spec hab.1 s
  have hsf : ({a,b,x} : Finset V) ∈ D.faces := hs.2.2 ▸ s.val.property
  have hxne := D.toTriangulation.edgeThird_height_ne_zero hab.1 s
  have hex : ∃ y, y ≠ a ∧ y ≠ b ∧ y ≠ x ∧ ({a,b,y} : Finset V) ∈ D.faces := by
    rcases lt_or_gt_of_ne hxne with hxneg | hxpos
    · have hsf' : ({b,a,x} : Finset V) ∈ D.faces := by
        simpa only [Finset.insert_comm] using hsf
      have hxpos' : 0 < edgeHeight (D.point b) (D.point a) (D.point x) := by
        rw [edgeHeight_swap (D.point_injective.ne hab.1)]
        exact neg_pos.mpr hxneg
      obtain ⟨y,hyb,hya,hyx,hyf,_⟩ := D.exists_opposite_face hsf' hab.1.symm hs.2.1 hs.1
        hi.symm hxpos'
      exact ⟨y,hya,hyb,hyx,by simpa only [Finset.insert_comm] using hyf⟩
    · obtain ⟨y,hya,hyb,hyx,hyf,_⟩ := D.exists_opposite_face hsf hab.1 hs.1 hs.2.1 hi hxpos
      exact ⟨y,hya,hyb,hyx,hyf⟩
  obtain ⟨y,hya,hyb,hyx,hyf⟩ := hex
  let t : D.toTriangulation.IncidentFace a b := ⟨⟨{a,b,y},hyf⟩,by simp,by simp⟩
  have hst : s ≠ t := by
    intro h
    have hsets := congrArg (fun u : D.toTriangulation.IncidentFace a b => u.val.val) h
    have hmem : y ∈ s.val.val := by rw [hsets]; simp [t]
    rw [hs.2.2] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    exact hmem.elim hya (fun h => h.elim hyb hyx)
  have hlo : 2 ≤ Fintype.card (D.toTriangulation.IncidentFace a b) := by
    have hlt : 1 < Fintype.card (D.toTriangulation.IncidentFace a b) := by
      simpa only [Finset.card_univ] using
        Finset.one_lt_card.mpr ⟨s,Finset.mem_univ s,t,Finset.mem_univ t,hst⟩
    omega
  exact le_antisymm (D.toTriangulation.incidentFace_card_le_two hab.1) hlo

theorem boundary_incidentFace_subsingleton {a b : V} (hab : a ≠ b)
    (ha : a ∈ D.boundary) (hb : b ∈ D.boundary) :
    Subsingleton (D.toTriangulation.IncidentFace a b) := by
  refine ⟨?_⟩
  intro s t
  by_contra hst
  have hs := D.toTriangulation.edgeThird_spec hab s
  have ht := D.toTriangulation.edgeThird_spec hab t
  have hxy := (D.toTriangulation.edgeThird_injective hab).ne hst
  have hsf : ({a,b,D.toTriangulation.edgeThird hab s} : Finset V) ∈ D.faces :=
    hs.2.2 ▸ s.val.property
  have htf : ({a,b,D.toTriangulation.edgeThird hab t} : Finset V) ∈ D.faces :=
    ht.2.2 ▸ t.val.property
  have hi := D.adjacent_faces_have_interior_endpoint hsf htf hab hxy hs.1 hs.2.1 ht.1 ht.2.1
  exact hi.elim (fun h => h ha) (fun h => h hb)

theorem incidentFace_card_eq_one {a b : V} (hab : D.toTriangulation.graph.Adj a b)
    (ha : a ∈ D.boundary) (hb : b ∈ D.boundary) :
    Fintype.card (D.toTriangulation.IncidentFace a b) = 1 := by
  letI := D.boundary_incidentFace_subsingleton hab.1 ha hb
  obtain ⟨s⟩ := D.toTriangulation.incidentFace_nonempty hab
  exact Fintype.card_eq_one_iff.mpr ⟨s,fun _ => Subsingleton.elim _ _⟩

end TriangularDisk

end NormalProjective.Planar

/-! ## ImageOpposite -/

/-! Actual intersection of two image triangles with opposite third vertices. -/

namespace NormalProjective.Planar

open Set

theorem triangle_height_zero_iff_edge {a b x z : ℂ}
    (hx : edgeHeight a b x ≠ 0)
    (hz : z ∈ convexHull ℝ ({a,b,x} : Set ℂ)) :
    edgeHeight a b z = 0 ↔ z ∈ segment ℝ a b := by
  let T : Triangle := ⟨![a,b,x],affineIndependent_triple_of_height_ne_zero hx⟩
  have hcarrier : T.carrier = convexHull ℝ ({a,b,x} : Set ℂ) := by
    change convexHull ℝ (Set.range ![a,b,x]) = convexHull ℝ ({a,b,x} : Set ℂ)
    congr 1
    ext w
    simp [Matrix.range_cons,or_comm,or_left_comm,or_assoc]
  have hzT : z ∈ T.carrier := hcarrier.symm ▸ hz
  simpa [T] using (T.mem_edge_iff_height_zero 0 1 2
    (by decide) (by decide) (by decide) hx hzT).symm

theorem triangles_opposite_intersection {a b x y : ℂ}
    (hab : a ≠ b) (hx : 0 < edgeHeight a b x) (hy : edgeHeight a b y < 0) :
    convexHull ℝ ({a,b,x} : Set ℂ) ∩ convexHull ℝ ({a,b,y} : Set ℂ) =
      segment ℝ a b := by
  apply Set.Subset.antisymm
  · intro z hz
    have hzpos := Triangulation.edgeHeight_nonneg_on_triangle hx.le hz.1
    have hyswap : 0 < edgeHeight b a y := by rw [edgeHeight_swap hab]; linarith
    have hzswap : z ∈ convexHull ℝ ({b,a,y} : Set ℂ) := by
      simpa only [Set.insert_comm] using hz.2
    have hzneg := Triangulation.edgeHeight_nonneg_on_triangle hyswap.le hzswap
    rw [edgeHeight_swap hab] at hzneg
    apply (triangle_height_zero_iff_edge hx.ne' hz.1).mp
    linarith
  · intro z hz
    constructor
    · exact (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hz
    · exact (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hz

theorem horizontal_segment_intersection_unique {a b z w : ℂ} {c : ℝ}
    (ha : a.im ≠ c) (hz : z ∈ segment ℝ a b) (hw : w ∈ segment ℝ a b)
    (hzc : z.im = c) (hwc : w.im = c) : z = w := by
  by_contra hzw
  exact ha (segment_endpoints_im_eq_of_two_points hz hw hzw hzc hwc).1

theorem opposite_slice_interiors_disjoint {a b x y : ℂ} {c r : ℝ}
    (hab : a ≠ b) (hx : 0 < edgeHeight a b x) (hy : edgeHeight a b y < 0)
    (ha : a.im ≠ c)
    {l₁ u₁ l₂ u₂ : ℝ}
    (hS : horizontalSlice (convexHull ℝ ({a,b,x} : Set ℂ)) c = Icc l₁ u₁)
    (hT : horizontalSlice (convexHull ℝ ({a,b,y} : Set ℂ)) c = Icc l₂ u₂)
    (hr₁ : l₁ < r ∧ r < u₁) (hr₂ : l₂ < r ∧ r < u₂) : False := by
  let s := (r + min u₁ u₂)/2
  have hsr : r < s := by dsimp [s]; linarith [lt_min hr₁.2 hr₂.2]
  have hsu₁ : s < u₁ := by dsimp [s]; linarith [min_le_left u₁ u₂]
  have hsu₂ : s < u₂ := by dsimp [s]; linarith [min_le_right u₁ u₂]
  have hpoint (t : ℝ) (ht₁ : t ∈ Icc l₁ u₁) (ht₂ : t ∈ Icc l₂ u₂) :
      horizontalPoint c t ∈ segment ℝ a b := by
    rw [← triangles_opposite_intersection hab hx hy]
    exact ⟨(Set.ext_iff.mp hS t).mpr ht₁,(Set.ext_iff.mp hT t).mpr ht₂⟩
  have hsame := horizontal_segment_intersection_unique ha
    (hpoint r ⟨hr₁.1.le,hr₁.2.le⟩ ⟨hr₂.1.le,hr₂.2.le⟩)
    (hpoint s ⟨(hr₁.1.trans hsr).le,hsu₁.le⟩ ⟨(hr₂.1.trans hsr).le,hsu₂.le⟩)
    (horizontalPoint_im c r) (horizontalPoint_im c s)
  have hreal := congrArg Complex.re hsame
  simp only [horizontalPoint_re] at hreal
  exact hsr.ne hreal

end NormalProjective.Planar

/-! ## TriangleNeighborhood -/

/-! Two actual triangles on opposite sides cover a neighborhood of their shared open edge. -/

namespace NormalProjective.Planar

open Set Filter
open scoped Topology

theorem opposite_triangle_union_mem_nhds {a b x y z : ℂ}
    (hx : 0 < edgeHeight a b x) (hy : edgeHeight a b y < 0)
    (hz : z ∈ openSegment ℝ a b) :
    convexHull ℝ ({a,b,x} : Set ℂ) ∪ convexHull ℝ ({a,b,y} : Set ℂ) ∈ 𝓝 z := by
  let S : Triangle := ⟨![a,b,x],affineIndependent_triple_of_height_ne_zero hx.ne'⟩
  let T : Triangle := ⟨![a,b,y],affineIndependent_triple_of_height_ne_zero hy.ne⟩
  have hS : S.carrier = convexHull ℝ ({a,b,x} : Set ℂ) := by
    change convexHull ℝ (Set.range ![a,b,x]) = convexHull ℝ ({a,b,x} : Set ℂ)
    congr 1
    ext w
    simp [Matrix.range_cons,or_comm,or_left_comm,or_assoc]
  have hT : T.carrier = convexHull ℝ ({a,b,y} : Set ℂ) := by
    change convexHull ℝ (Set.range ![a,b,y]) = convexHull ℝ ({a,b,y} : Set ℂ)
    congr 1
    ext w
    simp [Matrix.range_cons,or_comm,or_left_comm,or_assoc]
  have hs := S.locally_carrier_is_halfplane_at_openEdge 0 1 2
    (by decide) (by decide) (by decide) hz
  have ht := T.locally_carrier_is_halfplane_at_openEdge 0 1 2
    (by decide) (by decide) (by decide) hz
  change ∀ᶠ u in 𝓝 z, u ∈ convexHull ℝ ({a,b,x} : Set ℂ) ∪
    convexHull ℝ ({a,b,y} : Set ℂ)
  filter_upwards [hs,ht] with u hsu htu
  have hsheight := S.coord_mul_height 0 1 2 (by decide) (by decide) (by decide) u
  have htheight := T.coord_mul_height 0 1 2 (by decide) (by decide) (by decide) u
  change S.coord 2 u * edgeHeight a b x = edgeHeight a b u at hsheight
  change T.coord 2 u * edgeHeight a b y = edgeHeight a b u at htheight
  rcases le_total 0 (edgeHeight a b u) with hu | hu
  · left
    rw [← hS,hsu]
    nlinarith
  · right
    rw [← hT,htu]
    nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V) (q : V → ℂ)
  (hind : ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q v.val))

 include hind in
 theorem drawing_frontier_point_on_open_edge (s : T.Face) {z : ℂ}
    (hz : z ∈ frontier (simplex q s.val)) (hv : ∀ v ∈ s.val, z ≠ q v) :
    ∃ a b : V, a ≠ b ∧ a ∈ s.val ∧ b ∈ s.val ∧
      z ∈ openSegment ℝ (q a) (q b) := by
  have hz' : z ∈ frontier (T.drawingTriangle q hind s).carrier := by
    simpa only [T.drawingTriangle_carrier] using hz
  obtain ⟨i,j,k,hij,hik,hjk,hzedge,_⟩ :=
    (T.drawingTriangle q hind s).frontier_point_on_open_edge hz'
      (fun i => hv _ (T.faceEnumeration s i).property)
  exact ⟨(T.faceEnumeration s i).val,(T.faceEnumeration s j).val,
    fun h => hij ((T.faceEnumeration s).injective (Subtype.ext h)),
    (T.faceEnumeration s i).property,(T.faceEnumeration s j).property,hzedge⟩

 include hind in
 theorem drawing_vertex_not_mem_opposite_face (s : T.Face) {v : V} (hv : v ∈ s.val) :
    q v ∉ simplex q (s.val.erase v) := by
  intro hx
  have hmem : q v ∈ simplex q (({v} : Finset V) ∩ s.val.erase v) := by
    rw [← independent_subface_intersection q (hind s)
      (Finset.singleton_subset_iff.mpr hv) (Finset.erase_subset _ _)]
    exact ⟨by simp [simplex],hx⟩
  simpa [simplex] using hmem

end Triangulation

end NormalProjective.Planar

/-! ## HarmonicImageAdjacency -/

/-!
# Exact image intersections across an actual interior edge

The nonfolding conclusion here is derived from the checked harmonic adjacent-face
lemma. It is not an assumption on the new drawing.
-/

namespace NormalProjective.Planar

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TriangularDisk

variable (D : TriangularDisk V) (w : V → V → ℝ)
  (hw : ∀ i j, 0 ≤ w i j)
  (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
  (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
  (q : V → ℂ) (hq : D.IsHarmonicDrawing w q)

 include hw he hoff hq in
 theorem harmonic_adjacent_image_intersection {s t : D.toTriangulation.Face}
    (hst : s ≠ t) {a b : V} (hab : a ≠ b)
    (has : a ∈ s.val) (hbs : b ∈ s.val) (hat : a ∈ t.val) (hbt : b ∈ t.val) :
    simplex q s.val ∩ simplex q t.val = segment ℝ (q a) (q b) := by
  obtain ⟨x,hxa,hxb,hsx⟩ := triangle_eq_insert_pair (D.face_card s.val s.property) hab has hbs
  obtain ⟨y,hya,hyb,hty⟩ := triangle_eq_insert_pair (D.face_card t.val t.property) hab hat hbt
  have hxy : x ≠ y := by
    intro h
    apply hst
    apply Subtype.ext
    rw [hsx,hty,h]
  have hsf : ({a,b,x} : Finset V) ∈ D.faces := hsx ▸ s.property
  have htf : ({a,b,y} : Finset V) ∈ D.faces := hty ▸ t.property
  have hsind := D.harmonic_face_independent w hw he hoff q hq s.val s.property
  have hxne := height_ne_zero_of_face_independent q hsind has hbs
    (by rw [hsx]; simp) hab hxa hxb
  have habq : q a ≠ q b := by
    intro h
    exact hab (congrArg Subtype.val (hsind.injective
      (a₁ := ⟨a,has⟩) (a₂ := ⟨b,hbs⟩) h))
  have hzeroa : edgeHeight (q a) (q b) (q a) = 0 := by simp [edgeHeight,edgeNormalize]
  have hzerob : edgeHeight (q a) (q b) (q b) = 0 := by
    simp [edgeHeight,edgeNormalize_right habq]
  rw [hsx,hty]
  simp only [simplex,Finset.coe_insert,Finset.coe_singleton,Set.image_insert_eq,Set.image_singleton]
  rcases lt_or_gt_of_ne hxne with hxneg | hxpos
  · have hypos : 0 < edgeHeight (q a) (q b) (q y) := by
      have hy := D.harmonic_height_negative_across_edge w hw he hoff
        (fun z => -edgeHeight (q a) (q b) (q z))
        (fun z hz => Dirichlet.harmonic_neg (IsHarmonicDrawing.height_harmonic D hq hz _ _))
        hsf htf hab hxy hxa hxb hya hyb (by simp [hzeroa]) (by simp [hzerob])
        (neg_pos.mpr hxneg)
      linarith
    rw [Set.inter_comm]
    exact triangles_opposite_intersection habq hypos hxneg
  · have hyneg := D.harmonic_height_negative_across_edge w hw he hoff
      (fun z => edgeHeight (q a) (q b) (q z))
      (fun z hz => IsHarmonicDrawing.height_harmonic D hq hz _ _) hsf htf hab hxy hxa hxb hya hyb
      hzeroa hzerob hxpos
    exact triangles_opposite_intersection habq hxpos hyneg

 include hw he hoff hq in
 theorem harmonic_adjacent_image_union_mem_nhds {s t : D.toTriangulation.Face}
    (hst : s ≠ t) {a b : V} (hab : a ≠ b)
    (has : a ∈ s.val) (hbs : b ∈ s.val) (hat : a ∈ t.val) (hbt : b ∈ t.val)
    {z : ℂ} (hz : z ∈ openSegment ℝ (q a) (q b)) :
    simplex q s.val ∪ simplex q t.val ∈ nhds z := by
  obtain ⟨x,hxa,hxb,hsx⟩ := triangle_eq_insert_pair (D.face_card s.val s.property) hab has hbs
  obtain ⟨y,hya,hyb,hty⟩ := triangle_eq_insert_pair (D.face_card t.val t.property) hab hat hbt
  have hxy : x ≠ y := by
    intro h
    apply hst
    apply Subtype.ext
    rw [hsx,hty,h]
  have hsf : ({a,b,x} : Finset V) ∈ D.faces := hsx ▸ s.property
  have htf : ({a,b,y} : Finset V) ∈ D.faces := hty ▸ t.property
  have hsind := D.harmonic_face_independent w hw he hoff q hq s.val s.property
  have hxne := height_ne_zero_of_face_independent q hsind has hbs
    (by rw [hsx]; simp) hab hxa hxb
  have habq : q a ≠ q b := by
    intro h
    exact hab (congrArg Subtype.val (hsind.injective
      (a₁ := ⟨a,has⟩) (a₂ := ⟨b,hbs⟩) h))
  have hzeroa : edgeHeight (q a) (q b) (q a) = 0 := by simp [edgeHeight,edgeNormalize]
  have hzerob : edgeHeight (q a) (q b) (q b) = 0 := by
    simp [edgeHeight,edgeNormalize_right habq]
  rw [hsx,hty]
  simp only [simplex,Finset.coe_insert,Finset.coe_singleton,Set.image_insert_eq,Set.image_singleton]
  rcases lt_or_gt_of_ne hxne with hxneg | hxpos
  · have hypos : 0 < edgeHeight (q a) (q b) (q y) := by
      have hy := D.harmonic_height_negative_across_edge w hw he hoff
        (fun z => -edgeHeight (q a) (q b) (q z))
        (fun z hz => Dirichlet.harmonic_neg (IsHarmonicDrawing.height_harmonic D hq hz _ _))
        hsf htf hab hxy hxa hxb hya hyb (by simp [hzeroa]) (by simp [hzerob])
        (neg_pos.mpr hxneg)
      linarith
    rw [Set.union_comm]
    exact opposite_triangle_union_mem_nhds hypos hxneg hz
  · have hyneg := D.harmonic_height_negative_across_edge w hw he hoff
      (fun z => edgeHeight (q a) (q b) (q z))
      (fun z hz => IsHarmonicDrawing.height_harmonic D hq hz _ _) hsf htf hab hxy hxa hxb hya hyb
      hzeroa hzerob hxpos
    exact opposite_triangle_union_mem_nhds hxpos hyneg hz

 theorem incident_faces_unique_other {a b : V} (hab : a ≠ b)
    {s t u : D.toTriangulation.IncidentFace a b} (hs : s ≠ u) (ht : t ≠ u) : s = t := by
  classical
  by_contra hst
  have hcard : ({s,t,u} : Finset (D.toTriangulation.IncidentFace a b)).card = 3 := by
    simp [hst,hs,ht]
  have hc := Finset.card_le_card (Finset.subset_univ
    ({s,t,u} : Finset (D.toTriangulation.IncidentFace a b)))
  rw [hcard,Finset.card_univ] at hc
  have hu := D.toTriangulation.incidentFace_card_le_two hab
  omega

 theorem exists_other_incident_face {s : D.toTriangulation.Face} {a b : V}
    (hab : a ≠ b) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary) :
    ∃ t : D.toTriangulation.Face, t ≠ s ∧ a ∈ t.val ∧ b ∈ t.val := by
  classical
  have hgraph : D.toTriangulation.graph.Adj a b := ⟨hab,s.val,s.property,ha,hb⟩
  have hc := D.incidentFace_card_eq_two hgraph hi
  let s' : D.toTriangulation.IncidentFace a b := ⟨s,ha,hb⟩
  have hex : ∃ t : D.toTriangulation.IncidentFace a b, t ≠ s' := by
    by_contra! h
    haveI : Subsingleton (D.toTriangulation.IncidentFace a b) :=
      ⟨fun x y => (h x).trans (h y).symm⟩
    have hle : Fintype.card (D.toTriangulation.IncidentFace a b) ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  obtain ⟨t,ht⟩ := hex
  refine ⟨t.val,?_,t.property.1,t.property.2⟩
  intro h
  exact ht (Subtype.ext h)

end TriangularDisk

namespace Triangulation

variable (T : Triangulation V) (q : V → ℂ)
  (hind : ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q v.val))

 include hind in
 theorem drawing_slice_endpoint_edges (c : ℝ) (hgeneric : ∀ v, (q v).im ≠ c)
    (s : T.Face) (hne : (horizontalSlice (simplex q s.val) c).Nonempty) :
    (∃ a b : V, a ≠ b ∧ a ∈ s.val ∧ b ∈ s.val ∧
      horizontalPoint c (sInf (horizontalSlice (simplex q s.val) c)) ∈
        openSegment ℝ (q a) (q b)) ∧
    (∃ a b : V, a ≠ b ∧ a ∈ s.val ∧ b ∈ s.val ∧
      horizontalPoint c (sSup (horizontalSlice (simplex q s.val) c)) ∈
        openSegment ℝ (q a) (q b)) := by
  have hne' : (horizontalSlice (T.drawingTriangle q hind s).carrier c).Nonempty := by
    simpa only [T.drawingTriangle_carrier] using hne
  have h := (T.drawingTriangle q hind s).slice_endpoint_on_open_edge c
    (T.drawingTriangle_generic q hind c hgeneric s) hne'
  constructor
  · obtain ⟨i,j,k,hij,hik,hjk,hz,hcoord⟩ := h.1
    refine ⟨(T.faceEnumeration s i).val,(T.faceEnumeration s j).val,?_,
      (T.faceEnumeration s i).property,(T.faceEnumeration s j).property,?_⟩
    · intro h
      exact hij ((T.faceEnumeration s).injective (Subtype.ext h))
    · rw [T.drawingTriangle_carrier] at hz
      simpa only [drawingTriangle] using hz
  · obtain ⟨i,j,k,hij,hik,hjk,hz,hcoord⟩ := h.2
    refine ⟨(T.faceEnumeration s i).val,(T.faceEnumeration s j).val,?_,
      (T.faceEnumeration s i).property,(T.faceEnumeration s j).property,?_⟩
    · intro h
      exact hij ((T.faceEnumeration s).injective (Subtype.ext h))
    · rw [T.drawingTriangle_carrier] at hz
      simpa only [drawingTriangle] using hz

end Triangulation

end NormalProjective.Planar

/- The finite interval-chain results are imported from the checked IntervalChain module. -/

/-! ## HorizontalDrawing -/

/-!
# The actual generic-line walk in the harmonic drawing

The finite relation below is built from actual image edges and actual adjacent
faces. Its termination and uniqueness hypotheses are derived geometrically.
-/

namespace NormalProjective.Planar

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TriangularDisk

variable (D : TriangularDisk V)

def CutFace (q : V → ℂ) (c : ℝ) :=
  {s : D.toTriangulation.Face // (horizontalSlice (simplex q s.val) c).Nonempty}

instance (q : V → ℂ) (c : ℝ) : Fintype (D.CutFace q c) := by
  classical
  unfold CutFace
  infer_instance

def cutLo (q : V → ℂ) (c : ℝ) (s : D.CutFace q c) : ℝ :=
  sInf (horizontalSlice (simplex q s.val.val) c)

def cutHi (q : V → ℂ) (c : ℝ) (s : D.CutFace q c) : ℝ :=
  sSup (horizontalSlice (simplex q s.val.val) c)

def NextCut (q : V → ℂ) (c : ℝ) (s t : D.CutFace q c) : Prop :=
  D.cutHi q c s = D.cutLo q c t ∧
  ∃ a b : V, a ≠ b ∧ a ∈ s.val.val ∧ b ∈ s.val.val ∧
    a ∈ t.val.val ∧ b ∈ t.val.val ∧
    horizontalPoint c (D.cutHi q c s) ∈ openSegment ℝ (q a) (q b)

variable (w : V → V → ℝ) (hw : ∀ i j, 0 ≤ w i j)
  (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
  (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
  (q : V → ℂ) (hq : D.IsHarmonicDrawing w q)
  (c : ℝ) (hgeneric : ∀ v, (q v).im ≠ c)

 include hw he hoff hq hgeneric in
 theorem cutLo_lt_cutHi (s : D.CutFace q c) : D.cutLo q c s < D.cutHi q c s := by
  let hind := fun s : D.toTriangulation.Face =>
    D.harmonic_face_independent w hw he hoff q hq s.val s.property
  have h := (D.toTriangulation.drawingTriangle q hind s.val).generic_slice_inf_lt_sup c
    (D.toTriangulation.drawingTriangle_generic q hind c hgeneric s.val)
    (by simpa only [D.toTriangulation.drawingTriangle_carrier] using s.property)
  simpa only [D.toTriangulation.drawingTriangle_carrier,cutLo,cutHi] using h

 theorem cutSlice_eq (s : D.CutFace q c) :
    horizontalSlice (simplex q s.val.val) c = Icc (D.cutLo q c s) (D.cutHi q c s) :=
  horizontalSlice_eq_Icc (simplex_isCompact q _) (convex_convexHull ℝ _) c s.property

 include hw he hq in
 theorem cut_bounds (s : D.CutFace q c) : 0 ≤ D.cutLo q c s ∧ D.cutHi q c s ≤ 1-c := by
  have hsub : simplex q s.val.val ⊆ baseTriangle :=
    D.toTriangulation.drawing_cell_subset q baseTriangle_convex
      (fun v => D.drawing_coordinates_nonnegative w hw he q hq v) s.val
  have hlo : horizontalPoint c (D.cutLo q c s) ∈ simplex q s.val.val :=
    (compact_horizontalSlice (simplex_isCompact q _) c).sInf_mem s.property
  have hhi : horizontalPoint c (D.cutHi q c s) ∈ simplex q s.val.val :=
    (compact_horizontalSlice (simplex_isCompact q _) c).sSup_mem s.property
  have ha := hsub hlo 1
  have hb := hsub hhi 0
  simp only [triangleCoordinate,horizontalPoint_re,horizontalPoint_im] at ha hb
  change 0 ≤ D.cutLo q c s at ha
  change 0 ≤ 1 - D.cutHi q c s - c at hb
  exact ⟨ha,by linarith⟩

 include hw he hoff hq hgeneric in
 theorem cut_common_point_unique {s t : D.CutFace q c} (hst : s.val ≠ t.val)
    {a b : V} (hab : a ≠ b)
    (has : a ∈ s.val.val) (hbs : b ∈ s.val.val)
    (hat : a ∈ t.val.val) (hbt : b ∈ t.val.val)
    {r u : ℝ}
    (hrs : r ∈ Icc (D.cutLo q c s) (D.cutHi q c s))
    (hrt : r ∈ Icc (D.cutLo q c t) (D.cutHi q c t))
    (hus : u ∈ Icc (D.cutLo q c s) (D.cutHi q c s))
    (hut : u ∈ Icc (D.cutLo q c t) (D.cutHi q c t)) : r = u := by
  have hinter := D.harmonic_adjacent_image_intersection w hw he hoff q hq
    hst hab has hbs hat hbt
  have hr : horizontalPoint c r ∈ segment ℝ (q a) (q b) := by
    rw [← hinter]
    exact ⟨(Set.ext_iff.mp (D.cutSlice_eq q c s) r).mpr hrs,
      (Set.ext_iff.mp (D.cutSlice_eq q c t) r).mpr hrt⟩
  have hu : horizontalPoint c u ∈ segment ℝ (q a) (q b) := by
    rw [← hinter]
    exact ⟨(Set.ext_iff.mp (D.cutSlice_eq q c s) u).mpr hus,
      (Set.ext_iff.mp (D.cutSlice_eq q c t) u).mpr hut⟩
  have hh := horizontal_segment_intersection_unique (hgeneric a) hr hu
    (horizontalPoint_im c r) (horizontalPoint_im c u)
  simpa only [horizontalPoint_re] using congrArg Complex.re hh

 include hw he hoff hq hgeneric in
 theorem cut_has_successor (s : D.CutFace q c) (hnot : D.cutHi q c s ≠ 1-c) :
    ∃ t : D.CutFace q c, D.NextCut q c s t := by
  classical
  let hind := fun s : D.toTriangulation.Face =>
    D.harmonic_face_independent w hw he hoff q hq s.val s.property
  obtain ⟨a,b,hab,ha,hb,hz⟩ :=
    (D.toTriangulation.drawing_slice_endpoint_edges q hind c hgeneric s.val s.property).2
  have hheight := D.generic_slice_height_range w hw he q hq c hgeneric s.property
  have hbounds := D.cut_bounds w hw he q hq c s
  have hinterval := D.cutLo_lt_cutHi w hw he hoff q hq c hgeneric s
  have hhi : D.cutHi q c s < 1-c := lt_of_le_of_ne hbounds.2 hnot
  have hzpos : ∀ j, 0 < triangleCoordinate j (horizontalPoint c (D.cutHi q c s)) := by
    intro j
    fin_cases j <;> simp only [triangleCoordinate,horizontalPoint_re,horizontalPoint_im]
    · change 0 < 1 - D.cutHi q c s - c
      linarith
    · change 0 < D.cutHi q c s
      linarith
    · change 0 < c
      exact hheight.1
  have hi := D.strict_coordinate_open_edge_interior w hw he q hq hab hz hzpos
  obtain ⟨t,hts,hat,hbt⟩ := D.exists_other_incident_face hab ha hb hi
  have hzt : horizontalPoint c (D.cutHi q c s) ∈ simplex q t.val :=
    (convex_convexHull ℝ (q '' (t.val : Set V))).segment_subset
      (point_mem_simplex q t.val hat)
      (point_mem_simplex q t.val hbt) (openSegment_subset_segment ℝ _ _ hz)
  let t' : D.CutFace q c := ⟨t,⟨D.cutHi q c s,hzt⟩⟩
  have hzt' : D.cutHi q c s ∈ Icc (D.cutLo q c t') (D.cutHi q c t') :=
    (Set.ext_iff.mp (D.cutSlice_eq q c t') _).mp hzt
  have heq : D.cutHi q c s = D.cutLo q c t' := by
    apply le_antisymm
    · by_contra hn
      have hlt : D.cutLo q c t' < D.cutHi q c s := lt_of_not_ge hn
      let r := (max (D.cutLo q c s) (D.cutLo q c t') + D.cutHi q c s)/2
      have hmax : max (D.cutLo q c s) (D.cutLo q c t') < D.cutHi q c s :=
        max_lt hinterval hlt
      have hrl : max (D.cutLo q c s) (D.cutLo q c t') < r := by dsimp [r]; linarith
      have hru : r < D.cutHi q c s := by dsimp [r]; linarith
      have hrs : r ∈ Icc (D.cutLo q c s) (D.cutHi q c s) :=
        ⟨(le_max_left _ _).trans hrl.le,hru.le⟩
      have hrt : r ∈ Icc (D.cutLo q c t') (D.cutHi q c t') :=
        ⟨(le_max_right _ _).trans hrl.le,hru.le.trans hzt'.2⟩
      have heq := D.cut_common_point_unique w hw he hoff q hq c hgeneric
        hts.symm hab ha hb hat hbt hrs hrt ⟨hinterval.le,le_rfl⟩ hzt'
      exact hru.ne heq
    · exact hzt'.1
  exact ⟨t',heq,a,b,hab,ha,hb,hat,hbt,hz⟩

 include hw he hoff hq hgeneric in
 theorem nextCut_predecessor_unique {s t k : D.CutFace q c}
    (hs : D.NextCut q c s k) (ht : D.NextCut q c t k) : s = t := by
  classical
  obtain ⟨hsk,a,b,hab,has,hbs,hak,hbk,hzab⟩ := hs
  obtain ⟨htk,u,v,huv,hut,hvt,huk,hvk,hzuv⟩ := ht
  have hzsame : D.cutHi q c s = D.cutHi q c t := hsk.trans htk.symm
  have hpairs : ({a,b} : Finset V) = {u,v} := by
    apply two_edges_eq_of_intersection_away_vertices q
      (z := horizontalPoint c (D.cutHi q c s))
      (D.harmonic_face_independent w hw he hoff q hq k.val.val k.val.property)
      (by simp [Finset.insert_subset_iff,has,hak,hbk])
      (by simp [Finset.insert_subset_iff,huk,hvk])
      (by simp [hab]) (by simp [huv])
    · simpa [simplex,convexHull_pair] using openSegment_subset_segment ℝ _ _ hzab
    · simpa [simplex,convexHull_pair,hzsame] using openSegment_subset_segment ℝ _ _ hzuv
    · intro x hx
      exact hgeneric x (by simpa only [horizontalPoint_im] using congrArg Complex.im hx.symm)
  have hat : a ∈ t.val.val := by
    have h : a ∈ ({u,v} : Finset V) := hpairs ▸ (by simp : a ∈ ({a,b} : Finset V))
    rcases Finset.mem_insert.mp h with h | h
    · exact h.symm ▸ hut
    · exact (Finset.mem_singleton.mp h).symm ▸ hvt
  have hbt : b ∈ t.val.val := by
    have h : b ∈ ({u,v} : Finset V) := hpairs ▸ (by simp : b ∈ ({a,b} : Finset V))
    rcases Finset.mem_insert.mp h with h | h
    · exact h.symm ▸ hut
    · exact (Finset.mem_singleton.mp h).symm ▸ hvt
  let s' : D.toTriangulation.IncidentFace a b := ⟨s.val,has,hbs⟩
  let t' : D.toTriangulation.IncidentFace a b := ⟨t.val,hat,hbt⟩
  let k' : D.toTriangulation.IncidentFace a b := ⟨k.val,hak,hbk⟩
  have hsk' : s' ≠ k' := by
    intro h
    have hval : s = k := Subtype.ext
      (congrArg (fun u : D.toTriangulation.IncidentFace a b => u.val) h)
    subst s
    exact (D.cutLo_lt_cutHi w hw he hoff q hq c hgeneric k).ne hsk.symm
  have htk' : t' ≠ k' := by
    intro h
    have hval : t = k := Subtype.ext
      (congrArg (fun u : D.toTriangulation.IncidentFace a b => u.val) h)
    subst t
    exact (D.cutLo_lt_cutHi w hw he hoff q hq c hgeneric k).ne htk.symm
  exact Subtype.ext (congrArg
    (fun u : D.toTriangulation.IncidentFace a b => u.val)
    (D.incident_faces_unique_other hab hsk' htk'))

 include hw he hoff hq hgeneric in
 theorem terminalCut_unique {s t : D.CutFace q c}
    (hs : D.cutHi q c s = 1-c) (ht : D.cutHi q c t = 1-c) : s = t := by
  classical
  let hind := fun s : D.toTriangulation.Face =>
    D.harmonic_face_independent w hw he hoff q hq s.val s.property
  have hcontains (k : D.CutFace q c) (hk : D.cutHi q c k = 1-c) :
      D.corner 1 ∈ k.val.val ∧ D.corner 2 ∈ k.val.val := by
    obtain ⟨a,b,hab,ha,hb,hz⟩ :=
      (D.toTriangulation.drawing_slice_endpoint_edges q hind c hgeneric k.val k.property).2
    change horizontalPoint c (D.cutHi q c k) ∈ _ at hz
    rw [hk] at hz
    have heq := D.open_edge_at_right_boundary w hw he q hq hab hz
    have hsub : ({a,b} : Finset V) ⊆ k.val.val :=
      Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
    rw [heq] at hsub
    exact ⟨hsub (by simp),hsub (by simp)⟩
  have hcs := hcontains s hs
  have hct := hcontains t ht
  have hsub : Subsingleton
      (D.toTriangulation.IncidentFace (D.corner 1) (D.corner 2)) :=
    D.boundary_incidentFace_subsingleton
      (D.corner.injective.ne (by decide : (1 : Fin 3) ≠ 2)) ⟨1,rfl⟩ ⟨2,rfl⟩
  have heq : (⟨s.val,hcs.1,hcs.2⟩ : D.toTriangulation.IncidentFace (D.corner 1) (D.corner 2)) =
      ⟨t.val,hct.1,hct.2⟩ :=
    @Subsingleton.elim (D.toTriangulation.IncidentFace (D.corner 1) (D.corner 2))
      hsub ⟨s.val,hcs.1,hcs.2⟩ ⟨t.val,hct.1,hct.2⟩
  exact Subtype.ext (congrArg
    (fun u : D.toTriangulation.IncidentFace (D.corner 1) (D.corner 2) => u.val) heq)

 include hw he hoff hq hgeneric in
 theorem harmonic_generic_cut_interiors_disjoint {s t : D.CutFace q c} {x : ℝ}
    (hs : D.cutLo q c s < x ∧ x < D.cutHi q c s)
    (ht : D.cutLo q c t < x ∧ x < D.cutHi q c t) : s = t := by
  classical
  apply interval_chain_interiors_disjoint (D.cutLo q c) (D.cutHi q c)
    (D.cutLo_lt_cutHi w hw he hoff q hq c hgeneric)
    (D.NextCut q c) (fun _ _ h => h.1)
    (fun _ _ _ hs ht => D.nextCut_predecessor_unique w hw he hoff q hq c hgeneric hs ht)
    (fun s => D.cutHi q c s = 1-c)
    (fun _ _ hs ht => D.terminalCut_unique w hw he hoff q hq c hgeneric hs ht)
    (fun s hs => D.cut_has_successor w hw he hoff q hq c hgeneric s hs) hs ht

end TriangularDisk

end NormalProjective.Planar

/-! ## ImageStars -/

/-!
# Actual local image neighborhoods at interior vertices

A punctured small ball is connected. Within that ball the finite image star has
no possible boundary: every remaining radial edge is shared with an image
triangle on the opposite side. The proof therefore derives a neighborhood in
the image star, without assuming global injectivity or a cyclic vertex link.
-/

namespace NormalProjective.Planar

open Set Finset Filter Metric
open scoped Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

def StarFace (v : V) := {s : T.Face // v ∈ s.val}

instance (v : V) : Fintype (T.StarFace v) := by
  classical
  unfold StarFace
  infer_instance

def imageStar (q : V → ℂ) (v : V) : Set ℂ :=
  ⋃ s : T.StarFace v, simplex q s.val.val

def imageOppositeStar (q : V → ℂ) (v : V) : Set ℂ :=
  ⋃ s : T.StarFace v, simplex q (s.val.val.erase v)

 theorem imageStar_closed (q : V → ℂ) (v : V) : IsClosed (T.imageStar q v) :=
  isClosed_iUnion_of_finite (fun s => (simplex_isCompact q _).isClosed)

 theorem imageOppositeStar_closed (q : V → ℂ) (v : V) : IsClosed (T.imageOppositeStar q v) :=
  isClosed_iUnion_of_finite (fun s => (simplex_isCompact q _).isClosed)

 theorem vertex_mem_imageStar (q : V → ℂ) (v : V) : q v ∈ T.imageStar q v := by
  obtain ⟨s,hs,hv⟩ := T.vertex_covered v
  exact mem_iUnion.mpr ⟨⟨⟨s,hs⟩,hv⟩,point_mem_simplex q s hv⟩

 theorem drawing_vertex_not_interior_face (q : V → ℂ)
    (hind : ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q v.val))
    (s : T.Face) {v : V} (hv : v ∈ s.val) : q v ∉ interior (simplex q s.val) := by
  let A := T.drawingTriangle q hind s
  let i := (T.faceEnumeration s).symm ⟨v,hv⟩
  have hi : A.point i = q v := by simp [A,i,drawingTriangle]
  obtain ⟨j,hji⟩ := exists_ne i
  intro hz
  have hz' : q v ∈ interior A.carrier := by
    simpa only [A,T.drawingTriangle_carrier] using hz
  have hp := (A.mem_interior_iff _).mp hz' j
  rw [← hi,A.coord_point,if_neg hji] at hp
  exact lt_irrefl _ hp

end Triangulation

namespace TriangularDisk

variable (D : TriangularDisk V) (w : V → V → ℝ)
  (hw : ∀ i j, 0 ≤ w i j)
  (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
  (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
  (q : V → ℂ) (hq : D.IsHarmonicDrawing w q)

 include hw he hoff hq in
 theorem imageStar_mem_nhds_of_interior {v : V} (hv : v ∉ D.boundary) :
    D.toTriangulation.imageStar q v ∈ 𝓝 (q v) := by
  classical
  let T := D.toTriangulation
  let hind := fun s : T.Face => D.harmonic_face_independent w hw he hoff q hq s.val s.property
  let S := T.imageStar q v
  let O := T.imageOppositeStar q v
  have hSclosed : IsClosed S := T.imageStar_closed q v
  have hOclosed : IsClosed O := T.imageOppositeStar_closed q v
  have hnot : q v ∉ O := by
    intro h
    obtain ⟨s,hs⟩ := mem_iUnion.mp h
    exact T.drawing_vertex_not_mem_opposite_face q hind s.val s.property hs
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hOclosed.isOpen_compl.mem_nhds hnot)
  let U : Set ℂ := ball (q v) ε \ {q v}
  have hU : IsPreconnected U := isPreconnected_convex_sdiff_countable
    (convex_ball _ _) isOpen_ball (Set.countable_singleton _)
    (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two)
  have hlocal : S ∩ U ⊆ interior S := by
    rintro y ⟨hyS,hyball,hyne⟩
    obtain ⟨s,hys⟩ := mem_iUnion.mp hyS
    have hyo : y ∉ O := hball hyball
    have hynotop : y ∉ simplex q (s.val.val.erase v) := by
      intro h
      exact hyo (mem_iUnion.mpr ⟨s,h⟩)
    have hnotvertex : ∀ u ∈ s.val.val, y ≠ q u := by
      intro u hu hyu
      by_cases huv : u = v
      · exact hyne (by simp [hyu,huv])
      · exact hynotop (hyu.symm ▸ point_mem_simplex q _ (Finset.mem_erase.mpr ⟨huv,hu⟩))
    by_cases hyint : y ∈ interior (simplex q s.val.val)
    · exact interior_mono (fun z hz => mem_iUnion.mpr ⟨s,hz⟩) hyint
    have hyfront : y ∈ frontier (simplex q s.val.val) :=
      ⟨subset_closure hys,hyint⟩
    obtain ⟨a,b,hab,ha,hb,hyedge⟩ := T.drawing_frontier_point_on_open_edge q hind s.val
      hyfront hnotvertex
    have hvab : v = a ∨ v = b := by
      by_contra! h
      have hsub : ({a,b} : Finset V) ⊆ s.val.val.erase v := by
        simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.mem_erase]
        exact ⟨⟨h.1.symm,ha⟩,h.2.symm,hb⟩
      apply hynotop
      apply convexHull_mono (Set.image_mono hsub)
      simpa [simplex,convexHull_pair] using openSegment_subset_segment ℝ _ _ hyedge
    have hi : a ∉ D.boundary ∨ b ∉ D.boundary := by
      rcases hvab with rfl | rfl
      · exact Or.inl hv
      · exact Or.inr hv
    obtain ⟨t,hts,hat,hbt⟩ := D.exists_other_incident_face hab ha hb hi
    have hvt : v ∈ t.val := hvab.elim (fun h => h.symm ▸ hat) (fun h => h.symm ▸ hbt)
    let t' : T.StarFace v := ⟨t,hvt⟩
    have hN := D.harmonic_adjacent_image_union_mem_nhds w hw he hoff q hq
      hts.symm hab ha hb hat hbt hyedge
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset hN
    intro z hz
    exact hz.elim (fun h => mem_iUnion.mpr ⟨s,h⟩) (fun h => mem_iUnion.mpr ⟨t',h⟩)
  have hnonempty : (U ∩ interior S).Nonempty := by
    obtain ⟨s,hs,hvs⟩ := T.vertex_covered v
    let s' : T.Face := ⟨s,hs⟩
    let A := T.drawingTriangle q hind s'
    have hcompact := simplex_isCompact q s
    have hinterior : (interior (simplex q s)).Nonempty := by
      simpa only [A,T.drawingTriangle_carrier] using A.interior_nonempty
    have hclosure : closure (interior (simplex q s)) = simplex q s := by
      unfold simplex
      rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hinterior]
      exact hcompact.isClosed.closure_eq
    have hqclosure : q v ∈ closure (interior (simplex q s)) :=
      hclosure.symm ▸ point_mem_simplex q s hvs
    obtain ⟨z,hzball,hzint⟩ := mem_closure_iff_nhds.mp hqclosure _
      (Metric.ball_mem_nhds _ hε)
    have hzneq : z ≠ q v := by
      intro h
      exact T.drawing_vertex_not_interior_face q hind s' hvs (h ▸ hzint)
    have hzS : z ∈ S := mem_iUnion.mpr ⟨⟨s',hvs⟩,interior_subset hzint⟩
    have hzU : z ∈ U := ⟨hzball,by simpa using hzneq⟩
    exact ⟨z,hzU,hlocal ⟨hzS,hzU⟩⟩
  have hUsub : U ⊆ interior S := hU.subset_of_closure_inter_subset isOpen_interior hnonempty
    (fun z hz => hlocal ⟨hSclosed.closure_subset_iff.mpr interior_subset hz.1,hz.2⟩)
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (q v) hε)
  intro z hz
  by_cases h : z = q v
  · simpa [h,S] using T.vertex_mem_imageStar q v
  · exact interior_subset (hUsub ⟨hz,by simpa using h⟩)

end TriangularDisk

end NormalProjective.Planar

/-! ## DrawingDisjoint -/

/-!
# Global nonoverlap and exact vertex-face incidence of the harmonic drawing

A generic horizontal line proves nonoverlap of face interiors. The local image
stars then rule out every nonincident vertex lying in an image triangle.
-/

namespace NormalProjective.Planar

open Set Finset Filter
open scoped Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

 theorem dense_away_drawing_frontiers (T : Triangulation V) (q : V → ℂ) :
    Dense (⋂ s : T.Face, (frontier (simplex q s.val))ᶜ) :=
  dense_iInter_of_isOpen (fun _ => isClosed_frontier.isOpen_compl)
    (fun s => interior_eq_empty_iff_dense_compl.mp
      (interior_frontier (simplex_isCompact q s.val).isClosed))

end Triangulation

namespace TriangularDisk

variable (D : TriangularDisk V) (w : V → V → ℝ)
  (hw : ∀ i j, 0 ≤ w i j)
  (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
  (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
  (q : V → ℂ) (hq : D.IsHarmonicDrawing w q)

 include hw he hoff hq in
 theorem harmonic_face_interiors_disjoint {s t : D.toTriangulation.Face} (hst : s ≠ t) :
    Disjoint (interior (simplex q s.val)) (interior (simplex q t.val)) := by
  classical
  apply Set.disjoint_left.mpr
  intro z hzs hzt
  let U := interior (simplex q s.val) ∩ interior (simplex q t.val)
  have hU : IsOpen U := isOpen_interior.inter isOpen_interior
  have hd : Dense (Complex.im ⁻¹' (Set.range (fun v => (q v).im))ᶜ) :=
    ((Set.finite_range (fun v => (q v).im)).countable.dense_compl ℝ).preimage
      Complex.isOpenMap_im
  obtain ⟨p,⟨hps,hpt⟩,hpgeneric⟩ := hd.inter_open_nonempty U hU ⟨z,hzs,hzt⟩
  have hgeneric : ∀ v, (q v).im ≠ p.im := by
    intro v heq
    exact hpgeneric ⟨v,heq⟩
  let s' : D.CutFace q p.im := ⟨s,⟨p.re,by
    change horizontalPoint p.im p.re ∈ simplex q s.val
    simpa only [horizontalPoint_eq rfl] using interior_subset hps⟩⟩
  let t' : D.CutFace q p.im := ⟨t,⟨p.re,by
    change horizontalPoint p.im p.re ∈ simplex q t.val
    simpa only [horizontalPoint_eq rfl] using interior_subset hpt⟩⟩
  have hps' : D.cutLo q p.im s' < p.re ∧ p.re < D.cutHi q p.im s' := by
    have hp := interior_horizontalSlice_of_interior
      (show horizontalPoint p.im p.re ∈ interior (simplex q s.val) by
        simpa only [horizontalPoint_eq rfl] using hps)
    rwa [D.cutSlice_eq q p.im s',interior_Icc] at hp
  have hpt' : D.cutLo q p.im t' < p.re ∧ p.re < D.cutHi q p.im t' := by
    have hp := interior_horizontalSlice_of_interior
      (show horizontalPoint p.im p.re ∈ interior (simplex q t.val) by
        simpa only [horizontalPoint_eq rfl] using hpt)
    rwa [D.cutSlice_eq q p.im t',interior_Icc] at hp
  have heq := D.harmonic_generic_cut_interiors_disjoint w hw he hoff q hq p.im hgeneric hps' hpt'
  exact hst (congrArg Subtype.val heq)

 include hw he hq in
 theorem drawing_coordinate_lt_one_of_ne_corner (j : Fin 3) (v : V)
    (hv : v ≠ D.corner j) : triangleCoordinate j (q v) < 1 := by
  by_cases hB : v ∈ D.boundary
  · obtain ⟨k,rfl⟩ := hB
    have hjk : j ≠ k := fun h => hv (congrArg D.corner h.symm)
    simp [hq.1,coordinate_basePoint,hjk]
  · have h0 := D.drawing_coordinates_positive w hw he q hq hB 0
    have h1 := D.drawing_coordinates_positive w hw he q hq hB 1
    have h2 := D.drawing_coordinates_positive w hw he q hq hB 2
    fin_cases j <;> simp [triangleCoordinate] at h0 h1 h2 ⊢ <;> linarith

 include hw he hoff hq in
 theorem harmonic_vertex_mem_face_iff (s : D.toTriangulation.Face) (v : V) :
    q v ∈ simplex q s.val ↔ v ∈ s.val := by
  constructor
  · intro hvface
    by_contra hvs
    by_cases hv : v ∈ D.boundary
    · obtain ⟨j,rfl⟩ := hv
      have hsub : simplex q s.val ⊆ {z | coordinateLinear j z < 1+coordinateThreshold j} := by
        apply convexHull_min
        · rintro z ⟨u,hu,rfl⟩
          have hne : u ≠ D.corner j := fun h => hvs (h ▸ hu)
          have hh := D.drawing_coordinate_lt_one_of_ne_corner w hw he q hq j u hne
          rw [coordinate_eq_linear] at hh
          change coordinateLinear j (q u) < 1 + coordinateThreshold j
          linarith
        · exact convex_halfSpace_lt (coordinateLinear j).toLinearMap.isLinear _
      have hh := hsub hvface
      have heq := coordinate_eq_linear j (q (D.corner j))
      rw [hq.1,coordinate_basePoint] at heq
      simp only [ite_true] at heq
      change coordinateLinear j (q (D.corner j)) < 1+coordinateThreshold j at hh
      rw [hq.1] at hh
      linarith
    · let hind := fun f : D.toTriangulation.Face =>
        D.harmonic_face_independent w hw he hoff q hq f.val f.property
      have hstar := D.imageStar_mem_nhds_of_interior w hw he hoff q hq hv
      have hstarint : interior (D.toTriangulation.imageStar q v) ∈ 𝓝 (q v) :=
        interior_mem_nhds.mpr hstar
      have hinterior : (interior (simplex q s.val)).Nonempty := by
        simpa only [D.toTriangulation.drawingTriangle_carrier] using
          (D.toTriangulation.drawingTriangle q hind s).interior_nonempty
      have hclosure : closure (interior (simplex q s.val)) = simplex q s.val := by
        unfold simplex
        rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hinterior]
        exact (simplex_isCompact q s.val).isClosed.closure_eq
      have hqclosure : q v ∈ closure (interior (simplex q s.val)) := hclosure.symm ▸ hvface
      obtain ⟨z,hzstar,hzface⟩ := mem_closure_iff_nhds.mp hqclosure _ hstarint
      let U := interior (simplex q s.val) ∩ interior (D.toTriangulation.imageStar q v)
      have hU : IsOpen U := isOpen_interior.inter isOpen_interior
      obtain ⟨p,⟨hpface,hpstar⟩,hpavoid⟩ :=
        (D.toTriangulation.dense_away_drawing_frontiers q).inter_open_nonempty U hU
          ⟨z,hzface,hzstar⟩
      obtain ⟨t,hpt⟩ := mem_iUnion.mp (interior_subset hpstar)
      have hpint : p ∈ interior (simplex q t.val.val) := by
        by_contra hn
        exact (mem_iInter.mp hpavoid t.val) ⟨subset_closure hpt,hn⟩
      have hst : s = t.val := by
        by_contra hne
        exact Set.disjoint_left.mp
          (D.harmonic_face_interiors_disjoint w hw he hoff q hq hne) hpface hpint
      exact hvs (hst.symm ▸ t.property)
  · exact point_mem_simplex q s.val

 include hw he hoff hq in
 theorem harmonic_drawing_injective : Function.Injective q := by
  intro a b hab
  obtain ⟨s,hs,ha⟩ := D.vertex_covered a
  let s' : D.toTriangulation.Face := ⟨s,hs⟩
  have hb : b ∈ s := (D.harmonic_vertex_mem_face_iff w hw he hoff q hq s' b).mp
    (hab ▸ point_mem_simplex q s ha)
  have hind := D.harmonic_face_independent w hw he hoff q hq s hs
  exact congrArg Subtype.val (hind.injective (a₁ := ⟨a,ha⟩) (a₂ := ⟨b,hb⟩) hab)

end TriangularDisk

end NormalProjective.Planar


/-! ## HarmonicTriangulation: exact intersections and coverage -/

namespace NormalProjective.Planar

open Set Finset Filter
open scoped Topology

theorem coordinates_positive_of_mem_interior_baseTriangle {z : ℂ}
    (hz : z ∈ interior baseTriangle) (j : Fin 3) :
    0 < triangleCoordinate j z := by
  have hsurj : Function.Surjective (coordinateLinear j) := by
    intro r
    fin_cases j
    · exact ⟨(-r : ℂ), by simp [coordinateLinear]⟩
    · exact ⟨(r : ℂ), by simp [coordinateLinear]⟩
    · exact ⟨(r : ℂ) * Complex.I, by simp [coordinateLinear]⟩
  have hsub : baseTriangle ⊆
      (coordinateLinear j) ⁻¹' Ici (coordinateThreshold j) := by
    intro p hp
    have h := hp j
    change coordinateThreshold j ≤ coordinateLinear j p
    simpa only [coordinate_eq_linear, sub_nonneg] using h
  have h := interior_mono hsub hz
  rw [(coordinateLinear j).interior_preimage hsurj, interior_Ici] at h
  rw [coordinate_eq_linear]
  exact sub_pos.mpr h

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

theorem drawing_frontier_open_edge (T : Triangulation V) (q : V → ℂ)
    (hind : ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q v.val))
    (s : T.Face) {z : ℂ} (hz : z ∈ frontier (simplex q s.val))
    (hv : ∀ v, z ≠ q v) :
    ∃ a b : V, a ≠ b ∧ a ∈ s.val ∧ b ∈ s.val ∧
      z ∈ openSegment ℝ (q a) (q b) :=
  T.drawing_frontier_point_on_open_edge q hind s hz (fun v _ => hv v)

end Triangulation

namespace TriangularDisk

variable (D : TriangularDisk V) (w : V → V → ℝ)
  (hw : ∀ i j, 0 ≤ w i j)
  (he : ∀ i j, D.toTriangulation.graph.Adj i j → 0 < w i j)
  (hoff : ∀ i j, ¬ D.toTriangulation.graph.Adj i j → w i j = 0)
  (q : V → ℂ) (hq : D.IsHarmonicDrawing w q)

include hw he hoff hq in
theorem harmonic_face_interior_nonempty (s : D.toTriangulation.Face) :
    (interior (simplex q s.val)).Nonempty := by
  let hind := fun f : D.toTriangulation.Face =>
    D.harmonic_face_independent w hw he hoff q hq f.val f.property
  simpa only [D.toTriangulation.drawingTriangle_carrier] using
    (D.toTriangulation.drawingTriangle q hind s).interior_nonempty

include hw he hoff hq in
theorem harmonic_face_closure_interior (s : D.toTriangulation.Face) :
    closure (interior (simplex q s.val)) = simplex q s.val := by
  unfold simplex
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
    (D.harmonic_face_interior_nonempty w hw he hoff q hq s)]
  exact (simplex_isCompact q s.val).isClosed.closure_eq

include hw he hoff hq in
theorem harmonic_face_not_interior_other {s t : D.toTriangulation.Face}
    (hst : s ≠ t) {z : ℂ} (hzs : z ∈ simplex q s.val) :
    z ∉ interior (simplex q t.val) := by
  intro hzt
  have hzcl : z ∈ closure (interior (simplex q s.val)) := by
    rwa [D.harmonic_face_closure_interior w hw he hoff q hq s]
  obtain ⟨p,hpt,hps⟩ := mem_closure_iff_nhds.mp hzcl _ (isOpen_interior.mem_nhds hzt)
  exact Set.disjoint_left.mp
    (D.harmonic_face_interiors_disjoint w hw he hoff q hq hst) hps hpt

include hw he hoff hq in
/-- A third image triangle cannot meet an open neighborhood covered by two
other image triangles.  The proof uses actual interior disjointness and the
density of points away from the finitely many triangle boundaries. -/
theorem harmonic_face_eq_of_union_nhds {s u t : D.toTriangulation.Face} {z : ℂ}
    (hzt : z ∈ simplex q t.val)
    (hN : simplex q s.val ∪ simplex q u.val ∈ 𝓝 z) : t = s ∨ t = u := by
  have hzcl : z ∈ closure (interior (simplex q t.val)) := by
    rwa [D.harmonic_face_closure_interior w hw he hoff q hq t]
  obtain ⟨x,hxN,hxt⟩ := mem_closure_iff_nhds.mp hzcl _ (interior_mem_nhds.mpr hN)
  let U := interior (simplex q t.val) ∩
    interior (simplex q s.val ∪ simplex q u.val)
  obtain ⟨p,⟨hpt,hpN⟩,hpavoid⟩ :=
    (D.toTriangulation.dense_away_drawing_frontiers q).inter_open_nonempty U
      (isOpen_interior.inter isOpen_interior) ⟨x,hxt,hxN⟩
  have heq : ∀ f : D.toTriangulation.Face, p ∈ simplex q f.val → t = f := by
    intro f hpf
    have hpint : p ∈ interior (simplex q f.val) := by
      by_contra hn
      exact (mem_iInter.mp hpavoid f) ⟨subset_closure hpf,hn⟩
    by_contra hne
    exact Set.disjoint_left.mp
      (D.harmonic_face_interiors_disjoint w hw he hoff q hq hne) hpt hpint
  exact (interior_subset hpN).elim (fun hs => Or.inl (heq s hs))
    (fun hu => Or.inr (heq u hu))

include hw he hq in
theorem harmonic_boundary_open_edges_eq {a b c d : V} {z : ℂ}
    (hab : a ≠ b) (hcd : c ≠ d) (ha : a ∈ D.boundary) (hb : b ∈ D.boundary)
    (hzab : z ∈ openSegment ℝ (q a) (q b))
    (hzcd : z ∈ openSegment ℝ (q c) (q d)) :
    ({a,b} : Finset V) = {c,d} := by
  obtain ⟨i,rfl⟩ := ha
  obtain ⟨j,rfl⟩ := hb
  have hij : i ≠ j := fun h => hab (congrArg D.corner h)
  obtain ⟨k,hki,hkj⟩ := (show ∀ i j : Fin 3, i ≠ j →
      ∃ k : Fin 3, k ≠ i ∧ k ≠ j by decide) i j hij
  have hzk : triangleCoordinate k z = 0 := by
    obtain ⟨r,s,hr,hs,hrs,rfl⟩ := hzab
    rw [triangleCoordinate_combo k _ _ r s hrs, hq.1, hq.1,
      coordinate_basePoint, coordinate_basePoint]
    simp [hki,hkj]
  have hends := D.open_image_edge_zero_coordinate w hw he q hq hzcd k hzk
  obtain ⟨l,hlk,rfl⟩ := (D.drawing_coordinate_zero_iff w hw he q hq c k).mp hends.1
  obtain ⟨m,hmk,rfl⟩ := (D.drawing_coordinate_zero_iff w hw he q hq d k).mp hends.2
  have hcover : ∀ n : Fin 3, n ≠ k → n = i ∨ n = j := by
    exact (show ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      ∀ n : Fin 3, n ≠ k → n = i ∨ n = j by decide) i j k hij hki hkj
  rcases hcover l hlk with rfl | rfl <;>
    rcases hcover m hmk with rfl | rfl <;> simp_all [Finset.pair_comm]

include hw he hoff hq in
/-- Every pair of closed image triangles meets in exactly its labelled common
face.  This includes triangles with no common vertices. -/
theorem harmonic_face_intersection (s t : D.toTriangulation.Face) :
    simplex q s.val ∩ simplex q t.val = simplex q (s.val ∩ t.val) := by
  classical
  by_cases hst : s = t
  · subst t
    simp
  apply Set.Subset.antisymm
  · intro z hz
    by_cases hv : ∃ v, z = q v
    · obtain ⟨v,rfl⟩ := hv
      exact point_mem_simplex q (s.val ∩ t.val) (Finset.mem_inter.mpr
        ⟨(D.harmonic_vertex_mem_face_iff w hw he hoff q hq s v).mp hz.1,
         (D.harmonic_vertex_mem_face_iff w hw he hoff q hq t v).mp hz.2⟩)
    · have hnov : ∀ v, z ≠ q v := by simpa only [not_exists] using hv
      let hind := fun f : D.toTriangulation.Face =>
        D.harmonic_face_independent w hw he hoff q hq f.val f.property
      have hzsf : z ∈ frontier (simplex q s.val) := ⟨subset_closure hz.1,
        D.harmonic_face_not_interior_other w hw he hoff q hq (Ne.symm hst) hz.2⟩
      obtain ⟨a,b,hab,has,hbs,hzab⟩ :=
        D.toTriangulation.drawing_frontier_open_edge q hind s hzsf hnov
      have hsegsub : ∀ (hat : a ∈ t.val) (hbt : b ∈ t.val),
          z ∈ simplex q (s.val ∩ t.val) := by
        intro hat hbt
        exact (convex_convexHull ℝ _).segment_subset
          (point_mem_simplex q _ (Finset.mem_inter.mpr ⟨has,hat⟩))
          (point_mem_simplex q _ (Finset.mem_inter.mpr ⟨hbs,hbt⟩))
          (openSegment_subset_segment ℝ _ _ hzab)
      by_cases hi : a ∉ D.boundary ∨ b ∉ D.boundary
      · obtain ⟨u,hus,hau,hbu⟩ := D.exists_other_incident_face hab has hbs hi
        have hN := D.harmonic_adjacent_image_union_mem_nhds w hw he hoff q hq
          hus.symm hab has hbs hau hbu hzab
        rcases D.harmonic_face_eq_of_union_nhds w hw he hoff q hq hz.2 hN with hts | htu
        · exact False.elim (hst hts.symm)
        · subst t
          exact hsegsub hau hbu
      · push_neg at hi
        have hztf : z ∈ frontier (simplex q t.val) := ⟨subset_closure hz.2,
          D.harmonic_face_not_interior_other w hw he hoff q hq hst hz.1⟩
        obtain ⟨c,d,hcd,hct,hdt,hzcd⟩ :=
          D.toTriangulation.drawing_frontier_open_edge q hind t hztf hnov
        have hedges := D.harmonic_boundary_open_edges_eq w hw he q hq
          hab hcd hi.1 hi.2 hzab hzcd
        apply hsegsub
        · have ha : a ∈ ({c,d} : Finset V) := hedges ▸ (by simp)
          have ha' : a = c ∨ a = d := by simpa only
            [Finset.mem_insert, Finset.mem_singleton] using ha
          rcases ha' with h | h
          · simpa [h] using hct
          · simpa [h] using hdt
        · have hb : b ∈ ({c,d} : Finset V) := hedges ▸ (by simp)
          have hb' : b = c ∨ b = d := by simpa only
            [Finset.mem_insert, Finset.mem_singleton] using hb
          rcases hb' with h | h
          · simpa [h] using hct
          · simpa [h] using hdt
  · intro z hz
    constructor
    · exact convexHull_mono (Set.image_mono (show (s.val ∩ t.val : Finset V) ⊆ s.val from
        Finset.inter_subset_left)) hz
    · exact convexHull_mono (Set.image_mono (show (s.val ∩ t.val : Finset V) ⊆ t.val from
        Finset.inter_subset_right)) hz

def imageDomain : Set ℂ := ⋃ s : D.toTriangulation.Face, simplex q s.val

theorem imageDomain_isClosed : IsClosed (D.imageDomain q) :=
  isClosed_iUnion_of_finite fun s => (simplex_isCompact q s.val).isClosed

include hw he hq in
theorem imageDomain_subset_baseTriangle : D.imageDomain q ⊆ baseTriangle := by
  intro z hz
  obtain ⟨s,hs⟩ := mem_iUnion.mp hz
  exact D.toTriangulation.drawing_cell_subset q baseTriangle_convex
    (fun v => D.drawing_coordinates_nonnegative w hw he q hq v) s hs

include hw he hoff hq in
theorem imageDomain_mem_nhds {z : ℂ} (hz : z ∈ D.imageDomain q)
    (hzbase : z ∈ interior baseTriangle) : D.imageDomain q ∈ 𝓝 z := by
  classical
  obtain ⟨s,hzs⟩ := mem_iUnion.mp hz
  by_cases hzi : z ∈ interior (simplex q s.val)
  · apply Filter.mem_of_superset (isOpen_interior.mem_nhds hzi)
    intro p hp
    exact mem_iUnion.mpr ⟨s,interior_subset hp⟩
  by_cases hv : ∃ v, z = q v
  · obtain ⟨v,rfl⟩ := hv
    have hvint : v ∉ D.boundary := by
      rintro ⟨j,rfl⟩
      obtain ⟨k,hkj⟩ := exists_ne j
      have h := coordinates_positive_of_mem_interior_baseTriangle hzbase k
      rw [hq.1,coordinate_basePoint] at h
      simp [hkj] at h
    apply Filter.mem_of_superset
      (D.imageStar_mem_nhds_of_interior w hw he hoff q hq hvint)
    intro p hp
    obtain ⟨t,ht⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨t.val,ht⟩
  · have hnov : ∀ v, z ≠ q v := by simpa only [not_exists] using hv
    let hind := fun f : D.toTriangulation.Face =>
      D.harmonic_face_independent w hw he hoff q hq f.val f.property
    obtain ⟨a,b,hab,has,hbs,hzab⟩ := D.toTriangulation.drawing_frontier_open_edge q hind s
      ⟨subset_closure hzs,hzi⟩ hnov
    have hi := D.strict_coordinate_open_edge_interior w hw he q hq hab hzab
      (coordinates_positive_of_mem_interior_baseTriangle hzbase)
    obtain ⟨t,hts,hat,hbt⟩ := D.exists_other_incident_face hab has hbs hi
    apply Filter.mem_of_superset
      (D.harmonic_adjacent_image_union_mem_nhds w hw he hoff q hq
        hts.symm hab has hbs hat hbt hzab)
    intro p hp
    exact hp.elim (fun hs => mem_iUnion.mpr ⟨s,hs⟩)
      (fun ht => mem_iUnion.mpr ⟨t,ht⟩)

include hw he hoff hq in
/-- The image triangles cover precisely the closed prescribed boundary triangle. -/
theorem imageDomain_eq_baseTriangle : D.imageDomain q = baseTriangle := by
  classical
  let B := interior baseTriangle
  let A : Set B := Subtype.val ⁻¹' D.imageDomain q
  letI : PreconnectedSpace B :=
    Subtype.preconnectedSpace baseTriangle_convex.interior.isPreconnected
  have hAc : IsClosed A := (D.imageDomain_isClosed q).preimage continuous_subtype_val
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      (D.imageDomain_mem_nhds w hw he hoff q hq hz z.property)
  obtain ⟨s,hs,hvs⟩ := D.vertex_covered (D.corner 0)
  let s' : D.toTriangulation.Face := ⟨s,hs⟩
  obtain ⟨z,hz⟩ := D.harmonic_face_interior_nonempty w hw he hoff q hq s'
  have hzbase : z ∈ B := interior_mono
    (D.toTriangulation.drawing_cell_subset q baseTriangle_convex
      (fun v => D.drawing_coordinates_nonnegative w hw he q hq v) s') hz
  have hAnonempty : A.Nonempty := ⟨⟨z,hzbase⟩,mem_iUnion.mpr ⟨s',interior_subset hz⟩⟩
  have hAuniv : A = univ := (show IsClopen A from ⟨hAc,hAo⟩).eq_univ hAnonempty
  have hBsub : B ⊆ D.imageDomain q := by
    intro p hp
    have hh : (⟨p,hp⟩ : B) ∈ A := hAuniv.symm ▸ mem_univ _
    exact hh
  apply Set.Subset.antisymm (D.imageDomain_subset_baseTriangle w hw he q hq)
  have hBclosure : closure B = baseTriangle := by
    have hclosed : IsClosed baseTriangle := by
      rw [baseTriangle_eq_convexHull]
      exact (Set.finite_range basePoint).isCompact_convexHull ℝ |>.isClosed
    rw [baseTriangle_convex.closure_interior_eq_closure_of_nonempty_interior
      ⟨z,hzbase⟩,hclosed.closure_eq]
  rw [← hBclosure]
  exact (D.imageDomain_isClosed q).closure_subset_iff.mpr hBsub

/-- The genuine geometric disk determined by a positive harmonic drawing.
All defining incidence, nondegeneracy, and coverage conditions are proved. -/
def harmonicTriangularDisk : TriangularDisk V where
  point := q
  point_injective := D.harmonic_drawing_injective w hw he hoff q hq
  faces := D.faces
  face_card := D.face_card
  face_independent := D.harmonic_face_independent w hw he hoff q hq
  intersection s hs t ht := D.harmonic_face_intersection w hw he hoff q hq ⟨s,hs⟩ ⟨t,ht⟩
  vertex_covered := D.vertex_covered
  corner := D.corner
  corner_point := hq.1
  domain_eq := D.imageDomain_eq_baseTriangle w hw he hoff q hq
  interior_vertex v hv := D.drawing_coordinates_positive w hw he q hq hv

@[simp] theorem harmonicTriangularDisk_point :
    (D.harmonicTriangularDisk w hw he hoff q hq).point = q := rfl

@[simp] theorem harmonicTriangularDisk_faces :
    (D.harmonicTriangularDisk w hw he hoff q hq).faces = D.faces := rfl

@[simp] theorem harmonicTriangularDisk_corner :
    (D.harmonicTriangularDisk w hw he hoff q hq).corner = D.corner := rfl

@[simp] theorem harmonicTriangularDisk_graph :
    (D.harmonicTriangularDisk w hw he hoff q hq).toTriangulation.graph =
      D.toTriangulation.graph := rfl

end TriangularDisk

end NormalProjective.Planar

#print axioms NormalProjective.Planar.TriangularDisk.harmonicTriangularDisk


/-! Read-only actual-body audit; generated from Verify.lean. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules : Array Name := #[`harmonic_embedding]
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let isLocal (n : Name) : Bool := localModules.contains (moduleOf n)
  let names := env.checked.get.constants.foldStage2
    (fun ns n _ => ns.push n) (#[] : Array Name)
  let names := names.qsort Name.lt
  let mut records : Array Json := #[]
  let mut boundaries : NameSet := {}
  for n in names do
    let some ci := env.find? n | throwError "Missing imported declaration {n}"
    match ci with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (ci.value? true).isSome do
          throwError "Local proof or definition body unavailable: {n}"
    | .axiomInfo _ => throwError "Local axiom declaration is forbidden: {n}"
    | _ => pure ()
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom {ax} in {n}"
    let typeDeps := ci.type.getUsedConstants
    let valueDeps := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
    let ctorDeps := match ci with
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
    let deps := (typeDeps ++ valueDeps ++ ctorDeps).foldl (fun s x => s.insert x) ({} : NameSet)
    for d in deps.toArray do
      unless isLocal d do boundaries := boundaries.insert d
    let typeString ← liftTermElabM <| return (← Meta.ppExpr ci.type).pretty
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("type", toJson typeString),
      ("proof_or_definition_body_available", toJson (ci.value? true).isSome),
      ("direct_dependencies", toJson (deps.toArray.qsort Name.lt |>.map Name.toString)),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let mut boundaryRecords : Array Json := #[]
  for n in boundaries.toArray.qsort Name.lt do
    let axs ← collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved library-boundary axiom {ax} in {n}"
    boundaryRecords := boundaryRecords.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let result := Json.mkObj [
    ("lean_version", toJson "4.35.0"),
    ("mathlib_commit", toJson "56a005855ea17e0b0958f73ec801ae140b0a1679"),
    ("local_modules", toJson (localModules.map Name.toString)),
    ("local_declarations", Json.arr records),
    ("pinned_library_boundary", Json.arr boundaryRecords),
    ("unapproved_axioms", Json.arr #[])]
  IO.FS.createDirAll ".lake/reports/audit/final"
  IO.FS.writeFile ".lake/reports/audit/final/HarmonicEmbedding_dependencies.json" result.pretty
  logInfo m!"Audited {records.size} local declarations and {boundaryRecords.size} pinned-library boundaries."
