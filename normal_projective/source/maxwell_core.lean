module

public import face_graph
public import harmonic_embedding
public import triangular_disk
public import Mathlib.Data.Finset.Powerset
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix

import boundary_corners
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Util.CollectAxioms
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson.Basic
import Lean.Data.Json.Printer

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit/final"


/-!
# Maxwell equilibrium, rigidity, and positive local folds

This is the first of the two authoritative Maxwell modules. It contains the
finite edge spaces, face planes, signed incidence identities, injectivity of
the height-to-stress map, surjectivity of the equilibrium map, and the positive
local-fold formula. All declaration statements and proof bodies are preserved
from the preceding development; exact ranges and hashes are recorded in
`development/maxwell-split-provenance.json`.

The remaining edge count, global cap construction, continuity, and complete
cap-path theorem are in `maxwell_development`.
-/

@[expose] public section
noncomputable section
open scoped Classical

/- Source section MaxwellAlgebra -/
section
namespace NormalProjective.Planar.Maxwell

def realDot (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

def turn (z : ℂ) : ℂ := Complex.I * z

@[simp] theorem turn_zero : turn 0 = 0 := by simp [turn]

@[simp] theorem turn_re (z : ℂ) : (turn z).re = -z.im := by simp [turn]
@[simp] theorem turn_im (z : ℂ) : (turn z).im = z.re := by simp [turn]

theorem turn_add (z w : ℂ) : turn (z+w) = turn z + turn w := by
  simp [turn,mul_add]

theorem turn_smul (r : ℝ) (z : ℂ) : turn (r • z) = r • turn z := by
  simp [turn,Complex.real_smul,mul_comm,mul_left_comm]

@[simp] theorem turn_turn (z : ℂ) : turn (turn z) = -z := by
  simp [turn,← mul_assoc]

def perpendicularCoefficient (d g : ℂ) : ℝ :=
  (g.im * d.re - g.re * d.im) / Complex.normSq d

def realDotLinear (w : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun z := realDot z w
  map_add' z u := by simp only [realDot,Complex.add_re,Complex.add_im]; ring
  map_smul' r z := by
    simp only [realDot,Complex.smul_re,Complex.smul_im,smul_eq_mul,RingHom.id_apply]
    ring

def turnLinear : ℂ →ₗ[ℝ] ℂ where
  toFun := turn
  map_add' := turn_add
  map_smul' r z := turn_smul r z

def coefficientLinear (d : ℂ) : ℂ →ₗ[ℝ] ℝ where
  toFun g := perpendicularCoefficient d g
  map_add' g h := by
    simp only [perpendicularCoefficient,Complex.add_re,Complex.add_im]
    ring
  map_smul' r g := by
    simp only [perpendicularCoefficient,Complex.smul_re,Complex.smul_im,smul_eq_mul,
      RingHom.id_apply]
    ring

theorem perpendicular_decomposition {d g : ℂ} (hd : d ≠ 0)
    (hperp : realDot g d = 0) :
    g = perpendicularCoefficient d g • turn d := by
  have hn : Complex.normSq d ≠ 0 := mt Complex.normSq_eq_zero.mp hd
  have hh : g.re * d.re + g.im * d.im = 0 := hperp
  apply Complex.ext
  · simp only [Complex.smul_re,smul_eq_mul,turn_re,perpendicularCoefficient]
    field_simp [hn]
    simp only [Complex.normSq_apply]
    linear_combination d.re * hh
  · simp only [Complex.smul_im,smul_eq_mul,turn_im,perpendicularCoefficient]
    field_simp [hn]
    simp only [Complex.normSq_apply]
    linear_combination d.im * hh

theorem perpendicularCoefficient_neg (d g : ℂ) :
    perpendicularCoefficient (-d) (-g) = perpendicularCoefficient d g := by
  simp [perpendicularCoefficient]

theorem realDot_turn (d x : ℂ) :
    realDot (turn d) x = d.re*x.im-d.im*x.re := by
  simp only [realDot,turn_re,turn_im]
  ring

theorem realDot_smul (r : ℝ) (z w : ℂ) :
    realDot (r • z) w = r * realDot z w := by
  simp only [realDot,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

end NormalProjective.Planar.Maxwell
end

/- Source section MaxwellEdges -/
section
namespace NormalProjective.Planar.TriangularDisk

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (D : TriangularDisk V)

theorem edge_pair_eq_iff {a b c d : V} :
    ({a,b} : Finset V) = {c,d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [← Finset.coe_inj,Finset.coe_pair,Finset.coe_pair,Set.pair_eq_pair_iff]

theorem edge_mem_pair_iff {v a b : V} :
    v ∈ ({a,b} : Finset V) ↔ v = a ∨ v = b := by
  simp only [Finset.mem_insert,Finset.mem_singleton]

abbrev InteriorVertex := {v : V // v ∉ D.boundary}

abbrev InteriorEdge := {e : Finset V // e.card = 2 ∧
  (∃ s ∈ D.faces, e ⊆ s) ∧ ∃ v ∈ e, v ∉ D.boundary}

instance interiorVertexFintype : Fintype D.InteriorVertex := by
  classical
  unfold InteriorVertex
  infer_instance

instance interiorEdgeFintype : Fintype D.InteriorEdge := by
  classical
  unfold InteriorEdge
  infer_instance

def interiorEdgeLeft (e : D.InteriorEdge) : V :=
  Classical.choose (Finset.card_eq_two.mp e.property.1)

def interiorEdgeRight (e : D.InteriorEdge) : V :=
  Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp e.property.1))

theorem interiorEdge_endpoints (e : D.InteriorEdge) :
    D.interiorEdgeLeft e ≠ D.interiorEdgeRight e ∧
      e.val = {D.interiorEdgeLeft e, D.interiorEdgeRight e} :=
  Classical.choose_spec (Classical.choose_spec (Finset.card_eq_two.mp e.property.1))

theorem interiorEdge_adj (e : D.InteriorEdge) :
    D.toTriangulation.graph.Adj (D.interiorEdgeLeft e) (D.interiorEdgeRight e) := by
  obtain ⟨s, hs, he⟩ := e.property.2.1
  have hends := D.interiorEdge_endpoints e
  refine ⟨hends.1, s, hs, he ?_, he ?_⟩ <;> simp [hends.2]

theorem interiorEdge_interior (e : D.InteriorEdge) :
    D.interiorEdgeLeft e ∉ D.boundary ∨ D.interiorEdgeRight e ∉ D.boundary := by
  obtain ⟨v, hv, hi⟩ := e.property.2.2
  rw [(D.interiorEdge_endpoints e).2] at hv
  rcases edge_mem_pair_iff.mp hv with rfl | rfl
  · exact Or.inl hi
  · exact Or.inr hi

def edgeOfAdjacent {a b : V} (hab : D.toTriangulation.graph.Adj a b)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary) : D.InteriorEdge where
  val := {a,b}
  property := by
    refine ⟨by simp [hab.1], ?_, ?_⟩
    · obtain ⟨_,s,hs,ha,hb⟩ := hab
      exact ⟨s,hs,by simp [Finset.insert_subset_iff,ha,hb]⟩
    · rcases hi with ha | hb
      · exact ⟨a,by simp,ha⟩
      · exact ⟨b,by simp,hb⟩

theorem edgeOfAdjacent_symm {a b : V} (hab : D.toTriangulation.graph.Adj a b)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary) :
    D.edgeOfAdjacent hab.symm hi.symm = D.edgeOfAdjacent hab hi := by
  apply Subtype.ext
  exact Finset.pair_comm b a

theorem edgeOfAdjacent_endpoints (e : D.InteriorEdge) :
    D.edgeOfAdjacent (D.interiorEdge_adj e) (D.interiorEdge_interior e) = e := by
  apply Subtype.ext
  exact (D.interiorEdge_endpoints e).2.symm

def edgeWeight (w : D.InteriorEdge → ℝ) (a b : V) : ℝ := by
  classical
  exact if h : D.toTriangulation.graph.Adj a b ∧ (a ∉ D.boundary ∨ b ∉ D.boundary)
    then w (D.edgeOfAdjacent h.1 h.2) else 0

theorem edgeWeight_of_adj (w : D.InteriorEdge → ℝ) {a b : V}
    (hab : D.toTriangulation.graph.Adj a b) (hi : a ∉ D.boundary ∨ b ∉ D.boundary) :
    D.edgeWeight w a b = w (D.edgeOfAdjacent hab hi) := by
  simp only [edgeWeight, dif_pos (And.intro hab hi)]

theorem edgeWeight_symm (w : D.InteriorEdge → ℝ) (a b : V) :
    D.edgeWeight w b a = D.edgeWeight w a b := by
  classical
  by_cases h : D.toTriangulation.graph.Adj a b ∧ (a ∉ D.boundary ∨ b ∉ D.boundary)
  · rw [D.edgeWeight_of_adj w h.1 h.2,
      D.edgeWeight_of_adj w h.1.symm h.2.symm, D.edgeOfAdjacent_symm]
  · have h' : ¬(D.toTriangulation.graph.Adj b a ∧
        (b ∉ D.boundary ∨ a ∉ D.boundary)) :=
      fun k => h ⟨k.1.symm,k.2.symm⟩
    simp only [edgeWeight,dif_neg h,dif_neg h']

theorem edgeWeight_endpoints (w : D.InteriorEdge → ℝ) (e : D.InteriorEdge) :
    D.edgeWeight w (D.interiorEdgeLeft e) (D.interiorEdgeRight e) = w e := by
  rw [D.edgeWeight_of_adj w (D.interiorEdge_adj e) (D.interiorEdge_interior e),
    D.edgeOfAdjacent_endpoints]

def extendInterior (h : D.InteriorVertex → ℝ) (v : V) : ℝ := by
  classical
  exact if hv : v ∉ D.boundary then h ⟨v,hv⟩ else 0

@[simp] theorem extendInterior_at (h : D.InteriorVertex → ℝ) (v : D.InteriorVertex) :
    D.extendInterior h v.val = h v := by
  simp only [extendInterior,dif_pos v.property]

@[simp] theorem extendInterior_corner (h : D.InteriorVertex → ℝ) (j : Fin 3) :
    D.extendInterior h (D.corner j) = 0 := by
  have hj : D.corner j ∈ D.boundary := ⟨j,rfl⟩
  simp [extendInterior,hj]

def extendInteriorLinear : (D.InteriorVertex → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := D.extendInterior
  map_add' h k := by
    funext v
    dsimp [extendInterior]
    split_ifs <;> simp
  map_smul' r h := by
    funext v
    dsimp [extendInterior]
    split_ifs <;> simp

end NormalProjective.Planar.TriangularDisk
end

/- Source section MaxwellFoundation -/
section
/- Source section Rigidity -/
section


/-!
# Infinitesimal rigidity of the harmonic triangular disk

This is the row-rank argument needed for Maxwell lifting. It uses the actual
nondegenerate image triangles and the proved connectivity of their face graph.
No generic-position or rigidity assumption is added to the input.
-/



namespace NormalProjective.Planar

open Set Finset

def signedArea (a b x : ℂ) : ℝ :=
  (b-a).re * (x-a).im - (b-a).im * (x-a).re

theorem edgeHeight_eq_area_div (a b x : ℂ) :
    edgeHeight a b x = signedArea a b x / Complex.normSq (b-a) := by
  simp only [edgeHeight,edgeNormalize,AffineMap.coe_mk,Complex.mul_im,
    Complex.inv_re,Complex.inv_im,signedArea]
  ring

theorem signedArea_ne_zero_of_height_ne_zero {a b x : ℂ}
    (h : edgeHeight a b x ≠ 0) : signedArea a b x ≠ 0 := by
  intro hz
  apply h
  rw [edgeHeight_eq_area_div,hz,zero_div]

def edgeStrain (a b u v : ℂ) : ℝ :=
  (b-a).re * (v-u).re + (b-a).im * (v-u).im

theorem velocity_zero_of_two_edges {a b x u : ℂ}
    (harea : signedArea a b x ≠ 0)
    (ha : edgeStrain a x 0 u = 0) (hb : edgeStrain b x 0 u = 0) : u = 0 := by
  simp only [edgeStrain,sub_zero,Complex.sub_re,Complex.sub_im] at ha hb
  have hfirst : u.re * signedArea a b x = 0 := by
    simp only [signedArea,Complex.sub_re,Complex.sub_im]
    linear_combination (x.im-b.im) * ha - (x.im-a.im) * hb
  have hsecond : u.im * signedArea a b x = 0 := by
    simp only [signedArea,Complex.sub_re,Complex.sub_im]
    linear_combination -(x.re-b.re) * ha + (x.re-a.re) * hb
  apply Complex.ext
  · exact (mul_eq_zero.mp hfirst).resolve_right harea
  · exact (mul_eq_zero.mp hsecond).resolve_right harea

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

theorem velocity_zero_on_face (q u : V → ℂ)
    (hind : ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q v.val))
    (hstrain : ∀ a b, T.graph.Adj a b → edgeStrain (q a) (q b) (u a) (u b) = 0)
    (s : T.Face) {a b : V} (hab : a ≠ b) (ha : a ∈ s.val) (hb : b ∈ s.val)
    (hua : u a = 0) (hub : u b = 0) : ∀ x ∈ s.val, u x = 0 := by
  intro x hx
  by_cases hxa : x = a
  · simpa [hxa] using hua
  by_cases hxb : x = b
  · simpa [hxb] using hub
  have hheight := height_ne_zero_of_face_independent q (hind s) ha hb hx hab hxa hxb
  apply velocity_zero_of_two_edges (signedArea_ne_zero_of_height_ne_zero hheight)
  · simpa only [hua] using hstrain a x ⟨Ne.symm hxa,s.val,s.property,ha,hx⟩
  · simpa only [hub] using hstrain b x ⟨Ne.symm hxb,s.val,s.property,hb,hx⟩

end Triangulation

namespace TriangularDisk

variable (D : TriangularDisk V)

/-- Every infinitesimal motion fixing the three actual boundary corners and
preserving all edge lengths vanishes. The image need only have the already
proved face nondegeneracy; global injectivity is not assumed here. -/
theorem velocity_zero (q u : V → ℂ)
    (hind : ∀ s : D.toTriangulation.Face,
      AffineIndependent ℝ (fun v : s.val => q v.val))
    (hboundary : ∀ j, u (D.corner j) = 0)
    (hstrain : ∀ a b, D.toTriangulation.graph.Adj a b →
      edgeStrain (q a) (q b) (u a) (u b) = 0) : ∀ v, u v = 0 := by
  have hab := D.boundary_edge 0 1 (by decide)
  obtain ⟨habne,s,hs,ha,hb⟩ := hab
  let s₀ : D.toTriangulation.Face := ⟨s,hs⟩
  letI : Nonempty D.toTriangulation.Face := ⟨s₀⟩
  have hstart : ∀ v ∈ s₀.val, u v = 0 :=
    D.toTriangulation.velocity_zero_on_face q u hind hstrain s₀ habne ha hb
      (hboundary 0) (hboundary 1)
  have hconvex : Convex ℝ D.toTriangulation.domain := by
    rw [D.domain_eq]
    exact baseTriangle_convex
  have hconn := D.toTriangulation.faceGraph_connected hconvex
  have hstep : ∀ s t : D.toTriangulation.Face,
      D.toTriangulation.faceGraph.Adj s t →
      (∀ v ∈ s.val, u v = 0) → ∀ v ∈ t.val, u v = 0 := by
    intro s t hst hs
    obtain ⟨a,hai,b,hbi,hab⟩ := Finset.one_lt_card.mp (by
      have := hst.2
      omega : 1 < (s.val ∩ t.val).card)
    have has := (Finset.mem_inter.mp hai).1
    have hat := (Finset.mem_inter.mp hai).2
    have hbs := (Finset.mem_inter.mp hbi).1
    have hbt := (Finset.mem_inter.mp hbi).2
    exact D.toTriangulation.velocity_zero_on_face q u hind hstrain t hab hat hbt
      (hs a has) (hs b hbs)
  have hwalk : ∀ {s t : D.toTriangulation.Face},
      D.toTriangulation.faceGraph.Walk s t →
      (∀ v ∈ s.val, u v = 0) → ∀ v ∈ t.val, u v = 0 := by
    intro s t p
    induction p with
    | nil => exact id
    | cons hst p ih => exact fun hs => ih (hstep _ _ hst hs)
  have hface : ∀ f : D.toTriangulation.Face, ∀ v ∈ f.val, u v = 0 := by
    intro f
    obtain ⟨p⟩ := hconn s₀ f
    exact hwalk p hstart
  intro v
  obtain ⟨s,hs,hvs⟩ := D.vertex_covered v
  exact hface ⟨s,hs⟩ v hvs

end TriangularDisk

end NormalProjective.Planar
end


/- Source section FacePlanes -/
section


/-!
# Actual affine face planes and uniqueness of a lifting

Every nondegenerate planar triangle determines its literal affine interpolant
of the three vertex heights. If the gradients agree across every shared edge,
the lifting is a single affine function; fixing the base corners to height
zero therefore makes it zero. This supplies injectivity in Maxwell's map.
-/



namespace NormalProjective.Planar

open Set Finset

theorem affine_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → (ℂ →ᵃ[ℝ] ℝ)) (z : ℂ) : (∑ i ∈ s, f i) z = ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih]

theorem basePoint_affineIndependent : AffineIndependent ℝ basePoint := by
  apply affineIndependent_triple_of_height_ne_zero
  norm_num [basePoint,edgeHeight,edgeNormalize]

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V) (q : V → ℂ)
  (hind : ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q v.val))

def faceBasis (s : T.Face) : AffineBasis s.val ℝ ℂ where
  toFun v := q v.val
  ind' := hind s
  tot' := (hind s).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
    simpa using T.face_card s.val s.property)

def facePlaneMap (s : T.Face) : (V → ℝ) →ₗ[ℝ] (ℂ →ᵃ[ℝ] ℝ) where
  toFun h := ∑ v : s.val, h v.val • (T.faceBasis q hind s).coord v
  map_add' h k := by
    simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r h := by
    simp only [RingHom.id_apply,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

theorem facePlaneMap_vertex (s : T.Face) (h : V → ℝ) (v : V) (hv : v ∈ s.val) :
    T.facePlaneMap q hind s h (q v) = h v := by
  change (∑ u : s.val, h u.val • (T.faceBasis q hind s).coord u) (q v) = _
  have hq : q v = T.faceBasis q hind s ⟨v,hv⟩ := rfl
  rw [hq]
  simp [affine_sum_apply,AffineBasis.coord_apply]

theorem facePlane_eq_of_linear_eq (h : V → ℝ) {s t : T.Face}
    (hst : T.faceGraph.Adj s t)
    (heq : (T.facePlaneMap q hind s h).linear = (T.facePlaneMap q hind t h).linear) :
    T.facePlaneMap q hind s h = T.facePlaneMap q hind t h := by
  have hne : (s.val ∩ t.val).Nonempty := by
    apply Finset.card_pos.mp
    have := hst.2
    omega
  obtain ⟨v,hv⟩ := hne
  apply AffineMap.ext_linear heq (p := q v)
  rw [T.facePlaneMap_vertex q hind s h v (Finset.mem_inter.mp hv).1,
    T.facePlaneMap_vertex q hind t h v (Finset.mem_inter.mp hv).2]

theorem all_facePlane_eq_of_neighbor_linear_eq [Nonempty T.Face]
    (hconvex : Convex ℝ T.domain) (h : V → ℝ)
    (heq : ∀ s t : T.Face, T.faceGraph.Adj s t →
      (T.facePlaneMap q hind s h).linear = (T.facePlaneMap q hind t h).linear)
    (s t : T.Face) : T.facePlaneMap q hind s h = T.facePlaneMap q hind t h := by
  obtain ⟨p⟩ := T.faceGraph_connected hconvex s t
  induction p with
  | nil => rfl
  | cons huv p ih => exact (T.facePlane_eq_of_linear_eq q hind h huv (heq _ _ huv)).trans ih

end Triangulation

namespace TriangularDisk

variable (D : TriangularDisk V) (q : V → ℂ)
  (hind : ∀ s : D.toTriangulation.Face,
    AffineIndependent ℝ (fun v : s.val => q v.val))

theorem height_zero_of_equal_neighbor_gradients
    (hcorner : ∀ j, q (D.corner j) = basePoint j) (h : V → ℝ)
    (hzero : ∀ j, h (D.corner j) = 0)
    (heq : ∀ s t : D.toTriangulation.Face, D.toTriangulation.faceGraph.Adj s t →
      (D.toTriangulation.facePlaneMap q hind s h).linear =
        (D.toTriangulation.facePlaneMap q hind t h).linear) : ∀ v, h v = 0 := by
  obtain ⟨s,hs,hsv⟩ := D.vertex_covered (D.corner 0)
  let s₀ : D.toTriangulation.Face := ⟨s,hs⟩
  letI : Nonempty D.toTriangulation.Face := ⟨s₀⟩
  let L := D.toTriangulation.facePlaneMap q hind s₀ h
  have hconvex : Convex ℝ D.toTriangulation.domain := by
    rw [D.domain_eq]
    exact baseTriangle_convex
  have hLv : ∀ v, L (q v) = h v := by
    intro v
    obtain ⟨t,ht,hvt⟩ := D.vertex_covered v
    have heq' := D.toTriangulation.all_facePlane_eq_of_neighbor_linear_eq
      q hind hconvex h heq s₀ ⟨t,ht⟩
    change D.toTriangulation.facePlaneMap q hind s₀ h (q v) = h v
    rw [heq']
    exact D.toTriangulation.facePlaneMap_vertex q hind ⟨t,ht⟩ h v hvt
  have hbase : ∀ j, L (basePoint j) = 0 := by
    intro j
    rw [← hcorner j,hLv,hzero]
  have Lzero : L = 0 := by
    apply AffineMap.ext_on (s := Set.range basePoint)
    · exact basePoint_affineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
    · rintro z ⟨j,rfl⟩
      exact hbase j
  intro v
  rw [← hLv,Lzero] <;> rfl

end TriangularDisk

end NormalProjective.Planar
end


/- Source section IncidenceAlgebra -/
section


/-!
# Oriented triangle incidences and the actual Maxwell edge differences

The orientation coefficient is computed from the determinant of the actual
three planar vertices. Its row sum vanishes by antisymmetry of that determinant.
Consequently the gradient differences satisfy equilibrium by a literal finite
sum, without an unproved topological incidence assumption.
-/



namespace NormalProjective.Planar

open Set Finset

def numericSign (x : ℝ) : ℝ := if 0 < x then 1 else if x < 0 then -1 else 0

@[simp] theorem numericSign_zero : numericSign 0 = 0 := by simp [numericSign]

theorem numericSign_of_pos {x : ℝ} (hx : 0 < x) : numericSign x = 1 := by
  simp [numericSign,hx]

theorem numericSign_of_neg {x : ℝ} (hx : x < 0) : numericSign x = -1 := by
  simp [numericSign,hx,hx.not_gt]

@[simp] theorem numericSign_neg (x : ℝ) : numericSign (-x) = -numericSign x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [numericSign_of_neg hx,numericSign_of_pos (neg_pos.mpr hx)]
    norm_num
  · simp
  · rw [numericSign_of_pos hx,numericSign_of_neg (neg_neg_of_pos hx)]

@[simp] theorem signedArea_repeat_left (a b : ℂ) : signedArea a b a = 0 := by
  simp [signedArea]

@[simp] theorem signedArea_repeat_right (a b : ℂ) : signedArea a b b = 0 := by
  simp [signedArea] <;> ring

@[simp] theorem signedArea_repeat_base (a x : ℂ) : signedArea a a x = 0 := by
  simp [signedArea]

theorem signedArea_swap_last (a b x : ℂ) : signedArea a x b = -signedArea a b x := by
  unfold signedArea
  ring

theorem signedArea_swap_base (a b x : ℂ) : signedArea b a x = -signedArea a b x := by
  simp only [signedArea,Complex.sub_re,Complex.sub_im]
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]

def faceIncidence (q : V → ℂ) (s : Finset V) (a b : V) : ℝ :=
  if a ∈ s ∧ b ∈ s then ∑ x ∈ s, numericSign (signedArea (q a) (q b) (q x)) else 0

theorem faceIncidence_antisymm (q : V → ℂ) (s : Finset V) (a b : V) :
    faceIncidence q s b a = -faceIncidence q s a b := by
  by_cases ha : a ∈ s
  · by_cases hb : b ∈ s
    · simp only [faceIncidence,ha,hb,and_self,ite_true]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [signedArea_swap_base,numericSign_neg]
    · simp [faceIncidence,ha,hb]
  · simp [faceIncidence,ha]

@[simp] theorem faceIncidence_self (q : V → ℂ) (s : Finset V) (a : V) :
    faceIncidence q s a a = 0 := by simp [faceIncidence]

theorem faceIncidence_row_sum (q : V → ℂ) (s : Finset V) (a : V) :
    ∑ b, faceIncidence q s a b = 0 := by
  by_cases ha : a ∈ s
  · have hreduce : ∑ b, faceIncidence q s a b =
        ∑ b ∈ s, ∑ x ∈ s, numericSign (signedArea (q a) (q b) (q x)) := by
      rw [← Finset.sum_subset (Finset.subset_univ s) (fun b hb hbs => by
        simp [faceIncidence,hbs])]
      exact Finset.sum_congr rfl (fun b hb => by simp only [faceIncidence,ha,hb,and_self,ite_true])
    rw [hreduce]
    have hneg : (∑ b ∈ s, ∑ x ∈ s, numericSign (signedArea (q a) (q b) (q x))) =
        -(∑ b ∈ s, ∑ x ∈ s, numericSign (signedArea (q a) (q b) (q x))) := by
      calc
        _ = ∑ x ∈ s, ∑ b ∈ s, numericSign (signedArea (q a) (q b) (q x)) :=
          Finset.sum_comm
        _ = ∑ x ∈ s, ∑ b ∈ s, -numericSign (signedArea (q a) (q x) (q b)) := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro b hb
          rw [signedArea_swap_last,numericSign_neg]
        _ = _ := by simp only [Finset.sum_neg_distrib]
    linarith
  · simp [faceIncidence,ha]

theorem faceIncidence_triple (q : V → ℂ) {a b x : V}
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    faceIncidence q {a,b,x} a b = numericSign (signedArea (q a) (q b) (q x)) := by
  simp [faceIncidence,hab,hxa,hxb]

def affineGradient (L : ℂ →ᵃ[ℝ] ℝ) : ℂ :=
  (L.linear 1 : ℂ) + (L.linear Complex.I : ℂ)*Complex.I

@[simp] theorem affineGradient_re (L : ℂ →ᵃ[ℝ] ℝ) :
    (affineGradient L).re = L.linear 1 := by simp [affineGradient]

@[simp] theorem affineGradient_im (L : ℂ →ᵃ[ℝ] ℝ) :
    (affineGradient L).im = L.linear Complex.I := by simp [affineGradient]

theorem realLinear_complex_coordinates (L : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    L z = z.re * L 1 + z.im * L Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg L hz
    _ = z.re * L 1 + z.im * L Complex.I := by
      simp only [map_add,map_smul,smul_eq_mul]

theorem affineGradient_dot_difference (L : ℂ →ᵃ[ℝ] ℝ) (a b : ℂ) :
    (affineGradient L).re * (b-a).re + (affineGradient L).im * (b-a).im = L b-L a := by
  rw [affineGradient_re,affineGradient_im]
  have h := realLinear_complex_coordinates L.linear (b-a)
  rw [← vsub_eq_sub,AffineMap.linear_apply_vsub] at h
  simpa only [vsub_eq_sub,mul_comm] using h.symm

theorem affineGradient_linear_eq {L M : ℂ →ᵃ[ℝ] ℝ}
    (h : affineGradient L = affineGradient M) : L.linear = M.linear := by
  have hre : L.linear 1 = M.linear 1 := by
    simpa using congrArg Complex.re h
  have him : L.linear Complex.I = M.linear Complex.I := by
    simpa using congrArg Complex.im h
  ext z
  rw [realLinear_complex_coordinates L.linear z,realLinear_complex_coordinates M.linear z,hre,him]

namespace Triangulation

variable (T : Triangulation V) (q : V → ℂ)
  (hind : ∀ s : T.Face, AffineIndependent ℝ (fun v : s.val => q v.val))

def edgeGradientDifference (h : V → ℝ) (a b : V) : ℂ :=
  -∑ s : T.Face, faceIncidence q s.val a b •
    affineGradient (T.facePlaneMap q hind s h)

theorem edgeGradientDifference_antisymm (h : V → ℝ) (a b : V) :
    T.edgeGradientDifference q hind h b a = -T.edgeGradientDifference q hind h a b := by
  have hs : (∑ s : T.Face, faceIncidence q s.val b a •
      affineGradient (T.facePlaneMap q hind s h)) =
      -(∑ s : T.Face, faceIncidence q s.val a b •
        affineGradient (T.facePlaneMap q hind s h)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    rw [faceIncidence_antisymm q s.val a b,neg_smul]
  simp only [edgeGradientDifference,hs,neg_neg]

theorem edgeGradientDifference_row_sum (h : V → ℝ) (a : V) :
    ∑ b, T.edgeGradientDifference q hind h a b = 0 := by
  simp only [edgeGradientDifference,Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul,faceIncidence_row_sum,zero_smul]
  simp

theorem edgeGradientDifference_off_graph (h : V → ℝ) {a b : V}
    (hab : ¬ T.graph.Adj a b) : T.edgeGradientDifference q hind h a b = 0 := by
  by_cases heq : a = b
  · subst b
    simp [edgeGradientDifference]
  · unfold edgeGradientDifference
    have hz : ∀ s : T.Face, faceIncidence q s.val a b = 0 := by
      intro s
      have hnot : ¬ (a ∈ s.val ∧ b ∈ s.val) := by
        rintro ⟨ha,hb⟩
        exact hab ⟨heq,s.val,s.property,ha,hb⟩
      simp [faceIncidence,hnot]
    simp [hz]

end Triangulation

end NormalProjective.Planar
end


/- Source section LinearLifting -/
section


/-!
# Exactness and a continuous canonical left inverse for Maxwell lifting

The geometric rank and incidence assertions are supplied by their separate
proofs. This file proves the finite-dimensional conclusion and its continuous
matrix formula; it does not assume an unproved lifting theorem.
-/



namespace NormalProjective.Planar

open Matrix

theorem range_eq_kernel_of_dimensions
    {H E F : Type*} [AddCommGroup H] [AddCommGroup E] [AddCommGroup F]
    [Module ℝ H] [Module ℝ E] [Module ℝ F]
    [FiniteDimensional ℝ H] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : H →ₗ[ℝ] E) (B : E →ₗ[ℝ] F)
    (hA : Function.Injective A) (hB : Function.Surjective B)
    (hzero : B.comp A = 0)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ H + Module.finrank ℝ F) :
    LinearMap.range A = LinearMap.ker B := by
  have hle : LinearMap.range A ≤ LinearMap.ker B := by
    rintro e ⟨h,rfl⟩
    change B (A h) = 0
    exact LinearMap.congr_fun hzero h
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hrA : Module.finrank ℝ (LinearMap.range A) = Module.finrank ℝ H :=
    LinearMap.finrank_range_of_inj hA
  have hrB : Module.finrank ℝ (LinearMap.range B) = Module.finrank ℝ F := by
    rw [LinearMap.range_eq_top.mpr hB]
    simp
  have hrank := B.finrank_range_add_finrank_ker
  omega

theorem existsUnique_lifting_of_dimensions
    {H E F : Type*} [AddCommGroup H] [AddCommGroup E] [AddCommGroup F]
    [Module ℝ H] [Module ℝ E] [Module ℝ F]
    [FiniteDimensional ℝ H] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : H →ₗ[ℝ] E) (B : E →ₗ[ℝ] F)
    (hA : Function.Injective A) (hB : Function.Surjective B)
    (hzero : B.comp A = 0)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ H + Module.finrank ℝ F)
    (w : E) (hw : B w = 0) : ∃! h, A h = w := by
  have hmem : w ∈ LinearMap.range A := by
    rw [range_eq_kernel_of_dimensions A B hA hB hzero hdim]
    exact hw
  obtain ⟨h,hh⟩ := hmem
  exact ⟨h,hh,fun k hk => hA (hk.trans hh.symm)⟩

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem gram_isUnit (M : Matrix J I ℝ) (hM : Function.Injective M.mulVec) :
    IsUnit (Mᵀ * M) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hz : (Mᵀ*M) *ᵥ (x-y) = 0 := by
    rw [Matrix.mulVec_sub,hxy,sub_self]
  have hnorm : (M *ᵥ (x-y)) ⬝ᵥ (M *ᵥ (x-y)) = 0 := by
    have h := congrArg (fun z => (x-y) ⬝ᵥ z) hz
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,
      dotProduct_zero] at h
    exact h
  have hMx : M *ᵥ (x-y) = 0 := dotProduct_self_eq_zero.mp hnorm
  have heq : x-y = 0 := hM (by simpa using hMx)
  exact sub_eq_zero.mp heq

def liftingLeftInverse (M : Matrix J I ℝ) (w : J → ℝ) : I → ℝ :=
  (Mᵀ*M)⁻¹ *ᵥ (Mᵀ *ᵥ w)

theorem liftingLeftInverse_apply (M : Matrix J I ℝ) (hM : Function.Injective M.mulVec)
    (h : I → ℝ) : liftingLeftInverse M (M *ᵥ h) = h := by
  have hu : IsUnit (Mᵀ*M).det := (Matrix.isUnit_iff_isUnit_det _).mp (gram_isUnit M hM)
  rw [liftingLeftInverse,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
    Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hu,Matrix.one_mulVec]

theorem liftingLeftInverse_solution (M : Matrix J I ℝ) (hM : Function.Injective M.mulVec)
    (w : J → ℝ) (hw : ∃ h, M *ᵥ h = w) : M *ᵥ liftingLeftInverse M w = w := by
  obtain ⟨h,rfl⟩ := hw
  rw [liftingLeftInverse_apply M hM]

theorem continuous_liftingLeftInverse {X : Type*} [TopologicalSpace X]
    (M : X → Matrix J I ℝ) (w : X → J → ℝ)
    (hM : Continuous M) (hw : Continuous w)
    (hinj : ∀ x, Function.Injective (M x).mulVec) :
    Continuous (fun x => liftingLeftInverse (M x) (w x)) := by
  have hMt : Continuous (fun x => (M x)ᵀ) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_apply i).comp ((continuous_apply j).comp hM)
  have hgram : Continuous (fun x => (M x)ᵀ * M x) := hMt.matrix_mul hM
  have hdet : ∀ x, ((M x)ᵀ*M x).det ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (gram_isUnit (M x) (hinj x))).ne_zero
  have hinv : Continuous (fun x => ((M x)ᵀ*M x)⁻¹) := by
    simp only [Matrix.inv_def,Ring.inverse_eq_inv]
    exact (hgram.matrix_det.inv₀ hdet).smul hgram.matrix_adjugate
  exact hinv.matrix_mulVec (hMt.matrix_mulVec hw)

end NormalProjective.Planar
end
end

/- Source section MaxwellIncidence -/
section
namespace NormalProjective.Planar

open Set Finset
open Maxwell

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

theorem incident_face_sign {a b : V} (hab : a ≠ b)
    (s : T.IncidentFace a b) :
    faceIncidence T.point s.val.val a b =
      if T.incidentSide hab s then (1 : ℝ) else -1 := by
  have hs := T.edgeThird_spec hab s
  rw [hs.2.2,faceIncidence_triple T.point hab hs.1 hs.2.1]
  have hd : T.point b - T.point a ≠ 0 :=
    sub_ne_zero.mpr (T.point_injective.ne hab.symm)
  have hn : 0 < Complex.normSq (T.point b-T.point a) := Complex.normSq_pos.mpr hd
  have hne := T.edgeThird_height_ne_zero hab s
  by_cases hp : 0 < edgeHeight (T.point a) (T.point b) (T.point (T.edgeThird hab s))
  · have ha : 0 < signedArea (T.point a) (T.point b) (T.point (T.edgeThird hab s)) := by
      rw [edgeHeight_eq_area_div] at hp
      exact (div_pos_iff_of_pos_right hn).mp hp
    simp [incidentSide,hp,numericSign_of_pos ha]
  · have hm : edgeHeight (T.point a) (T.point b) (T.point (T.edgeThird hab s)) < 0 :=
      lt_of_le_of_ne (not_lt.mp hp) hne
    have ha : signedArea (T.point a) (T.point b) (T.point (T.edgeThird hab s)) < 0 := by
      rw [edgeHeight_eq_area_div] at hm
      simpa only [zero_mul] using (div_lt_iff₀ hn).mp hm
    simp [incidentSide,hp,numericSign_of_neg ha]

theorem sum_faceIncidence_eq_incident (q : V → ℂ) (a b : V) :
    (∑ s : T.Face, faceIncidence q s.val a b) =
      ∑ s : T.IncidentFace a b, faceIncidence q s.val.val a b := by
  classical
  let S := (Finset.univ : Finset T.Face).filter (fun s => a ∈ s.val ∧ b ∈ s.val)
  have heq : (∑ s ∈ S, faceIncidence q s.val a b) =
      ∑ s : T.IncidentFace a b, faceIncidence q s.val.val a b := by
    apply Finset.sum_subtype
    intro s
    simp [S]
  rw [← heq]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s hs hnot
  have hn : ¬(a ∈ s.val ∧ b ∈ s.val) := by simpa [S] using hnot
  simp [faceIncidence,hn]

end Triangulation

namespace TriangularDisk

variable (D : TriangularDisk V)

theorem interior_edge_incidence_balance {a b : V}
    (hab : D.toTriangulation.graph.Adj a b)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary) :
    ∑ s : D.toTriangulation.Face, faceIncidence D.point s.val a b = 0 := by
  classical
  rw [D.toTriangulation.sum_faceIncidence_eq_incident]
  let f := D.toTriangulation.incidentSide hab.1
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨D.toTriangulation.incidentSide_injective hab.1,
        by simpa using D.incidentFace_card_eq_two hab hi⟩
  let e : D.toTriangulation.IncidentFace a b ≃ Bool := Equiv.ofBijective f hf
  calc
    (∑ s : D.toTriangulation.IncidentFace a b,
        faceIncidence D.point s.val.val a b) =
        ∑ s : D.toTriangulation.IncidentFace a b, if e s then (1 : ℝ) else -1 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact D.toTriangulation.incident_face_sign hab.1 s
    _ = ∑ k : Bool, if k then (1 : ℝ) else -1 :=
      e.sum_comp (fun k : Bool => if k then (1 : ℝ) else -1)
    _ = 0 := by simp

abbrev facePlane (h : V → ℝ) (s : D.toTriangulation.Face) : ℂ →ᵃ[ℝ] ℝ :=
  D.toTriangulation.facePlaneMap D.point
    (fun s => D.face_independent s.val s.property) s h

abbrev edgeDifference (h : V → ℝ) (a b : V) : ℂ :=
  D.toTriangulation.edgeGradientDifference D.point
    (fun s => D.face_independent s.val s.property) h a b

theorem interior_edge_difference_perpendicular (h : V → ℝ) {a b : V}
    (hab : D.toTriangulation.graph.Adj a b)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary) :
    realDot (D.edgeDifference h a b) (D.point b-D.point a) = 0 := by
  classical
  let d := D.point b-D.point a
  have hterm (s : D.toTriangulation.Face) :
      faceIncidence D.point s.val a b * realDot (affineGradient (D.facePlane h s)) d =
        faceIncidence D.point s.val a b * (h b-h a) := by
    by_cases hs : a ∈ s.val ∧ b ∈ s.val
    · congr 1
      rw [realDot,affineGradient_dot_difference]
      rw [D.toTriangulation.facePlaneMap_vertex D.point _ s h b hs.2,
        D.toTriangulation.facePlaneMap_vertex D.point _ s h a hs.1]
    · simp [faceIncidence,hs]
  change realDotLinear d (-∑ s : D.toTriangulation.Face,
    faceIncidence D.point s.val a b • affineGradient (D.facePlane h s)) = 0
  rw [map_neg,map_sum]
  simp_rw [map_smul,smul_eq_mul]
  change -(∑ s : D.toTriangulation.Face,
    faceIncidence D.point s.val a b * realDot (affineGradient (D.facePlane h s)) d) = 0
  simp_rw [hterm]
  rw [← Finset.sum_mul,D.interior_edge_incidence_balance hab hi,zero_mul,neg_zero]

def stressAt (h : V → ℝ) (a b : V) : ℝ :=
  perpendicularCoefficient (D.point b-D.point a) (D.edgeDifference h a b)

theorem stressAt_symm (h : V → ℝ) (a b : V) :
    D.stressAt h b a = D.stressAt h a b := by
  change perpendicularCoefficient (D.point a-D.point b)
    (D.toTriangulation.edgeGradientDifference D.point _ h b a) = _
  rw [D.toTriangulation.edgeGradientDifference_antisymm,← neg_sub]
  exact perpendicularCoefficient_neg _ _

theorem interior_edge_stress_identity (h : V → ℝ) {a b : V}
    (hab : D.toTriangulation.graph.Adj a b)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary) :
    D.edgeDifference h a b = D.stressAt h a b • turn (D.point b-D.point a) :=
  perpendicular_decomposition (sub_ne_zero.mpr (D.point_injective.ne hab.1.symm))
    (D.interior_edge_difference_perpendicular h hab hi)

end TriangularDisk

end NormalProjective.Planar
end

/- Source section MaxwellStress -/
section
namespace NormalProjective.Planar

open Set Finset
open Maxwell

def affineGradientLinear : (ℂ →ᵃ[ℝ] ℝ) →ₗ[ℝ] ℂ where
  toFun := affineGradient
  map_add' L M := by
    apply Complex.ext <;> simp [affineGradient]
  map_smul' r L := by
    apply Complex.ext <;> simp [affineGradient,Complex.real_smul]

namespace TriangularDisk

variable {V : Type*} [Fintype V] [DecidableEq V] (D : TriangularDisk V)

def edgeDifferenceLinear (a b : V) : (V → ℝ) →ₗ[ℝ] ℂ :=
  -(∑ s : D.toTriangulation.Face, faceIncidence D.point s.val a b •
    (affineGradientLinear.comp (D.toTriangulation.facePlaneMap D.point
      (fun s => D.face_independent s.val s.property) s)))

theorem edgeDifferenceLinear_apply (h : V → ℝ) (a b : V) :
    D.edgeDifferenceLinear a b h = D.edgeDifference h a b := by
  simp [edgeDifferenceLinear,edgeDifference,Triangulation.edgeGradientDifference,
    affineGradientLinear]

def stressLinear : (D.InteriorVertex → ℝ) →ₗ[ℝ] (D.InteriorEdge → ℝ) :=
  LinearMap.pi (fun e =>
    (coefficientLinear (D.point (D.interiorEdgeRight e)-D.point (D.interiorEdgeLeft e))).comp
      ((D.edgeDifferenceLinear (D.interiorEdgeLeft e) (D.interiorEdgeRight e)).comp
        D.extendInteriorLinear))

theorem stressLinear_apply (h : D.InteriorVertex → ℝ) (e : D.InteriorEdge) :
    D.stressLinear h e = D.stressAt (D.extendInterior h)
      (D.interiorEdgeLeft e) (D.interiorEdgeRight e) := by
  change perpendicularCoefficient _ (D.edgeDifferenceLinear _ _ (D.extendInterior h)) = _
  rw [D.edgeDifferenceLinear_apply] <;> rfl

theorem stressLinear_on_edge (h : D.InteriorVertex → ℝ) {a b : V}
    (hab : D.toTriangulation.graph.Adj a b)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary) :
    D.stressLinear h (D.edgeOfAdjacent hab hi) = D.stressAt (D.extendInterior h) a b := by
  rw [D.stressLinear_apply]
  have hp : {D.interiorEdgeLeft (D.edgeOfAdjacent hab hi),
        D.interiorEdgeRight (D.edgeOfAdjacent hab hi)} = ({a,b} : Finset V) :=
    (D.interiorEdge_endpoints (D.edgeOfAdjacent hab hi)).2.symm
  rcases edge_pair_eq_iff.mp hp with horder | horder
  · rw [horder.1,horder.2]
  · rw [horder.1,horder.2,D.stressAt_symm]

def edgeWeightLinear (a b : V) : (D.InteriorEdge → ℝ) →ₗ[ℝ] ℝ where
  toFun w := D.edgeWeight w a b
  map_add' w z := by
    classical
    simp only [edgeWeight]
    split_ifs <;> simp
  map_smul' r w := by
    classical
    simp only [edgeWeight]
    split_ifs <;> simp

def equilibriumLinear : (D.InteriorEdge → ℝ) →ₗ[ℝ] (D.InteriorVertex → ℂ) :=
  LinearMap.pi (fun a => ∑ b : V,
    (D.edgeWeightLinear a.val b).smulRight (D.point b-D.point a.val))

theorem equilibriumLinear_apply (w : D.InteriorEdge → ℝ) (a : D.InteriorVertex) :
    D.equilibriumLinear w a = ∑ b : V, D.edgeWeight w a.val b • (D.point b-D.point a.val) := by
  simp [equilibriumLinear,edgeWeightLinear]

theorem difference_eq_weight_turn (h : D.InteriorVertex → ℝ) (a : D.InteriorVertex) (b : V) :
    D.edgeDifference (D.extendInterior h) a.val b =
      D.edgeWeight (D.stressLinear h) a.val b • turn (D.point b-D.point a.val) := by
  by_cases hab : D.toTriangulation.graph.Adj a.val b
  · have hi : a.val ∉ D.boundary ∨ b ∉ D.boundary := Or.inl a.property
    rw [D.edgeWeight_of_adj _ hab hi,D.stressLinear_on_edge h hab hi]
    exact D.interior_edge_stress_identity (D.extendInterior h) hab hi
  · have hz : D.edgeDifference (D.extendInterior h) a.val b = 0 :=
      D.toTriangulation.edgeGradientDifference_off_graph D.point _ (D.extendInterior h) hab
    rw [hz]
    simp [edgeWeight,hab]

theorem equilibrium_stress (h : D.InteriorVertex → ℝ) :
    D.equilibriumLinear (D.stressLinear h) = 0 := by
  funext a
  change D.equilibriumLinear (D.stressLinear h) a = (0 : ℂ)
  rw [D.equilibriumLinear_apply]
  have hturn : turnLinear (∑ b : V,
      D.edgeWeight (D.stressLinear h) a.val b • (D.point b-D.point a.val)) = 0 := by
    rw [map_sum]
    simp_rw [map_smul]
    change (∑ b : V, D.edgeWeight (D.stressLinear h) a.val b •
      turn (D.point b-D.point a.val)) = 0
    simp_rw [← D.difference_eq_weight_turn h a]
    exact D.toTriangulation.edgeGradientDifference_row_sum D.point _ (D.extendInterior h) a.val
  change turn (∑ b : V,
    D.edgeWeight (D.stressLinear h) a.val b • (D.point b-D.point a.val)) = 0 at hturn
  have hh := congrArg turn hturn
  simpa only [turn_turn,turn_zero,neg_eq_zero] using hh

theorem equilibrium_comp_stress : D.equilibriumLinear.comp D.stressLinear = 0 := by
  apply LinearMap.ext
  intro h
  funext a
  exact congrFun (D.equilibrium_stress h) a

end TriangularDisk
end NormalProjective.Planar
end

/- Source section MaxwellInjective -/
section
namespace NormalProjective.Planar.Triangulation

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (T : Triangulation V)

theorem incident_eq_one_of_two {a b : V} (hab : a ≠ b)
    (s t : T.IncidentFace a b) (hst : s ≠ t) (u : T.IncidentFace a b) :
    u = s ∨ u = t := by
  have hside : T.incidentSide hab s ≠ T.incidentSide hab t :=
    (T.incidentSide_injective hab).ne hst
  have hu : T.incidentSide hab u = T.incidentSide hab s ∨
      T.incidentSide hab u = T.incidentSide hab t := by
    cases hs : T.incidentSide hab s <;>
      cases ht : T.incidentSide hab t <;>
      cases hv : T.incidentSide hab u <;> simp_all
  exact hu.imp (fun h => T.incidentSide_injective hab h)
    (fun h => T.incidentSide_injective hab h)

theorem sum_faces_of_two_incident {M : Type*} [AddCommMonoid M]
    {a b : V} (hab : a ≠ b) (s t : T.Face) (hst : s ≠ t)
    (hs : a ∈ s.val ∧ b ∈ s.val) (ht : a ∈ t.val ∧ b ∈ t.val)
    (f : T.Face → M) (hz : ∀ u, ¬(a ∈ u.val ∧ b ∈ u.val) → f u = 0) :
    ∑ u : T.Face, f u = f s + f t := by
  classical
  have hrestrict : (∑ u ∈ ({s,t} : Finset T.Face), f u) = ∑ u : T.Face, f u := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u hu hnot
    apply hz u
    intro hui
    let si : T.IncidentFace a b := ⟨s,hs⟩
    let ti : T.IncidentFace a b := ⟨t,ht⟩
    let ui : T.IncidentFace a b := ⟨u,hui⟩
    have hsit : si ≠ ti := fun he => hst (congrArg Subtype.val he)
    rcases T.incident_eq_one_of_two hab si ti hsit ui with he | he
    · apply hnot
      have : u = s := congrArg Subtype.val he
      simp [this]
    · apply hnot
      have : u = t := congrArg Subtype.val he
      simp [this]
  simpa only [Finset.sum_pair hst] using hrestrict.symm

end NormalProjective.Planar.Triangulation

namespace NormalProjective.Planar.TriangularDisk

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (D : TriangularDisk V)

theorem shared_edge_interior {a b : V} (hab : a ≠ b)
    (s t : D.toTriangulation.Face) (hst : s ≠ t)
    (hs : a ∈ s.val ∧ b ∈ s.val) (ht : a ∈ t.val ∧ b ∈ t.val) :
    a ∉ D.boundary ∨ b ∉ D.boundary := by
  by_contra h
  push_neg at h
  letI := D.boundary_incidentFace_subsingleton hab h.1 h.2
  let si : D.toTriangulation.IncidentFace a b := ⟨s,hs⟩
  let ti : D.toTriangulation.IncidentFace a b := ⟨t,ht⟩
  exact hst (congrArg Subtype.val (Subsingleton.elim si ti))

theorem incident_coefficient_ne_zero {a b : V} (hab : a ≠ b)
    (s : D.toTriangulation.Face) (hs : a ∈ s.val ∧ b ∈ s.val) :
    faceIncidence D.point s.val a b ≠ 0 := by
  have hsign := D.toTriangulation.incident_face_sign hab ⟨s,hs⟩
  rw [hsign]
  split_ifs <;> norm_num

theorem gradients_eq_of_edge_difference_zero (h : V → ℝ) {a b : V}
    (hab : a ≠ b) (s t : D.toTriangulation.Face) (hst : s ≠ t)
    (hs : a ∈ s.val ∧ b ∈ s.val) (ht : a ∈ t.val ∧ b ∈ t.val)
    (hzero : D.edgeDifference h a b = 0) :
    affineGradient (D.facePlane h s) = affineGradient (D.facePlane h t) := by
  have habG : D.toTriangulation.graph.Adj a b := ⟨hab,s.val,s.property,hs.1,hs.2⟩
  have hi := D.shared_edge_interior hab s t hst hs ht
  have hsum : (∑ u : D.toTriangulation.Face, faceIncidence D.point u.val a b) =
      faceIncidence D.point s.val a b + faceIncidence D.point t.val a b :=
    D.toTriangulation.sum_faces_of_two_incident hab s t hst hs ht _
      (fun u hu => by simp [faceIncidence,hu])
  have hb := D.interior_edge_incidence_balance habG hi
  rw [hsum] at hb
  have htneg : faceIncidence D.point t.val a b = -faceIncidence D.point s.val a b := by
    linarith
  have hsumgrad : (∑ u : D.toTriangulation.Face,
      faceIncidence D.point u.val a b • affineGradient (D.facePlane h u)) =
      faceIncidence D.point s.val a b • affineGradient (D.facePlane h s) +
        faceIncidence D.point t.val a b • affineGradient (D.facePlane h t) :=
    D.toTriangulation.sum_faces_of_two_incident hab s t hst hs ht _
      (fun u hu => by simp [faceIncidence,hu])
  change -(∑ u : D.toTriangulation.Face,
    faceIncidence D.point u.val a b • affineGradient (D.facePlane h u)) = 0 at hzero
  rw [hsumgrad,neg_eq_zero,htneg,neg_smul,← sub_eq_add_neg,← smul_sub] at hzero
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left
    (D.incident_coefficient_ne_zero hab s hs))

theorem stressLinear_injective : Function.Injective D.stressLinear := by
  intro h k hhk
  have hz : D.stressLinear (h-k) = 0 := by rw [map_sub,hhk,sub_self]
  have hheight : ∀ v, D.extendInterior (h-k) v = 0 := by
    apply D.height_zero_of_equal_neighbor_gradients D.point
      (fun s => D.face_independent s.val s.property) D.corner_point
      (D.extendInterior (h-k)) (D.extendInterior_corner (h-k))
    intro s t hst
    have hcard := hst.2
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (s.val ∩ t.val).card)
    have hs : a ∈ s.val ∧ b ∈ s.val :=
      ⟨(Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp hb).1⟩
    have ht : a ∈ t.val ∧ b ∈ t.val :=
      ⟨(Finset.mem_inter.mp ha).2,(Finset.mem_inter.mp hb).2⟩
    have habG : D.toTriangulation.graph.Adj a b := ⟨hab,s.val,s.property,hs.1,hs.2⟩
    have hi := D.shared_edge_interior hab s t hst.1 hs ht
    have hcoeff : D.stressAt (D.extendInterior (h-k)) a b = 0 := by
      have hh := congrFun hz (D.edgeOfAdjacent habG hi)
      rw [D.stressLinear_on_edge] at hh
      exact hh
    have hdiff : D.edgeDifference (D.extendInterior (h-k)) a b = 0 := by
      rw [D.interior_edge_stress_identity (D.extendInterior (h-k)) habG hi,hcoeff,zero_smul]
    exact affineGradient_linear_eq
      (D.gradients_eq_of_edge_difference_zero (D.extendInterior (h-k)) hab s t hst.1 hs ht hdiff)
  funext i
  have hi := hheight i.val
  rw [D.extendInterior_at,Pi.sub_apply] at hi
  exact sub_eq_zero.mp hi

end NormalProjective.Planar.TriangularDisk
end

/- Source section MaxwellSurjective -/
section
namespace NormalProjective.Planar.TriangularDisk

open Set Finset
open Maxwell

variable {V : Type*} [Fintype V] [DecidableEq V] (D : TriangularDisk V)

theorem edgeOfAdjacent_eq_iff {a b : V} (hab : D.toTriangulation.graph.Adj a b)
    (hi : a ∉ D.boundary ∨ b ∉ D.boundary) (e : D.InteriorEdge) :
    D.edgeOfAdjacent hab hi = e ↔
      (a = D.interiorEdgeLeft e ∧ b = D.interiorEdgeRight e) ∨
      (a = D.interiorEdgeRight e ∧ b = D.interiorEdgeLeft e) := by
  constructor
  · intro he
    have hs := congrArg Subtype.val he
    change ({a,b} : Finset V) = e.val at hs
    rw [(D.interiorEdge_endpoints e).2] at hs
    exact edge_pair_eq_iff.mp hs
  · intro h
    apply Subtype.ext
    change ({a,b} : Finset V) = e.val
    rw [(D.interiorEdge_endpoints e).2]
    exact edge_pair_eq_iff.mpr h

theorem edgeWeight_basis (e : D.InteriorEdge) (a b : V) :
    D.edgeWeight (Pi.single e (1 : ℝ)) a b =
      (if a = D.interiorEdgeLeft e ∧ b = D.interiorEdgeRight e then 1 else 0) +
      (if a = D.interiorEdgeRight e ∧ b = D.interiorEdgeLeft e then 1 else 0) := by
  classical
  have hlr := (D.interiorEdge_endpoints e).1
  by_cases h : D.toTriangulation.graph.Adj a b ∧ (a ∉ D.boundary ∨ b ∉ D.boundary)
  · rw [D.edgeWeight_of_adj _ h.1 h.2]
    by_cases he : D.edgeOfAdjacent h.1 h.2 = e
    · rw [he,Pi.single_eq_same]
      rcases (D.edgeOfAdjacent_eq_iff h.1 h.2 e).mp he with hc | hc
      · simp [hc.1,hc.2,hlr,Ne.symm hlr]
      · simp [hc.1,hc.2,hlr,Ne.symm hlr]
    · have hnot := (not_congr (D.edgeOfAdjacent_eq_iff h.1 h.2 e)).mp he
      have h1 := not_or.mp hnot |>.1
      have h2 := not_or.mp hnot |>.2
      simp [Pi.single_apply,he,Ne.symm he,h1,h2]
  · have h1 : ¬(a = D.interiorEdgeLeft e ∧ b = D.interiorEdgeRight e) := by
      rintro ⟨rfl,rfl⟩
      exact h ⟨D.interiorEdge_adj e,D.interiorEdge_interior e⟩
    have h2 : ¬(a = D.interiorEdgeRight e ∧ b = D.interiorEdgeLeft e) := by
      rintro ⟨rfl,rfl⟩
      exact h ⟨(D.interiorEdge_adj e).symm,(D.interiorEdge_interior e).symm⟩
    simp [edgeWeight,h,h1,h2]

/-- A force at a vertex, automatically zero if that vertex is on the boundary. -/
def vertexForce (v : V) : ℂ →ₗ[ℝ] (D.InteriorVertex → ℂ) where
  toFun z i := if i.val = v then z else 0
  map_add' z w := by
    funext i
    by_cases hi : i.val = v <;> simp [hi]
  map_smul' r z := by
    funext i
    by_cases hi : i.val = v <;> simp [hi]

theorem vertexForce_boundary {v : V} (hv : v ∈ D.boundary) : D.vertexForce v = 0 := by
  ext z i
  have hi : i.val ≠ v := fun he => i.property (he.symm ▸ hv)
  simp [vertexForce,hi]

theorem equilibrium_basis (e : D.InteriorEdge) :
    D.equilibriumLinear (Pi.single e (1 : ℝ)) =
      D.vertexForce (D.interiorEdgeLeft e)
        (D.point (D.interiorEdgeRight e)-D.point (D.interiorEdgeLeft e)) +
      D.vertexForce (D.interiorEdgeRight e)
        (D.point (D.interiorEdgeLeft e)-D.point (D.interiorEdgeRight e)) := by
  classical
  funext a
  rw [D.equilibriumLinear_apply]
  simp_rw [D.edgeWeight_basis,add_smul]
  rw [Finset.sum_add_distrib]
  have hlr := (D.interiorEdge_endpoints e).1
  by_cases ha : a.val = D.interiorEdgeLeft e
  · by_cases hb : a.val = D.interiorEdgeRight e
    · exact False.elim (hlr (ha.symm.trans hb))
    · simp [ha,hb,vertexForce,hlr,Ne.symm hlr]
  · by_cases hb : a.val = D.interiorEdgeRight e
    · simp [ha,hb,vertexForce,hlr,Ne.symm hlr]
    · simp [ha,hb,vertexForce,hlr,Ne.symm hlr]

def dualVelocity (φ : (D.InteriorVertex → ℂ) →ₗ[ℝ] ℝ) (v : V) : ℂ :=
  (φ (D.vertexForce v 1) : ℂ) + (φ (D.vertexForce v Complex.I) : ℂ) * Complex.I

@[simp] theorem dualVelocity_re (φ : (D.InteriorVertex → ℂ) →ₗ[ℝ] ℝ) (v : V) :
    (D.dualVelocity φ v).re = φ (D.vertexForce v 1) := by simp [dualVelocity]

@[simp] theorem dualVelocity_im (φ : (D.InteriorVertex → ℂ) →ₗ[ℝ] ℝ) (v : V) :
    (D.dualVelocity φ v).im = φ (D.vertexForce v Complex.I) := by simp [dualVelocity]

theorem dual_on_vertexForce (φ : (D.InteriorVertex → ℂ) →ₗ[ℝ] ℝ) (v : V) (z : ℂ) :
    φ (D.vertexForce v z) = realDot (D.dualVelocity φ v) z := by
  have hh := realLinear_complex_coordinates (φ.comp (D.vertexForce v)) z
  change φ (D.vertexForce v z) = z.re*φ (D.vertexForce v 1) +
    z.im*φ (D.vertexForce v Complex.I) at hh
  rw [hh,realDot,D.dualVelocity_re,D.dualVelocity_im]
  ring

theorem dualVelocity_boundary (φ : (D.InteriorVertex → ℂ) →ₗ[ℝ] ℝ)
    {v : V} (hv : v ∈ D.boundary) : D.dualVelocity φ v = 0 := by
  simp [dualVelocity,D.vertexForce_boundary hv]

theorem dual_eq_zero_of_velocity_zero (φ : (D.InteriorVertex → ℂ) →ₗ[ℝ] ℝ)
    (hφ : ∀ v, D.dualVelocity φ v = 0) : φ = 0 := by
  classical
  apply LinearMap.ext
  intro x
  have hdecomp : x = ∑ i : D.InteriorVertex, D.vertexForce i.val (x i) := by
    funext j
    simp [vertexForce,Finset.sum_apply,Subtype.val_inj,eq_comm]
  rw [hdecomp,map_sum]
  simp_rw [D.dual_on_vertexForce,hφ]
  simp [realDot]

theorem equilibrium_dual_annihilator_zero
    (φ : (D.InteriorVertex → ℂ) →ₗ[ℝ] ℝ)
    (hφ : ∀ w, φ (D.equilibriumLinear w) = 0) : φ = 0 := by
  apply D.dual_eq_zero_of_velocity_zero φ
  apply D.velocity_zero D.point (D.dualVelocity φ)
    (fun s => D.face_independent s.val s.property)
  · intro j
    exact D.dualVelocity_boundary φ ⟨j,rfl⟩
  · intro a b hab
    by_cases hi : a ∉ D.boundary ∨ b ∉ D.boundary
    · let e := D.edgeOfAdjacent hab hi
      have he := D.interiorEdge_endpoints e
      have hforce : φ (D.equilibriumLinear (Pi.single e (1 : ℝ))) = 0 := hφ _
      rw [D.equilibrium_basis,map_add,D.dual_on_vertexForce,D.dual_on_vertexForce] at hforce
      have hstrain : edgeStrain (D.point (D.interiorEdgeLeft e))
          (D.point (D.interiorEdgeRight e)) (D.dualVelocity φ (D.interiorEdgeLeft e))
          (D.dualVelocity φ (D.interiorEdgeRight e)) = 0 := by
        simp only [realDot,edgeStrain,Complex.sub_re,Complex.sub_im] at hforce ⊢
        linear_combination -hforce
      have hp : ({a,b} : Finset V) =
          {D.interiorEdgeLeft e,D.interiorEdgeRight e} := he.2
      rcases edge_pair_eq_iff.mp hp with horder | horder
      · simpa [horder.1,horder.2] using hstrain
      · simp only [horder.1,horder.2,edgeStrain,Complex.sub_re,Complex.sub_im] at hstrain ⊢
        nlinarith [hstrain]
    · have ha : a ∈ D.boundary := not_not.mp ((not_or.mp hi).1)
      have hb : b ∈ D.boundary := not_not.mp ((not_or.mp hi).2)
      rw [D.dualVelocity_boundary φ ha,D.dualVelocity_boundary φ hb]
      simp [edgeStrain]

/-- Every interior load is produced by some edge stress. This is a consequence
of actual nondegenerate triangles and the proved rigidity theorem. -/
theorem equilibriumLinear_surjective : Function.Surjective D.equilibriumLinear := by
  apply LinearMap.range_eq_top.mp
  by_contra h
  obtain ⟨φ, hφ, hker⟩ :=
    (LinearMap.range D.equilibriumLinear).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.mpr h)
  apply hφ
  apply D.equilibrium_dual_annihilator_zero φ
  intro w
  exact hker ⟨w, rfl⟩

end NormalProjective.Planar.TriangularDisk
end

/- Source section MaxwellPositive -/
section
namespace NormalProjective.Planar.TriangularDisk

open Set Finset
open Maxwell

variable {V : Type*} [Fintype V] [DecidableEq V] (D : TriangularDisk V)

theorem roof_gap_on_positive_side (h : V → ℝ) {a b v : V}
    (hab : a ≠ b) (hva : v ≠ a) (hvb : v ≠ b)
    (s t : D.toTriangulation.Face) (hst : s ≠ t)
    (hs : a ∈ s.val ∧ b ∈ s.val) (ht : t.val = {a,b,v})
    (harea : 0 < signedArea (D.point a) (D.point b) (D.point v)) :
    D.facePlane h s (D.point v)-h v =
      D.stressAt h a b * signedArea (D.point a) (D.point b) (D.point v) := by
  have hta : a ∈ t.val := by simp [ht]
  have htb : b ∈ t.val := by simp [ht]
  have htv : v ∈ t.val := by simp [ht]
  have habG : D.toTriangulation.graph.Adj a b := ⟨hab,s.val,s.property,hs.1,hs.2⟩
  have hi := D.shared_edge_interior hab s t hst hs ⟨hta,htb⟩
  have hsigT : faceIncidence D.point t.val a b = 1 := by
    rw [ht,faceIncidence_triple D.point hab hva hvb,numericSign_of_pos harea]
  have hsum := D.toTriangulation.sum_faces_of_two_incident hab s t hst hs ⟨hta,htb⟩
    (fun u => faceIncidence D.point u.val a b)
    (fun u hu => by simp [faceIncidence,hu])
  have hbalance := D.interior_edge_incidence_balance habG hi
  rw [hsum,hsigT] at hbalance
  have hsigS : faceIncidence D.point s.val a b = -1 := by linarith
  have hdiff : D.edgeDifference h a b =
      affineGradient (D.facePlane h s)-affineGradient (D.facePlane h t) := by
    change -(∑ u : D.toTriangulation.Face,
      faceIncidence D.point u.val a b • affineGradient (D.facePlane h u)) = _
    rw [D.toTriangulation.sum_faces_of_two_incident hab s t hst hs ⟨hta,htb⟩ _
      (fun u hu => by simp [faceIncidence,hu]),hsigS,hsigT]
    simp only [neg_one_smul,one_smul,neg_add_rev,neg_neg]
    simp only [sub_eq_add_neg,add_comm]
  have hDot (L : ℂ →ᵃ[ℝ] ℝ) :
      realDot (affineGradient L) (D.point v-D.point a) = L (D.point v)-L (D.point a) :=
    affineGradient_dot_difference L (D.point a) (D.point v)
  have hsubdot (z w x : ℂ) : realDot (z-w) x = realDot z x-realDot w x := by
    simp only [realDot,Complex.sub_re,Complex.sub_im]
    ring
  calc
    D.facePlane h s (D.point v)-h v =
        realDot (affineGradient (D.facePlane h s)-affineGradient (D.facePlane h t))
          (D.point v-D.point a) := by
      rw [hsubdot,hDot,hDot,
        D.toTriangulation.facePlaneMap_vertex D.point _ s h a hs.1,
        D.toTriangulation.facePlaneMap_vertex D.point _ t h a hta,
        D.toTriangulation.facePlaneMap_vertex D.point _ t h v htv]
      ring
    _ = realDot (D.edgeDifference h a b) (D.point v-D.point a) := by rw [hdiff]
    _ = D.stressAt h a b * signedArea (D.point a) (D.point b) (D.point v) := by
      rw [D.interior_edge_stress_identity h habG hi,realDot_smul,realDot_turn] <;> rfl

theorem stress_positive_local_folds (h : D.InteriorVertex → ℝ)
    (hpos : ∀ e, 0 < D.stressLinear h e) :
    ∀ s t : D.toTriangulation.Face, D.toTriangulation.faceGraph.Adj s t →
      ∀ v ∈ t.val, v ∉ s.val →
        D.extendInterior h v < D.facePlane (D.extendInterior h) s (D.point v) := by
  intro s t hst v hvt hvs
  have hcard := hst.2
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (s.val ∩ t.val).card)
  have hs : a ∈ s.val ∧ b ∈ s.val :=
    ⟨(Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp hb).1⟩
  have ht : a ∈ t.val ∧ b ∈ t.val :=
    ⟨(Finset.mem_inter.mp ha).2,(Finset.mem_inter.mp hb).2⟩
  have hva : v ≠ a := by intro he; subst v; exact hvs hs.1
  have hvb : v ≠ b := by intro he; subst v; exact hvs hs.2
  have htset : t.val = {a,b,v} := by
    symm
    apply Finset.eq_of_subset_of_card_le (by simp [Finset.insert_subset_iff,ht.1,ht.2,hvt])
    rw [D.face_card t.val t.property]
    simp [hab,hva,hvb,Ne.symm hva,Ne.symm hvb]
  have hheight := D.toTriangulation.face_third_height_ne_zero t.property
    ht.1 ht.2 hvt hab hva hvb
  have harea := signedArea_ne_zero_of_height_ne_zero hheight
  have hgap : 0 < D.facePlane (D.extendInterior h) s (D.point v)-D.extendInterior h v := by
    rcases lt_or_gt_of_ne harea with hn | hp
    · have hp' : 0 < signedArea (D.point b) (D.point a) (D.point v) := by
        rw [signedArea_swap_base]
        exact neg_pos.mpr hn
      have htswap : t.val = {b,a,v} := by simpa only [Finset.insert_comm] using htset
      rw [D.roof_gap_on_positive_side (D.extendInterior h) hab.symm hvb hva s t hst.1
        hs.symm htswap hp']
      have habG : D.toTriangulation.graph.Adj b a :=
        ⟨hab.symm,s.val,s.property,hs.2,hs.1⟩
      have hi := D.shared_edge_interior hab.symm s t hst.1 hs.symm ht.symm
      have hw := hpos (D.edgeOfAdjacent habG hi)
      rw [D.stressLinear_on_edge] at hw
      exact mul_pos hw hp'
    · rw [D.roof_gap_on_positive_side (D.extendInterior h) hab hva hvb s t hst.1 hs htset hp]
      have habG : D.toTriangulation.graph.Adj a b :=
        ⟨hab,s.val,s.property,hs.1,hs.2⟩
      have hi := D.shared_edge_interior hab s t hst.1 hs ht
      have hw := hpos (D.edgeOfAdjacent habG hi)
      rw [D.stressLinear_on_edge] at hw
      exact mul_pos hw hp
  exact sub_pos.mp hgap

end NormalProjective.Planar.TriangularDisk
end


/-! Read-only actual-body audit; generated from Verify.lean. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules : Array Name := #[`maxwell_core]
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
  IO.FS.writeFile ".lake/reports/audit/final/MaxwellCore_dependencies.json" result.pretty
  logInfo m!"Audited {records.size} local declarations and {boundaryRecords.size} pinned-library boundaries."
