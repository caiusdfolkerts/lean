module
public import consolidated.deletion_fields
public import consolidated.root_generic
public import consolidated.root_graph
public import consolidated_dev.intrinsic_figure_geometry
public import consolidated_dev.actual_geometry
public import consolidated.incidence_core_geometry
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Sym.Sym2
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option Elab.async false

section BundlePart0
/- Source: Papers/PolytopeBasicExtreme.lean -/





@[expose] public section

/-!
# Thin extreme-vertex facts

Uncompiled draft. These lemmas depend directly on the defining
extreme-point equation of ConvexPolytope and Mathlib's segment
characterization of an extreme point. They replace legacy helper names
that would otherwise pull the large paper proof closure into the
elementary geometry.
-/

namespace Papers.PolytopeBasicExtreme

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem vertex_mem_body (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : v ∈ P.toSet :=
  subset_convexHull ℝ _ hv

theorem vertex_mem_extreme (P : ConvexPolytope d) {v : E d}
    (hv : v ∈ P.vertices) : v ∈ P.toSet.extremePoints ℝ := by
  change v ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
  rw [← P.vertices_eq_extremePoints]
  exact hv

theorem extreme_point_on_segment (A : Set (E d)) {v x y : E d}
    (hv : v ∈ A.extremePoints ℝ) (hx : x ∈ A) (hy : y ∈ A)
    (hseg : v ∈ segment ℝ x y) : v = x ∨ v = y := by
  have h := (mem_extremePoints_iff_forall_segment.mp hv).2 x hx y hy hseg
  exact h.imp Eq.symm Eq.symm

end Papers.PolytopeBasicExtreme

end
end BundlePart0

section BundlePart1
/- Source: Papers/RationalityTenPolygonMorseGraph.lean -/
@[expose] public section







/-!
Finite graph lemmas for the generic-height proof of Euler's formula in
dimension three.  Proper connected induced subgraphs of a connected graph
of degree at most two are trees.  A strict-descent rule makes each nonempty
sublevel induced graph connected.

DRAFT: these proofs have not compiled in the unavailable execution environment.
-/
namespace Papers.RationalityTen.PolygonMorseGraph

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cycle_support_closed
    (hdeg : ∀ v, G.degree v ≤ 2)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle)
    {v w : V} (hv : v ∈ c.support) (hvw : G.Adj v w) :
    w ∈ c.support := by
  let q := c.rotate v hv
  have hq : q.IsCycle := hc.rotate hv
  have hne : q.snd ≠ q.penultimate := hq.snd_ne_penultimate
  have hs : G.Adj v q.snd := SimpleGraph.Walk.adj_snd hq.not_nil
  have ht : G.Adj v q.penultimate :=
    (SimpleGraph.Walk.adj_penultimate hq.not_nil).symm
  have hsub : ({q.snd,q.penultimate} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr hs
    · exact (G.mem_neighborFinset _ _).mpr ht
  have heq : ({q.snd,q.penultimate} : Finset V) = G.neighborFinset v := by
    apply Finset.eq_of_subset_of_card_le hsub
    have hh := hdeg v
    change (G.neighborFinset v).card ≤ 2 at hh
    simpa [hne] using hh
  have hw : w ∈ ({q.snd,q.penultimate} : Finset V) := by
    rw [heq]
    exact (G.mem_neighborFinset _ _).mpr hvw
  have hwq : w ∈ q.support := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact q.getVert_mem_support 1
    · exact q.getVert_mem_support (q.length - 1)
  exact (c.mem_support_rotate_iff v hv).mp hwq

theorem cycle_support_all
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    ∀ v, v ∈ c.support := by
  have hwalk : ∀ {a b : V} (p : G.Walk a b),
      a ∈ c.support → b ∈ c.support := by
    intro a b p
    induction p with
    | nil => exact fun h => h
    | @cons a b d hab p ih =>
        intro ha
        exact ih (cycle_support_closed G hdeg c hc ha hab)
  intro v
  obtain ⟨p⟩ := hconn.preconnected u v
  exact hwalk p c.start_mem_support

/-- This requires a genuinely proper vertex subset.  In particular it does
not assert that the entire polygon graph is acyclic. -/
theorem proper_induce_acyclic
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    (S : Set V) (hproper : ∃ v, v ∉ S) :
    (G.induce S).IsAcyclic := by
  classical
  intro v c hc
  let f : G.induce S →g G := (SimpleGraph.Embedding.induce S).toHom
  have hf : Function.Injective f := Subtype.val_injective
  have hm : (c.map f).IsCycle := hc.map hf
  obtain ⟨w, hw⟩ := hproper
  have hws := cycle_support_all G hconn hdeg (c.map f) hm w
  rw [SimpleGraph.Walk.support_map] at hws
  obtain ⟨x,hx,hxw⟩ := List.mem_map.mp hws
  exact hw (hxw ▸ x.property)

theorem proper_connected_induce_tree
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    (S : Set V) (hproper : ∃ v, v ∉ S)
    (hS : (G.induce S).Connected) :
    (G.induce S).IsTree :=
  ⟨hS, proper_induce_acyclic G hconn hdeg S hproper⟩

theorem proper_connected_induce_edge_count
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    (S : Set V) (hproper : ∃ v, v ∉ S)
    (hS : (G.induce S).Connected) :
    Nat.card (G.induce S).edgeSet + 1 = Nat.card S := by
  classical
  letI : Fintype S := Fintype.ofFinite _
  letI : Fintype (G.induce S).edgeSet := Fintype.ofFinite _
  have hh := (proper_connected_induce_tree G hconn hdeg S hproper hS).card_edgeFinset
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using hh

noncomputable def lowerRank (φ : V → ℝ) (v : V) : Nat :=
  (Finset.univ.filter fun w => φ w < φ v).card

theorem lowerRank_lt {φ : V → ℝ} {v w : V} (h : φ v < φ w) :
    lowerRank φ v < lowerRank φ w := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨_, hx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hx h⟩
  · intro heq
    have hv : v ∈ Finset.univ.filter fun x => φ x < φ w :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [← heq] at hv
    exact (lt_irrefl (φ v)) (Finset.mem_filter.mp hv).2

theorem sublevel_connected_of_descent
    (φ : V → ℝ) (m : V)
    (hdescent : ∀ v, v ≠ m → ∃ w, G.Adj v w ∧ φ w < φ v)
    (a : ℝ) (hma : φ m < a) :
    (G.induce {v | φ v < a}).Connected := by
  classical
  let S : Set V := {v | φ v < a}
  let mm : S := ⟨m,hma⟩
  have hreach : ∀ k : Nat, ∀ v : V, lowerRank φ v = k →
      ∀ hv : φ v < a, (G.induce S).Reachable ⟨v,hv⟩ mm := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro v hvk hv
        by_cases hvm : v = m
        · subst v
          exact SimpleGraph.Reachable.rfl
        · obtain ⟨w,hvw,hwv⟩ := hdescent v hvm
          have hw : φ w < a := lt_trans hwv hv
          have hrank : lowerRank φ w < k := by
            rw [← hvk]
            exact lowerRank_lt hwv
          have hadj : (G.induce S).Adj ⟨v,hv⟩ ⟨w,hw⟩ := hvw
          exact hadj.reachable.trans (ih (lowerRank φ w) hrank w rfl hw)
  letI : Nonempty S := ⟨mm⟩
  refine ⟨?_⟩
  intro v w
  exact (hreach _ v.val rfl v.property).trans
    (hreach _ w.val rfl w.property).symm

theorem sublevel_edge_count
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 2)
    (φ : V → ℝ) (m : V)
    (hdescent : ∀ v, v ≠ m → ∃ w, G.Adj v w ∧ φ w < φ v)
    (a : ℝ) (hma : φ m < a) (hproper : ∃ v, a ≤ φ v) :
    Nat.card (G.induce {v | φ v < a}).edgeSet + 1 =
      Nat.card {v | φ v < a} := by
  classical
  apply proper_connected_induce_edge_count G hconn hdeg
    {v | φ v < a}
  · obtain ⟨v,hv⟩ := hproper
    exact ⟨v, not_lt.mpr hv⟩
  · exact sublevel_connected_of_descent G φ m hdescent a hma

end Papers.RationalityTen.PolygonMorseGraph

end
end BundlePart1

section BundlePart2
/- Source: Papers/PolytopeEulerRadialFigure.lean -/








@[expose] public section

/-!
# The radial vertex figure used in the Euler argument

Uncompiled draft. The order isomorphism is built from the actual section
D.politopo; its vertex map is proved to be D.attra. Thus a height sign at
a neighbor is transported by a strictly positive scalar, not inferred
from an arbitrary combinatorial vertex figure.
-/

noncomputable section

namespace Papers.PolytopeEulerRadialFigure

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeBalinski Papers.PolytopeVertexCone
open scoped Classical

variable {n : ℕ} {P : ConvexPolytope n} {v : E n}

@[reducible] def toGaloisData (D : DatiFetta P v) :
    VertexFigureGaloisData P P.toSet v := by
  choose Finv hFinvF hFinvV hFinvD hFinvS using
    fun G : PolytopeFace D.politopo => D.faccia_dalla_fetta G.isFace
  refine
    { figure := D.politopo
      faceEquiv :=
        { toFun := fun F =>
            ⟨F.carrier ∩ {z | D.l z = D.c},
              D.faccia_fetta F.isFace F.mem_vertex F.dim_pos⟩
          invFun := fun G =>
            ⟨Finv G, hFinvF G, face_subset_toSet P (hFinvF G),
              hFinvV G, hFinvD G⟩
          left_inv := ?_
          right_inv := ?_ }
      map_subset_iff := ?_
      map_dim := ?_ }
  · intro F
    apply PositiveVertexStarFace.ext
    have hs := hFinvS
      ⟨F.carrier ∩ {z | D.l z = D.c},
        D.faccia_fetta F.isFace F.mem_vertex F.dim_pos⟩
    exact Set.Subset.antisymm
      (D.fetta_mono (hFinvF _) (hFinvV _) F.isFace F.mem_vertex hs.subset)
      (D.fetta_mono F.isFace F.mem_vertex (hFinvF _) (hFinvV _) hs.symm.subset)
  · intro G
    apply PolytopeFace.ext
    exact hFinvS G
  · intro F G
    constructor
    · intro h z hz
      exact ⟨h hz.1, hz.2⟩
    · exact D.fetta_mono F.isFace F.mem_vertex G.isFace G.mem_vertex
  · intro F
    exact D.fetta_faceDim F.isFace F.mem_vertex F.dim_pos

@[simp] theorem toGaloisData_figure (D : DatiFetta P v) :
    (toGaloisData D).figure = D.politopo := rfl

@[simp] theorem toGaloisData_face (D : DatiFetta P v)
    (F : PositiveVertexStarFace P P.toSet v) :
    ((toGaloisData D).faceEquiv F).carrier =
      F.carrier ∩ {z | D.l z = D.c} := rfl

theorem neighborImage_eq_attra (D : DatiFetta P v)
    (y : Papers.PolytopeVertexCone.actualNeighbors P v) :
    (neighborImage (toGaloisData D) D.hv y).val = D.attra y.val := by
  have hstep := neighbor_step P v y
  have hyc : D.l y.val < D.c := D.hsep y.val hstep.1 hstep.2.1.symm
  have hmem : D.attra y.val ∈
      ((toGaloisData D).faceEquiv (neighborStarFace P D.hv y)).carrier := by
    rw [toGaloisData_face]
    exact ⟨D.attra_mem_segment hyc, D.attra_level hyc⟩
  rw [neighborImage_face] at hmem
  exact (Set.mem_singleton_iff.mp hmem).symm

theorem neighborImage_height_difference (D : DatiFetta P v)
    (L : E n →L[ℝ] ℝ) (y : Papers.PolytopeVertexCone.actualNeighbors P v) :
    L (neighborImage (toGaloisData D) D.hv y).val - L v =
      ((D.l v - D.c) / (D.l v - D.l y.val)) * (L y.val - L v) := by
  rw [neighborImage_eq_attra, ← map_sub, D.attra_sub]
  simp only [map_smul, map_sub, smul_eq_mul]

theorem neighborImage_height_lt_iff (D : DatiFetta P v)
    (L : E n →L[ℝ] ℝ) (y : Papers.PolytopeVertexCone.actualNeighbors P v) :
    L (neighborImage (toGaloisData D) D.hv y).val < L v ↔ L y.val < L v := by
  have hstep := neighbor_step P v y
  have hτ := D.tau_pos (D.hsep y.val hstep.1 hstep.2.1.symm)
  rw [← sub_neg, neighborImage_height_difference]
  constructor
  · intro h
    have : L y.val - L v < 0 := by nlinarith
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hτ (sub_neg.mpr h)

theorem neighborImage_height_gt_iff (D : DatiFetta P v)
    (L : E n →L[ℝ] ℝ) (y : Papers.PolytopeVertexCone.actualNeighbors P v) :
    L v < L (neighborImage (toGaloisData D) D.hv y).val ↔ L v < L y.val := by
  have hstep := neighbor_step P v y
  have hτ := D.tau_pos (D.hsep y.val hstep.1 hstep.2.1.symm)
  rw [← sub_pos, neighborImage_height_difference, mul_pos_iff_of_pos_left hτ, sub_pos]

def lowerNeighborEquiv (D : DatiFetta P v) (L : E n →L[ℝ] ℝ) :
    {y : Papers.PolytopeVertexCone.actualNeighbors P v // L y.val < L v} ≃
      {q : D.politopo.vertices // L q.val < L v} where
  toFun y := ⟨neighborEquiv (toGaloisData D) D.hv y.val,
    (neighborImage_height_lt_iff D L y.val).mpr y.property⟩
  invFun q := ⟨(neighborEquiv (toGaloisData D) D.hv).symm q.val, by
    apply (neighborImage_height_lt_iff D L _).mp
    change L ((neighborEquiv (toGaloisData D) D.hv)
      ((neighborEquiv (toGaloisData D) D.hv).symm q.val)).val < L v
    simpa using q.property⟩
  left_inv y := Subtype.ext ((neighborEquiv (toGaloisData D) D.hv).left_inv y.val)
  right_inv q := Subtype.ext ((neighborEquiv (toGaloisData D) D.hv).right_inv q.val)

theorem figure_dim_two (D : DatiFetta P v) (hdim : P.dim = 3) :
    D.politopo.dim = 2 := by
  have hpos : 1 ≤ faceDim P.toSet := by
    change 1 ≤ P.dim
    omega
  have hh := D.fetta_faceDim (toSet_isFace P)
    (Papers.PolytopeBasicExtreme.vertex_mem_body P D.hv) hpos
  rw [← D.politopo_toSet] at hh
  change D.politopo.dim + 1 = P.dim at hh
  omega

end Papers.PolytopeEulerRadialFigure

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/ActualPlaneEdgeBound.lean -/






@[expose] public section

/-!
# Three actual incident edges cannot lie in an affine plane

Restrict the three actual edge support forms to the direction span.
Their zero-diagonal, strictly positive off-diagonal evaluation matrix
makes three linear forms independent. A plane has dual dimension at
most two. This proof uses no lower-bound or decomposability theorem.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open ExposedEdgeCenters
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem no_three_actual_edges_in_dim_two_set
    (P : ConvexPolytope d) (S : Set (E d)) (hS : faceDim S ≤ 2)
    (u : P.vertices) (hu : u.val ∈ S)
    (x : Fin 3 → P.vertices) (hinj : Function.Injective x)
    (hxS : ∀ i, (x i).val ∈ S)
    (hedge : ∀ i, GeneralVertexStep P u.val (x i).val) :
    False := by
  let L := vectorSpan ℝ S
  let v : Fin 3 → L := fun i =>
    ⟨(x i).val - u.val,vsub_mem_vectorSpan ℝ (hxS i) hu⟩
  let g : Fin 3 → E d →ᵃ[ℝ] ℝ := fun i =>
    Classical.choose (exists_nonnegative_affine_edge_form P u.property (hedge i))
  have hs (i : Fin 3) :
      (∀ z ∈ P.toSet, 0 ≤ g i z) ∧
      (∀ z ∈ P.toSet, g i z = 0 ↔ z ∈ segment ℝ u.val (x i).val) :=
    Classical.choose_spec (exists_nonnegative_affine_edge_form P u.property (hedge i))
  have hgu (i : Fin 3) : g i u.val = 0 :=
    ((hs i).2 u.val (vertex_mem_body_of_mem_vertices P u.property)).mpr
      (left_mem_segment ℝ _ _)
  have hgx (i : Fin 3) : g i (x i).val = 0 :=
    ((hs i).2 (x i).val (vertex_mem_body_of_mem_vertices P (x i).property)).mpr
      (right_mem_segment ℝ _ _)
  let f : Fin 3 → L →ₗ[ℝ] ℝ := fun i => (g i).linear.comp L.subtype
  have heval (i j : Fin 3) : f j (v i) = g j (x i).val := by
    change (g j).linear ((x i).val - u.val) = g j (x i).val
    have h := (g j).map_vadd u.val ((x i).val - u.val)
    change g j (((x i).val - u.val) + u.val) =
      (g j).linear ((x i).val - u.val) + g j u.val at h
    rw [sub_add_cancel,hgu j,add_zero] at h
    exact h.symm
  have hzero : ∀ i, f i (v i) = 0 := by
    intro i
    rw [heval,hgx]
  have hpositive : ∀ i j, i ≠ j → 0 < f j (v i) := by
    intro i j hij
    rw [heval]
    have hn := (hs j).1 (x i).val (vertex_mem_body_of_mem_vertices P (x i).property)
    have hne : g j (x i).val ≠ 0 := by
      intro hzero
      have hseg := ((hs j).2 (x i).val
        (vertex_mem_body_of_mem_vertices P (x i).property)).mp hzero
      rcases extreme_point_on_segment P.toSet
        (vertex_mem_body_extremePoints P (x i).property)
        (vertex_mem_body_of_mem_vertices P u.property)
        (vertex_mem_body_of_mem_vertices P (x j).property) hseg with h | h
      · exact (hedge i).2.1 h.symm
      · exact hij (hinj (Subtype.ext h))
    exact lt_of_le_of_ne hn hne.symm
  have hlin := Papers.RationalityTen.three_linearForms_independent_of_evaluations
    f v hzero hpositive
  have hmono := Submodule.finrank_mono
    (show Submodule.span ℝ (Set.range f) ≤ (⊤ : Submodule ℝ (L →ₗ[ℝ] ℝ)) from le_top)
  have hdual : finrank ℝ (L →ₗ[ℝ] ℝ) = finrank ℝ L :=
    LinearEquiv.finrank_eq (Basis.ofVectorSpace ℝ L).toDualEquiv.symm
  rw [finrank_span_eq_card hlin,Fintype.card_fin,finrank_top,hdual] at hmono
  change finrank ℝ L ≤ 2 at hS
  omega

theorem no_three_actual_edges_in_plane
    (P : ConvexPolytope d) {w x y z : E d}
    (hw : w ∈ P.vertices) (hx : x ∈ P.vertices)
    (hy : y ∈ P.vertices) (hz : z ∈ P.vertices)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hwx : GeneralVertexStep P w x) (hwy : GeneralVertexStep P w y)
    (hwz : GeneralVertexStep P w z)
    (hplane : finrank ℝ (vectorSpan ℝ ({w,x,y,z} : Set (E d))) ≤ 2) :
    False := by
  let pts : Fin 3 → P.vertices := ![⟨x,hx⟩,⟨y,hy⟩,⟨z,hz⟩]
  apply no_three_actual_edges_in_dim_two_set P {w,x,y,z} hplane ⟨w,hw⟩
    (by simp) pts
  · intro i j hij
    have hval := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [pts]
  · intro i
    fin_cases i <;> simp [pts]
  · intro i
    fin_cases i
    · exact hwx
    · exact hwy
    · exact hwz

end Papers.Polytopes


end
end
end BundlePart3

section BundlePart4
/- Source: Papers/TwoFaceGraph.lean -/






@[expose] public section

/-!
# The actual graph of a two-face

This module depends only on the original polytope foundation, actual
edge supports, the tangent-span degree bound, and elementary linear
algebra. It does not import the homothety-cover or lower-bound theory.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ}

def actualFaceNeighbors (P : ConvexPolytope d) (F : Set (E d)) (v : E d) :
    Finset (E d) :=
  P.vertices.filter (fun w => w ∈ F ∧ GeneralVertexStep P v w)

theorem actualFaceNeighbors_card_le_two_of_dim_le_two
    (P : ConvexPolytope d) (F : Set (E d)) (hdim : faceDim F ≤ 2)
    {w : E d} (hw : w ∈ P.vertices) (hwF : w ∈ F) :
    (actualFaceNeighbors P F w).card ≤ 2 := by
  let N := actualFaceNeighbors P F w
  by_contra hn
  change ¬ N.card ≤ 2 at hn
  have hbig : 3 ≤ N.card := Nat.succ_le_of_lt (lt_of_not_ge hn)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 3) hbig)
  have hcarderase : 1 < (N.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y,hy,z,hz,hyz⟩ := Finset.one_lt_card.mp hcarderase
  have hyN := Finset.mem_of_mem_erase hy
  have hzN := Finset.mem_of_mem_erase hz
  have hxy : x ≠ y := (Finset.ne_of_mem_erase hy).symm
  have hxz : x ≠ z := (Finset.ne_of_mem_erase hz).symm
  obtain ⟨hxP,hxF,hwx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyP,hyF,hwy⟩ := Finset.mem_filter.mp hyN
  obtain ⟨hzP,hzF,hwz⟩ := Finset.mem_filter.mp hzN
  have hsub : ({w,x,y,z} : Set (E d)) ⊆ F := by
    intro v hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hplane : finrank ℝ (vectorSpan ℝ ({w,x,y,z} : Set (E d))) ≤ 2 :=
    (Submodule.finrank_mono (vectorSpan_mono ℝ hsub)).trans hdim
  exact no_three_actual_edges_in_plane P hw hxP hyP hzP hxy hxz hyz hwx hwy hwz hplane

theorem actualStep_of_facePolytope
    (P : ConvexPolytope d) (F : Set (E d)) (hF : P.IsFace F)
    {x y : E d} (hxy : GeneralVertexStep (facePolytope P hF) x y) :
    GeneralVertexStep P x y := by
  obtain ⟨hy,hne,G,hG,hdim,hxG,hyG⟩ := hxy
  have hyP : y ∈ P.vertices := (Finset.mem_filter.mp hy).1
  exact ⟨hyP,hne,G,isFace_of_facePolytope P hF hG,hdim,hxG,hyG⟩

theorem faceDim_le_actualFaceNeighbors_card
    (P : ConvexPolytope d) (F : Set (E d)) (hF : P.IsFace F)
    {v : E d} (hv : v ∈ P.vertices) (hvF : v ∈ F) :
    faceDim F ≤ (actualFaceNeighbors P F v).card := by
  let Q := facePolytope P hF
  have hvQ : v ∈ Q.vertices := Finset.mem_filter.mpr ⟨hv,hvF⟩
  let f : Papers.PolytopeVertexCone.actualNeighbors Q v → actualFaceNeighbors P F v :=
    fun w => by
      have hwQ : w.val ∈ Q.vertices := (Finset.mem_filter.mp w.property).1
      have hwP : w.val ∈ P.vertices := (Finset.mem_filter.mp hwQ).1
      have hwF : w.val ∈ F := (Finset.mem_filter.mp hwQ).2
      have hstep : GeneralVertexStep Q v w.val := (Finset.mem_filter.mp w.property).2
      exact ⟨w.val,Finset.mem_filter.mpr
        ⟨hwP,hwF,actualStep_of_facePolytope P F hF hstep⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : actualFaceNeighbors P F v => z.val) h
    exact Subtype.ext hh
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hc
  have hd := actual_neighbor_card_ge_dim Q hvQ
  have hdim : Q.dim = faceDim F := by
    change faceDim Q.toSet = faceDim F
    rw [facePolytope_toSet P hF]
  omega

abbrev TwoFaceVertexType (P : ConvexPolytope d) (F : Set (E d)) :=
  {v : P.vertices // v.val ∈ F}

def twoFaceVertexGraph (P : ConvexPolytope d) (F : Set (E d)) :
    SimpleGraph (TwoFaceVertexType P F) where
  Adj x y := GeneralVertexStep P x.val.val y.val.val
  symm := ⟨by intro x y hxy; exact actualStep_symm x.val.property hxy⟩
  loopless := ⟨by intro x hxx; exact hxx.2.1 rfl⟩

def twoFaceGraphNeighborEquiv
    (P : ConvexPolytope d) (F : Set (E d)) (x : TwoFaceVertexType P F) :
    (twoFaceVertexGraph P F).neighborSet x ≃ actualFaceNeighbors P F x.val.val where
  toFun y := ⟨y.val.val.val,Finset.mem_filter.mpr
    ⟨y.val.val.property,y.val.property,y.property⟩⟩
  invFun y := ⟨⟨⟨y.val,(Finset.mem_filter.mp y.property).1⟩,
    (Finset.mem_filter.mp y.property).2.1⟩,
    (Finset.mem_filter.mp y.property).2.2⟩
  left_inv := by rintro ⟨⟨⟨y,hyP⟩,hyF⟩,hxy⟩; rfl
  right_inv := by rintro ⟨y,hy⟩; rfl

theorem twoFaceVertexGraph_degree_eq_actualFaceNeighbors
    (P : ConvexPolytope d) (F : Set (E d)) (x : TwoFaceVertexType P F) :
    (twoFaceVertexGraph P F).degree x = (actualFaceNeighbors P F x.val.val).card := by
  simpa only [SimpleGraph.card_neighborSet_eq_degree,Fintype.card_coe] using
    Fintype.card_congr (twoFaceGraphNeighborEquiv P F x)

theorem twoFaceVertexGraph_degree_two
    (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 2)
    (x : TwoFaceVertexType P F) :
    (twoFaceVertexGraph P F).degree x = 2 := by
  rw [twoFaceVertexGraph_degree_eq_actualFaceNeighbors]
  have hlow := faceDim_le_actualFaceNeighbors_card P F hF x.val.property x.property
  have hupp := actualFaceNeighbors_card_le_two_of_dim_le_two
    P F (by omega) x.val.property x.property
  omega

end Papers.Polytopes


end
end
end BundlePart4

section BundlePart5
/- Source: Papers/PolytopeFaceCounting.lean -/










@[expose] public section

/-!
# Finite actual faces and graph edges

Uncompiled draft. Faces are ordinary exposed subsets of the original
polytope, with their ordinary affine dimension. The finite coding is used
only to obtain a finite type; equality is proved from convex hulls of the
actual vertices. Graph edges correspond to the actual one-dimensional
faces, not to a separate abstract incidence object.
-/

noncomputable section

namespace Papers.PolytopeFaceCounting

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeBalinski
open scoped Classical

variable {n : ℕ}

abbrev Face (P : ConvexPolytope n) (k : ℕ) :=
  {F : PolytopeFace P // faceDim F.carrier = k}

theorem face_has_vertex (P : ConvexPolytope n) {F : Set (E n)}
    (hF : P.IsFace F) : ∃ v ∈ P.vertices, v ∈ F := by
  obtain ⟨v, hv⟩ := (facePolytope P hF).vertices_nonempty
  change v ∈ P.vertices.filter (· ∈ F) at hv
  exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩

theorem face_eq_of_vertex_membership (P : ConvexPolytope n)
    {F G : Set (E n)} (hF : P.IsFace F) (hG : P.IsFace G)
    (h : ∀ v : P.vertices, v.val ∈ F ↔ v.val ∈ G) : F = G := by
  rw [face_eq_hull_vertices P hF, face_eq_hull_vertices P hG]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter]
  by_cases hx : x ∈ P.vertices
  · simp only [hx, true_and]
    exact h ⟨x,hx⟩
  · simp [hx]

def faceCode (P : ConvexPolytope n) (k : ℕ) (F : Face P k) :
    Finset P.vertices := Finset.univ.filter fun v => v.val ∈ F.val.carrier

theorem faceCode_injective (P : ConvexPolytope n) (k : ℕ) :
    Function.Injective (faceCode P k) := by
  intro F G heq
  apply Subtype.ext
  apply PolytopeFace.ext
  apply face_eq_of_vertex_membership P F.val.isFace G.val.isFace
  intro v
  have hh : v ∈ faceCode P k F ↔ v ∈ faceCode P k G := by rw [heq]
  simpa [faceCode] using hh

instance finiteFace (P : ConvexPolytope n) (k : ℕ) : Finite (Face P k) :=
  Finite.of_injective (faceCode P k) (faceCode_injective P k)

noncomputable instance fintypeFace (P : ConvexPolytope n) (k : ℕ) : Fintype (Face P k) :=
  Fintype.ofFinite _

theorem edge_out_adj (P : ConvexPolytope n) (e : (vertexGraph P).edgeSet) :
    GeneralVertexStep P e.val.out.1.val e.val.out.2.val := by
  change s(e.val.out.1, e.val.out.2) ∈ (vertexGraph P).edgeSet
  rw [Sym2.mk_fst_out_snd_out]
  exact e.property

def edgeFace (P : ConvexPolytope n) (e : (vertexGraph P).edgeSet) : Face P 1 :=
  ⟨⟨segment ℝ e.val.out.1.val e.val.out.2.val,
      segment_isFace_of_generalVertexStep P e.val.out.1.property (edge_out_adj P e)⟩,
    segment_faceDim_of_generalVertexStep P e.val.out.1.property (edge_out_adj P e)⟩

theorem edgeFace_vertex_iff (P : ConvexPolytope n)
    (e : (vertexGraph P).edgeSet) (v : P.vertices) :
    v.val ∈ (edgeFace P e).val.carrier ↔ v ∈ e.val := by
  have hmem : v ∈ e.val ↔ v = e.val.out.1 ∨ v = e.val.out.2 := by
    conv_lhs => rw [← Sym2.mk_fst_out_snd_out e.val]
    exact Sym2.mem_iff
  rw [hmem]
  constructor
  · intro hv
    have hh := Papers.PolytopeBasicExtreme.extreme_point_on_segment P.toSet
      (Papers.PolytopeBasicExtreme.vertex_mem_extreme P v.property)
      (Papers.PolytopeBasicExtreme.vertex_mem_body P e.val.out.1.property)
      (Papers.PolytopeBasicExtreme.vertex_mem_body P e.val.out.2.property) hv
    rcases hh with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _

theorem edgeFace_injective (P : ConvexPolytope n) :
    Function.Injective (edgeFace P) := by
  intro e f heq
  apply Subtype.ext
  apply Sym2.ext
  intro v
  rw [← edgeFace_vertex_iff P e v, ← edgeFace_vertex_iff P f v, heq]

theorem edgeFace_surjective (P : ConvexPolytope n) :
    Function.Surjective (edgeFace P) := by
  intro F
  obtain ⟨x,hx,hxF⟩ := face_has_vertex P F.val.isFace
  obtain ⟨y,hy,hyF,hyx,hseg⟩ :=
    spigolo_segmento P F.val.isFace F.property hx hxF
  let xx : P.vertices := ⟨x,hx⟩
  let yy : P.vertices := ⟨y,hy⟩
  have hxy : GeneralVertexStep P x y :=
    ⟨hy,hyx.symm,F.val.carrier,F.val.isFace,F.property,hxF,hyF⟩
  let e : (vertexGraph P).edgeSet := ⟨s(xx,yy),hxy⟩
  refine ⟨e,?_⟩
  apply Subtype.ext
  apply PolytopeFace.ext
  apply face_eq_of_vertex_membership P (edgeFace P e).val.isFace F.val.isFace
  intro v
  rw [edgeFace_vertex_iff]
  change (v ∈ s(xx,yy)) ↔ v.val ∈ F.val.carrier
  rw [Sym2.mem_iff]
  constructor
  · rintro (rfl | rfl) <;> assumption
  · intro hv
    have hvseg : v.val ∈ segment ℝ x y := by simpa only [← hseg] using hv
    have hh := Papers.PolytopeBasicExtreme.extreme_point_on_segment P.toSet
      (Papers.PolytopeBasicExtreme.vertex_mem_extreme P v.property)
      (Papers.PolytopeBasicExtreme.vertex_mem_body P hx)
      (Papers.PolytopeBasicExtreme.vertex_mem_body P hy) hvseg
    rcases hh with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

def edgeFaceEquiv (P : ConvexPolytope n) :
    (vertexGraph P).edgeSet ≃ Face P 1 :=
  Equiv.ofBijective (edgeFace P) ⟨edgeFace_injective P,edgeFace_surjective P⟩

/-- Edges all of whose endpoints belong to a prescribed vertex subset. -/
abbrev EdgeIn {V : Type*} (G : SimpleGraph V) (S : Set V) :=
  {e : G.edgeSet // ∀ v, v ∈ e.val → v ∈ S}

def induceEdgeEquiv {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (G.induce S).edgeSet ≃ EdgeIn G S := by
  let f : (G.induce S).edgeSet → EdgeIn G S := fun e =>
    ⟨(SimpleGraph.Embedding.induce S).mapEdgeSet e, by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
      exact w.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro e e' heq
    exact (SimpleGraph.Embedding.induce S).mapEdgeSet.injective
      (congrArg Subtype.val heq)
  · intro e
    let x : S := ⟨e.val.val.out.1,e.property _ (Sym2.out_fst_mem _)⟩
    let y : S := ⟨e.val.val.out.2,e.property _ (Sym2.out_snd_mem _)⟩
    have hxy : G.Adj x.val y.val := by
      change s(e.val.val.out.1,e.val.val.out.2) ∈ G.edgeSet
      rw [Sym2.mk_fst_out_snd_out]
      exact e.val.property
    let ee : (G.induce S).edgeSet := ⟨s(x,y),hxy⟩
    refine ⟨ee,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change s(e.val.val.out.1,e.val.val.out.2) = e.val.val
    exact Sym2.mk_fst_out_snd_out _

abbrev FaceIn (P : ConvexPolytope n) (k : ℕ) (S : Set P.vertices) :=
  {F : Face P k // ∀ v : P.vertices, v.val ∈ F.val.carrier → v ∈ S}

def edgeInFaceEquiv (P : ConvexPolytope n) (S : Set P.vertices) :
    EdgeIn (vertexGraph P) S ≃ FaceIn P 1 S where
  toFun e := ⟨edgeFaceEquiv P e.val, by
    intro v hv
    exact e.property v ((edgeFace_vertex_iff P e.val v).mp hv)⟩
  invFun F := ⟨(edgeFaceEquiv P).symm F.val, by
    intro v hv
    apply F.property v
    have hh := (edgeFace_vertex_iff P ((edgeFaceEquiv P).symm F.val) v).mpr hv
    simpa only [show edgeFace P ((edgeFaceEquiv P).symm F.val) =
      F.val from (edgeFaceEquiv P).apply_symm_apply F.val] using hh⟩
  left_inv e := Subtype.ext ((edgeFaceEquiv P).left_inv e.val)
  right_inv F := Subtype.ext ((edgeFaceEquiv P).right_inv F.val)

def inducedEdgeFaceEquiv (P : ConvexPolytope n) (S : Set P.vertices) :
    ((vertexGraph P).induce S).edgeSet ≃ FaceIn P 1 S :=
  (induceEdgeEquiv (vertexGraph P) S).trans (edgeInFaceEquiv P S)

theorem graph_edge_card_eq_one_face_card (P : ConvexPolytope n) :
    Nat.card (vertexGraph P).edgeSet = Nat.card (Face P 1) :=
  Nat.card_congr (edgeFaceEquiv P)

end Papers.PolytopeFaceCounting

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/PolytopeEulerLowerFaces.lean -/







@[expose] public section

/-!
# Highest faces and the actual lower vertex figure

Uncompiled draft. A face has highest vertex v exactly when every vertex of
its radial slice has height below v. The converse is proved by applying
the actual local-to-global linear maximum theorem to the face polytope.
The resulting bijection counts precisely the original faces, not assumed
abstract lower links.
-/

noncomputable section

namespace Papers.PolytopeEulerLowerFaces

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeVertexCone Papers.PolytopeEulerRadialFigure
open Papers.PolytopeFaceCounting Papers.PolytopeBalinski
open scoped BigOperators Classical

variable {n : ℕ} {P : ConvexPolytope n} {v : E n}

theorem step_facePolytope_to_original (P : ConvexPolytope n)
    {F : Set (E n)} (hF : P.IsFace F) {x y : E n}
    (hxy : GeneralVertexStep (facePolytope P hF) x y) :
    GeneralVertexStep P x y := by
  obtain ⟨hy,hne,A,hA,hdim,hxA,hyA⟩ := hxy
  have hyP : y ∈ P.vertices := (Finset.mem_filter.mp hy).1
  exact ⟨hyP,hne,A,isFace_of_facePolytope P hF hA,hdim,hxA,hyA⟩

theorem neighborImage_mem_iff (D : DatiFetta P v)
    (F : PositiveVertexStarFace P P.toSet v)
    (y : Papers.PolytopeVertexCone.actualNeighbors P v) :
    (neighborImage (toGaloisData D) D.hv y).val ∈
      ((toGaloisData D).faceEquiv F).carrier ↔ y.val ∈ F.carrier := by
  constructor
  · intro h
    have hsub : (neighborStarFace P D.hv y).carrier ⊆ F.carrier := by
      apply ((toGaloisData D).map_subset_iff _ _).mpr
      rw [neighborImage_face]
      exact Set.singleton_subset_iff.mpr h
    exact hsub (right_mem_segment ℝ _ _)
  · intro hyF
    have hconv : Convex ℝ F.carrier := F.isFace.1.convex (convex_convexHull ℝ _)
    have hsub : (neighborStarFace P D.hv y).carrier ⊆ F.carrier :=
      hconv.segment_subset F.mem_vertex hyF
    have himage := ((toGaloisData D).map_subset_iff _ _).mp hsub
    rw [neighborImage_face] at himage
    exact himage (Set.mem_singleton _)

def TopAt (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ) (v : E n)
    (F : Set (E n)) : Prop :=
  v ∈ F ∧ ∀ w ∈ P.vertices, w ∈ F → w ≠ v → L w < L v

theorem topAt_iff_lower_figure_vertices
    (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    (F : PositiveVertexStarFace P P.toSet v) :
    TopAt P L v F.carrier ↔
      ∀ q : D.politopo.vertices,
        q.val ∈ ((toGaloisData D).faceEquiv F).carrier → L q.val < L v := by
  constructor
  · intro ht q hq
    obtain ⟨y,hyq⟩ := (neighborEquiv (toGaloisData D) D.hv).surjective q
    have hmem : (neighborImage (toGaloisData D) D.hv y).val ∈
        ((toGaloisData D).faceEquiv F).carrier := by
      simpa only [show neighborImage (toGaloisData D) D.hv y = q from hyq] using hq
    have hstep := neighbor_step P v y
    have hylow := ht.2 y.val hstep.1
      ((neighborImage_mem_iff D F y).mp hmem) hstep.2.1.symm
    have hh := (neighborImage_height_lt_iff D L y).mpr hylow
    simpa only [show neighborImage (toGaloisData D) D.hv y = q from hyq] using hh
  · intro hlower
    refine ⟨F.mem_vertex,?_⟩
    intro w hw hwF hwv
    let Q := facePolytope P F.isFace
    have hvQ : v ∈ Q.vertices :=
      Finset.mem_filter.mpr ⟨D.hv,F.mem_vertex⟩
    have hlocal : ∀ y, GeneralVertexStep Q v y → L y ≤ L v := by
      intro y hy
      have hyP := step_facePolytope_to_original P F.isFace hy
      let yy : Papers.PolytopeVertexCone.actualNeighbors P v :=
        ⟨y,Finset.mem_filter.mpr ⟨hyP.1,hyP⟩⟩
      have hyF : y ∈ F.carrier := (Finset.mem_filter.mp hy.1).2
      have himage := (neighborImage_mem_iff D F yy).mpr hyF
      have hlow := hlower (neighborImage (toGaloisData D) D.hv yy) himage
      exact ((neighborImage_height_lt_iff D L yy).mp hlow).le
    have hwQ : w ∈ Q.vertices := Finset.mem_filter.mpr ⟨hw,hwF⟩
    have hmax := maximum_on_vertices_of_neighbors Q L hvQ hlocal w hwQ
    rcases lt_or_eq_of_le hmax with hlt | heq
    · exact hlt
    · exact (hwv (hinj hw D.hv heq)).elim

abbrev TopFace (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (v : E n) (k : ℕ) :=
  {F : Face P k // TopAt P L v F.val.carrier}

def topFaceStar (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (v : E n) (k : ℕ) (F : TopFace P L v (k + 1)) :
    PositiveVertexStarFace P P.toSet v where
  carrier := F.val.val.carrier
  isFace := F.val.val.isFace
  subset_base := face_subset_toSet P F.val.val.isFace
  mem_vertex := F.property.1
  dim_pos := by rw [F.val.property]; omega

def topFaceFigure (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    (k : ℕ) (F : TopFace P L v (k + 1)) :
    FaceIn D.politopo k {q | L q.val < L v} := by
  let S := topFaceStar P L v k F
  let G := (toGaloisData D).faceEquiv S
  have hdim : faceDim G.carrier = k := by
    have h := (toGaloisData D).map_dim S
    change faceDim G.carrier + 1 = faceDim F.val.val.carrier at h
    rw [F.val.property] at h
    omega
  refine ⟨⟨G,hdim⟩,?_⟩
  exact (topAt_iff_lower_figure_vertices D L hinj S).mp F.property

def figureTopFace (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    (k : ℕ) (G : FaceIn D.politopo k {q | L q.val < L v}) :
    TopFace P L v (k + 1) := by
  let S := (toGaloisData D).faceEquiv.symm G.val.val
  have himage : (toGaloisData D).faceEquiv S = G.val.val :=
    (toGaloisData D).faceEquiv.apply_symm_apply _
  have hdim : faceDim S.carrier = k + 1 := by
    have h := (toGaloisData D).map_dim S
    rw [himage,G.val.property] at h
    omega
  refine ⟨⟨⟨S.carrier,S.isFace⟩,hdim⟩,?_⟩
  apply (topAt_iff_lower_figure_vertices D L hinj S).mpr
  intro q hq
  rw [himage] at hq
  exact G.property q hq

def topFaceFigureEquiv (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n))) (k : ℕ) :
    TopFace P L v (k + 1) ≃ FaceIn D.politopo k {q | L q.val < L v} where
  toFun := topFaceFigure D L hinj k
  invFun := figureTopFace D L hinj k
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    apply PolytopeFace.ext
    change ((toGaloisData D).faceEquiv.symm
      ((toGaloisData D).faceEquiv (topFaceStar P L v k F))).carrier =
        F.val.val.carrier
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv G := by
    apply Subtype.ext
    apply Subtype.ext
    apply PolytopeFace.ext
    change ((toGaloisData D).faceEquiv
      ((toGaloisData D).faceEquiv.symm G.val.val)).carrier = G.val.val.carrier
    rw [Equiv.apply_symm_apply]

def topTwoFaceLowerEdgeEquiv (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n))) :
    TopFace P L v 2 ≃
      ((vertexGraph D.politopo).induce {q : D.politopo.vertices | L q.val < L v}).edgeSet :=
  (topFaceFigureEquiv D L hinj 1).trans
    (inducedEdgeFaceEquiv D.politopo {q | L q.val < L v}).symm

theorem top_two_face_card_eq_lower_edge_card
    (D : DatiFetta P v) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n))) :
    Nat.card (TopFace P L v 2) =
      Nat.card ((vertexGraph D.politopo).induce
        {q : D.politopo.vertices | L q.val < L v}).edgeSet :=
  Nat.card_congr (topTwoFaceLowerEdgeEquiv D L hinj)


theorem exists_topAt (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    {k : ℕ} (F : Face P k) :
    ∃ v : P.vertices, TopAt P L v.val F.val.carrier := by
  let X := P.vertices.filter fun x => x ∈ F.val.carrier
  have hX : X.Nonempty := by
    obtain ⟨v,hv,hvF⟩ := face_has_vertex P F.val.isFace
    exact ⟨v,Finset.mem_filter.mpr ⟨hv,hvF⟩⟩
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image X L hX
  have hvP := (Finset.mem_filter.mp hv).1
  have hvF := (Finset.mem_filter.mp hv).2
  refine ⟨⟨v,hvP⟩,hvF,?_⟩
  intro w hw hwF hwv
  have hle := hmax w (Finset.mem_filter.mpr ⟨hw,hwF⟩)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact (hwv (hinj hw hvP heq)).elim

theorem topAt_unique (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    {F : Set (E n)} {v w : P.vertices}
    (hv : TopAt P L v.val F) (hw : TopAt P L w.val F) : v = w := by
  by_contra hne
  have hvw : v.val ≠ w.val := fun heq => hne (Subtype.ext heq)
  have h1 := hv.2 w.val w.property hw.1 hvw.symm
  have h2 := hw.2 v.val v.property hv.1 hvw
  exact lt_asymm h1 h2

def topFacePartition (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n))) (k : ℕ) :
    (Σ v : P.vertices, TopFace P L v.val k) ≃ Face P k := by
  apply Equiv.ofBijective (fun z => z.2.val)
  constructor
  · rintro ⟨v,F⟩ ⟨w,G⟩ hFG
    change F.val = G.val at hFG
    have hw : TopAt P L w.val F.val.val.carrier := by
      rw [hFG]
      exact G.property
    have hvw : v = w := topAt_unique P L F.property hw
    subst w
    have hface : F = G := Subtype.ext hFG
    cases hface
    rfl
  · intro F
    obtain ⟨v,hv⟩ := exists_topAt P L hinj F
    exact ⟨⟨v,⟨F,hv⟩⟩,rfl⟩

theorem sum_top_face_card (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n))) (k : ℕ) :
    (∑ v : P.vertices, Nat.card (TopFace P L v.val k)) = Nat.card (Face P k) := by
  classical
  letI : Fintype (Face P k) := Fintype.ofFinite _
  letI : ∀ v : P.vertices, Fintype (TopFace P L v.val k) :=
    fun _ => Fintype.ofFinite _
  have hh := Fintype.card_congr (topFacePartition P L hinj k)
  simpa only [Fintype.card_sigma, Nat.card_eq_fintype_card] using hh

end Papers.PolytopeEulerLowerFaces

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/FiniteGraphHeightCount.lean -/









@[expose] public section

/-!
# Finite height counts on an ordinary graph

Uncompiled draft. Each edge is charged to its higher endpoint under an
injective height. The charge decomposition and the two-regular edge count
are proved by explicit finite bijections and the degree-sum formula.
-/

noncomputable section

namespace Papers.FiniteGraphHeightCount

open SimpleGraph
open scoped BigOperators Classical

variable {V : Type*}

abbrev LowerNeighbor (G : SimpleGraph V) (φ : V → ℝ) (v : V) :=
  {w : V // G.Adj v w ∧ φ w < φ v}

def lowerEdgeMap (G : SimpleGraph V) (φ : V → ℝ) :
    (Σ v, LowerNeighbor G φ v) → G.edgeSet :=
  fun e => ⟨s(e.1,e.2.val),e.2.property.1⟩

theorem lowerEdgeMap_injective (G : SimpleGraph V) (φ : V → ℝ) :
    Function.Injective (lowerEdgeMap G φ) := by
  rintro ⟨v,⟨w,hvw,hwv⟩⟩ ⟨x,⟨y,hxy,hyx⟩⟩ heq
  have hp : s(v,w) = s(x,y) := congrArg Subtype.val heq
  rcases Sym2.eq_iff.mp hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact (lt_asymm hwv hyx).elim

theorem lowerEdgeMap_surjective (G : SimpleGraph V) (φ : V → ℝ)
    (hinj : Function.Injective φ) :
    Function.Surjective (lowerEdgeMap G φ) := by
  intro e
  let a := e.val.out.1
  let b := e.val.out.2
  have hab : G.Adj a b := by
    change s(e.val.out.1,e.val.out.2) ∈ G.edgeSet
    rw [Sym2.mk_fst_out_snd_out]
    exact e.property
  rcases lt_trichotomy (φ a) (φ b) with hlt | heq | hgt
  · refine ⟨⟨b,⟨a,hab.symm,hlt⟩⟩,?_⟩
    apply Subtype.ext
    change s(b,a) = e.val
    exact Sym2.eq_swap.trans (Sym2.mk_fst_out_snd_out e.val)
  · exact (hab.ne (hinj heq)).elim
  · refine ⟨⟨a,⟨b,hab,hgt⟩⟩,?_⟩
    apply Subtype.ext
    exact Sym2.mk_fst_out_snd_out e.val

def lowerEdgeEquiv (G : SimpleGraph V) (φ : V → ℝ)
    (hinj : Function.Injective φ) :
    (Σ v, LowerNeighbor G φ v) ≃ G.edgeSet :=
  Equiv.ofBijective (lowerEdgeMap G φ)
    ⟨lowerEdgeMap_injective G φ,lowerEdgeMap_surjective G φ hinj⟩

theorem sum_lower_card_eq_edge_card [Fintype V]
    (G : SimpleGraph V) (φ : V → ℝ) (hinj : Function.Injective φ) :
    (∑ v, Nat.card (LowerNeighbor G φ v)) = Nat.card G.edgeSet := by
  classical
  letI : ∀ v, Fintype (LowerNeighbor G φ v) := fun _ => Fintype.ofFinite _
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  have hh := Fintype.card_congr (lowerEdgeEquiv G φ hinj)
  simpa only [Fintype.card_sigma, Nat.card_eq_fintype_card] using hh

theorem two_regular_edge_card [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v = 2) :
    Nat.card G.edgeSet = Nat.card V := by
  classical
  have hh := G.sum_degrees_eq_twice_card_edges
  have htwo : 2 * Fintype.card V = 2 * G.edgeFinset.card := by
    simpa [hdeg, mul_comm] using hh
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  exact Nat.mul_left_cancel (by decide : 0 < 2) htwo.symm

theorem euler_of_local_indices
    [Fintype V] (down topFaces : V → ℕ) (lo hi : V) (hne : lo ≠ hi)
    (hloD : down lo = 0) (hloF : topFaces lo = 0)
    (hhi : down hi = topFaces hi)
    (hregular : ∀ v, v ≠ lo → v ≠ hi → down v = topFaces v + 1) :
    (Fintype.card V : ℤ) - (∑ v, (down v : ℤ)) +
      (∑ v, (topFaces v : ℤ)) = 2 := by
  have hlocal (v : V) :
      (1 : ℤ) - down v + topFaces v =
        (if v = lo then 1 else 0) + (if v = hi then 1 else 0) := by
    by_cases hvlo : v = lo
    · subst v
      simp [hloD,hloF,hne]
    · by_cases hvhi : v = hi
      · subst v
        simp only [hvlo,if_false,if_true]
        omega
      · have hh := hregular v hvlo hvhi
        simp only [hvlo,hvhi,if_false]
        omega
  have hs : (∑ v, ((1 : ℤ) - down v + topFaces v)) = 2 := by
    calc
      _ = ∑ v, ((if v = lo then 1 else 0) + (if v = hi then 1 else 0)) :=
        Finset.sum_congr rfl (fun v _ => hlocal v)
      _ = 2 := by simp [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  simpa using hs

end Papers.FiniteGraphHeightCount

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/PolytopeEulerLocal.lean -/









@[expose] public section

/-!
# Actual local Euler indices in intrinsic dimension three

Uncompiled draft. Interior height levels give proper nonempty connected
subgraphs of the actual polygonal vertex figure. The minimum and maximum
are treated separately. No local Euler equation is assumed.
-/

noncomputable section

namespace Papers.PolytopeEulerLocal

open Set Module SimpleGraph
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeVertexCone Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeEulerRadialFigure
open Papers.PolytopeEulerLowerFaces Papers.FiniteGraphHeightCount
open Papers.RationalityTen.PolygonMorseGraph
open scoped Classical

variable {n : ℕ}

abbrev Low (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ) (v : P.vertices) :=
  LowerNeighbor (vertexGraph P) (fun w : P.vertices => L w.val) v

def lowActualEquiv (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ) (v : P.vertices) :
    Low P L v ≃
      {y : Papers.PolytopeVertexCone.actualNeighbors P v.val // L y.val < L v.val} where
  toFun w := ⟨⟨w.val.val,Finset.mem_filter.mpr
    ⟨w.val.property,w.property.1⟩⟩,w.property.2⟩
  invFun y := ⟨⟨y.val.val,(Finset.mem_filter.mp y.val.property).1⟩,
    (Finset.mem_filter.mp y.val.property).2,y.property⟩
  left_inv w := by cases w; rfl
  right_inv y := by cases y; rfl

def lowFigureEquiv (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (v : P.vertices) (D : DatiFetta P v.val) :
    Low P L v ≃ {q : D.politopo.vertices // L q.val < L v.val} :=
  (lowActualEquiv P L v).trans (lowerNeighborEquiv D L)

def wholeFaceGraphIso (Q : ConvexPolytope n) :
    vertexGraph Q ≃g twoFaceVertexGraph Q Q.toSet where
  toEquiv :=
    { toFun := fun q => ⟨q,Papers.PolytopeBasicExtreme.vertex_mem_body Q q.property⟩
      invFun := fun q => q.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

theorem polygon_vertex_degree_two (Q : ConvexPolytope n) (hdim : Q.dim = 2)
    (q : Q.vertices) : (vertexGraph Q).degree q = 2 := by
  have hh := twoFaceVertexGraph_degree_two Q Q.toSet (toSet_isFace Q)
    (show faceDim Q.toSet = 2 from hdim) (wholeFaceGraphIso Q q)
  rw [(wholeFaceGraphIso Q).degree_eq q] at hh
  exact hh

theorem lower_figure_connected (P : ConvexPolytope n)
    (L : E n →L[ℝ] ℝ) (v : P.vertices) (D : DatiFetta P v.val)
    (hlow : Nonempty (Low P L v)) :
    ((vertexGraph D.politopo).induce
      {q : D.politopo.vertices | L q.val < L v.val}).Connected := by
  obtain ⟨w⟩ := hlow
  let q := lowFigureEquiv P L v D w
  have hpos : ∃ z ∈ D.politopo.vertices, -L v.val < (-L) z :=
    ⟨q.val.val,q.val.property,by simpa using q.property⟩
  have hh := positive_vertexGraph_connected D.politopo (-L) (-L v.val) hpos
  have hs : {z : D.politopo.vertices | -L v.val < (-L) z.val} =
      {z : D.politopo.vertices | L z.val < L v.val} := by
    ext z
    simp
  change ((vertexGraph D.politopo).induce
    {z : D.politopo.vertices | -L v.val < (-L) z.val}).Connected at hh
  exact hs ▸ hh

theorem regular_local_count (P : ConvexPolytope n) (hdim : P.dim = 3)
    (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    (v : P.vertices) (D : DatiFetta P v.val)
    (hlow : Nonempty (Low P L v))
    (hhigh : ∃ y : Papers.PolytopeVertexCone.actualNeighbors P v.val,
      L v.val < L y.val) :
    Nat.card (Low P L v) = Nat.card (TopFace P L v.val 2) + 1 := by
  let Q := D.politopo
  let S : Set Q.vertices := {q | L q.val < L v.val}
  have hQdim : Q.dim = 2 := figure_dim_two D hdim
  have hdeg : ∀ q, (vertexGraph Q).degree q ≤ 2 := fun q =>
    (polygon_vertex_degree_two Q hQdim q).le
  have hproper : ∃ q : Q.vertices, q ∉ S := by
    obtain ⟨y,hy⟩ := hhigh
    refine ⟨neighborImage (toGaloisData D) D.hv y,?_⟩
    exact not_lt_of_ge ((neighborImage_height_gt_iff D L y).mpr hy).le
  have hc := proper_connected_induce_edge_count (vertexGraph Q)
    (vertexGraph_connected Q) hdeg S hproper
    (lower_figure_connected P L v D hlow)
  have hv := Nat.card_congr (lowFigureEquiv P L v D)
  have hf := top_two_face_card_eq_lower_edge_card D L hinj
  change Nat.card (Low P L v) = Nat.card S at hv
  change Nat.card (TopFace P L v.val 2) =
    Nat.card ((vertexGraph Q).induce S).edgeSet at hf
  omega

theorem minimum_local_count (P : ConvexPolytope n) (L : E n →L[ℝ] ℝ)
    (v : P.vertices) (hmin : ∀ w ∈ P.vertices, L v.val ≤ L w) :
    Nat.card (Low P L v) = 0 ∧ Nat.card (TopFace P L v.val 2) = 0 := by
  have hempty : IsEmpty (Low P L v) :=
    ⟨fun w => not_lt_of_ge (hmin w.val.val w.val.property) w.property.2⟩
  have hfempty : IsEmpty (TopFace P L v.val 2) := by
    refine ⟨fun F => ?_⟩
    obtain ⟨w,hw,hwF⟩ := DatiFetta.esiste_vertice_altro
      F.val.val.isFace F.property.1 (by rw [F.val.property]; omega)
    have hwP := Finset.mem_of_mem_erase hw
    have hwv := Finset.ne_of_mem_erase hw
    exact not_lt_of_ge (hmin w hwP) (F.property.2 w hwP hwF hwv)
  letI := hempty
  letI := hfempty
  simp

theorem maximum_local_count (P : ConvexPolytope n) (hdim : P.dim = 3)
    (L : E n →L[ℝ] ℝ)
    (hinj : Set.InjOn L (P.vertices : Set (E n)))
    (v : P.vertices) (D : DatiFetta P v.val)
    (hmax : ∀ w ∈ P.vertices, L w ≤ L v.val) :
    Nat.card (Low P L v) = Nat.card (TopFace P L v.val 2) := by
  let Q := D.politopo
  let S : Set Q.vertices := {q | L q.val < L v.val}
  have hs : S = Set.univ := by
    ext q
    simp only [Set.mem_univ, iff_true]
    obtain ⟨y,hyq⟩ := (neighborEquiv (toGaloisData D) D.hv).surjective q
    have hstep := neighbor_step P v.val y
    have hylt : L y.val < L v.val := by
      rcases lt_or_eq_of_le (hmax y.val hstep.1) with hlt | heq
      · exact hlt
      · exact (hstep.2.1 (hinj hstep.1 v.property heq).symm).elim
    have hh := (neighborImage_height_lt_iff D L y).mpr hylt
    change L q.val < L v.val
    simpa only [show neighborImage (toGaloisData D) D.hv y = q from hyq] using hh
  have hv := Nat.card_congr (lowFigureEquiv P L v D)
  have hf := top_two_face_card_eq_lower_edge_card D L hinj
  have hV : Nat.card S = Nat.card Q.vertices := by
    rw [hs]
    exact Nat.card_congr (Equiv.Set.univ Q.vertices)
  have hE : Nat.card ((vertexGraph Q).induce S).edgeSet =
      Nat.card (vertexGraph Q).edgeSet := by
    rw [hs]
    exact Nat.card_congr (SimpleGraph.induceUnivIso (vertexGraph Q)).mapEdgeSet
  change Nat.card (Low P L v) = Nat.card S at hv
  change Nat.card (TopFace P L v.val 2) =
    Nat.card ((vertexGraph Q).induce S).edgeSet at hf
  have hdegree := two_regular_edge_card (vertexGraph Q)
    (polygon_vertex_degree_two Q (figure_dim_two D hdim))
  omega

end Papers.PolytopeEulerLocal

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/RationalityTenMorseEulerCounts.lean -/







@[expose] public section

/-!
# Generic linear heights and finite Morse double counting

Uncompiled draft. The first theorem constructs a linear height separating
any finite set of points. The second derives the ordinary three-dimensional
Euler count from the explicitly stated local lower-link counts. Geometric
identification of these counts with actual vertex figures is a separate
dependency, not silently assumed here.
-/

noncomputable section

namespace Papers.RationalityTen.MorseEulerCounts

open scoped BigOperators Classical
open Papers.FaceIncidenceEuler

theorem exists_linear_height_injective
    {W : Type*} [AddCommGroup W] [Module ℝ W] (s : Finset W) :
    ∃ l : W →ₗ[ℝ] ℝ, Set.InjOn l (s : Set W) := by
  classical
  let I := {p : s × s // p.1 ≠ p.2}
  let d : I → W := fun i => ((i.val.1 : s) : W) - ((i.val.2 : s) : W)
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    apply sub_ne_zero.mpr
    intro heq
    exact i.property (Subtype.ext heq)
  obtain ⟨l, hl⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) d hd
  refine ⟨l, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  let i : I := ⟨(⟨x,hx⟩, ⟨y,hy⟩), fun heq => hne (congrArg Subtype.val heq)⟩
  apply hl i
  change l (x - y) = 0
  rw [map_sub, hxy, sub_self]

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

/-- Charge each edge and each polygonal face to its unique highest vertex.
At the minimum both charged counts vanish; at the maximum they agree;
every other lower link is a nonempty proper polygonal path. -/
theorem euler_three_from_lower_links
    (edgeTop : E → V) (faceTop : F → V) (lo hi : V)
    (hne : lo ≠ hi)
    (hloE : rowCount (fun v e => edgeTop e = v) lo = 0)
    (hloF : rowCount (fun v f => faceTop f = v) lo = 0)
    (hhi : rowCount (fun v e => edgeTop e = v) hi =
      rowCount (fun v f => faceTop f = v) hi)
    (hregular : ∀ v, v ≠ lo → v ≠ hi →
      rowCount (fun v e => edgeTop e = v) v =
        rowCount (fun v f => faceTop f = v) v + 1) :
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F = 2 := by
  let eCount := rowCount (fun v e => edgeTop e = v)
  let fCount := rowCount (fun v f => faceTop f = v)
  have heTotal : (∑ v, eCount v) = (Fintype.card E : ℤ) := by
    have hh := sum_constant_columns (fun v e => edgeTop e = v) 1
      (by intro e; simp [colCount])
    simpa [eCount] using hh
  have hfTotal : (∑ v, fCount v) = (Fintype.card F : ℤ) := by
    have hh := sum_constant_columns (fun v f => faceTop f = v) 1
      (by intro f; simp [colCount])
    simpa [fCount] using hh
  have hlocal (v : V) :
      (1 : ℤ) - eCount v + fCount v =
        (if v = lo then 1 else 0) + (if v = hi then 1 else 0) := by
    by_cases hvlo : v = lo
    · subst v
      simpa [eCount, fCount, hloE, hloF, hne]
    · by_cases hvhi : v = hi
      · subst v
        have hh : eCount hi = fCount hi := hhi
        simp only [hvlo, if_false, if_true]
        omega
      · have hh : eCount v = fCount v + 1 := hregular v hvlo hvhi
        simp only [hvlo, hvhi, if_false]
        omega
  have hsum : (∑ v, (1 - eCount v + fCount v)) = (2 : ℤ) := by
    calc
      _ = ∑ v, ((if v = lo then 1 else 0) + (if v = hi then 1 else 0)) :=
        Finset.sum_congr rfl (fun v _ => hlocal v)
      _ = 2 := by simp [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, heTotal, hfTotal] at hsum
  simpa using hsum

end Papers.RationalityTen.MorseEulerCounts

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/PolytopeEulerThree.lean -/







@[expose] public section

/-!
# Euler's formula for every actual three-dimensional convex polytope

Uncompiled draft. The sole geometric hypothesis is the intrinsic dimension
P.dim = 3. Vertices are the actual extreme vertices of P, and the two face
types are actual exposed subsets with affine dimensions one and two.
The proof derives every local index from the radial vertex figure.
-/

noncomputable section

namespace Papers.PolytopeEulerThree

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.PolytopeVertexCone Papers.PolytopeBalinski
open Papers.PolytopeFaceCounting Papers.PolytopeEulerLowerFaces
open Papers.PolytopeEulerLocal Papers.FiniteGraphHeightCount
open Papers.RationalityTen.MorseEulerCounts
open scoped BigOperators Classical

variable {n : ℕ}

theorem euler_three (P : ConvexPolytope n) (hdim : P.dim = 3) :
    (P.vertices.card : ℤ) - Nat.card (Face P 1) + Nat.card (Face P 2) = 2 := by
  obtain ⟨l,hl⟩ := exists_linear_height_injective P.vertices
  let L : E n →L[ℝ] ℝ := l.toContinuousLinearMap
  have hinj : Set.InjOn L (P.vertices : Set (E n)) := hl
  have hinjV : Function.Injective (fun v : P.vertices => L v.val) := by
    intro v w hvw
    exact Subtype.ext (hinj v.property w.property hvw)
  have hpos : 1 ≤ faceDim P.toSet := by
    change 1 ≤ P.dim
    omega
  let D (v : P.vertices) : DatiFetta P v.val :=
    Classical.choice (esiste_datiFetta P v.property hpos)
  obtain ⟨x,hx,hxmin⟩ := Finset.exists_max_image P.vertices (-L) P.vertices_nonempty
  obtain ⟨y,hy,hymax⟩ := Finset.exists_max_image P.vertices L P.vertices_nonempty
  let lo : P.vertices := ⟨x,hx⟩
  let hi : P.vertices := ⟨y,hy⟩
  have hmin : ∀ w ∈ P.vertices, L lo.val ≤ L w := by
    intro w hw
    simpa only [ContinuousLinearMap.neg_apply,neg_le_neg_iff] using hxmin w hw
  have hmax : ∀ w ∈ P.vertices, L w ≤ L hi.val := hymax
  have hne : lo ≠ hi := by
    intro hlohi
    obtain ⟨w,hw⟩ := (D lo).hW
    have hwP := Finset.mem_of_mem_erase hw
    have hwlo := Finset.ne_of_mem_erase hw
    have hle : L w ≤ L lo.val := by simpa only [hlohi] using hmax w hwP
    have heq : L w = L lo.val := le_antisymm hle (hmin w hwP)
    exact hwlo (hinj hwP lo.property heq)
  let down : P.vertices → ℕ := fun v => Nat.card (Low P L v)
  let tops : P.vertices → ℕ := fun v => Nat.card (TopFace P L v.val 2)
  have hminimum : down lo = 0 ∧ tops lo = 0 :=
    minimum_local_count P L lo hmin
  have hmaximum : down hi = tops hi :=
    maximum_local_count P hdim L hinj hi (D hi) hmax
  have hregular : ∀ v, v ≠ lo → v ≠ hi → down v = tops v + 1 := by
    intro v hvlo hvhi
    have hlower : L lo.val < L v.val := by
      rcases lt_or_eq_of_le (hmin v.val v.property) with hlt | heq
      · exact hlt
      · exact (hvlo (Subtype.ext (hinj lo.property v.property heq).symm)).elim
    have hupper : L v.val < L hi.val := by
      rcases lt_or_eq_of_le (hmax v.val v.property) with hlt | heq
      · exact hlt
      · exact (hvhi (Subtype.ext (hinj v.property hi.property heq))).elim
    have hneg : (-L) v.val < (-L) lo.val := by simpa using hlower
    obtain ⟨w,hw,hwL⟩ := exists_improving_neighbor P (-L) v.property lo.property hneg
    have hlow : Nonempty (Low P L v) :=
      ⟨⟨⟨w,hw.1⟩,hw,by simpa using hwL⟩⟩
    obtain ⟨z,hz,hzL⟩ := exists_improving_neighbor P L v.property hi.property hupper
    have hhigh : ∃ z : Papers.PolytopeVertexCone.actualNeighbors P v.val,
        L v.val < L z.val :=
      ⟨⟨z,Finset.mem_filter.mpr ⟨hz.1,hz⟩⟩,hzL⟩
    exact regular_local_count P hdim L hinj v (D v) hlow hhigh
  have heTotalNat :
      (∑ v : P.vertices, down v) = Nat.card (vertexGraph P).edgeSet :=
    sum_lower_card_eq_edge_card (vertexGraph P) (fun v : P.vertices => L v.val) hinjV
  have hfTotalNat :
      (∑ v : P.vertices, tops v) = Nat.card (Face P 2) :=
    sum_top_face_card P L hinj 2
  have heTotal : (∑ v : P.vertices, (down v : ℤ)) =
      (Nat.card (vertexGraph P).edgeSet : ℤ) := by
    simpa only [Nat.cast_sum] using congrArg (fun z : ℕ => (z : ℤ)) heTotalNat
  have hfTotal : (∑ v : P.vertices, (tops v : ℤ)) =
      (Nat.card (Face P 2) : ℤ) := by
    simpa only [Nat.cast_sum] using congrArg (fun z : ℕ => (z : ℤ)) hfTotalNat
  have heuler := euler_of_local_indices down tops lo hi hne
    hminimum.1 hminimum.2 hmaximum hregular
  rw [heTotal,hfTotal,graph_edge_card_eq_one_face_card P] at heuler
  simpa only [Fintype.card_coe] using heuler

theorem vertices_add_faces_eq_edges_add_two
    (P : ConvexPolytope n) (hdim : P.dim = 3) :
    P.vertices.card + Nat.card (Face P 2) = Nat.card (Face P 1) + 2 := by
  have hh := euler_three P hdim
  omega

end Papers.PolytopeEulerThree

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/PolytopeIncidenceCounting.lean -/







@[expose] public section

/-!
# Actual incidence dictionaries for Euler counting

Uncompiled draft. All incidence types use membership or inclusion of actual
exposed faces. Every finite equivalence is built from the face polytope or
the proved vertex-figure correspondence. No abstract Euler or manifold
assumption occurs in these definitions.
-/

noncomputable section

namespace Papers.PolytopeIncidenceCounting

open Set Module
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.Polytopes.ActualVertexFigure
open Papers.PolytopeFaceCounting Papers.PolytopeEulerLocal
open Papers.PolytopeBalinski Papers.FiniteGraphHeightCount
open scoped Classical BigOperators

variable {n : ℕ}

abbrev VerticesOn (P : ConvexPolytope n) (A : Set (E n)) :=
  {v : P.vertices // v.val ∈ A}

abbrev FaceBelow (P : ConvexPolytope n) (A : Set (E n)) (k : ℕ) :=
  {F : Face P k // F.val.carrier ⊆ A}

abbrev Coface (P : ConvexPolytope n) (A : Set (E n)) (k : ℕ) :=
  {F : Face P k // A ⊆ F.val.carrier}

abbrev IncidentFace (P : ConvexPolytope n) (v : E n) (k : ℕ) :=
  {F : Face P k // v ∈ F.val.carrier}

def faceVerticesEquiv (P : ConvexPolytope n) {A : Set (E n)}
    (hA : P.IsFace A) : VerticesOn P A ≃ (facePolytope P hA).vertices where
  toFun v := ⟨v.val.val,Finset.mem_filter.mpr ⟨v.val.property,v.property⟩⟩
  invFun v := ⟨⟨v.val,(Finset.mem_filter.mp v.property).1⟩,
    (Finset.mem_filter.mp v.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def faceBelowEquiv (P : ConvexPolytope n) {A : Set (E n)}
    (hA : P.IsFace A) (k : ℕ) :
    FaceBelow P A k ≃ Face (facePolytope P hA) k where
  toFun F := ⟨⟨F.val.val.carrier,
    facePolytope_isFace_of P hA F.val.val.isFace F.property⟩,F.val.property⟩
  invFun F := ⟨⟨⟨F.val.carrier,
    isFace_of_facePolytope P hA F.val.isFace⟩,F.property⟩,by
      have h := face_subset_toSet (facePolytope P hA) F.val.isFace
      simpa only [facePolytope_toSet] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl

def zeroFace (P : ConvexPolytope n) (v : P.vertices) : Face P 0 :=
  ⟨⟨{v.val},vertex_isFace P v.property⟩,faceDim_singleton _⟩

def zeroFaceEquiv (P : ConvexPolytope n) : P.vertices ≃ Face P 0 := by
  apply Equiv.ofBijective (zeroFace P)
  constructor
  · intro v w h
    apply Subtype.ext
    exact Set.singleton_injective (congrArg (fun F => F.val.carrier) h)
  · intro F
    obtain ⟨v,hv,hF⟩ := actual_zeroFace_is_vertex P F.val.carrier
      F.val.isFace F.property
    refine ⟨⟨v,hv⟩,?_⟩
    apply Subtype.ext
    apply PolytopeFace.ext
    exact hF.symm

def incidentStar (P : ConvexPolytope n) (v : E n) (k : ℕ)
    (F : IncidentFace P v (k + 1)) :
    PositiveVertexStarFace P P.toSet v where
  carrier := F.val.val.carrier
  isFace := F.val.val.isFace
  subset_base := face_subset_toSet P F.val.val.isFace
  mem_vertex := F.property
  dim_pos := by rw [F.val.property]; omega

def incidentFigureEquiv {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v) (k : ℕ) :
    IncidentFace P v (k + 1) ≃ Face D.figure k where
  toFun F := ⟨D.faceEquiv (incidentStar P v k F),by
    have h := D.map_dim (incidentStar P v k F)
    change faceDim (D.faceEquiv (incidentStar P v k F)).carrier + 1 =
      faceDim F.val.val.carrier at h
    rw [F.val.property] at h
    omega⟩
  invFun G := by
    let S := D.faceEquiv.symm G.val
    have himage : D.faceEquiv S = G.val := D.faceEquiv.apply_symm_apply _
    have hd : faceDim S.carrier = k + 1 := by
      have h := D.map_dim S
      rw [himage,G.property] at h
      exact h.symm
    exact ⟨⟨⟨S.carrier,S.isFace⟩,hd⟩,S.mem_vertex⟩
  left_inv F := by
    apply Subtype.ext
    apply Subtype.ext
    apply PolytopeFace.ext
    exact congrArg PositiveVertexStarFace.carrier
      (D.faceEquiv.symm_apply_apply (incidentStar P v k F))
  right_inv G := by
    apply Subtype.ext
    apply PolytopeFace.ext
    exact congrArg PolytopeFace.carrier (D.faceEquiv.apply_symm_apply G.val)

@[simp] theorem incidentFigure_carrier {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v) (k : ℕ)
    (F : IncidentFace P v (k + 1)) :
    ((incidentFigureEquiv D k) F).val.carrier =
      (D.faceEquiv (incidentStar P v k F)).carrier := rfl

/-- A coface interval above an edge becomes an incidence star at one
vertex of the first vertex figure. -/
def cofaceFigureEquiv {P : ConvexPolytope n} {v : E n}
    (D : VertexFigureGaloisData P P.toSet v)
    (A : PositiveVertexStarFace P P.toSet v) (k : ℕ) :
    Coface P A.carrier (k + 1) ≃
      Coface D.figure (D.faceEquiv A).carrier k where
  toFun F := by
    let I : IncidentFace P v (k + 1) :=
      ⟨F.val,F.property A.mem_vertex⟩
    refine ⟨incidentFigureEquiv D k I,?_⟩
    exact (D.map_subset_iff A (incidentStar P v k I)).mp F.property
  invFun G := by
    let I := (incidentFigureEquiv D k).symm G.val
    refine ⟨I.val,?_⟩
    have h : D.faceEquiv (incidentStar P v k I) = G.val.val := by
      exact congrArg Subtype.val ((incidentFigureEquiv D k).apply_symm_apply G.val)
    apply (D.map_subset_iff A (incidentStar P v k I)).mpr
    simpa only [h] using G.property
  left_inv F := by
    apply Subtype.ext
    change ((incidentFigureEquiv D k).symm
      ((incidentFigureEquiv D k) (⟨F.val,F.property A.mem_vertex⟩ : IncidentFace P v (k+1)))).val = F.val
    exact congrArg Subtype.val ((incidentFigureEquiv D k).symm_apply_apply
      (⟨F.val,F.property A.mem_vertex⟩ : IncidentFace P v (k + 1)))
  right_inv G := Subtype.ext ((incidentFigureEquiv D k).apply_symm_apply G.val)

def singletonCofaceEquiv (P : ConvexPolytope n) (v : E n) (k : ℕ) :
    Coface P ({v} : Set (E n)) k ≃ IncidentFace P v k where
  toFun F := ⟨F.val,F.property (Set.mem_singleton v)⟩
  invFun F := ⟨F.val,Set.singleton_subset_iff.mpr F.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_eq_two_of_two {T : Type*} (a b : T) (hab : a ≠ b)
    (hcover : ∀ x : T, x = a ∨ x = b) : Nat.card T = 2 := by
  let f : Bool → T := fun t => if t then a else b
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      cases x <;> cases y <;> simp_all [f]
    · intro x
      rcases hcover x with h | h
      · exact ⟨true,by simpa [f] using h.symm⟩
      · exact ⟨false,by simpa [f] using h.symm⟩
  have h := Nat.card_congr (Equiv.ofBijective f hf)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_bool] using h.symm

theorem one_face_vertex_card (P : ConvexPolytope n) (F : Face P 1) :
    Nat.card (VerticesOn P F.val.carrier) = 2 := by
  obtain ⟨e,rfl⟩ := (edgeFaceEquiv P).surjective F
  let x : VerticesOn P (edgeFace P e).val.carrier :=
    ⟨e.val.out.1,(edgeFace_vertex_iff P e _).mpr (Sym2.out_fst_mem _)⟩
  let y : VerticesOn P (edgeFace P e).val.carrier :=
    ⟨e.val.out.2,(edgeFace_vertex_iff P e _).mpr (Sym2.out_snd_mem _)⟩
  have hxy : x ≠ y := by
    intro h
    have hval := congrArg (fun z => z.val.val) h
    exact (edge_out_adj P e).2.1 hval
  apply card_eq_two_of_two x y hxy
  intro z
  have hz := (edgeFace_vertex_iff P e z.val).mp z.property
  rw [← Sym2.mk_fst_out_snd_out e.val,Sym2.mem_iff] at hz
  rcases hz with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- The genuine diamond property implies that a codimension-two face lies
in exactly two facets, in every intrinsic dimension. -/
theorem ridge_coface_card (P : ConvexPolytope n) (k : ℕ)
    (hdim : P.dim = k + 2) (A : Face P k) :
    Nat.card (Coface P A.val.carrier (k + 1)) = 2 := by
  have hAT : A.val.carrier ⊂ P.toSet := by
    refine (face_subset_toSet P A.val.isFace).ssubset_of_ne ?_
    intro h
    have hd := congrArg faceDim h
    change faceDim A.val.carrier = P.dim at hd
    rw [A.property,hdim] at hd
    omega
  obtain ⟨B,hB,hAB,hBT,hdB⟩ := facet_above_proper_face P A.val.isFace hAT
  have hBd : faceDim B = k + 1 := by
    change faceDim B + 1 = P.dim at hdB
    omega
  have hAB' : A.val.carrier ⊂ B := by
    refine hAB.ssubset_of_ne ?_
    intro h
    have hd := congrArg faceDim h
    rw [A.property,hBd] at hd
    omega
  have hrank : faceDim P.toSet = faceDim A.val.carrier + 2 := by
    change P.dim = _
    rw [A.property,hdim]
  obtain ⟨C,hC,hAC,hCT,hCB⟩ :=
    secondo_intermedio P A.val.isFace (toSet_isFace P) hrank hB hAB' hBT
  have hCd : faceDim C = k + 1 := by
    have hlo := faceDim_lt_of_ssubset P A.val.isFace hC hAC
    have hhi := faceDim_lt_of_ssubset P hC (toSet_isFace P) hCT
    change faceDim C < P.dim at hhi
    rw [A.property] at hlo
    omega
  let b : Coface P A.val.carrier (k + 1) := ⟨⟨⟨B,hB⟩,hBd⟩,hAB⟩
  let c : Coface P A.val.carrier (k + 1) := ⟨⟨⟨C,hC⟩,hCd⟩,hAC.1⟩
  have hbc : b ≠ c := by
    intro h
    exact hCB (congrArg (fun z => z.val.val.carrier) h).symm
  apply card_eq_two_of_two b c hbc
  intro F
  have hAF : A.val.carrier ⊂ F.val.val.carrier := by
    refine F.property.ssubset_of_ne ?_
    intro h
    have hd := congrArg faceDim h
    rw [A.property,F.val.property] at hd
    omega
  have hFT : F.val.val.carrier ⊂ P.toSet := by
    refine (face_subset_toSet P F.val.val.isFace).ssubset_of_ne ?_
    intro h
    have hd := congrArg faceDim h
    change faceDim F.val.val.carrier = P.dim at hd
    rw [F.val.property,hdim] at hd
    omega
  have hc := atMostTwo_middle_faces P A.val.isFace (toSet_isFace P) hrank
    hB hAB' hBT hC hAC hCT F.val.val.isFace hAF hFT
  rcases hc with h | h | h
  · exact (hCB h.symm).elim
  · left
    apply Subtype.ext
    apply Subtype.ext
    exact PolytopeFace.ext h.symm
  · right
    apply Subtype.ext
    apply Subtype.ext
    exact PolytopeFace.ext h.symm

theorem polygon_vertices_eq_edges (P : ConvexPolytope n) (hdim : P.dim = 2) :
    Nat.card P.vertices = Nat.card (Face P 1) := by
  have h := two_regular_edge_card (vertexGraph P)
    (polygon_vertex_degree_two P hdim)
  rw [graph_edge_card_eq_one_face_card] at h
  exact h.symm

theorem two_face_vertices_eq_edges (P : ConvexPolytope n) (R : Face P 2) :
    Nat.card (VerticesOn P R.val.carrier) =
      Nat.card (FaceBelow P R.val.carrier 1) := by
  let Q := facePolytope P R.val.isFace
  have hQ : Q.dim = 2 := by
    change faceDim Q.toSet = 2
    rw [facePolytope_toSet]
    exact R.property
  calc
    Nat.card (VerticesOn P R.val.carrier) = Nat.card Q.vertices :=
      Nat.card_congr (faceVerticesEquiv P R.val.isFace)
    _ = Nat.card (Face Q 1) := polygon_vertices_eq_edges Q hQ
    _ = Nat.card (FaceBelow P R.val.carrier 1) :=
      (Nat.card_congr (faceBelowEquiv P R.val.isFace 1)).symm

end Papers.PolytopeIncidenceCounting

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/PolytopeThreeIncidences.lean -/






@[expose] public section

/-!
# Three-dimensional vertex--facet incidence counts

Euler's formula and the actual ridge diamond give the exact total number
of vertex--facet incidences.  Removing any collection of facets only
strengthens the strict bipartite incidence bound used for rational peeling.
-/

noncomputable section
namespace Papers.PolytopeThreeIncidences

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeEulerThree
open Papers.IncidenceCoreGeometry

variable {d : ℕ}

def facetEdgeIncidenceEquiv (P : ConvexPolytope d) :
    (Σ F : Face P 2, FaceBelow P F.val.carrier 1) ≃
      (Σ E : Face P 1, Coface P E.val.carrier 2) where
  toFun x := ⟨x.2.val,⟨x.1,x.2.property⟩⟩
  invFun x := ⟨x.2.val,⟨x.1,x.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem total_vertex_facet_incidences
    (P : ConvexPolytope d) (hdim : P.dim=3) :
    ∑ F : Face P 2, (Nat.card (VerticesOn P F.val.carrier) : ℤ) =
      2*((P.vertices.card : ℤ)+Nat.card (Face P 2)-2) := by
  classical
  letI : Fintype (Face P 1) := Fintype.ofFinite _
  letI : Fintype (Face P 2) := Fintype.ofFinite _
  have hsum : (∑ F : Face P 2, Nat.card (VerticesOn P F.val.carrier)) =
      2*Nat.card (Face P 1) := by
    simp_rw [two_face_vertices_eq_edges]
    rw [← Nat.card_sigma,Nat.card_congr (facetEdgeIncidenceEquiv P),Nat.card_sigma]
    simp only [ridge_coface_card P 1 (by simpa using hdim)]
    simp [Nat.card_eq_fintype_card,mul_comm]
  have hsumZ : (∑ F : Face P 2, (Nat.card (VerticesOn P F.val.carrier) : ℤ)) =
      2*(Nat.card (Face P 1) : ℤ) := by exact_mod_cast hsum
  have heuler := euler_three P hdim
  linarith

theorem face_vertex_card_gt_dimension (P : ConvexPolytope d)
    (k : ℕ) (F : Face P k) : k<Nat.card (VerticesOn P F.val.carrier) := by
  have h := actual_vertices_card_gt_dim (facePolytope P F.val.isFace)
  have hd : (facePolytope P F.val.isFace).dim=k := by
    change faceDim (facePolytope P F.val.isFace).toSet=k
    rw [facePolytope_toSet,F.property]
  rw [hd] at h
  have hh : k<Nat.card (facePolytope P F.val.isFace).vertices := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using h
  rw [← Nat.card_congr (faceVerticesEquiv P F.val.isFace)] at hh
  exact hh

/-- Deleting unselected actual facets removes at least three incidences
per facet.  The remaining incidence count is strictly below twice the
number of remaining point and facet nodes. -/
theorem selected_facet_incidence_bound
    (P : ConvexPolytope d) (hdim : P.dim=3) (T : Finset (Face P 2)) :
    ∑ F∈T, (Nat.card (VerticesOn P F.val.carrier) : ℤ) <
      2*((P.vertices.card : ℤ)+T.card) := by
  classical
  letI : Fintype (Face P 2) := Fintype.ofFinite _
  let w : Face P 2 → ℤ := fun F => Nat.card (VerticesOn P F.val.carrier)
  have hmin : ∀ F, 3≤w F := by
    intro F
    have h := face_vertex_card_gt_dimension P 2 F
    change (3:ℤ) ≤ (Nat.card (VerticesOn P F.val.carrier):ℤ)
    exact_mod_cast (show 3≤Nat.card (VerticesOn P F.val.carrier) by omega)
  have houtside : 3*((Finset.univ\T).card : ℤ) ≤ ∑ F∈Finset.univ\T,w F := by
    calc
      3*((Finset.univ\T).card : ℤ) = ∑ _F∈Finset.univ\T,(3:ℤ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun F _ => hmin F
  have hsplit : (∑ F∈T,w F)+(∑ F∈Finset.univ\T,w F)=∑ F,w F :=
    Finset.sum_add_sum_compl T w
  have hcard : T.card+(Finset.univ\T).card=Nat.card (Face P 2) := by
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_add_card_compl T
  have htotal := total_vertex_facet_incidences P hdim
  change (∑ F,w F)=_ at htotal
  have hcardZ : (T.card:ℤ)+(Finset.univ\T).card=Nat.card (Face P 2) := by
    exact_mod_cast hcard
  change (∑ F∈T,w F)<_
  have hn : (0:ℤ)≤(Finset.univ\T).card := by exact_mod_cast Nat.zero_le ((Finset.univ\T).card)
  linarith

end Papers.PolytopeThreeIncidences

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/PolytopeIncidencePeeling.lean -/



@[expose] public section

/-!
# Every induced three-polytope incidence graph has a low-degree node

The active point hull retains every old two-face containing three active
vertices. If all degrees were at least four, two retained faces would
force that hull to remain three-dimensional. Its actual Euler incidence
bound then contradicts the degree lower bound on the active bipartite graph.
-/

noncomputable section
namespace Papers.PolytopeIncidencePeeling

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open Papers.PolytopeIncidenceCounting Papers.PolytopeThreeIncidences
open Papers.IncidenceCoreGeometry Papers.BipartiteIncidencePeeling

variable {d : ℕ}

def pointFacetIncident (P : ConvexPolytope d) (x : E d) (F : Face P 2) : Prop :=
  x∈F.val.carrier

def restrictedTwoFace (P Q : ConvexPolytope d) (hQP : Q.toSet⊆P.toSet)
    (F : Face P 2) (hF : 3≤(Q.vertices.filter (·∈F.val.carrier)).card) :
    Face Q 2 :=
  ⟨⟨F.val.carrier∩Q.toSet,(retained_two_face P Q hQP F.val.isFace F.property hF).1⟩,
    (retained_two_face P Q hQP F.val.isFace F.property hF).2⟩

theorem restrictedTwoFace_injective
    (P Q : ConvexPolytope d) (hQP : Q.toSet⊆P.toSet)
    (T : Finset (Face P 2))
    (hc : ∀ F∈T, 3≤(Q.vertices.filter (·∈F.val.carrier)).card) :
    Function.Injective (fun F : T => restrictedTwoFace P Q hQP F.val (hc F.val F.property)) := by
  intro F G heq
  apply Subtype.ext
  apply Subtype.ext
  apply PolytopeFace.ext
  let A := F.val.val.carrier∩Q.toSet
  have hA : A.Nonempty :=
    (retained_two_face P Q hQP F.val.val.isFace F.val.property
      (hc F.val F.property)).1.2
  have heq' : F.val.val.carrier∩Q.toSet=G.val.val.carrier∩Q.toSet :=
    congrArg (fun X : Face Q 2 => X.val.carrier) heq
  apply faces_eq_of_full_dim_common_subset P F.val.val.isFace G.val.val.isFace hA
  · exact Set.inter_subset_left
  · intro x hx
    change x∈F.val.val.carrier∩Q.toSet at hx
    rw [heq'] at hx
    exact hx.1
  · rw [F.val.property]
    exact le_of_eq ((retained_two_face P Q hQP F.val.val.isFace F.val.property
      (hc F.val F.property)).2.symm)
  · rw [G.val.property]
    exact le_of_eq ((retained_two_face P Q hQP F.val.val.isFace F.val.property
      (hc F.val F.property)).2.symm)

def restrictedVerticesEquiv (Q : ConvexPolytope d) (F : Set (E d)) :
    VerticesOn Q (F∩Q.toSet) ≃ (Q.vertices.filter (·∈F)) where
  toFun x := ⟨x.val.val,Finset.mem_filter.mpr ⟨x.val.property,x.property.1⟩⟩
  invFun x := ⟨⟨x.val,(Finset.mem_filter.mp x.property).1⟩,
    (Finset.mem_filter.mp x.property).2,
    vertex_mem_body Q (Finset.mem_filter.mp x.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem restricted_vertex_card (Q : ConvexPolytope d) (F : Set (E d)) :
    Nat.card (VerticesOn Q (F∩Q.toSet))=(Q.vertices.filter (·∈F)).card := by
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
    Nat.card_congr (restrictedVerticesEquiv Q F)

/-- The exact geometric low-degree alternative, for arbitrary selected
vertices and selected actual two-faces of an intrinsic three-polytope. -/
theorem exists_low_degree
    (P : ConvexPolytope d) (hdim : P.dim=3)
    (S : Finset (E d)) (hSP : S⊆P.vertices) (T : Finset (Face P 2))
    (hne : S.Nonempty ∨ T.Nonempty) :
    (∃ x∈S, (T.filter (fun F => x∈F.val.carrier)).card≤3) ∨
      (∃ F∈T, (S.filter (fun x => x∈F.val.carrier)).card≤3) := by
  classical
  by_contra h
  have hleft : ∀ x∈S, 4≤(T.filter (fun F => x∈F.val.carrier)).card := by
    intro x hx
    by_contra hh
    exact h (Or.inl ⟨x,hx,by omega⟩)
  have hright : ∀ F∈T, 4≤(S.filter (fun x => x∈F.val.carrier)).card := by
    intro F hF
    by_contra hh
    exact h (Or.inr ⟨F,hF,by omega⟩)
  have hS : S.Nonempty := by
    rcases hne with hS | hT
    · exact hS
    · obtain ⟨F,hF⟩ := hT
      have hc := hright F hF
      obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<(S.filter (fun x => x∈F.val.carrier)).card by omega)
      exact ⟨x,(Finset.mem_filter.mp hx).1⟩
  let Q := vertexSubsetPolytope P S hS hSP
  have hQP : Q.toSet⊆P.toSet := vertexSubset_body_subset P S hS hSP
  have hc : ∀ F∈T, 3≤(Q.vertices.filter (·∈F.val.carrier)).card := by
    intro F hF
    exact le_trans (by decide : 3≤4) (hright F hF)
  obtain ⟨x,hx⟩ := hS
  have hTcard : 1<T.card := by
    have h4 := hleft x hx
    have hh := Finset.card_filter_le T (fun F => x∈F.val.carrier)
    omega
  obtain ⟨F,hF,G,hG,hFG⟩ := Finset.one_lt_card.mp hTcard
  have hFG' : F.val.carrier≠G.val.carrier := by
    intro heq
    exact hFG (Subtype.ext (PolytopeFace.ext heq))
  have hQdim : Q.dim=3 := dimension_three_of_two_retained_faces P Q hdim hQP
    F.val.isFace G.val.isFace F.property G.property hFG' (hc F hF) (hc G hG)
  let f : T → Face Q 2 := fun F => restrictedTwoFace P Q hQP F.val (hc F.val F.property)
  have hf : Function.Injective f := restrictedTwoFace_injective P Q hQP T hc
  let U : Finset (Face Q 2) := Finset.univ.image f
  have hUcard : U.card=T.card := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hweight : ∀ F : T, Nat.card (VerticesOn Q (f F).val.carrier)=
      (S.filter (fun x => x∈F.val.val.carrier)).card := by
    intro F
    exact restricted_vertex_card Q F.val.val.carrier
  have hUsum : (∑ H∈U,(Nat.card (VerticesOn Q H.val.carrier) : ℤ)) =
      ∑ F∈T,((S.filter (fun x => x∈F.val.carrier)).card : ℤ) := by
    rw [Finset.sum_image (fun a _ b _ h => hf h)]
    simp_rw [hweight]
    exact Finset.sum_coe_sort T (fun F : Face P 2 => ((S.filter (fun x => x∈F.val.carrier)).card : ℤ))
  have hbound := selected_facet_incidence_bound Q hQdim U
  rw [hUsum,hUcard] at hbound
  change (∑ F∈T,((S.filter (fun x => x∈F.val.carrier)).card : ℤ)) <
    2*((S.card : ℤ)+T.card) at hbound
  have hsum : (∑ x∈S,(pointDegree (pointFacetIncident P) T x : ℤ)) =
      ∑ F∈T,(faceDegree (pointFacetIncident P) S F : ℤ) := by
    exact_mod_cast sum_degrees (pointFacetIncident P) S T
  have hbound' : (∑ x∈S,(pointDegree (pointFacetIncident P) T x : ℤ)) <
      2*((S.card : ℤ)+T.card) := by
    rw [hsum]
    exact hbound
  exact h (exists_degree_le_three (pointFacetIncident P) S T hbound')

end Papers.PolytopeIncidencePeeling

end
end
end BundlePart13
