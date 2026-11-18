module

public import closed_cover
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# Actual finite planar triangulations

Faces are finite sets of vertex labels and their carriers are their actual
convex hulls in `ℂ = ℝ²`. The intersection axiom is the usual geometric
simplicial-complex condition, not a predicate about harmonic maps. Connectivity
of the one-skeleton, and of its positive-half-plane induced subgraphs, is proved
from this geometry by a finite closed-cover argument.
-/

@[expose] public section

namespace NormalProjective.Planar

open Set Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def simplex (p : V → ℂ) (s : Finset V) : Set ℂ :=
  convexHull ℝ (p '' (s : Set V))

theorem point_mem_simplex (p : V → ℂ) (s : Finset V) {v : V} (hv : v ∈ s) :
    p v ∈ simplex p s := subset_convexHull ℝ _ ⟨v,hv,rfl⟩

theorem simplex_isCompact (p : V → ℂ) (s : Finset V) :
    IsCompact (simplex p s) := (s.finite_toSet.image p).isCompact_convexHull ℝ

/-- A finite geometric triangulation with all its vertices explicitly labelled.
The domain is defined as the union of the actual closed triangles. -/
structure Triangulation (V : Type*) [Fintype V] [DecidableEq V] where
  point : V → ℂ
  point_injective : Function.Injective point
  faces : Finset (Finset V)
  face_card : ∀ s ∈ faces, s.card = 3
  face_independent : ∀ s ∈ faces, AffineIndependent ℝ (fun v : s => point v)
  intersection : ∀ s ∈ faces, ∀ t ∈ faces,
    simplex point s ∩ simplex point t = simplex point (s ∩ t)
  vertex_covered : ∀ v, ∃ s ∈ faces, v ∈ s

namespace Triangulation

variable (T : Triangulation V)

abbrev Face := {s : Finset V // s ∈ T.faces}

def cell (s : T.Face) : Set ℂ := simplex T.point s.val

def domain : Set ℂ := ⋃ s : T.Face, T.cell s

def graph : SimpleGraph V where
  Adj i j := i ≠ j ∧ ∃ s ∈ T.faces, i ∈ s ∧ j ∈ s
  symm := ⟨by
    rintro i j ⟨hij,s,hs,hi,hj⟩
    exact ⟨hij.symm,s,hs,hj,hi⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

theorem adj_iff {i j : V} :
    T.graph.Adj i j ↔ i ≠ j ∧ ∃ s ∈ T.faces, i ∈ s ∧ j ∈ s := Iff.rfl

theorem cell_isCompact (s : T.Face) : IsCompact (T.cell s) :=
  simplex_isCompact T.point s.val

theorem point_mem_cell (s : T.Face) {v : V} (hv : v ∈ s.val) :
    T.point v ∈ T.cell s := point_mem_simplex T.point s.val hv

theorem point_mem_domain (v : V) : T.point v ∈ T.domain := by
  obtain ⟨s,hs,hv⟩ := T.vertex_covered v
  exact mem_iUnion.mpr ⟨⟨s,hs⟩,T.point_mem_cell ⟨s,hs⟩ hv⟩

theorem cell_intersection (s t : T.Face) :
    T.cell s ∩ T.cell t = simplex T.point (s.val ∩ t.val) :=
  T.intersection s.val s.property t.val t.property

theorem common_vertex_of_intersection (s t : T.Face)
    (h : (T.cell s ∩ T.cell t).Nonempty) :
    ((s.val : Set V) ∩ (t.val : Set V)).Nonempty := by
  rw [T.cell_intersection] at h
  obtain ⟨_,v,hv,rfl⟩ := convexHull_nonempty_iff.mp h
  exact ⟨v,(mem_inter.mp hv).1,(mem_inter.mp hv).2⟩

theorem graph_connected [Nonempty V] (hconn : IsPreconnected T.domain) :
    T.graph.Connected := by
  apply connected_of_closed_cell_cover T.graph T.cell (fun s => (s.val : Set V)) T.point
  · exact fun s => (T.cell_isCompact s).isClosed
  · exact fun s v hv => T.point_mem_cell s hv
  · intro v
    obtain ⟨s,hs,hv⟩ := T.vertex_covered v
    exact ⟨⟨s,hs⟩,hv⟩
  · intro s v w hv hw hvw
    exact ⟨hvw,s.val,s.property,hv,hw⟩
  · exact T.common_vertex_of_intersection
  · exact hconn

/-- A positive linear-functional value somewhere in a simplex is positive at
one of its vertices. The contrapositive is convexity of a closed half-space. -/
theorem exists_positive_vertex (l : ℂ →L[ℝ] ℝ) (c : ℝ) (s : Finset V)
    {z : ℂ} (hz : z ∈ simplex T.point s) (hpos : c < l z) :
    ∃ v ∈ s, c < l (T.point v) := by
  by_contra! h
  have hsub : simplex T.point s ⊆ {z | l z ≤ c} := by
    apply convexHull_min
    · rintro _ ⟨v,hv,rfl⟩
      exact h v hv
    · exact convex_halfSpace_le l.toLinearMap.isLinear c
  exact not_le_of_gt hpos (hsub hz)

/-- The one-skeleton of a geometric triangulation of a convex domain remains
connected after restriction to any nonempty open half-plane. This proves the
boundary-corner accessibility needed by the strong maximum principle without
assuming an abstract planar connectivity axiom. -/
theorem positive_induce_connected (hconvex : Convex ℝ T.domain)
    (l : ℂ →L[ℝ] ℝ) (c : ℝ)
    (hne : ∃ v, c < l (T.point v)) :
    (T.graph.induce {v | c < l (T.point v)}).Connected := by
  classical
  let S : Set V := {v | c < l (T.point v)}
  let U : Set ℂ := {z | c < l z}
  letI : Nonempty S := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  let C : T.Face → Set U := fun s => {z | (z : ℂ) ∈ T.cell s}
  let P : S → U := fun v => ⟨T.point v,v.property⟩
  have hcell : ∀ s, IsClosed (C s) := fun s =>
    (T.cell_isCompact s).isClosed.preimage continuous_subtype_val
  have hconn : IsPreconnected (⋃ s, C s) := by
    apply (Topology.IsInducing.isPreconnected_image Topology.IsInducing.subtypeVal).mp
    have himage : Subtype.val '' (⋃ s, C s) = T.domain ∩ U := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨s,hs⟩ := mem_iUnion.mp hx
        exact ⟨mem_iUnion.mpr ⟨s,hs⟩,x.property⟩
      · rintro ⟨hz,hzU⟩
        obtain ⟨s,hs⟩ := mem_iUnion.mp hz
        exact ⟨⟨z,hzU⟩,mem_iUnion.mpr ⟨s,hs⟩,rfl⟩
    rw [himage]
    exact (hconvex.inter (convex_halfSpace_gt l.toLinearMap.isLinear c)).isPreconnected
  apply connected_of_closed_cell_cover (T.graph.induce S) C
    (fun s => {v : S | (v : V) ∈ s.val}) P hcell
  · intro s v hv
    exact T.point_mem_cell s hv
  · intro v
    obtain ⟨s,hs,hv⟩ := T.vertex_covered v.val
    exact ⟨⟨s,hs⟩,hv⟩
  · intro s v w hv hw hvw
    exact ⟨fun h => hvw (Subtype.ext h),s.val,s.property,hv,hw⟩
  · intro s t h
    obtain ⟨z,hzs,hzt⟩ := h
    have hz : (z : ℂ) ∈ simplex T.point (s.val ∩ t.val) := by
      rw [← T.cell_intersection]
      exact ⟨hzs,hzt⟩
    obtain ⟨v,hv,hvpos⟩ := T.exists_positive_vertex l c (s.val ∩ t.val) hz z.property
    exact ⟨⟨v,hvpos⟩,(mem_inter.mp hv).1,(mem_inter.mp hv).2⟩
  · exact hconn

end Triangulation

end NormalProjective.Planar
