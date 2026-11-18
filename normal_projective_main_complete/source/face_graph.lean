module

public import subfaces
public import punctured_convex
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Actual face-adjacency connectivity

Removing the finite vertex set from the interior of a convex triangulated
domain leaves a connected set. The closed triangle carriers cover that set,
and two of them can meet there only along a common edge. This proves the
connectivity needed to propagate nondegeneracy, without assuming a dual-graph
axiom in the definition of a triangulation.
-/

@[expose] public section

noncomputable section

namespace NormalProjective.Planar

open Set Finset

theorem connected_of_closed_cover_nerve {I X : Type*} [Fintype I]
    [TopologicalSpace X] [Nonempty I] (G : SimpleGraph I)
    (cell : I → Set X) (hclosed : ∀ i, IsClosed (cell i))
    (hne : ∀ i, (cell i).Nonempty)
    (hmeet : ∀ i j, (cell i ∩ cell j).Nonempty → i = j ∨ G.Adj i j)
    (hconn : IsPreconnected (⋃ i, cell i)) : G.Connected := by
  classical
  refine ⟨fun a b => ?_⟩
  by_contra hab
  let U : Set X := ⋃ i : {i // G.Reachable a i}, cell i.val
  let W : Set X := ⋃ i : {i // ¬ G.Reachable a i}, cell i.val
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun i => hclosed i.val)
  have hW : IsClosed W := isClosed_iUnion_of_finite (fun i => hclosed i.val)
  have hcover : (⋃ i, cell i) ⊆ U ∪ W := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    by_cases h : G.Reachable a i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i,h⟩,hi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i,h⟩,hi⟩)
  have ha : ((⋃ i,cell i) ∩ U).Nonempty := by
    obtain ⟨x,hx⟩ := hne a
    exact ⟨x,mem_iUnion.mpr ⟨a,hx⟩,mem_iUnion.mpr ⟨⟨a,.refl a⟩,hx⟩⟩
  have hb : ((⋃ i,cell i) ∩ W).Nonempty := by
    obtain ⟨x,hx⟩ := hne b
    exact ⟨x,mem_iUnion.mpr ⟨b,hx⟩,mem_iUnion.mpr ⟨⟨b,hab⟩,hx⟩⟩
  obtain ⟨x,_,hxU,hxW⟩ := isPreconnected_closed_iff.mp hconn U W hU hW hcover ha hb
  obtain ⟨i,hi⟩ := mem_iUnion.mp hxU
  obtain ⟨j,hj⟩ := mem_iUnion.mp hxW
  rcases hmeet i.val j.val ⟨x,hi,hj⟩ with heq | hadj
  · exact j.property (heq ▸ i.property)
  · exact j.property (i.property.trans hadj.reachable)

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Triangulation

variable (T : Triangulation V)

def faceGraph : SimpleGraph T.Face where
  Adj s t := s ≠ t ∧ 2 ≤ (s.val ∩ t.val).card
  symm := ⟨by intro s t h; exact ⟨h.1.symm,by simpa [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨by intro s h; exact h.1 rfl⟩

theorem interior_cell_nonempty (s : T.Face) : (interior (T.cell s)).Nonempty := by
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  have hspan := (T.face_independent s.val s.property).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    (by simpa [Complex.finrank_real_complex] using T.face_card s.val s.property)
  have hrange : Set.range (fun v : s.val => T.point v) = T.point '' (s.val : Set V) := by
    ext z
    simp only [Set.mem_range,Set.mem_image,Finset.mem_coe]
    constructor
    · rintro ⟨v,rfl⟩
      exact ⟨v.val,v.property,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨⟨v,hv⟩,rfl⟩
  rw [hrange] at hspan
  exact hspan

theorem faceGraph_connected [Nonempty T.Face] (hconvex : Convex ℝ T.domain) :
    T.faceGraph.Connected := by
  classical
  let U : Set ℂ := interior T.domain \ Set.range T.point
  let C : T.Face → Set U := fun s => {z | (z : ℂ) ∈ T.cell s}
  have hclosed : ∀ s, IsClosed (C s) := fun s =>
    (T.cell_isCompact s).isClosed.preimage continuous_subtype_val
  have hne : ∀ s, (C s).Nonempty := by
    intro s
    obtain ⟨z,hzi,hznot⟩ := (Set.finite_range T.point).countable.dense_compl ℝ
      |>.inter_open_nonempty (interior (T.cell s)) isOpen_interior (T.interior_cell_nonempty s)
    have hdom : z ∈ interior T.domain := interior_mono (fun x hx =>
      mem_iUnion.mpr ⟨s,hx⟩) hzi
    refine ⟨⟨z,hdom,hznot⟩,?_⟩
    change z ∈ T.cell s
    exact interior_subset hzi
  have hmeet : ∀ s t, (C s ∩ C t).Nonempty → s = t ∨ T.faceGraph.Adj s t := by
    intro s t h
    by_cases hst : s = t
    · exact Or.inl hst
    refine Or.inr ⟨hst,?_⟩
    obtain ⟨z,hzs,hzt⟩ := h
    have hz : (z : ℂ) ∈ simplex T.point (s.val ∩ t.val) := by
      rw [← T.cell_intersection]
      exact ⟨hzs,hzt⟩
    by_contra hc
    have hcard : (s.val ∩ t.val).card ≤ 1 := by omega
    rcases Nat.eq_zero_or_pos (s.val ∩ t.val).card with hzero | hpos
    · have he : s.val ∩ t.val = ∅ := Finset.card_eq_zero.mp hzero
      simpa [he,simplex] using hz
    · have hone : (s.val ∩ t.val).card = 1 := by omega
      obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hone
      have hzeq : (z : ℂ) = T.point v := by simpa [hv,simplex] using hz
      exact z.property.2 ⟨v,hzeq.symm⟩
  have hconn : IsPreconnected (⋃ s,C s) := by
    apply (Topology.IsInducing.isPreconnected_image Topology.IsInducing.subtypeVal).mp
    have himage : Subtype.val '' (⋃ s,C s) = U := by
      ext z
      constructor
      · rintro ⟨x,_,rfl⟩
        exact x.property
      · intro hz
        obtain ⟨s,hs⟩ := mem_iUnion.mp (interior_subset hz.1)
        exact ⟨⟨z,hz⟩,mem_iUnion.mpr ⟨s,hs⟩,rfl⟩
    rw [himage]
    exact isPreconnected_convex_sdiff_countable hconvex.interior isOpen_interior
      (Set.finite_range T.point).countable (by
        rw [Complex.rank_real_complex]
        exact Cardinal.one_lt_two)
  exact connected_of_closed_cover_nerve T.faceGraph C hclosed hne hmeet hconn

end Triangulation

end NormalProjective.Planar
