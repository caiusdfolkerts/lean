module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Topology.Connected.Clopen

/-!
# Graph connectivity from a finite geometric cover

The vertices carried by any one closed cell form a graph clique. Intersecting
cells share an actual vertex. Consequently a connected union of cells has a
connected vertex graph. This supplies the graph-connectivity bridge for the
geometric triangulation, including its open half-plane restrictions.
-/

@[expose] public section

namespace NormalProjective.Planar

open Set

variable {V I E : Type*} [Finite I] [TopologicalSpace E]

theorem connected_of_closed_cell_cover (G : SimpleGraph V) [Nonempty V]
    (cell : I → Set E) (vertices : I → Set V) (p : V → E)
    (hclosed : ∀ i, IsClosed (cell i))
    (hvertex : ∀ i v, v ∈ vertices i → p v ∈ cell i)
    (hcover : ∀ v, ∃ i, v ∈ vertices i)
    (hclique : ∀ i v w, v ∈ vertices i → w ∈ vertices i → v ≠ w → G.Adj v w)
    (hinter : ∀ i j, (cell i ∩ cell j).Nonempty →
      (vertices i ∩ vertices j).Nonempty)
    (hconn : IsPreconnected (⋃ i, cell i)) : G.Connected := by
  classical
  refine ⟨?_⟩
  intro a b
  by_contra hab
  let good : I → Prop := fun i => ∃ v ∈ vertices i, G.Reachable a v
  let U : Set E := ⋃ i : {i // good i}, cell i.val
  let W : Set E := ⋃ i : {i // ¬ good i}, cell i.val
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun i => hclosed i.val)
  have hW : IsClosed W := isClosed_iUnion_of_finite (fun i => hclosed i.val)
  have hUW : (⋃ i, cell i) ⊆ U ∪ W := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    by_cases hg : good i
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i,hg⟩,hi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨i,hg⟩,hi⟩)
  have hreachable : ∀ i v w, v ∈ vertices i → w ∈ vertices i → G.Reachable v w := by
    intro i v w hv hw
    by_cases hvw : v = w
    · subst w
      exact .refl v
    · exact (hclique i v w hv hw hvw).reachable
  have ha : ((⋃ i, cell i) ∩ U).Nonempty := by
    obtain ⟨i,hi⟩ := hcover a
    have hg : good i := ⟨a,hi,.refl a⟩
    exact ⟨p a,mem_iUnion.mpr ⟨i,hvertex i a hi⟩,
      mem_iUnion.mpr ⟨⟨i,hg⟩,hvertex i a hi⟩⟩
  have hb : ((⋃ i, cell i) ∩ W).Nonempty := by
    obtain ⟨i,hi⟩ := hcover b
    have hg : ¬ good i := by
      rintro ⟨v,hv,hav⟩
      exact hab (hav.trans (hreachable i v b hv hi))
    exact ⟨p b,mem_iUnion.mpr ⟨i,hvertex i b hi⟩,
      mem_iUnion.mpr ⟨⟨i,hg⟩,hvertex i b hi⟩⟩
  obtain ⟨x,_,hxU,hxW⟩ :=
    isPreconnected_closed_iff.mp hconn U W hU hW hUW ha hb
  obtain ⟨i,hi⟩ := mem_iUnion.mp hxU
  obtain ⟨j,hj⟩ := mem_iUnion.mp hxW
  obtain ⟨v,hvi,hvj⟩ := hinter i.val j.val ⟨x,hi,hj⟩
  obtain ⟨w,hwi,haw⟩ := i.property
  exact j.property ⟨v,hvj,haw.trans (hreachable i.val w v hwi hvi)⟩

end NormalProjective.Planar
