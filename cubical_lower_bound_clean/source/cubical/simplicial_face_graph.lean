module

public import cubical.simplicial_faces
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # The edge count of a simplicial family equals its number of two-element faces -/

@[expose] public section

namespace Cubical.Simplicial

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

theorem mem_vertices_link_vertex (s : Finset (Finset V)) (v w : V) :
    w ∈ vertices id (link s {v}) ↔ (oneSkeleton id s).Adj v w := by
  constructor
  · intro hw
    obtain ⟨t, ht, hwt⟩ := (mem_vertices id (link s {v}) w).mp hw
    obtain ⟨hdisj, hmem⟩ := (mem_link s {v} t).mp ht
    have hvt : v ∉ t := by simpa using hdisj
    refine ⟨fun h => hvt (h.symm ▸ hwt), {v} ∪ t, hmem, by simp, ?_⟩
    exact Finset.mem_union_right _ hwt
  · rintro ⟨hvw, t, ht, hvt, hwt⟩
    change v ∈ t at hvt
    change w ∈ t at hwt
    refine (mem_vertices id (link s {v}) w).mpr ⟨t.erase v, ?_, ?_⟩
    · apply (mem_link s {v} (t.erase v)).mpr
      refine ⟨by simp, ?_⟩
      simpa only [Finset.singleton_union, Finset.insert_erase hvt] using ht
    · exact Finset.mem_erase.mpr ⟨hvw.symm, hwt⟩

theorem supportGraph_degree (s : Finset (Finset V)) (v : {v // v ∈ vertices id s})
    [Fintype ((supportGraph id s).neighborSet v)] :
    (supportGraph id s).degree v = (vertices id (link s {v.val})).card := by
  classical
  have himage : ((supportGraph id s).neighborFinset v).image Subtype.val =
      vertices id (link s {v.val}) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
      exact (mem_vertices_link_vertex s v.val x.val).mpr
        ((supportGraph id s).mem_neighborFinset v x |>.mp hx)
    · intro hw
      have hadj := (mem_vertices_link_vertex s v.val w).mp hw
      have hwm := (oneSkeleton_adj_vertices hadj).2
      exact Finset.mem_image.mpr ⟨⟨w, hwm⟩,
        ((supportGraph id s).mem_neighborFinset v ⟨w, hwm⟩).mpr hadj, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  exact ((supportGraph id s).card_neighborFinset_eq_degree v).symm

theorem supportGraph_edge_count_eq_faces (s : Finset (Finset V)) :
    Nat.card (supportGraph id s).edgeSet = (faces s 2).card := by
  classical
  have hsum := (supportGraph id s).sum_degrees_eq_twice_card_edges
  have hlink : (∑ v : {v // v ∈ vertices id s}, (supportGraph id s).degree v) =
      2 * (faces s 2).card := by
    simp_rw [supportGraph_degree]
    change (∑ v ∈ (vertices id s).attach, (vertices id (link s {v.val})).card) = _
    rw [Finset.sum_attach (vertices id s) (fun v => (vertices id (link s {v})).card)]
    exact sum_link_vertices s
  rw [hlink, ← SimpleGraph.card_edgeSet] at hsum
  rw [Nat.card_eq_fintype_card]
  omega

end Cubical.Simplicial
