module

public import Papers.GraphicalZonotopes.SingleVertexGraph
public import Papers.GraphicalZonotopes.ThreeTreeInducedEquality
public import Papers.GraphicalZonotopes.ThreeTreeSharedEdges

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace SingleVertexGraph
open Finset BooleanModule BooleanVertexExtension SetFunctionEmbedding
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem all_vertices_eq_insert :
    (univ : Finset (BooleanVertexExtension.Vertex V)) =
      insert (Sum.inr 0) (hubSet (J := Fin 1) (univ : Finset V)) := by
  ext x
  cases x with
  | inl v => simp
  | inr j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp

/-- A spanning admissible three-tree survives deleting a newly attached
vertex with at most three available neighbors. The proof uses exact edge
counts on arbitrary induced subsets, so no construction order is assumed. -/
theorem admissible_spanning_prune {G : SimpleGraph V} {N : Finset V}
    (hV : 4 ≤ Fintype.card V) (hN : N.card ≤ 3)
    (h : HasAdmissibleSpanningThreeTree (graph G N)) :
    HasAdmissibleSpanningThreeTree G := by
  obtain ⟨H,hHG,hH,hA⟩ := h
  let C : Finset (BooleanVertexExtension.Vertex V) := hubSet (univ : Finset V)
  have hC : C.card = Fintype.card V := by simp [C,hubSet]
  have hw : Sum.inr 0 ∉ C := notMem_hubSet_outer _ _
  have hsize : (edgeFamily H).card = 3*(Fintype.card V+1)-6 := by
    simpa only [card_univ,Fintype.card_sum,Fintype.card_fin] using hH.edgeFamily_card
  have hnb : earlierNeighbors H C (Sum.inr 0) ⊆ hubSet (J := Fin 1) N := by
    intro x hx
    obtain ⟨hxC,hwx⟩ := (mem_earlierNeighbors _ _ _ _).mp hx
    cases x with
    | inl v =>
      exact (mem_hubSet_hub _ _).mpr (hHG hwx)
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact False.elim (hw hxC)
  have hnb3 : (earlierNeighbors H C (Sum.inr 0)).card ≤ 3 := by
    have hh := card_le_card hnb
    simp only [hubSet,card_map] at hh
    exact hh.trans hN
  have hsplit : (edgeFamily H).card = (edgeFamily (inducedOn H C)).card +
      (earlierNeighbors H C (Sum.inr 0)).card := by
    have hh := induced_edge_count_insert H C (Sum.inr 0) hw
    have hu : insert (Sum.inr 0) C = univ := all_vertices_eq_insert.symm
    rw [hu,inducedOn_univ] at hh
    exact hh
  have hbound := hH.induced_edge_bound C (subset_univ C) (by omega)
  have he : (edgeFamily (inducedOn H C)).card = 3*C.card-6 := by omega
  have hp : ThreeTreeOn C (inducedOn H C) :=
    hH.induced_equality C (subset_univ C) (by omega) he
  have hrange : ∀ x ∈ C, x ∈ Set.range (old : V ↪ BooleanVertexExtension.Vertex V) := by
    intro x hx
    obtain ⟨v,hv,hvx⟩ := mem_map.mp hx
    exact ⟨v,hvx⟩
  have hcomap : (inducedOn H C).comap old = H.comap old := by
    ext u v
    change (H.Adj (Sum.inl u) (Sum.inl v) ∧ Sum.inl u ∈ C ∧ Sum.inl v ∈ C) ↔ _
    simp [C,old]
  have hset : pullSet old C = univ := by
    ext v
    simp [C,old]
  have htOld : IsThreeTree (H.comap old) := by
    have ht := hp.comap old hrange
    rw [hcomap,hset] at ht
    exact ht
  have hAP : Admissible (inducedOn H C) := by
    intro T hT hcl
    exact (triangleMultiplicity_mono (inducedOn_le H C) T).trans
      (hA T hT (fun u hu v hv huv => (hcl hu hv huv).1))
  have hmap : ((inducedOn H C).comap old).map old = inducedOn H C :=
    map_comap_of_supported old _ (fun u v huv => hrange u huv.2.1)
  have hAO : Admissible (H.comap old) := by
    have hh := Admissible.of_map old (G := (inducedOn H C).comap old) (by rwa [hmap])
    rwa [hcomap] at hh
  exact ⟨H.comap old,fun u v huv => hHG huv,htOld,hAO⟩

end SingleVertexGraph
end GraphicalZonotopes
