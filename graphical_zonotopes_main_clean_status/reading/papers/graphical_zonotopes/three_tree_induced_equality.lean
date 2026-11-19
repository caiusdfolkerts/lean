module

public import Papers.GraphicalZonotopes.PartialThreeTreeGraph
public import Papers.GraphicalZonotopes.ThreeTreeEmbedding

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ThreeTreeOn.induced_self {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : inducedOn G S = G := by
  ext u v
  exact ⟨fun huv => huv.1,fun huv => ⟨huv,h.edges_supported huv⟩⟩

theorem ThreeTreeOn.edgeFamily_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (edgeFamily G).card = 3*S.card-6 := by
  induction h with
  | tetrahedron C hC =>
    rw [edgeFamily_cliqueGraph,card_powersetCard,hC]
    decide
  | @attach S G h u hu T hT hTS hc ih =>
    have hn : earlierNeighbors (G ⊔ attachmentStar u T) S u = T := by
      ext v
      rw [mem_earlierNeighbors]
      constructor
      · exact fun hv => (attached_vertex_adj_iff h hu hTS v).mp hv.2
      · exact fun hv => ⟨hTS hv,(attached_vertex_adj_iff h hu hTS v).mpr hv⟩
    have ha := ThreeTreeOn.attach h u hu T hT hTS hc
    rw [← ha.induced_self,induced_edge_count_insert _ _ _ hu,
      inducedOn_attachment_of_not_mem _ _ _ _ hu,h.induced_self,ih,hn,hT,
      card_insert_of_notMem hu]
    have hs := h.active_card_ge_four
    omega

theorem clique_of_induced_edge_count_eq_choose {G : SimpleGraph V} {U : Finset V}
    (h : (edgeFamily (inducedOn G U)).card = U.card.choose 2) : G.IsClique U := by
  have he : edgeFamily (inducedOn G U) = U.powersetCard 2 := by
    apply eq_of_subset_of_card_le (edgeFamily_inducedOn_subset G U)
    simpa only [card_powersetCard] using h.ge
  intro u hu v hv huv
  change u ∈ U at hu
  change v ∈ U at hv
  have hp : ({u,v} : Finset V) ∈ U.powersetCard 2 :=
    mem_powersetCard.mpr ⟨by simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hu hv,
      card_pair huv⟩
  rw [← he] at hp
  exact ((pair_mem_edgeFamily _ huv).mp hp).1

/-- Every induced subgraph meeting the maximal partial-three-tree edge
count is itself a three-tree. The statement includes arbitrary vertex
subsets, not only initial segments of a chosen construction. -/
theorem ThreeTreeOn.induced_equality {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (U : Finset V) (hUS : U ⊆ S) (hU : 4 ≤ U.card)
    (he : (edgeFamily (inducedOn G U)).card = 3*U.card-6) :
    ThreeTreeOn U (inducedOn G U) := by
  induction h generalizing U with
  | tetrahedron C hC =>
    have hcard := card_le_card hUS
    have hU4 : U.card = 4 := by omega
    have hcl : (cliqueGraph C).IsClique U :=
      clique_of_induced_edge_count_eq_choose (G := cliqueGraph C) (U := U)
        (by norm_num [hU4,Nat.choose] at he ⊢; exact he)
    rw [inducedOn_clique hcl]
    exact ThreeTreeOn.tetrahedron U hU4
  | @attach S G h u hu T hT hTS hc ih =>
    by_cases hU4 : U.card = 4
    · have hcl : (G ⊔ attachmentStar u T).IsClique U :=
        clique_of_induced_edge_count_eq_choose (G := G ⊔ attachmentStar u T) (U := U)
          (by norm_num [hU4,Nat.choose] at he ⊢; exact he)
      rw [inducedOn_clique hcl]
      exact ThreeTreeOn.tetrahedron U hU4
    · by_cases huU : u ∈ U
      · let W := U.erase u
        have huW : u ∉ W := notMem_erase _ _
        have hWsub : W ⊆ S := by
          intro v hv
          exact (mem_insert.mp (hUS (mem_of_mem_erase hv))).resolve_left (ne_of_mem_erase hv)
        have hWcard : W.card = U.card-1 := card_erase_of_mem huU
        have hW4 : 4 ≤ W.card := by omega
        have hWU : insert u W = U := insert_erase huU
        have hbound := h.induced_edge_bound W hWsub (by omega)
        let N := earlierNeighbors (G ⊔ attachmentStar u T) W u
        have hNT : N ⊆ T := by
          intro v hv
          exact (attached_vertex_adj_iff h hu hTS v).mp
            ((mem_earlierNeighbors _ _ _ _).mp hv).2
        have hN3 : N.card ≤ 3 := by simpa only [hT] using card_le_card hNT
        have hsplit : (edgeFamily (inducedOn (G ⊔ attachmentStar u T) U)).card =
            (edgeFamily (inducedOn G W)).card + N.card := by
          rw [← hWU,induced_edge_count_insert _ _ _ huW,
            inducedOn_attachment_of_not_mem _ _ _ _ huW]
        have hEq : (edgeFamily (inducedOn G W)).card = 3*W.card-6 := by omega
        have hNcard : N.card = 3 := by omega
        have hNT' : N = T := eq_of_subset_of_card_le hNT (by omega)
        have hTW : T ⊆ W := by
          rw [← hNT']
          exact fun v hv => ((mem_earlierNeighbors _ _ _ _).mp hv).1
        have hold := ih W hWsub hW4 hEq
        have hnew := ThreeTreeOn.attach hold u huW T hT hTW
          (fun v hv w hw hvw => ⟨hc hv hw hvw,hTW hv,hTW hw⟩)
        have hgraph : inducedOn (G ⊔ attachmentStar u T) U =
            inducedOn G W ⊔ attachmentStar u T := by
          rw [← hWU,inducedOn_insert_eq_attach _ W T u huW hNT',
            inducedOn_attachment_of_not_mem _ _ _ _ huW]
        rw [hgraph,← hWU]
        exact hnew
      · have hsmall : U ⊆ S := by
          intro v hv
          exact (mem_insert.mp (hUS hv)).resolve_left (fun he => huU (he ▸ hv))
        rw [inducedOn_attachment_of_not_mem _ _ _ _ huU] at he ⊢
        exact ih U hsmall hU he

end GraphicalZonotopes
