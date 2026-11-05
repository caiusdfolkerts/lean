module

public import Papers.GraphicalZonotopes.TetrahedralGrowth
public import Papers.GraphicalZonotopes.ThreeTreeCliques

@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A partial 3-tree is a subgraph of a 3-tree on the same vertices. Every
graph on at most three vertices is included, as in the paper's convention. -/
def IsPartialThreeTree (G : SimpleGraph V) : Prop :=
  Fintype.card V ≤ 3 ∨ ∃ H : SimpleGraph V,IsThreeTree H ∧ G ≤ H

theorem edgeFamily_mono {G H : SimpleGraph V} (h : G ≤ H) :
    edgeFamily G ⊆ edgeFamily H := by
  intro C hC
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily G C).mp hC
  exact (mem_edgeFamily H C).mpr ⟨hc,fun u hu v hv huv => h (hcl u hu v hv huv)⟩

theorem graph_eq_of_edgeFamily_eq {G H : SimpleGraph V}
    (h : edgeFamily G = edgeFamily H) : G = H := by
  ext u v
  by_cases huv : u = v
  · subst v
    simp
  · rw [← pair_mem_edgeFamily G huv,← pair_mem_edgeFamily H huv,h]

theorem graph_eq_of_le_card_edges {G H : SimpleGraph V} (h : G ≤ H)
    (hc : (edgeFamily H).card ≤ (edgeFamily G).card) : G = H :=
  graph_eq_of_edgeFamily_eq (eq_of_subset_of_card_le (edgeFamily_mono h) hc)

theorem inducedOn_mono {G H : SimpleGraph V} (h : G ≤ H) (U : Finset V) :
    inducedOn G U ≤ inducedOn H U := by
  intro u v huv
  exact ⟨h huv.1,huv.2⟩

theorem inducedOn_le (G : SimpleGraph V) (U : Finset V) : inducedOn G U ≤ G :=
  fun _ _ h => h.1

theorem edgeFamily_inducedOn_subset (G : SimpleGraph V) (U : Finset V) :
    edgeFamily (inducedOn G U) ⊆ U.powersetCard 2 := by
  intro C hC
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ C).mp hC
  apply mem_powersetCard.mpr
  refine ⟨?_,hc⟩
  intro u hu
  obtain ⟨v,hv,hvu⟩ := exists_mem_ne (by omega : 1 < C.card) u
  exact (hcl u hu v hv (Ne.symm hvu)).2.1

theorem induced_edge_count_le_choose (G : SimpleGraph V) (U : Finset V) :
    (edgeFamily (inducedOn G U)).card ≤ U.card.choose 2 := by
  simpa only [card_powersetCard] using card_le_card (edgeFamily_inducedOn_subset G U)

theorem inducedOn_attachment_of_not_mem (G : SimpleGraph V) (u : V)
    (T U : Finset V) (hu : u ∉ U) :
    inducedOn (G ⊔ attachmentStar u T) U = inducedOn G U := by
  ext v w
  constructor
  · rintro ⟨h,hv,hw⟩
    rcases h with h | h
    · exact ⟨h,hv,hw⟩
    · rcases h.2 with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> contradiction
  · rintro ⟨h,hv,hw⟩
    exact ⟨Or.inl h,hv,hw⟩

/-- Every induced subgraph of a 3-tree satisfies the sharp partial-3-tree
edge bound. The proof includes arbitrary subsets, not merely construction
prefixes, which is essential for the support classification. -/
theorem ThreeTreeOn.induced_edge_bound {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (U : Finset V) (hUS : U ⊆ S) (hU : 3 ≤ U.card) :
    (edgeFamily (inducedOn G U)).card ≤ 3*U.card-6 := by
  classical
  induction h generalizing U with
  | tetrahedron C hC =>
    have hcard := card_le_card hUS
    have hb := induced_edge_count_le_choose (cliqueGraph C) U
    have hu : U.card = 3 ∨ U.card = 4 := by omega
    rcases hu with hu | hu <;> rw [hu] at hb ⊢ <;> norm_num at hb ⊢ <;> exact hb
  | @attach S G h u hu T hT hTS hcl ih =>
    by_cases hc : U.card = 3
    · have hb := induced_edge_count_le_choose (G ⊔ attachmentStar u T) U
      rw [hc] at hb ⊢
      norm_num at hb ⊢
      exact hb
    · by_cases huU : u ∈ U
      · have heU : U = insert u (U.erase u) := (insert_erase huU).symm
        have hsmall : U.erase u ⊆ S := by
          intro v hv
          exact (mem_insert.mp (hUS (mem_of_mem_erase hv))).resolve_left (ne_of_mem_erase hv)
        have hcard : (U.erase u).card = U.card-1 := card_erase_of_mem huU
        have hprev := ih (U.erase u) hsmall (by omega)
        have hsub : earlierNeighbors (G ⊔ attachmentStar u T) (U.erase u) u ⊆ T := by
          intro v hv
          exact (attached_vertex_adj_iff h hu hTS v).mp
            ((mem_earlierNeighbors _ _ _ _).mp hv).2
        have hnb := card_le_card hsub
        rw [hT] at hnb
        rw [heU,induced_edge_count_insert _ _ _ (notMem_erase _ _)]
        rw [inducedOn_attachment_of_not_mem _ _ _ _ (notMem_erase _ _)]
        have hIns : (insert u (U.erase u)).card = U.card := by rw [insert_erase huU]
        omega
      · have hsmall : U ⊆ S := by
          intro v hv
          exact (mem_insert.mp (hUS hv)).resolve_left (fun he => huU (he ▸ hv))
        rw [inducedOn_attachment_of_not_mem _ _ _ _ huU]
        exact ih U hsmall hU

theorem IsPartialThreeTree.induced_edge_bound {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (U : Finset V) (hU : 3 ≤ U.card) :
    (edgeFamily (inducedOn G U)).card ≤ 3*U.card-6 := by
  rcases hG with hsmall | ⟨H,hH,hGH⟩
  · have hc : U.card = 3 := by
      have hcard := card_le_card (subset_univ U)
      simp only [card_univ] at hcard
      omega
    have hb := induced_edge_count_le_choose G U
    rw [hc] at hb ⊢
    norm_num at hb ⊢
    exact hb
  · exact (card_le_card (edgeFamily_mono (inducedOn_mono hGH U))).trans
      (hH.induced_edge_bound U (subset_univ _) hU)

theorem IsPartialThreeTree.cliqueFree_five {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) : G.CliqueFree 5 := by
  intro C hC
  rcases hG with hsmall | ⟨H,hH,hGH⟩
  · have hc := card_le_card (subset_univ C)
    rw [hC.card_eq,card_univ] at hc
    omega
  · exact hH.cliqueFree_five C ⟨fun u hu v hv huv => hGH (hC.isClique hu hv huv),hC.card_eq⟩

/-- A triangle-connected tetrahedral family in a partial 3-tree has no
extra ambient edges on its vertices and is itself an induced 3-tree. -/
theorem IsPartialThreeTree.connected_family_threeTree {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (F : Finset (Finset V)) (hne : F.Nonempty)
    (hcl : ∀ C ∈ F,C.card = 4 ∧ G.IsClique C)
    (hconn : (tetrahedronGraph F).Preconnected) :
    ThreeTreeOn (F.biUnion id) (inducedOn G (F.biUnion id)) := by
  have hg := tetrahedralGrowth_of_connected_family G F hne hcl hconn
  have hu := hg.card_ge_four
  obtain ⟨hl,he⟩ := hg.edge_bound_and_equality
  apply he
  exact le_antisymm (hG.induced_edge_bound _ (by omega)) hl

end GraphicalZonotopes
