module

public import Papers.GraphicalZonotopes.ActiveDeletion

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangleMultiplicity_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {A : Finset V}
    (hA : A.card=3) (hAS : A⊆S) (hcA : G.IsClique A) (T : Finset V) :
    triangleMultiplicity (G⊔attachmentStar u A) T=
      triangleMultiplicity G T+if T⊆insert u A then 1 else 0 := by
  classical
  simp only [triangleMultiplicity,tetrahedra_after_attachment h hu hA hAS hcA,
    filter_insert]
  split_ifs with ht
  · rw [card_insert_of_notMem (by
      intro hm
      exact attached_tetrahedron_not_old h hu (mem_filter.mp hm).1)]
  · simp

theorem ThreeTreeOn.triangleMultiplicity_eq_zero_of_outside
    {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    {u : V} (hu : u∉S) {T : Finset V} (huT : u∈T) :
    triangleMultiplicity G T=0 := by
  classical
  unfold triangleMultiplicity
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro C hC hTC
  obtain ⟨hc,hcl⟩:=(mem_filter.mp hC).2
  exact hu (h.clique_subset_active (by omega) hcl (hTC huT))

/-- The exact separator dictionary for every triangle of a 3-tree, proved
on the actual active vertex type. Thus unused ambient vertices cannot create
spurious components in the induction. -/
theorem ThreeTreeOn.triangle_components_eq_multiplicity
    {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (T : Finset V) (hT : T.card=3) (hcT : G.IsClique T) :
    Nat.card (activeDelete G S T).ConnectedComponent=triangleMultiplicity G T := by
  classical
  induction h generalizing T with
  | tetrahedron C hC =>
    have hTC:=(ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT
    rw [VertexExtension.connected_component_card_one
      (cliqueGraph_activeDelete_connected C T (by omega))]
    simp only [triangleMultiplicity,tetrahedra_cliqueGraph hC]
    rw [Finset.filter_singleton]
    simp only [if_pos hTC, Finset.card_singleton]
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huT : u∈T
    · have hTsub : T⊆insert u A := by
        intro v hv
        by_cases he : v=u
        · exact mem_insert.mpr (Or.inl he)
        · exact mem_insert.mpr (Or.inr
            ((attached_vertex_adj_iff h hu hAS v).mp (hcT huT hv (Ne.symm he))))
      have hconn : (activeDelete (G⊔attachmentStar u A) (insert u S) T).Connected :=
        (activeRemovedIso (G:=G) hu A T huT).connected_iff.mp
          (h.delete_at_most_two_connected (T.erase u) (by
            rw [card_erase_of_mem huT,hT]))
      rw [VertexExtension.connected_component_card_one hconn,
        triangleMultiplicity_after_attachment h hu hA hAS hcA,
        h.triangleMultiplicity_eq_zero_of_outside hu huT,if_pos hTsub]
    · have hcOld : G.IsClique T:=clique_before_attachment huT hcT
      have hnewcard := Nat.card_congr
        (activeAttachIso h hu A hAS T huT).connectedComponentEquiv
      rw [← hnewcard,triangleMultiplicity_after_attachment h hu hA hAS hcA]
      by_cases hTA : T=A
      · subst T
        have hN : ({v : {v : V // v∈S ∧ v∉A} | v.1∈A} : Set _)=∅ := by
          ext v
          exact ⟨fun hv => v.2.2 hv,False.elim⟩
        rw [hN,VertexExtension.isolated_component_card,
          ih A hA hcA,if_pos (subset_insert _ _)]
      · have hnot : ¬A⊆T := by
          intro hAT
          exact hTA (eq_of_subset_of_card_le hAT (by omega)).symm
        obtain ⟨v,hvA,hvT⟩:=not_subset.mp hnot
        have hN : ({v : {v : V // v∈S ∧ v∉T} | v.1∈A} : Set _).Nonempty :=
          ⟨⟨v,hAS hvA,hvT⟩,hvA⟩
        have hnotSub : ¬T⊆insert u A := by
          intro ht
          have htA : T⊆A := by
            intro w hw
            exact (mem_insert.mp (ht hw)).resolve_left (fun he => huT (he ▸ hw))
          exact hTA (eq_of_subset_of_card_le htA (by omega))
        rw [VertexExtension.component_card _ _ hN (active_neighbors_clique hcA),
          ih T hT hcOld,if_neg hnotSub,Nat.add_zero]

/-- Literal vertex deletion on a full 3-tree has exactly one component per
maximal tetrahedron containing the deleted triangle. -/
theorem IsThreeTree.triangle_components_eq_multiplicity {G : SimpleGraph V}
    (hG : IsThreeTree G) (T : Finset V) (hT : T.card=3) (hcT : G.IsClique T) :
    Nat.card (G.induce ((T : Set V)ᶜ)).ConnectedComponent=triangleMultiplicity G T := by
  rw [← activeDelete_univ_components]
  exact ThreeTreeOn.triangle_components_eq_multiplicity hG T hT hcT

theorem IsThreeTree.admissible_iff_triangle_deletion {G : SimpleGraph V}
    (hG : IsThreeTree G) :
    Admissible G ↔ ∀ T : Finset V,T.card=3 → G.IsClique T →
      Nat.card (G.induce ((T : Set V)ᶜ)).ConnectedComponent≤3 := by
  constructor
  · intro h T ht hc
    rw [hG.triangle_components_eq_multiplicity T ht hc]
    exact h T ht hc
  · intro h T ht hc
    rw [← hG.triangle_components_eq_multiplicity T ht hc]
    exact h T ht hc

end GraphicalZonotopes
