module

public import Papers.GraphicalZonotopes.GraphModels

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem ThreeTreeOn.edges_supported {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u v : V} (huv : G.Adj u v) : u∈S ∧ v∈S := by
  induction h generalizing u v with
  | tetrahedron C hC => exact ⟨huv.2.1,huv.2.2⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    rcases huv with huv | huv
    · have hv:=ih (u:=u) (v:=v) huv
      exact ⟨mem_insert_of_mem hv.1,mem_insert_of_mem hv.2⟩
    · rcases huv.2 with ⟨rfl,hv⟩ | ⟨rfl,hu⟩
      · exact ⟨mem_insert_self _ _,mem_insert_of_mem (hTS hv)⟩
      · exact ⟨mem_insert_of_mem (hTS hu),mem_insert_self _ _⟩

theorem ThreeTreeOn.active_card_ge_four {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : 4≤S.card := by
  induction h with
  | tetrahedron C hC => omega
  | attach h u hu T hT hTS hcl ih =>
    rw [card_insert_of_notMem hu]
    omega

theorem ThreeTreeOn.clique_subset_active {S C : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hcard : 2≤C.card) (hC : G.IsClique C) : C⊆S := by
  intro u hu
  obtain ⟨v,hv,hvu⟩ := exists_mem_ne (by omega : 1<C.card) u
  exact (h.edges_supported (hC hu hv (Ne.symm hvu))).1

theorem clique_before_attachment {G : SimpleGraph V} {u : V} {T C : Finset V}
    (hu : u∉C) (hC : (G⊔attachmentStar u T).IsClique C) : G.IsClique C := by
  intro v hv w hw hvw
  rcases hC hv hw hvw with h | h
  · exact h
  · rcases h.2 with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> contradiction

theorem attached_vertex_adj_iff {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V} (hTS : T⊆S)
    (v : V) : (G⊔attachmentStar u T).Adj u v ↔ v∈T := by
  constructor
  · intro hadj
    rcases hadj with hadj | hadj
    · exact False.elim (hu (h.edges_supported hadj).1)
    · rcases hadj.2 with ⟨_,hv⟩ | ⟨he,huT⟩
      · exact hv
      · exact False.elim (hu (hTS huT))
  · intro hv
    refine Or.inr ⟨?_,Or.inl ⟨rfl,hv⟩⟩
    intro he
    subst v
    exact hu (hTS hv)

theorem attached_tetrahedron_clique {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V} (hTS : T⊆S)
    (hT : G.IsClique T) : (G⊔attachmentStar u T).IsClique (insert u T : Finset V) := by
  intro v hv w hw hvw
  change v ∈ (insert u T : Finset V) at hv
  change w ∈ (insert u T : Finset V) at hw
  rcases mem_insert.mp hv with hvu | hv
  · subst v
    have hwT : w∈T := (mem_insert.mp hw).resolve_left (Ne.symm hvw)
    exact (attached_vertex_adj_iff h hu hTS w).mpr hwT
  · rcases mem_insert.mp hw with hwu | hw
    · subst w
      exact (G⊔attachmentStar u T).adj_symm
        ((attached_vertex_adj_iff h hu hTS v).mpr hv)
    · exact Or.inl (hT hv hw hvw)

theorem ThreeTreeOn.clique_card_le_four {S C : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hC : G.IsClique C) : C.card≤4 := by
  induction h generalizing C with
  | tetrahedron S hS =>
    by_cases hc : 2≤C.card
    · have hsub := (ThreeTreeOn.tetrahedron S hS).clique_subset_active hc hC
      simpa only [hS] using card_le_card hsub
    · omega
  | @attach S G h u hu T hT hTS hcl ih =>
    by_cases huC : u∈C
    · have herase : C.erase u⊆T := by
        intro v hv
        exact (attached_vertex_adj_iff h hu hTS v).mp
          (hC huC (mem_of_mem_erase hv) (Ne.symm (ne_of_mem_erase hv)))
      have hcard := card_le_card herase
      rw [card_erase_of_mem huC,hT] at hcard
      omega
    · exact ih (C:=C) (clique_before_attachment huC hC)

theorem ThreeTreeOn.cliqueFree_five {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : G.CliqueFree 5 := by
  intro C hc
  have hb:=h.clique_card_le_four hc.isClique
  rw [hc.card_eq] at hb
  omega

theorem tetrahedra_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V}
    (hT : T.card=3) (hTS : T⊆S) (hcl : G.IsClique T) :
    tetrahedra (G⊔attachmentStar u T)=insert (insert u T) (tetrahedra G) := by
  classical
  have huT : u∉T := fun huT => hu (hTS huT)
  ext C
  simp only [tetrahedra,mem_filter,mem_univ,true_and,mem_insert]
  constructor
  · rintro ⟨hC,hclC⟩
    by_cases huC : u∈C
    · left
      have herase : C.erase u⊆T := by
        intro v hv
        exact (attached_vertex_adj_iff h hu hTS v).mp
          (hclC huC (mem_of_mem_erase hv) (Ne.symm (ne_of_mem_erase hv)))
      have he : C.erase u=T := eq_of_subset_of_card_le herase (by
        rw [card_erase_of_mem huC,hC,hT])
      rw [← he,insert_erase huC]
    · right
      exact ⟨hC,clique_before_attachment huC hclC⟩
  · rintro (rfl | ⟨hC,hclC⟩)
    · exact ⟨by rw [card_insert_of_notMem huT,hT],attached_tetrahedron_clique h hu hTS hcl⟩
    · exact ⟨hC,fun v hv w hw hvw => Or.inl (hclC hv hw hvw)⟩

theorem attached_tetrahedron_not_old {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {T : Finset V} :
    insert u T∉tetrahedra G := by
  classical
  intro hm
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hm).2
  have hs:=h.clique_subset_active (by omega) hcl
  exact hu (hs (mem_insert_self _ _))

theorem tetrahedra_cliqueGraph {C : Finset V} (hC : C.card=4) :
    tetrahedra (cliqueGraph C)={C} := by
  classical
  ext D
  simp only [tetrahedra,mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · rintro ⟨hD,hcl⟩
    exact eq_of_subset_of_card_le
      ((ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcl) (by omega)
  · rintro rfl
    exact ⟨hC,fun u hu v hv huv => ⟨huv,hu,hv⟩⟩

/-- Every 3-tree on its full active vertex set has exactly |S|-3 actual
tetrahedra. The assertion concerns all cliques, independently of a selected
construction sequence. -/
theorem ThreeTreeOn.tetrahedra_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (tetrahedra G).card=S.card-3 := by
  induction h with
  | tetrahedron C hC => rw [tetrahedra_cliqueGraph hC,card_singleton,hC]
  | @attach S G h u hu T hT hTS hcl ih =>
    rw [tetrahedra_after_attachment h hu hT hTS hcl,
      card_insert_of_notMem (attached_tetrahedron_not_old h hu),ih,
      card_insert_of_notMem hu]
    have hs:=h.active_card_ge_four
    omega

theorem ThreeTreeOn.tetrahedra_cover {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (tetrahedra G).biUnion id=S := by
  classical
  induction h with
  | tetrahedron C hC => simp [tetrahedra_cliqueGraph hC]
  | @attach S G h u hu T hT hTS hcl ih =>
    rw [tetrahedra_after_attachment h hu hT hTS hcl,biUnion_insert,ih]
    change insert u T∪S=insert u S
    rw [insert_union,union_eq_right.mpr hTS]

end GraphicalZonotopes
