module

public import Papers.GraphicalZonotopes.GraphComponentExtension
public import Papers.GraphicalZonotopes.ThreeTreeLink

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Delete vertices from the actual active graph. Ambient isolated vertices
outside `S` are not included in this graph's vertex type. -/
def activeDelete (G : SimpleGraph V) (S D : Finset V) :
    SimpleGraph {v : V // v∈S ∧ v∉D} := G.induce {v | v∈S ∧ v∉D}

def activeAttachEquiv {S : Finset V} {u : V} (hu : u∉S)
    (D : Finset V) (huD : u∉D) :
    Option {v : V // v∈S ∧ v∉D} ≃ {v : V // v∈insert u S ∧ v∉D} where
  toFun x := match x with
    | none => ⟨u,mem_insert_self _ _,huD⟩
    | some v => ⟨v.1,mem_insert_of_mem v.2.1,v.2.2⟩
  invFun v := if hv : v.1=u then none else
    some ⟨v.1,(mem_insert.mp v.2.1).resolve_left hv,v.2.2⟩
  left_inv := by
    intro x
    cases x with
    | none => simp
    | some v =>
      have hv : v.1≠u:=fun he => hu (he ▸ v.2.1)
      simp [hv]
  right_inv := by
    intro v
    by_cases hv : v.1=u
    · simp only [dif_pos hv]
      exact Subtype.ext hv.symm
    · simp only [dif_neg hv]

/-- The exact graph after a new vertex survives deletion: it is the old
deleted graph with one vertex attached to the surviving attachment clique. -/
def activeAttachIso {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    {u : V} (hu : u∉S) (A : Finset V) (hAS : A⊆S)
    (D : Finset V) (huD : u∉D) :
    VertexExtension.graph (activeDelete G S D) {v | v.1∈A} ≃g
      activeDelete (G⊔attachmentStar u A) (insert u S) D where
  toEquiv := activeAttachEquiv hu D huD
  map_rel_iff' := by
    intro x y
    cases x with
    | none =>
      cases y with
      | none =>
        change (G⊔attachmentStar u A).Adj u u ↔ False
        simp
      | some v =>
        change (G⊔attachmentStar u A).Adj u v.1 ↔ v.1∈A
        exact attached_vertex_adj_iff h hu hAS v.1
    | some v =>
      cases y with
      | none =>
        change (G⊔attachmentStar u A).Adj v.1 u ↔ v.1∈A
        rw [SimpleGraph.adj_comm]
        exact attached_vertex_adj_iff h hu hAS v.1
      | some w =>
        change (G⊔attachmentStar u A).Adj v.1 w.1 ↔ G.Adj v.1 w.1
        constructor
        · exact adj_before_attachment (fun he => hu (he ▸ v.2.1))
            (fun he => hu (he ▸ w.2.1))
        · exact Or.inl

def activeRemovedEquiv {S : Finset V} {u : V} (hu : u∉S)
    (D : Finset V) (huD : u∈D) :
    {v : V // v∈S ∧ v∉D.erase u} ≃ {v : V // v∈insert u S ∧ v∉D} where
  toFun v := ⟨v.1,mem_insert_of_mem v.2.1,by
    intro hvD
    exact v.2.2 (mem_erase.mpr ⟨fun he => hu (he ▸ v.2.1),hvD⟩)⟩
  invFun v := ⟨v.1,(mem_insert.mp v.2.1).resolve_left
    (fun he => v.2.2 (he.symm ▸ huD)),fun hv => v.2.2 (mem_of_mem_erase hv)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- If the newly attached vertex is deleted, no new edge survives. Removing
that vertex from the deletion set gives precisely the old induced graph. -/
def activeRemovedIso {S : Finset V} {G : SimpleGraph V} {u : V} (hu : u∉S)
    (A D : Finset V) (huD : u∈D) :
    activeDelete G S (D.erase u) ≃g
      activeDelete (G⊔attachmentStar u A) (insert u S) D where
  toEquiv := activeRemovedEquiv hu D huD
  map_rel_iff' := by
    intro v w
    change (G⊔attachmentStar u A).Adj v.1 w.1 ↔ G.Adj v.1 w.1
    exact ⟨adj_before_attachment (fun he => hu (he ▸ v.2.1))
      (fun he => hu (he ▸ w.2.1)),Or.inl⟩

theorem active_neighbors_nonempty {S A D : Finset V} (hAS : A⊆S)
    (hcard : D.card<A.card) :
    ({v : {v : V // v∈S ∧ v∉D} | v.1∈A} : Set _).Nonempty := by
  have hnot : ¬A⊆D:=fun h => Nat.not_lt_of_ge (card_le_card h) hcard
  obtain ⟨v,hvA,hvD⟩:=not_subset.mp hnot
  exact ⟨⟨v,hAS hvA,hvD⟩,hvA⟩

theorem active_neighbors_clique {G : SimpleGraph V} {S A D : Finset V}
    (hA : G.IsClique A) :
    (activeDelete G S D).IsClique {v | v.1∈A} := by
  intro v hv w hw hvw
  exact hA hv hw (fun he => hvw (Subtype.ext he))

theorem cliqueGraph_activeDelete_connected (C D : Finset V) (hcard : D.card<C.card) :
    (activeDelete (cliqueGraph C) C D).Connected := by
  have hn : ¬C⊆D:=fun hs => Nat.not_lt_of_ge (card_le_card hs) hcard
  obtain ⟨v,hvC,hvD⟩:=not_subset.mp hn
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨v,hvC,hvD⟩,?_⟩
  intro w
  by_cases he : v=w.1
  · have he' : (⟨v,hvC,hvD⟩ : {v : V // v∈C ∧ v∉D})=w:=Subtype.ext he
    rw [he']
  · exact SimpleGraph.Adj.reachable ⟨he,hvC,w.2.1⟩

/-- Deleting at most two vertices from a 3-tree leaves its active graph
connected. The deletion set is arbitrary; it need not lie inside `S`. -/
theorem ThreeTreeOn.delete_at_most_two_connected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (D : Finset V) (hD : D.card≤2) :
    (activeDelete G S D).Connected := by
  induction h generalizing D with
  | tetrahedron C hC =>
    exact cliqueGraph_activeDelete_connected C D (by omega)
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases huD : u∈D
    · exact (activeRemovedIso (G:=G) hu A D huD).connected_iff.mp
        (ih (D.erase u) ((card_erase_le (s:=D) (a:=u)).trans hD))
    · exact (activeAttachIso h hu A hAS D huD).connected_iff.mp
        (VertexExtension.connected _ _ (ih D hD)
          (active_neighbors_nonempty hAS (by omega)))

theorem activeDelete_univ_components (G : SimpleGraph V) (D : Finset V) :
    Nat.card (activeDelete G univ D).ConnectedComponent=
      Nat.card (G.induce ((D : Set V)ᶜ)).ConnectedComponent := by
  let e : {v : V // v∈(univ : Finset V) ∧ v∉D} ≃ {v : V // v∉D} :=
    { toFun := fun v => ⟨v.1,v.2.2⟩
      invFun := fun v => ⟨v.1,mem_univ _,v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let iso : activeDelete G univ D ≃g G.induce ((D : Set V)ᶜ) :=
    { toEquiv := e
      map_rel_iff' := by intro v w; rfl }
  exact Nat.card_congr iso.connectedComponentEquiv

end GraphicalZonotopes
