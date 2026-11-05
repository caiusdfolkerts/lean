module

public import Papers.GraphicalZonotopes.TriangularBooleanExtension
public import Papers.GraphicalZonotopes.GraphComponentExtension

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace SingleVertexGraph
open Finset BooleanModule BooleanVertexExtension
variable {V : Type*} [Fintype V] [DecidableEq V]

def old : V ↪ Vertex V := ⟨Sum.inl,Sum.inl_injective⟩

def graph (G : SimpleGraph V) (N : Finset V) : SimpleGraph (Vertex V) where
  Adj x y := match x,y with
    | Sum.inl u,Sum.inl v => G.Adj u v
    | Sum.inl u,Sum.inr _ => u ∈ N
    | Sum.inr _,Sum.inl v => v ∈ N
    | Sum.inr _,Sum.inr _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro x hx
    cases x with
    | inl v => exact G.irrefl hx
    | inr j => exact hx⟩

@[simp] theorem graph_old_adj (G : SimpleGraph V) (N : Finset V) (u v : V) :
    (graph G N).Adj (Sum.inl u) (Sum.inl v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem graph_new_adj (G : SimpleGraph V) (N : Finset V) (u : V) :
    (graph G N).Adj (Sum.inr 0) (Sum.inl u) ↔ u ∈ N := Iff.rfl

@[simp] theorem graph_adj_new (G : SimpleGraph V) (N : Finset V) (u : V) :
    (graph G N).Adj (Sum.inl u) (Sum.inr 0) ↔ u ∈ N := Iff.rfl

theorem old_le (G : SimpleGraph V) (N : Finset V) : G.map old ≤ graph G N := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj old G x y).mp hxy
  exact huv

theorem old_comap (G : SimpleGraph V) (N : Finset V) : (graph G N).comap old = G := rfl

theorem connected {G : SimpleGraph V} (hG : G.Connected) {N : Finset V}
    (hN : N.Nonempty) : (graph G N).Connected := by
  obtain ⟨v,hv⟩ := hN
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inr 0,?_⟩
  intro x
  cases x with
  | inl u =>
    exact (SimpleGraph.Adj.reachable (show (graph G N).Adj (Sum.inr 0) (Sum.inl v) from hv)).trans
      ((hG v u).map ⟨Sum.inl,fun h => h⟩)
  | inr j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact SimpleGraph.Reachable.rfl

theorem card_hubs_of_new_not_mem {C : Finset (Vertex V)} (hC : Sum.inr 0 ∉ C) :
    (hubs C).card = C.card := by
  have he : hubSet (J := Fin 1) (hubs C) = C := by
    ext x
    cases x with
    | inl u => simp
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [hC]
  have hc := congrArg Finset.card he
  simpa only [hubSet,card_map] using hc

theorem card_hubs_of_new_mem {C : Finset (Vertex V)} (hC : Sum.inr 0 ∈ C) :
    (hubs C).card + 1 = C.card := by
  have he : insert (Sum.inr 0) (hubSet (J := Fin 1) (hubs C)) = C := by
    ext x
    cases x with
    | inl u => simp
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [hC]
  have hc := congrArg Finset.card he
  rw [card_insert_of_notMem (notMem_hubSet_outer _ (0 : Fin 1)),hubSet,card_map] at hc
  exact hc

theorem cliqueFree_five {G : SimpleGraph V} (hG : G.CliqueFree 5)
    {N : Finset V} (hN : N.card ≤ 3) : (graph G N).CliqueFree 5 := by
  intro C hC
  obtain ⟨hcl,hcard⟩ := hC
  have hc : G.IsClique (hubs C) := by
    intro u hu v hv huv
    exact hcl ((mem_hubs _ _).mp hu) ((mem_hubs _ _).mp hv) (fun he => huv (Sum.inl_injective he))
  by_cases hw : Sum.inr 0 ∈ C
  · have hs : hubs C ⊆ N := by
      intro u hu
      exact hcl hw ((mem_hubs _ _).mp hu) (by simp)
    have hsz := card_le_card hs
    have hcard' := card_hubs_of_new_mem hw
    omega
  · exact hG _ ⟨hc,(card_hubs_of_new_not_mem hw).trans hcard⟩

def newEdges (N : Finset V) : Finset (Finset (Vertex V)) :=
  N.image (fun v => {Sum.inl v,Sum.inr 0})

theorem newEdge_injective : Function.Injective
    (fun v : V => ({Sum.inl v,Sum.inr 0} : Finset (Vertex V))) := by
  intro u v he
  change ({Sum.inl u,Sum.inr 0} : Finset (Vertex V)) = {Sum.inl v,Sum.inr 0} at he
  have h : Sum.inl u ∈ ({Sum.inl v,Sum.inr 0} : Finset (Vertex V)) := by
    rw [← he]
    simp
  simpa only [mem_insert,mem_singleton,Sum.inl.injEq,Sum.inl_ne_inr,or_false] using h

theorem edgeFamily_eq (G : SimpleGraph V) (N : Finset V) :
    edgeFamily (graph G N) =
      (edgeFamily G).image (fun C => C.map old) ∪ newEdges N := by
  ext C
  constructor
  · intro hC
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ C).mp hC
    obtain ⟨x,y,hxy,rfl⟩ := card_eq_two.mp hc
    have hxyG := hcl x (by simp) y (by simp) hxy
    cases x with
    | inl u =>
      cases y with
      | inl v =>
        apply mem_union_left
        refine mem_image.mpr ⟨{u,v},?_,?_⟩
        · exact (pair_mem_edgeFamily G (fun he => hxy (congrArg Sum.inl he))).mpr hxyG
        · simp [old]
      | inr j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        exact mem_union_right _ (mem_image.mpr ⟨u,hxyG,rfl⟩)
    | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      cases y with
      | inl v =>
        exact mem_union_right _ (mem_image.mpr ⟨v,hxyG,pair_comm _ _⟩)
      | inr j => exact False.elim hxyG
  · intro hC
    rcases mem_union.mp hC with hC | hC
    · obtain ⟨D,hD,rfl⟩ := mem_image.mp hC
      obtain ⟨hd,hcl⟩ := (mem_edgeFamily G D).mp hD
      refine (mem_edgeFamily _ _).mpr ⟨by simpa only [card_map] using hd,?_⟩
      intro x hx y hy hxy
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
      exact hcl u hu v hv (fun he => hxy (congrArg old he))
    · obtain ⟨u,hu,rfl⟩ := mem_image.mp hC
      exact (pair_mem_edgeFamily _ (by simp)).mpr hu

theorem edgeFamily_card (G : SimpleGraph V) (N : Finset V) :
    (edgeFamily (graph G N)).card = (edgeFamily G).card + N.card := by
  rw [edgeFamily_eq,card_union_of_disjoint]
  · rw [card_image_of_injective _ (Finset.map_injective old)]
    unfold newEdges
    exact congrArg (_ + ·) (card_image_of_injective N newEdge_injective)
  · apply disjoint_left.mpr
    intro C hC hN
    obtain ⟨D,hD,rfl⟩ := mem_image.mp hC
    obtain ⟨u,hu,he⟩ := mem_image.mp hN
    have hw : Sum.inr 0 ∈ D.map old := by rw [← he]; simp
    obtain ⟨v,hv,hvw⟩ := mem_map.mp hw
    exact Sum.inl_ne_inr hvw

end SingleVertexGraph
end GraphicalZonotopes
