module

public import Papers.GraphicalZonotopes.SingleVertexGraph
public import Papers.GraphicalZonotopes.TetrahedralGrowth
public import Papers.GraphicalZonotopes.EdgeCoordinates
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The literal join of a graph with a two-vertex clique. The two new
vertices are added successively, each adjacent to every previous vertex.
No tree or degree condition is incorporated into the graph definition. -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Vertex (V : Type*) := (V ⊕ Fin 1) ⊕ Fin 1

def graph (T : SimpleGraph V) : SimpleGraph (Vertex V) :=
  SingleVertexGraph.graph (SingleVertexGraph.graph T univ) univ

def old : V ↪ Vertex V := ⟨fun v => Sum.inl (Sum.inl v),by
  intro u v h
  exact Sum.inl_injective (Sum.inl_injective h)⟩

def a : Vertex V := Sum.inr 0
def b : Vertex V := Sum.inl (Sum.inr 0)

def core (S : Finset V) : Finset (Vertex V) := insert a (insert b (S.map old))

def outer (C : Finset (Vertex V)) : Finset V := univ.filter (fun v => old v ∈ C)

@[simp] theorem mem_outer (C : Finset (Vertex V)) (v : V) :
    v ∈ outer C ↔ old v ∈ C := by simp [outer]

@[simp] theorem a_mem_core (S : Finset V) : a ∈ core S := by simp [core]
@[simp] theorem b_mem_core (S : Finset V) : b ∈ core S := by simp [core]
@[simp] theorem old_mem_core (S : Finset V) (v : V) : old v ∈ core S ↔ v ∈ S := by
  simp [core,old,a,b]

@[simp] theorem core_card (S : Finset V) : (core S).card = S.card+2 := by
  simp [core,a,b,old]

theorem core_mono {S U : Finset V} (h : S ⊆ U) : core S ⊆ core U :=
  insert_subset_insert _ (insert_subset_insert _ (map_subset_map.mpr h))

theorem vertex_cases (x : Vertex V) : x=a ∨ x=b ∨ ∃ v,x=old v := by
  rcases x with (v|i)|j
  · exact Or.inr (Or.inr ⟨v,rfl⟩)
  · have hi : i=0 := Subsingleton.elim _ _
    subst i
    exact Or.inr (Or.inl rfl)
  · have hj : j=0 := Subsingleton.elim _ _
    subst j
    exact Or.inl rfl

@[simp] theorem core_univ : core (univ : Finset V)=univ := by
  apply eq_univ_iff_forall.mpr
  intro x
  rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩ <;> simp

theorem core_outer {C : Finset (Vertex V)} (ha : a∈C) (hb : b∈C) : core (outer C)=C := by
  ext x
  rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩ <;> simp [ha,hb]

@[simp] theorem graph_old_adj (T : SimpleGraph V) (u v : V) :
    (graph T).Adj (old u) (old v) ↔ T.Adj u v := Iff.rfl

theorem core_clique_iff (T : SimpleGraph V) (S : Finset V) :
    (graph T).IsClique (core S) ↔ T.IsClique S := by
  constructor
  · intro h u hu v hv huv
    exact h ((old_mem_core S u).mpr hu) ((old_mem_core S v).mpr hv)
      (fun he => huv (old.injective he))
  · intro h x hx y hy hxy
    rcases vertex_cases x with rfl|rfl|⟨u,rfl⟩ <;>
      rcases vertex_cases y with rfl|rfl|⟨v,rfl⟩
    all_goals try { simp [a,b,graph,SingleVertexGraph.graph,old] at hxy ⊢ }
    exact h ((old_mem_core S u).mp hx) ((old_mem_core S v).mp hy)
      (fun he => hxy (congrArg old he))

theorem edgeFamily_card (T : SimpleGraph V) :
    (edgeFamily (graph T)).card=(edgeFamily T).card+2*Fintype.card V+1 := by
  rw [graph,SingleVertexGraph.edgeFamily_card,SingleVertexGraph.edgeFamily_card]
  simp only [card_univ,Fintype.card_sum,Fintype.card_fin]
  omega

theorem tree_edgeFamily_card {T : SimpleGraph V} (hT : T.IsTree) :
    (edgeFamily T).card+1=Fintype.card V := by
  rw [edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]
  exact hT.card_edgeFinset

/-- Every connected graph with at least two vertices admits a tetrahedral
growth after adjoining the two universal adjacent vertices. -/
theorem connected_growth {T : SimpleGraph V} (hT : T.Connected)
    (hn : 2 ≤ Fintype.card V) : TetrahedralGrowth (graph T) univ := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨u⟩ := hT.nonempty
  obtain ⟨v,huv⟩ := hT.preconnected.exists_adj_of_nontrivial u
  let C := core ({u,v} : Finset V)
  have hCcard : C.card=4 := by simp [C,core_card,T.ne_of_adj huv]
  have hCcl : (graph T).IsClique C := (core_clique_iff T _).mpr
    (by simpa only [coe_pair,SimpleGraph.isClique_pair] using (fun _ : u≠v => huv))
  let candidates : Finset (Finset (Vertex V)) := univ.filter
    (fun U => C⊆U ∧ TetrahedralGrowth (graph T) U)
  have hbase : C∈candidates := mem_filter.mpr
    ⟨mem_univ _,Subset.rfl,TetrahedralGrowth.base C hCcard hCcl⟩
  obtain ⟨U,hU,hmax⟩ := candidates.exists_max_image Finset.card ⟨C,hbase⟩
  obtain ⟨hCU,hgrowth⟩ := (mem_filter.mp hU).2
  have ha : a∈U := hCU (a_mem_core _)
  have hb : b∈U := hCU (b_mem_core _)
  have hclosed : ∀ x y : V,old x∈U → T.Adj x y → old y∈U := by
    intro x y hx hxy
    let D := core ({x,y} : Finset V)
    have hDcard : D.card=4 := by simp [D,core_card,T.ne_of_adj hxy]
    have hDcl : (graph T).IsClique D := (core_clique_iff T _).mpr
      (by simpa only [coe_pair,SimpleGraph.isClique_pair] using (fun _ : x≠y => hxy))
    have hsub : core ({x} : Finset V)⊆D∩U := by
      intro z hz
      refine mem_inter.mpr ⟨core_mono (by simp) hz,?_⟩
      rcases vertex_cases z with rfl|rfl|⟨w,rfl⟩
      · exact ha
      · exact hb
      · have he : w=x := by simpa using (old_mem_core _ _).mp hz
        simpa only [he] using hx
    have hover : 3≤(D∩U).card := by
      simpa only [core_card,card_singleton] using card_le_card hsub
    have hg := hgrowth.extend_fourClique D hDcard hDcl hover
    have hcand : U∪D∈candidates := mem_filter.mpr
      ⟨mem_univ _,hCU.trans subset_union_left,hg⟩
    have he : U∪D=U := (eq_of_subset_of_card_le subset_union_left (hmax _ hcand)).symm
    rw [←he]
    exact mem_union_right U ((old_mem_core _ y).mpr (by simp))
  have hu : old u∈U := hCU ((old_mem_core _ u).mpr (by simp))
  have hall : ∀ w : V,old w∈U := by
    intro w
    have hp := (SimpleGraph.reachable_iff_reflTransGen (G := T) u w).mp (hT u w)
    induction hp with
    | refl => exact hu
    | @tail x y hp hxy ih => exact hclosed x y ih hxy
  have hUeq : U=univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    rcases vertex_cases x with rfl|rfl|⟨w,rfl⟩
    · exact ha
    · exact hb
    · exact hall w
  simpa only [hUeq] using hgrowth

/-- The join of a tree having at least two vertices with K₂ is a genuine
3-tree, by tetrahedral growth and the exact edge count. -/
theorem isThreeTree {T : SimpleGraph V} (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card V) : IsThreeTree (graph T) := by
  have hg := connected_growth hT.connected hn
  have hc := hg.edge_bound_and_equality.2
  simp only [inducedOn_univ,card_univ] at hc
  apply hc
  rw [edgeFamily_card]
  have ht := tree_edgeFamily_card hT
  simp only [Vertex,Fintype.card_sum,Fintype.card_fin]
  omega

/-- A finite nonempty forest with n−1 edges is connected. The proof extends
it to an actual spanning tree and uses equality of finite edge sets. -/
theorem forest_isTree_of_card {T : SimpleGraph V} [Nonempty V]
    (hT : T.IsAcyclic) (hc : T.edgeFinset.card+1=Fintype.card V) : T.IsTree := by
  obtain ⟨H,hTH,hHtop,hH⟩ :=
    (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
      (show T≤⊤ from le_top) hT
  have he : T.edgeFinset=H.edgeFinset :=
    eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hTH) (by
      have hcard := hH.card_edgeFinset
      omega)
  have hEq : T=H := SimpleGraph.edgeFinset_inj.mp he
  rwa [hEq]

end GraphicalZonotopes.TreeJoin
