module

public import Papers.GraphicalZonotopes.TreewidthLowDegree
public import Papers.GraphicalZonotopes.SingleVertexGraph
public import Papers.GraphicalZonotopes.EdgeCoordinates

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset BooleanModule BooleanVertexExtension
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Relabeling graph vertices preserves the number of unordered edges.
No order on the vertex types is needed. -/
theorem edgeFamily_card_map (e : V ↪ W) (G : SimpleGraph V) :
    (edgeFamily (G.map e)).card = (edgeFamily G).card := by
  classical
  rw [edgeFamily_eq_image_edgeFinset,
    card_image_of_injective _ sym2_toFinset_injective,
    edgeFamily_eq_image_edgeFinset,
    card_image_of_injective _ sym2_toFinset_injective]
  simpa only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] using
    SimpleGraph.card_edgeFinset_map e G

theorem HasTreewidthAtMost.comap {G : SimpleGraph V} {w : ℕ}
    (h : HasTreewidthAtMost G w) (e : W ↪ V) : HasTreewidthAtMost (G.comap e) w := by
  obtain ⟨m,T,bag,hT,hs,hc,he,hcon⟩ := h
  let b : Fin m → Finset W := fun i => SetFunctionEmbedding.pullSet e (bag i)
  refine ⟨m,T,b,hT,?_,?_,?_,?_⟩
  · intro i
    have hsub : (b i).map e ⊆ bag i := by
      intro v hv
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hv
      exact (SetFunctionEmbedding.mem_pullSet e _ _).mp hu
    have hcard := card_le_card hsub
    rw [card_map] at hcard
    exact hcard.trans (hs i)
  · intro v
    obtain ⟨i,hi⟩ := hc (e v)
    exact ⟨i,(SetFunctionEmbedding.mem_pullSet e _ _).mpr hi⟩
  · intro u v huv
    obtain ⟨i,hu,hv⟩ := he (e u) (e v) huv
    exact ⟨i,(SetFunctionEmbedding.mem_pullSet e _ _).mpr hu,
      (SetFunctionEmbedding.mem_pullSet e _ _).mpr hv⟩
  · intro v
    have hsets : {i | v ∈ b i} = {i | e v ∈ bag i} := by
      ext i
      exact SetFunctionEmbedding.mem_pullSet e _ _
    rw [hsets]
    exact hcon (e v)

/-- A finite tree decomposition with one specified bag containing the
displayed boundary. The index type is only presentation data. -/
structure RootedTreeDecomposition (G : SimpleGraph V) (w : ℕ) (B : Finset V) where
  Index : Type
  [indexFintype : Fintype Index]
  [indexDecidableEq : DecidableEq Index]
  tree : SimpleGraph Index
  bag : Index → Finset V
  root : Index
  isTree : tree.IsTree
  size : ∀ i, (bag i).card ≤ w+1
  cover : ∀ v, ∃ i, v ∈ bag i
  edge : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  occurrence : ∀ v, (tree.induce {i | v ∈ bag i}).Connected
  boundary : B ⊆ bag root

attribute [instance] RootedTreeDecomposition.indexFintype RootedTreeDecomposition.indexDecidableEq

theorem RootedTreeDecomposition.hasTreewidthAtMost {G : SimpleGraph V} {w : ℕ}
    {B : Finset V} (d : RootedTreeDecomposition G w B) : HasTreewidthAtMost G w := by
  let e := Fintype.equivFin d.Index
  let T : SimpleGraph (Fin (Fintype.card d.Index)) := d.tree.comap e.symm
  let bag : Fin (Fintype.card d.Index) → Finset V := fun i => d.bag (e.symm i)
  let iso : T ≃g d.tree := { e.symm with map_rel_iff' := by intros; rfl }
  refine ⟨Fintype.card d.Index,T,bag,iso.isTree_iff.mpr d.isTree,
    fun i => d.size (e.symm i),?_,?_,?_⟩
  · intro v
    obtain ⟨i,hi⟩ := d.cover v
    exact ⟨e i,by simpa only [bag,Equiv.symm_apply_apply] using hi⟩
  · intro u v huv
    obtain ⟨i,hu,hv⟩ := d.edge u v huv
    exact ⟨e i,by simpa only [bag,Equiv.symm_apply_apply] using hu,
      by simpa only [bag,Equiv.symm_apply_apply] using hv⟩
  · intro v
    let e' : (T.induce {i | v ∈ bag i}) ≃g (d.tree.induce {i | v ∈ d.bag i}) :=
      { toFun := fun i => ⟨e.symm i.1,i.2⟩
        invFun := fun i => ⟨e i.1,by
          change v ∈ d.bag (e.symm (e i.1))
          simpa only [Equiv.symm_apply_apply] using (show v ∈ d.bag i.1 from i.2)⟩
        left_inv := by intro i; apply Subtype.ext; simp
        right_inv := by intro i; apply Subtype.ext; simp
        map_rel_iff' := by intros; rfl }
    exact e'.connected_iff.mpr (d.occurrence v)

def RootedTreeDecomposition.restrictBoundary {G : SimpleGraph V} {w : ℕ}
    {B C : Finset V} (d : RootedTreeDecomposition G w B) (h : C ⊆ B) :
    RootedTreeDecomposition G w C := { d with boundary := h.trans d.boundary }

theorem edgeFamily_card_eq_edgeFinset_card (G : SimpleGraph V) :
    (edgeFamily G).card = G.edgeFinset.card := by
  rw [edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]

theorem SingleVertexGraph.isTree_singleton {G : SimpleGraph V} (hG : G.IsTree) (r : V) :
    (SingleVertexGraph.graph G {r}).IsTree := by
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨SingleVertexGraph.connected hG.connected (singleton_nonempty _),?_⟩
  simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_fin]
  rw [← SimpleGraph.edgeFinset_card,← edgeFamily_card_eq_edgeFinset_card,
    SingleVertexGraph.edgeFamily_card,card_singleton,edgeFamily_card_eq_edgeFinset_card,
    hG.card_edgeFinset]

/-- Appending a leaf bag proves the ordinary width bound after attaching a
new graph vertex to vertices already sharing the specified boundary bag. -/
def RootedTreeDecomposition.append {G : SimpleGraph V} {w : ℕ} {B : Finset V}
    (d : RootedTreeDecomposition G w B) (hB : B.card ≤ w) :
    RootedTreeDecomposition (SingleVertexGraph.graph G B) w
      (insert (Sum.inr 0) (hubSet (J := Fin 1) B)) := by
  let I := d.Index
  let T : SimpleGraph (BooleanVertexExtension.Vertex I) :=
    SingleVertexGraph.graph d.tree {d.root}
  let bag : BooleanVertexExtension.Vertex I → Finset (BooleanVertexExtension.Vertex V)
    | Sum.inl i => hubSet (d.bag i)
    | Sum.inr _ => insert (Sum.inr 0) (hubSet B)
  refine {
    Index := BooleanVertexExtension.Vertex I
    tree := T
    bag := bag
    root := Sum.inr 0
    isTree := SingleVertexGraph.isTree_singleton d.isTree d.root
    size := ?_
    cover := ?_
    edge := ?_
    occurrence := ?_
    boundary := Subset.rfl }
  · intro i
    cases i with
    | inl i => simpa only [bag,hubSet,card_map] using d.size i
    | inr j =>
      change (insert (Sum.inr 0) (hubSet (J := Fin 1) B)).card ≤ w+1
      rw [card_insert_of_notMem (notMem_hubSet_outer B (0 : Fin 1)),hubSet,card_map]
      omega
  · intro v
    cases v with
    | inl v =>
      obtain ⟨i,hi⟩ := d.cover v
      exact ⟨Sum.inl i,by simpa only [bag,mem_hubSet_hub] using hi⟩
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact ⟨Sum.inr 0,mem_insert_self _ _⟩
  · intro u v huv
    cases u with
    | inl u =>
      cases v with
      | inl v =>
        obtain ⟨i,hu,hv⟩ := d.edge u v huv
        exact ⟨Sum.inl i,by simpa only [bag,mem_hubSet_hub] using hu,
          by simpa only [bag,mem_hubSet_hub] using hv⟩
      | inr j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        change u ∈ B at huv
        exact ⟨Sum.inr 0,by simpa only [bag,mem_insert,Sum.inl_ne_inr,false_or,
          mem_hubSet_hub] using huv,mem_insert_self _ _⟩
    | inr i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      cases v with
      | inl v =>
        change v ∈ B at huv
        exact ⟨Sum.inr 0,mem_insert_self _ _,by simpa only [bag,mem_insert,
          Sum.inl_ne_inr,false_or,mem_hubSet_hub] using huv⟩
      | inr j => exact False.elim huv
  · intro v
    cases v with
    | inl v =>
      let f : (d.tree.induce {i | v ∈ d.bag i}) →g (T.induce {i | Sum.inl v ∈ bag i}) :=
        { toFun := fun i => ⟨Sum.inl i.1,by
            change Sum.inl v ∈ hubSet (J := Fin 1) (d.bag i.1)
            exact (mem_hubSet_hub _ _).mpr i.2⟩
          map_rel' := by intro i j hij; exact hij }
      obtain ⟨i,hi⟩ := d.cover v
      apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
      refine ⟨f ⟨i,hi⟩,?_⟩
      intro j
      rcases j with ⟨j,hj⟩
      cases j with
      | inl k =>
        have hk : v ∈ d.bag k := by
          change Sum.inl v ∈ hubSet (J := Fin 1) (d.bag k) at hj
          exact (mem_hubSet_hub _ _).mp hj
        exact ((d.occurrence v) ⟨i,hi⟩ ⟨k,hk⟩).map f
      | inr k =>
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        have hvB : v ∈ B := by
          change Sum.inl v ∈ insert (Sum.inr 0) (hubSet (J := Fin 1) B) at hj
          simpa only [mem_insert,Sum.inl_ne_inr,false_or,mem_hubSet_hub] using hj
        have hvr : v ∈ d.bag d.root := d.boundary hvB
        refine (((d.occurrence v) ⟨i,hi⟩ ⟨d.root,hvr⟩).map f).trans ?_
        apply SimpleGraph.Adj.reachable
        exact mem_singleton_self _
    | inr v =>
      have hv : v = 0 := Subsingleton.elim _ _
      subst v
      apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
      refine ⟨⟨Sum.inr 0,mem_insert_self _ _⟩,?_⟩
      rintro ⟨i,hi⟩
      cases i with
      | inl i =>
        change Sum.inr (0 : Fin 1) ∈ hubSet (d.bag i) at hi
        exact False.elim (notMem_hubSet_outer _ _ hi)
      | inr i =>
        have hi0 : i = 0 := Subsingleton.elim _ _
        subst i
        exact SimpleGraph.Reachable.rfl

end GraphicalZonotopes
