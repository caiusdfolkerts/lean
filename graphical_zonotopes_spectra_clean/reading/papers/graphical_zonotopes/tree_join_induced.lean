module

public import Papers.GraphicalZonotopes.TreeJoinCliques
public import Papers.GraphicalZonotopes.ThreeTreeInducedEquality

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual induced graph on U, with the canonical finite subtype U as
its vertex type. Adjacency is exactly ambient adjacency of the two values. -/
def subtree (T : SimpleGraph V) (U : Finset V) : SimpleGraph U :=
  T.comap (Subtype.val : U → V)

theorem subtree_eq_induce (T : SimpleGraph V) (U : Finset V) :
    subtree T U=T.induce (U : Set V) := rfl

def subtreeUnivIso (T : SimpleGraph V) : subtree T univ ≃g T where
  toFun := Subtype.val
  invFun := fun v => ⟨v,mem_univ v⟩
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl
  map_rel_iff' := by intros; rfl

def inclusion (U : Finset V) : Vertex U ↪ Vertex V :=
  (Function.Embedding.sumMap
    (Function.Embedding.sumMap ⟨Subtype.val,Subtype.val_injective⟩
      (Function.Embedding.refl (Fin 1))) (Function.Embedding.refl (Fin 1)))

@[simp] theorem inclusion_a (U : Finset V) : inclusion U a=a := rfl
@[simp] theorem inclusion_b (U : Finset V) : inclusion U b=b := rfl
@[simp] theorem inclusion_old (U : Finset V) (v : U) : inclusion U (old v)=old v.1 := rfl

theorem inclusion_mem_core (U : Finset V) (x : Vertex U) : inclusion U x∈core U := by
  rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩
  · simp
  · simp
  · simpa using v.property

theorem mem_core_range (U : Finset V) {x : Vertex V} (hx : x∈core U) :
    x∈Set.range (inclusion U) := by
  rcases vertex_cases x with rfl|rfl|⟨v,rfl⟩
  · exact ⟨a,rfl⟩
  · exact ⟨b,rfl⟩
  · exact ⟨old ⟨v,(old_mem_core U v).mp hx⟩,rfl⟩

theorem univ_map_inclusion (U : Finset V) : univ.map (inclusion U)=core U := by
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
    exact inclusion_mem_core U v
  · intro hx
    obtain ⟨v,rfl⟩ := mem_core_range U hx
    exact mem_map.mpr ⟨v,mem_univ _,rfl⟩

theorem inclusion_adj (T : SimpleGraph V) (U : Finset V) (x y : Vertex U) :
    (graph (subtree T U)).Adj x y ↔
      (graph T).Adj (inclusion U x) (inclusion U y) := by
  rcases vertex_cases x with rfl|rfl|⟨u,rfl⟩ <;>
    rcases vertex_cases y with rfl|rfl|⟨v,rfl⟩ <;>
    simp [graph,SingleVertexGraph.graph,inclusion,old,a,b,subtree]

theorem map_induced (T : SimpleGraph V) (U : Finset V) :
    (graph (subtree T U)).map (inclusion U)=inducedOn (graph T) (core U) := by
  ext x y
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨u,v,huv,rfl,rfl⟩
    exact ⟨(inclusion_adj T U u v).mp huv,inclusion_mem_core U u,inclusion_mem_core U v⟩
  · rintro ⟨hxy,hx,hy⟩
    obtain ⟨u,rfl⟩ := mem_core_range U hx
    obtain ⟨v,rfl⟩ := mem_core_range U hy
    exact ⟨u,v,(inclusion_adj T U u v).mpr hxy,rfl,rfl⟩

theorem comap_induced (T : SimpleGraph V) (U : Finset V) :
    (inducedOn (graph T) (core U)).comap (inclusion U)=graph (subtree T U) := by
  ext x y
  change ((graph T).Adj (inclusion U x) (inclusion U y) ∧
    inclusion U x∈core U ∧ inclusion U y∈core U) ↔ _
  simp only [inclusion_mem_core,and_true]
  exact (inclusion_adj T U x y).symm

theorem forest_tree_of_join_threeTree {T : SimpleGraph V} (hT : T.IsAcyclic)
    (hG : IsThreeTree (graph T)) : T.IsTree := by
  have hn := hG.active_card_ge_four
  simp only [card_univ,Vertex,Fintype.card_sum,Fintype.card_fin] at hn
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  apply forest_isTree_of_card hT
  have he := hG.edgeFamily_card
  rw [edgeFamily_card] at he
  simp only [card_univ,Vertex,Fintype.card_sum,Fintype.card_fin] at he
  have hcount : (edgeFamily T).card=T.edgeFinset.card := by
    rw [edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]
  omega

theorem induced_core_threeTree_iff {T : SimpleGraph V} (hT : T.IsAcyclic)
    (U : Finset V) (hn : 2≤U.card) :
    ThreeTreeOn (core U) (inducedOn (graph T) (core U)) ↔
      (subtree T U).IsTree := by
  constructor
  · intro h
    have hh := h.comap (inclusion U) (fun _ hv => mem_core_range U hv)
    have hset : SetFunctionEmbedding.pullSet (inclusion U) (core U)=univ := by
      ext x
      simp [SetFunctionEmbedding.mem_pullSet,inclusion_mem_core]
    rw [hset,comap_induced] at hh
    exact forest_tree_of_join_threeTree (hT.induce _) hh
  · intro h
    have hg := (isThreeTree h (by simpa only [Fintype.card_coe] using hn)).map (inclusion U)
    rwa [univ_map_inclusion,map_induced] at hg

theorem induced_core_admissible_iff {T : SimpleGraph V} (hT : T.IsAcyclic)
    (U : Finset V) :
    Admissible (inducedOn (graph T) (core U)) ↔
      (subtree T U).maxDegree≤3 := by
  rw [←map_induced]
  constructor
  · intro h
    exact (admissible_iff_maxDegree (hT.induce _)).mp (Admissible.of_map (inclusion U) h)
  · intro h
    exact ((admissible_iff_maxDegree (hT.induce _)).mpr h).map (inclusion U)

/-- Every induced admissible 3-tree in the two-hub join consists of both
hubs together with a genuine connected induced subtree of maximum degree
at most three. The converse is proved by the preceding two equivalences. -/
theorem induced_admissible_subtree {T : SimpleGraph V} (hT : T.IsAcyclic)
    {S : Finset (Vertex V)} (hS : ThreeTreeOn S (inducedOn (graph T) S))
    (hA : Admissible (inducedOn (graph T) S)) :
    ∃ U : Finset V,S=core U ∧ 2≤U.card ∧
      (subtree T U).IsTree ∧ (subtree T U).maxDegree≤3 := by
  obtain ⟨C,hC⟩ := hS.tetrahedra_nonempty
  obtain ⟨hc,hcl⟩ := (mem_tetrahedra_iff _ C).mp hC
  have hcl' : (graph T).IsClique C := fun u hu v hv huv => (hcl hu hv huv).1
  obtain ⟨ha,hb⟩ := tetrahedron_hubs hT hc hcl'
  have hCS := hS.clique_subset_active (by omega : 2≤C.card) hcl
  have he := core_outer (hCS ha) (hCS hb)
  have hn : 2≤(outer S).card := by
    have hcard := hS.active_card_ge_four
    have h := core_card (outer S)
    rw [he] at h
    omega
  refine ⟨outer S,he.symm,hn,?_,?_⟩
  · apply (induced_core_threeTree_iff hT (outer S) hn).mp
    simpa only [he] using hS
  · apply (induced_core_admissible_iff hT (outer S)).mp
    simpa only [he] using hA

end GraphicalZonotopes.TreeJoin
