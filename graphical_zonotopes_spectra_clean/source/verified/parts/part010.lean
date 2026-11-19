module

public import Aesop
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Omega
public import Lean.Meta.Basic
public import Lean.PrettyPrinter
public import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.Graph.Maps
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.Graph.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Order.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.Sum.Order
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UnitInterval

public import verified.parts.part009
import all verified.parts.part009

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart129
/- Source: Papers/GraphicalZonotopes/ThreeTreeInducedEquality.lean -/





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

end
end
end BundlePart129

section BundlePart130
/- Source: Papers/GraphicalZonotopes/TreeJoinInduced.lean -/





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
    (U : Finset V) (hn : 2≤ U.card) :
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
    ∃ U : Finset V,S=core U ∧ 2≤ U.card ∧
      (subtree T U).IsTree ∧ (subtree T U).maxDegree≤3 := by
  obtain ⟨C,hC⟩ := hS.tetrahedra_nonempty
  obtain ⟨hc,hcl⟩ := (mem_tetrahedra_iff _ C).mp hC
  have hcl' : (graph T).IsClique C := fun u hu v hv huv => (hcl hu hv huv).1
  obtain ⟨ha,hb⟩ := tetrahedron_hubs hT hc hcl'
  have hCS := hS.clique_subset_active (by omega : 2≤ C.card) hcl
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

end
end
end BundlePart130

section BundlePart131
/- Source: Papers/GraphicalZonotopes/TreeJoinSubtrees.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A connected subgraph of a forest already contains every ambient edge
between its vertices. Thus the word "subtree" does not restrict s₃ to a
smaller class when we represent it as an induced graph. -/
theorem connected_subgraph_eq {W : Type*} {G H : SimpleGraph W}
    (hG : G.IsAcyclic) (hH : H.Connected) (hHG : H≤ G) : H=G := by
  have htree : G.IsTree := ⟨hH.mono hHG,hG⟩
  have hmin := SimpleGraph.isTree_iff_minimal_connected.mp htree
  exact le_antisymm hHG (hmin.2 hH hHG)

theorem induced_subcubic_iff_subtree {T : SimpleGraph V} (hT : T.IsAcyclic)
    (U : Finset V) :
    ((subtree T U).IsTree ∧ (subtree T U).maxDegree≤3) ↔
      ∃ H : SimpleGraph U,H≤ subtree T U ∧ H.IsTree ∧ H.maxDegree≤3 := by
  constructor
  · rintro ⟨ht,hd⟩
    exact ⟨_,le_rfl,ht,hd⟩
  · rintro ⟨H,hH,ht,hd⟩
    have he := connected_subgraph_eq (hT.induce _) ht.connected hH
    subst H
    exact ⟨ht,hd⟩

def subcubicSubtreeSets (T : SimpleGraph V) : Finset (Finset V) :=
  univ.filter (fun U => (subtree T U).IsTree ∧
    (subtree T U).maxDegree≤3)

/-- The largest number of vertices in a nonempty connected subtree with
maximum degree at most three. `induced_subcubic_iff_subtree` proves that on
a forest this is exactly the maximum over all connected subgraphs. -/
def s3 (T : SimpleGraph V) : ℕ := (subcubicSubtreeSets T).sup Finset.card

theorem subtree_card_le_s3 {T : SimpleGraph V} {U : Finset V}
    (ht : (subtree T U).IsTree) (hd : (subtree T U).maxDegree≤3) :
    U.card≤ s3 T := by
  apply le_sup
  exact mem_filter.mpr ⟨mem_univ _,ht,hd⟩

theorem singleton_subtree (T : SimpleGraph V) (v : V) :
    ({v} : Finset V)∈subcubicSubtreeSets T := by
  letI : Nonempty ({v} : Finset V) := ⟨⟨v,by simp⟩⟩
  letI : Subsingleton ({v} : Finset V) := ⟨by
    intro x y
    apply Subtype.ext
    have hx : x.1=v := mem_singleton.mp x.2
    have hy : y.1=v := mem_singleton.mp y.2
    exact hx.trans hy.symm⟩
  exact mem_filter.mpr ⟨mem_univ _,SimpleGraph.IsTree.of_subsingleton,by simp⟩

theorem s3_pos (T : SimpleGraph V) [Nonempty V] : 1≤ s3 T := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  have h := le_sup (s := subcubicSubtreeSets T) (f := Finset.card) (singleton_subtree T v)
  simpa only [card_singleton,s3] using h

theorem s3_le_card (T : SimpleGraph V) : s3 T≤ Fintype.card V := by
  apply Finset.sup_le_iff.mpr
  intro U hU
  exact card_le_univ U

theorem s3_attained (T : SimpleGraph V) [Nonempty V] :
    ∃ U : Finset V,(subtree T U).IsTree ∧
      (subtree T U).maxDegree≤3 ∧ U.card=s3 T := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  obtain ⟨U,hU,hmax⟩ := (subcubicSubtreeSets T).exists_max_image Finset.card
    ⟨{v},singleton_subtree T v⟩
  obtain ⟨ht,hd⟩ := (mem_filter.mp hU).2
  exact ⟨U,ht,hd,le_antisymm (subtree_card_le_s3 ht hd) (Finset.sup_le_iff.mpr hmax)⟩

theorem s3_eq_card_iff {T : SimpleGraph V} (hT : T.IsTree) :
    s3 T=Fintype.card V ↔ T.maxDegree≤3 := by
  letI : Nonempty V := hT.connected.nonempty
  have hdeg : (subtree T univ).maxDegree=T.maxDegree := by
    exact (subtreeUnivIso T).maxDegree_eq
  constructor
  · intro he
    obtain ⟨U,ht,hd,hcard⟩ := s3_attained T
    have hU : U=univ := eq_univ_of_card U (hcard.trans he)
    subst U
    rwa [hdeg] at hd
  · intro hd
    apply le_antisymm (s3_le_card T)
    have ht : (subtree T univ).IsTree := by
      exact (subtreeUnivIso T).isTree_iff.mpr hT
    have h := subtree_card_le_s3 ht (by rwa [hdeg])
    simpa only [card_univ] using h

end GraphicalZonotopes.TreeJoin

end
end
end BundlePart131

section BundlePart132
/- Source: Papers/GraphicalZonotopes/SupportDimensionBound.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Removing inactive coordinates gives the full support-sensitive affine
dimension bound, including the empty support. -/
theorem finrank_vectorSpan_le_support {z : SetFunction V} {S : Finset V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hdep : DependsOn z S) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z))≤ S.card-1 := by
  let W:=vectorSpan ℝ (basePolytope z)
  have hzero : ∀ (x : W) v,v∉S → x.1 v=0 := by
    intro x v hv
    exact vectorSpan_le_evaluation_ker_of_dependsOn hn hs hdep hv x.2
  by_cases hS : S.Nonempty
  · let r : W →ₗ[ℝ] (S → ℝ) := {
      toFun x v:=x.1 v.1
      map_add' _ _:=rfl
      map_smul' _ _:=rfl }
    have hr : ∀ x : W,r x∈(totalLinear (V:=S)).ker := by
      intro x
      change (∑ v : S,x.1 v.1)=0
      rw [Finset.sum_coe_sort]
      have htotal : (∑ v : V,x.1 v)=0 :=
        vectorSpan_basePolytope_le_total_ker (basePolytope_nonempty hn.1 hs) x.2
      rw [← htotal]
      exact sum_subset (subset_univ S) (fun v hv hvS => hzero x v hvS)
    let q:=r.codRestrict (totalLinear (V:=S)).ker hr
    have hq : Function.Injective q := by
      intro x y hxy
      apply Subtype.ext
      funext v
      by_cases hv : v∈S
      · exact congrArg (fun t : (totalLinear (V:=S)).ker => t.1 ⟨v,hv⟩) hxy
      · rw [hzero x v hv,hzero y v hv]
    have hb:=LinearMap.finrank_le_finrank_of_injective hq
    obtain ⟨v,hv⟩:=hS
    rw [finrank_total_ker_fintype (⟨v,hv⟩ : S),Fintype.card_coe] at hb
    exact hb
  · have hW : W=⊥ := by
      apply le_antisymm
      · intro x hx
        change x=0
        funext v
        exact hzero ⟨x,hx⟩ v (fun hv => hS ⟨v,hv⟩)
      · exact bot_le
    change Module.finrank ℝ W≤ _
    rw [hW,finrank_bot]
    exact Nat.zero_le _

namespace Separator
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- The active separator blocks contain the complete Möbius support, even
when some of the original private branches are zero. -/
theorem dependsOn_active_branches (h : Partition G B A) (z : graphicalFunctionSpace G) :
    DependsOn z.1 (B ∪ univ.biUnion (fun j : Gluing.ActiveBranch
      (((functionEquiv h).symm z).2) => A j.1)) := by
  classical
  let f:=((functionEquiv h).symm z).2
  let T:=B ∪ univ.biUnion (fun j : Gluing.ActiveBranch f => A j.1)
  have hy:=(mobius_cliqueSupported_iff G z.1).mpr z.2
  rw [← zeta_mobius z.1]
  apply zeta_dependsOn
  intro C hCT
  by_cases hcl : IsCliqueCoordinate G C
  · have hCB : ¬C⊆B:=fun hc => hCT (hc.trans subset_union_left)
    obtain ⟨j,hCj,huniq⟩:=h.clique_unique_branch ⟨C,hcl⟩ hCB
    let D : privateIndex G B A j:=⟨⟨C,hcl⟩,hCB,hCj⟩
    by_cases hf : f j=0
    · have hh:=congrFun hf D
      exact hh
    · apply False.elim
      apply hCT
      intro v hv
      rcases mem_union.mp (hCj hv) with hvB | hvA
      · exact mem_union_left _ hvB
      · exact mem_union_right _ (mem_biUnion.mpr ⟨⟨j,hf⟩,mem_univ _,hvA⟩)
  · exact coefficient_zero_of_not_clique hy C hcl

/-- For singleton private branches, the number of active branches controls
the genuine affine dimension. This does not assume full ambient dimension. -/
theorem finrank_le_boundary_add_active (h : Partition G B A)
    (hA : ∀ j,(A j).card≤1) (z : graphicalFunctionSpace G) (hz : Supermodular z.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))≤
      B.card+Fintype.card (Gluing.ActiveBranch (((functionEquiv h).symm z).2))-1 := by
  classical
  let f:=((functionEquiv h).symm z).2
  have hb:=finrank_vectorSpan_le_support z.2.1 hz (dependsOn_active_branches h z)
  have hu : (univ.biUnion (fun j : Gluing.ActiveBranch f => A j.1)).card≤
      Fintype.card (Gluing.ActiveBranch f) := by
    apply card_biUnion_le.trans
    calc
      (∑ j : Gluing.ActiveBranch f,(A j.1).card)≤∑ j : Gluing.ActiveBranch f,1 :=
        sum_le_sum (fun j hj => hA j.1)
      _=Fintype.card (Gluing.ActiveBranch f):=by simp
  have hc:=card_union_le B (univ.biUnion (fun j : Gluing.ActiveBranch f => A j.1))
  exact hb.trans (Nat.sub_le_sub_right (hc.trans (Nat.add_le_add_left hu B.card)) 1)

end Separator
end GraphicalZonotopes

end
end
end BundlePart132

section BundlePart133
/- Source: Papers/GraphicalZonotopes/WeakSummandReduction.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every actual weak summand has its genuine normalized graphical support
function, preserving affine dimension. Points are handled explicitly rather
than excluded by an extra hypothesis. -/
theorem weak_summand_extreme_or_zero {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    ∃ z : graphicalFunctionSpace G,Supermodular z.1 ∧
      (z.1=0 ∨ ExtremeSupermodular z.1) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) := by
  obtain ⟨c,hc,R,hR,hRc,hnR,hQR⟩:=hw
  have hTn : Normalized (c • graphFunction G) := by
    change c*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs:=(graphFunction_supermodular G).smul hc.le
  have hbase : Q+R=basePolytope (c • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) hc.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  let f:=lowerSupport Q
  have hfn : Normalized f:=lowerSupport_normalized hQ.compact hi.1
  have hfs : Supermodular f:=summand_lowerSupport_supermodular hTn hTs
    hQ.compact hR hi.1 hnR hbase
  have hbody : Q=basePolytope f:=summand_eq_basePolytope hTn hTs
    hQ.compact hR hQ.convex hi.1 hnR hbase
  have hgf : Graphical G f := by
    apply ((isMinkowskiSummand_graphical_iff hfn hfs hc.le).mp ?_).1
    rw [← hbody]
    exact ⟨R,hR,hRc,hnR,hQR⟩
  have hgn : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgf u v huv hnon S hu hv
  refine ⟨⟨normalize f,normalize_translationNormalized hfn,hgn⟩,hfs.normalize,?_,?_⟩
  · by_cases hz:normalize f=0
    · exact Or.inl hz
    · exact Or.inr (MinkowskiIndecomposable.extremeSupermodular_normalize
        hfn hfs hz (hbody ▸ hi))
  · rw [vectorSpan_basePolytope_normalize,← hbody]

theorem weak_summand_dimension_le {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤ Fintype.card V-1 := by
  obtain ⟨z,hz,he,hd⟩:=weak_summand_extreme_or_zero hQ hi hw
  rw [hd]
  simpa only [card_univ] using finrank_vectorSpan_le_support z.2.1 hz
    (show DependsOn z.1 univ from fun T => by rw [inter_univ])

/-- Every actual witness contributes its real affine dimension to the
paper's maximum invariant; boundedness follows from ambient geometry. -/
theorem dimension_le_maximum {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤ maximumIndecomposableDimension G := by
  apply le_csSup
  · refine ⟨Fintype.card V-1,?_⟩
    rintro d ⟨R,hR,hr,hs,hd⟩
    rw [← hd]
    exact weak_summand_dimension_le hR hr hs
  · exact ⟨Q,hQ,hi,hw,rfl⟩

theorem Graphical.mono_graph {G H : SimpleGraph V} {z : SetFunction V}
    (hHG : H≤ G) (hz : Graphical H z) : Graphical G z := by
  intro u v huv hnon S hu hv
  exact hz u v huv (fun h => hnon (hHG h)) S hu hv

end GraphicalZonotopes

end
end
end BundlePart133

section BundlePart134
/- Source: Papers/GraphicalZonotopes/PartialThreeTreeSupport.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [LinearOrder V]

namespace RefinedTriangleComponents
open PositiveDecomposition

private theorem adjusted_zero_function' : adjusted (0 : SetFunction V) = 0 := by
  have ha : allocation (0 : SetFunction V) = 0 := by
    funext C
    by_cases hC : C.card = 2
    · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
      rw [allocation_pair _ huv]
      have hm : minimumSlack (0 : SetFunction V) u v = 0 :=
        minimumSlack_eq_zero (by intros; simp [delta])
      simp [hm]
    · exact allocation_zero _ hC
  rw [adjusted,ha]
  change 0+zetaLinear 0=0
  simp

/-- Positive decomposition also identifies the unique interacting clique
class without assuming full ambient dimension. The dimension hypothesis
rules out the segment and isolated-triangle pieces. -/
theorem extreme_has_component_of_dimension_ge_three {z : SetFunction V}
    (hz : ExtremeSupermodular z)
    (hdim : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z)))
    (hdegree : ∀ C,mobius z C ≠ 0 → C.card ≤ 4) :
    ∃ a : Component (mobius z),∃ t : ℝ,0 < t ∧
      adjusted (higherClass (mobius z) (classOf (mobius z)) (Sum.inl a)) = t • z ∧
      DependsOn z ((family (mobius z)).biUnion id) := by
  classical
  let y := mobius z
  have hy : y ∅ = 0 ∧ ∀ v,y {v} = 0 :=
    (zeta_normalized_iff y).mp (by simpa [y] using hz.1)
  obtain ⟨hp,he⟩ := pieces_positive hy hdegree (by simpa [y] using hz.2.1)
  have hez : (∑ i,pieces y i) = z := by simpa [y] using he
  have hex : ∃ i,pieces y i ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i,pieces y i) = 0 := sum_eq_zero (fun i _ => h i)
    exact hz.2.2.1 (hez.symm.trans hzero)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨t,ht,hscale⟩ := hz.finite_summand (pieces y)
    (fun i => (hp i).1) (fun i => (hp i).2) hez hi
  have hsupport : ∀ S,DependsOn (pieces y i) S → 4 ≤ S.card := by
    intro S hS
    rw [hscale] at hS
    have hb := finrank_vectorSpan_le_support hz.1 hz.2.1
      (DependsOn.of_smul (ne_of_gt ht) hS)
    omega
  cases i with
  | inr C =>
    have hC : C.card = 2 := by
      by_contra hnot
      have hzC := residual_zero y (higherClass y (classOf y)) hnot
      exact hi (by simp [pieces,hzC])
    have hdep : DependsOn (pieces y (Sum.inr C)) C := (setMonomial_dependsOn C).smul _
    have hc := hsupport C hdep
    omega
  | inl c =>
    cases c with
    | inr T =>
      have hT : T.card = 3 := by
        by_contra hnot
        have hzero := higher_right_zero_of_card_ne_three hdegree hnot
        exact hi (by simp only [y,pieces,Sum.elim_inl,hzero,adjusted_zero_function'])
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_right_dependsOn hdegree T)
      have hc := hsupport T hdep
      omega
    | inl a =>
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_left_dependsOn hdegree a)
      refine ⟨a,t,ht,hscale,?_⟩
      change DependsOn (pieces y (Sum.inl (Sum.inl a))) ((family y).biUnion id) at hdep
      rw [hscale] at hdep
      exact DependsOn.of_smul (ne_of_gt ht) hdep

/-- Corollary 4.4 in its full, possibly lower-dimensional form: the actual
edge directions are precisely the union of the nonzero tetrahedral
coefficients, and that family is connected through triangles. -/
theorem refined_support_of_dimension_ge_three {G : SimpleGraph V}
    (hG : G.CliqueFree 5) {z : SetFunction V} (hz : ExtremeSupermodular z)
    (hgraph : Graphical G z)
    (hdim : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z))) :
    (family (mobius z)).Nonempty ∧
      (tetrahedronGraph (family (mobius z))).Preconnected ∧
      actualDirectionGraph (basePolytope z) = edgeGraph (mobius z) ∧
      DependsOn z ((family (mobius z)).biUnion id) := by
  classical
  let y := mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hgraph⟩
  have hdegree : ∀ C,y C ≠ 0 → C.card ≤ 4 := fun C hC => nonzero_card_le_four hG hy hC
  obtain ⟨a,t,ht,hscale,hdep⟩ := extreme_has_component_of_dimension_ge_three hz hdim hdegree
  have hcomp := same_component_of_positive_piece a (ne_of_gt ht)
    (by simpa only [zeta_mobius] using hscale)
  have hconnected : (tetrahedronGraph (family y)).Preconnected := by
    intro C D
    exact SimpleGraph.ConnectedComponent.exact ((hcomp C).trans (hcomp D).symm)
  have hne : (family y).Nonempty := by
    obtain ⟨C,hC⟩ := a.exists_rep
    exact ⟨C.1,C.2⟩
  refine ⟨hne,hconnected,?_,hdep⟩
  have hpiece : Graphical (edgeGraph y)
      (adjusted (higherClass y (classOf y) (Sum.inl a))) :=
    adjusted_graphical ((cliqueSupported_iff _ _).mp (left_coefficients_supported hdegree a)).2
  have hzedge : Graphical (edgeGraph y) z := by
    intro u v huv hnon S hu hv
    have h := hpiece u v huv hnon S hu hv
    rw [hscale,delta_smul] at h
    exact mul_left_cancel₀ (ne_of_gt ht) (by simpa using h)
  ext u v
  constructor
  · intro h
    exact actualRootEdge_of_graphical hz.1.1 hz.2.1 hzedge h
  · rintro ⟨huv,C,hC,hu,hv⟩
    exact actualRootEdge_of_nonzero_coefficient hz.1.1 hz.2.1
      ((mem_family y C).mp hC).2 huv hu hv

end RefinedTriangleComponents

open RefinedTriangleComponents

/-- Necessity in Corollary 6.6 on the actual active coordinate set. -/
theorem partial_threeTree_extreme_support {G : SimpleGraph V} (hG : IsPartialThreeTree G)
    {z : SetFunction V} (hz : ExtremeSupermodular z) (hg : Graphical G z)
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z))) :
    ∃ U : Finset V,4 ≤ U.card ∧
      actualDirectionGraph (basePolytope z) = inducedOn G U ∧
      ThreeTreeOn U (inducedOn G U) ∧ Admissible (inducedOn G U) ∧
      Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = U.card-1 := by
  classical
  let F := family (mobius z)
  let U := F.biUnion id
  obtain ⟨hne,hconn,hactual,hdep⟩ := refined_support_of_dimension_ge_three
    hG.cliqueFree_five hz hg hd
  have hy : CliqueSupported G (mobius z) := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hg⟩
  have hcl : ∀ C ∈ F,C.card = 4 ∧ G.IsClique C := by
    intro C hC
    obtain ⟨hc,hn⟩ := (mem_family _ C).mp hC
    refine ⟨hc,?_⟩
    by_contra hnot
    exact hn (coefficient_zero_of_not_clique hy C (by rintro ⟨_,hh⟩; exact hnot hh))
  have htree := hG.connected_family_threeTree F hne hcl hconn
  have hU : 4 ≤ U.card := htree.active_card_ge_four
  let H := actualDirectionGraph (basePolytope z)
  have hHU : H ≤ inducedOn G U := by
    intro u v huv
    have he : (edgeGraph (mobius z)).Adj u v := by simpa only [H,hactual] using huv
    obtain ⟨_,C,hC,hu,hv⟩ := he
    exact ⟨actualRootEdge_of_graphical hz.1.1 hz.2.1 hg huv,
      mem_biUnion.mpr ⟨C,hC,hu⟩,mem_biUnion.mpr ⟨C,hC,hv⟩⟩
  have hclH : ∀ C ∈ F,C.card = 4 ∧ H.IsClique C := by
    intro C hC
    refine ⟨(mem_family _ C).mp hC |>.1,?_⟩
    rw [show H = edgeGraph (mobius z) from hactual]
    exact family_subset_edgeGraph_clique hC
  have hHg := tetrahedralGrowth_of_connected_family H F hne hclH hconn
  have hiH : inducedOn H U = H := by
    ext u v
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,(hHU h).2⟩
  have hlow := hHg.edge_bound_and_equality.1
  change 3*U.card-6 ≤ (edgeFamily (inducedOn H U)).card at hlow
  rw [hiH] at hlow
  have heq : H = inducedOn G U := graph_eq_of_le_card_edges hHU
    ((hG.induced_edge_bound U (by omega)).trans hlow)
  have htreeH : ThreeTreeOn U (actualDirectionGraph (basePolytope z)) := by
    change ThreeTreeOn U H
    rw [heq]
    exact htree
  obtain ⟨hdim,hA⟩ := threeTree_actual_dimension_admissible hz htreeH
  exact ⟨U,hU,heq,htree,heq ▸ hA,hdim⟩

/-- Actual weak summands have normalized lower-support functions preserving
both affine dimension and the literal graph of exposed edge directions. -/
theorem weak_summand_normalized_function {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    ∃ z : graphicalFunctionSpace G,Supermodular z.1 ∧
      (z.1 = 0 ∨ ExtremeSupermodular z.1) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) ∧
      actualDirectionGraph Q = actualDirectionGraph (basePolytope z.1) := by
  obtain ⟨c,hc,R,hR,hRc,hnR,hQR⟩ := hw
  have hTn : Normalized (c • graphFunction G) := by
    change c*graphFunction G ∅=0
    rw [graphFunction_normalized,mul_zero]
  have hTs := (graphFunction_supermodular G).smul hc.le
  have hbase : Q+R=basePolytope (c • graphFunction G) := by
    rw [basePolytope_smul (graphFunction_normalized G) (graphFunction_supermodular G) hc.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  let f := lowerSupport Q
  have hfn : Normalized f := lowerSupport_normalized hQ.compact hi.1
  have hfs : Supermodular f := summand_lowerSupport_supermodular hTn hTs
    hQ.compact hR hi.1 hnR hbase
  have hbody : Q=basePolytope f := summand_eq_basePolytope hTn hTs
    hQ.compact hR hQ.convex hi.1 hnR hbase
  have hgf : Graphical G f := by
    apply ((isMinkowskiSummand_graphical_iff hfn hfs hc.le).mp ?_).1
    rw [← hbody]
    exact ⟨R,hR,hRc,hnR,hQR⟩
  have hgn : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgf u v huv hnon S hu hv
  refine ⟨⟨normalize f,normalize_translationNormalized hfn,hgn⟩,hfs.normalize,?_,?_,?_⟩
  · by_cases hz : normalize f=0
    · exact Or.inl hz
    · exact Or.inr (MinkowskiIndecomposable.extremeSupermodular_normalize
        hfn hfs hz (hbody ▸ hi))
  · rw [vectorSpan_basePolytope_normalize,← hbody]
  · rw [actualDirectionGraph_normalize,← hbody]

/-- Corollary 6.6, necessity for ordinary polytopes, with no full-dimension
assumption on the ambient coordinate space. -/
theorem partial_threeTree_polytope_support {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G))
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q)) :
    ∃ U : Finset V,4 ≤ U.card ∧ actualDirectionGraph Q = inducedOn G U ∧
      ThreeTreeOn U (inducedOn G U) ∧ Admissible (inducedOn G U) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = U.card-1 := by
  obtain ⟨z,hz,he,hdim,hgraph⟩ := weak_summand_normalized_function hQ hi hw
  have hdz : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) := by rwa [hdim] at hd
  have hext : ExtremeSupermodular z.1 := by
    rcases he with he | he
    · rw [he,basePolytope_zero,_root_.vectorSpan_singleton,finrank_bot] at hdz
      omega
    · exact he
  obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_extreme_support hG hext z.2.2 hdz
  exact ⟨U,hU,hgraph.trans ha,ht,hA,hdim.trans hD⟩

/-- The converse in Corollary 6.6 supplies a lattice representative on every
permitted induced support and fixes all coordinates outside that support. -/
theorem induced_admissible_threeTree_witness {G : SimpleGraph V} {U : Finset V}
    (hU : ThreeTreeOn U (inducedOn G U)) (hA : Admissible (inducedOn G U)) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      actualDirectionGraph Q = inducedOn G U ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = U.card-1 := by
  obtain ⟨f,hf,hi,hd,ha,hg⟩ := admissible_threeTree_active_witness hU hA
  refine ⟨basePolytope f,hi.basePolytope hf.1.1 hf.2.1,hf.minkowskiIndecomposable,?_,ha,hd⟩
  exact (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
    (hg.mono_graph (inducedOn_le G U))

/-- The complete actual-direction-support classification of Corollary 6.6.
The graph on the right is induced on its active vertices; vertices outside
it are isolated. Both implications quantify over arbitrary finite graphs. -/
theorem partial_threeTree_support_classification {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (H : SimpleGraph V) :
    (∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) ∧ actualDirectionGraph Q = H) ↔
    ∃ U : Finset V,H = inducedOn G U ∧ ThreeTreeOn U H ∧ Admissible H := by
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd,rfl⟩
    obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_polytope_support hG hQ hi hw hd
    exact ⟨U,ha,ha.symm ▸ ht,ha.symm ▸ hA⟩
  · rintro ⟨U,rfl,ht,hA⟩
    obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness ht hA
    have hU := ht.active_card_ge_four
    refine ⟨Q,?_,hi,hw,?_,ha⟩
    · exact hQ.finitePolytope
    · omega

end GraphicalZonotopes

end
end
end BundlePart134

section BundlePart135
/- Source: Papers/GraphicalZonotopes/PartialThreeTreeSpectrumGraph.lean -/






/-! # Admissible clique collections in partial 3-trees

The collections below consist of actual tetrahedra, connected by shared
triangles. Their multiplicity condition is imposed on the selected collection,
not on all tetrahedra of the ambient graph.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Admissible.mono {G H : SimpleGraph V} (hH : Admissible H) (hGH : G ≤ H) :
    Admissible G := by
  intro T hT hc
  exact (triangleMultiplicity_mono hGH T).trans
    (hH T hT (fun u hu v hv huv => hGH (hc hu hv huv)))

/-- Construction prefixes can have any requested size, and remain genuine
subgraphs of the final 3-tree. -/
theorem ThreeTreeOn.prefix {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {m : ℕ} (hm : 4 ≤ m) (hmS : m ≤ S.card) :
    ∃ T : Finset V, ∃ H : SimpleGraph V,
      T ⊆ S ∧ T.card = m ∧ H ≤ G ∧ ThreeTreeOn T H := by
  induction h generalizing m with
  | tetrahedron C hC =>
    have he : m = 4 := by omega
    exact ⟨C,cliqueGraph C,Subset.rfl,by omega,le_rfl,ThreeTreeOn.tetrahedron C hC⟩
  | @attach S G h u hu A hA hAS hcA ih =>
    by_cases hmold : m ≤ S.card
    · obtain ⟨T,H,hTS,hT,hHG,hH⟩ := ih hm hmold
      exact ⟨T,H,hTS.trans (subset_insert _ _),hT,hHG.trans le_sup_left,hH⟩
    · have he : (insert u S).card = m := by
        rw [card_insert_of_notMem hu] at hmS ⊢
        omega
      exact ⟨insert u S,G ⊔ attachmentStar u A,Subset.rfl,he,le_rfl,
        ThreeTreeOn.attach h u hu A hA hAS hcA⟩

theorem ThreeTreeOn.tetrahedronGraph_preconnected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (tetrahedronGraph (tetrahedra G)).Preconnected := by
  intro C D
  have hp := h.tetrahedra_reachable C.2 D.2
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  have hh : ∀ E, Relation.ReflTransGen (TriangleComponents.cliqueGraph G).Adj C.1 E →
      ∃ hE : E ∈ tetrahedra G,
        (tetrahedronGraph (tetrahedra G)).Reachable C ⟨E,hE⟩ := by
    intro E hE
    induction hE with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hE hEF ih =>
      obtain ⟨hEmem,hreach⟩ := ih
      have hFmem : F ∈ tetrahedra G := mem_filter.mpr
        ⟨mem_univ _,hEF.2.1,hEF.2.2.2.1⟩
      refine ⟨hFmem,hreach.trans (SimpleGraph.Adj.reachable ?_)⟩
      exact ⟨fun he => hEF.2.2.2.2.1 (congrArg Subtype.val he),hEF.2.2.2.2.2⟩
  obtain ⟨hD,hreach⟩ := hh _ hp
  exact hreach

structure IsAdmissibleCliqueCollection (G : SimpleGraph V)
    (F : Finset (Finset V)) : Prop where
  nonempty : F.Nonempty
  included : F ⊆ tetrahedra G
  connected : (tetrahedronGraph F).Preconnected
  thin : ∀ T : Finset V, T.card = 3 → (F.filter (fun C => T ⊆ C)).card ≤ 3

theorem admissibleCliqueCollection_singleton {G : SimpleGraph V} {C : Finset V}
    (hC : C ∈ tetrahedra G) : IsAdmissibleCliqueCollection G {C} := by
  refine ⟨singleton_nonempty _,singleton_subset_iff.mpr hC,?_,?_⟩
  · intro A B
    have he : A = B := by
      apply Subtype.ext
      exact (mem_singleton.mp A.2).trans (mem_singleton.mp B.2).symm
    subst B
    exact SimpleGraph.Reachable.rfl
  · intro T hT
    have hc := card_filter_le (s := ({C} : Finset (Finset V))) (p := fun D => T ⊆ D)
    simp only [card_singleton] at hc
    omega

theorem ThreeTreeOn.admissibleCliqueCollection {S : Finset V} {H G : SimpleGraph V}
    (h : ThreeTreeOn S H) (hA : Admissible H) (hHG : H ≤ G) :
    IsAdmissibleCliqueCollection G (tetrahedra H) := by
  refine ⟨h.tetrahedra_nonempty,tetrahedra_mono hHG,h.tetrahedronGraph_preconnected,?_⟩
  intro T hT
  by_cases hc : H.IsClique T
  · exact hA T hT hc
  · have he : (tetrahedra H).filter (fun C => T ⊆ C) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro C hC
      obtain ⟨hC,hTC⟩ := mem_filter.mp hC
      have hcl := (mem_filter.mp hC).2.2
      exact hc (fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv)
    rw [he,card_empty]
    omega

theorem IsAdmissibleCliqueCollection.four {G : SimpleGraph V}
    {F : Finset (Finset V)} (hF : IsAdmissibleCliqueCollection G F) :
    ∀ C ∈ F, C.card = 4 ∧ G.IsClique C := by
  intro C hC
  exact (mem_filter.mp (hF.included hC)).2

/-- In a partial 3-tree a connected collection already contains every
tetrahedron induced on its union. There are no hidden extra clique nodes. -/
theorem IsAdmissibleCliqueCollection.induced_structure {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) {F : Finset (Finset V)}
    (hF : IsAdmissibleCliqueCollection G F) :
    ThreeTreeOn (F.biUnion id) (inducedOn G (F.biUnion id)) ∧
      tetrahedra (inducedOn G (F.biUnion id)) = F ∧
      Admissible (inducedOn G (F.biUnion id)) ∧
      (F.biUnion id).card = F.card + 3 := by
  let U := F.biUnion id
  have ht := hG.connected_family_threeTree F hF.nonempty hF.four hF.connected
  have hsub : F ⊆ tetrahedra (inducedOn G U) := by
    intro C hC
    refine mem_filter.mpr ⟨mem_univ _,(hF.four C hC).1,?_⟩
    intro u hu v hv huv
    exact ⟨(hF.four C hC).2 hu hv huv,
      mem_biUnion.mpr ⟨C,hC,hu⟩,mem_biUnion.mpr ⟨C,hC,hv⟩⟩
  have hu := connected_tetrahedra_union_card F hF.nonempty
    (fun C hC => (hF.four C hC).1) hF.connected
  have hfour : 4 ≤ U.card := ht.active_card_ge_four
  have hcard : (tetrahedra (inducedOn G U)).card = U.card - 3 := ht.tetrahedra_card
  have he : tetrahedra (inducedOn G U) = F := by
    apply (eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard]
    change U.card ≤ F.card + 3 at hu
    omega
  refine ⟨ht,he,?_,?_⟩
  · intro T hT hc
    change ((tetrahedra (inducedOn G U)).filter (fun C => T ⊆ C)).card ≤ 3
    rw [he]
    exact hF.thin T hT
  · rw [he] at hcard
    change U.card = F.card + 3
    omega

def admissibleCliqueCollections (G : SimpleGraph V) : Finset (Finset (Finset V)) := by
  classical
  exact univ.filter (IsAdmissibleCliqueCollection G)

/-- The invariant M(G) of Corollaries 6.7 and 6.8. -/
def maximumAdmissibleCliqueCount (G : SimpleGraph V) : ℕ :=
  (admissibleCliqueCollections G).sup Finset.card

theorem admissibleClique_count_le_maximum {G : SimpleGraph V} {F : Finset (Finset V)}
    (hF : IsAdmissibleCliqueCollection G F) : F.card ≤ maximumAdmissibleCliqueCount G := by
  apply le_sup
  exact mem_filter.mpr ⟨mem_univ _,hF⟩

theorem maximumAdmissibleCliqueCount_attained {G : SimpleGraph V}
    (hG : (tetrahedra G).Nonempty) :
    ∃ F : Finset (Finset V), IsAdmissibleCliqueCollection G F ∧
      F.card = maximumAdmissibleCliqueCount G := by
  obtain ⟨C,hC⟩ := hG
  have hne : (admissibleCliqueCollections G).Nonempty :=
    ⟨{C},mem_filter.mpr ⟨mem_univ _,admissibleCliqueCollection_singleton hC⟩⟩
  obtain ⟨F,hF,hmax⟩ := (admissibleCliqueCollections G).exists_max_image Finset.card hne
  have hf := (mem_filter.mp hF).2
  refine ⟨F,hf,le_antisymm (admissibleClique_count_le_maximum hf) ?_⟩
  exact Finset.sup_le_iff.mpr hmax

end GraphicalZonotopes

end
end
end BundlePart135

section BundlePart136
/- Source: Papers/GraphicalZonotopes/PartialThreeTreeSpectrum.lean -/




/-! # Dimension maxima and all intermediate dimensions in partial 3-trees

These are the mathematical assertions in Corollaries 6.7 and 6.8. The
algorithmic running-time assertion is not encoded by these theorems.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- A simplex on any actual clique is a lattice indecomposable weak summand.
The affine dimension is the clique size minus one in the full ambient space. -/
theorem clique_simplex_witness {G : SimpleGraph V} {C : Finset V}
    (hC : 2 ≤ C.card) (hcl : G.IsClique C) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = C.card-1 := by
  let e₀ := (Fintype.equivFin C).symm
  let e : Fin (Fintype.card C) ↪ V := e₀.toEmbedding.trans
    ⟨Subtype.val,Subtype.val_injective⟩
  let f : SetFunction (Fin (Fintype.card C)) := setMonomial univ
  have hcard : 2 ≤ Fintype.card C := by simpa only [Fintype.card_coe] using hC
  have hf : ExtremeSupermodular f := setMonomial_extreme (by simpa only [card_univ,
    Fintype.card_fin] using hcard)
  have hfi : IntegerValued f := by
    intro S
    by_cases hs : (univ : Finset (Fin (Fintype.card C))) ⊆ S
    · exact ⟨1,by simp [f,setMonomial,hs]⟩
    · exact ⟨0,by simp [f,setMonomial,hs]⟩
  have hg : Graphical (G.comap e) f := by
    apply (setMonomial_graphical univ).mono_graph
    intro u v huv
    exact hcl (e₀ u).2 (e₀ v).2 (fun he => huv.1 (e.injective he))
  have hext : ExtremeSupermodular (extend e f) := extend_extreme e hf
  have hdim := complete_simplex_fullDimension hcard
  refine ⟨basePolytope (extend e f),(extend_integer e hfi).basePolytope hext.1.1 hext.2.1,
    hext.minkowskiIndecomposable,?_,?_⟩
  · exact (isWeakMinkowskiSummand_graphical_iff hext.1.1 hext.2.1).mpr (extend_graphical e hg)
  · rw [finrank_vectorSpan_extend e hf.1]
    simpa only [FullDimension,Fintype.card_fin,Fintype.card_coe] using hdim

theorem partial_threeTree_dimension_le_clique_count {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ maximumAdmissibleCliqueCount G+2 := by
  by_cases hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q)
  · obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_polytope_support hG hQ hi hw hd
    have hF := ht.admissibleCliqueCollection hA (inducedOn_le G U)
    have hb := admissibleClique_count_le_maximum hF
    rw [ht.tetrahedra_card] at hb
    omega
  · omega

/-- The maximum admissible clique collection gives an actual lattice witness
for the supremum defining the dimension invariant. -/
theorem partial_threeTree_maximum_witness {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : (tetrahedra G).Nonempty) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = maximumAdmissibleCliqueCount G+2 := by
  obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
  obtain ⟨ht,he,hA,hcard⟩ := hF.induced_structure hG
  obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness ht hA
  exact ⟨Q,hQ,hi,hw,by omega⟩

theorem partial_threeTree_maximum_dimension {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : (tetrahedra G).Nonempty) :
    maximumIndecomposableDimension G = maximumAdmissibleCliqueCount G+2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact partial_threeTree_dimension_le_clique_count hG hQ hi hw
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := partial_threeTree_maximum_witness hG hK
    rw [← hd]
    exact dimension_le_maximum hQ.finitePolytope hi hw

/-- Every positive integer through the sharp maximum occurs, with no gap and
with a lattice representative. The construction uses an arbitrary prefix of
a maximizing admissible three-tree and actual clique simplices at dimensions
one and two. -/
theorem partial_threeTree_dimension_spectrum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : (tetrahedra G).Nonempty)
    (d : ℕ) (hd : 1 ≤ d) (hdM : d ≤ maximumAdmissibleCliqueCount G+2) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hd3 : 3 ≤ d
  · obtain ⟨F,hF,hmax⟩ := maximumAdmissibleCliqueCount_attained hK
    obtain ⟨ht,he,hA,hcard⟩ := hF.induced_structure hG
    obtain ⟨U,H,hU,hcardU,hH,htH⟩ := ht.prefix (m := d+1) (by omega) (by omega)
    have hHA : Admissible H := hA.mono hH
    obtain ⟨f,hf,hfi,hfd,hfa,hfg⟩ := admissible_threeTree_active_witness htH hHA
    refine ⟨basePolytope f,hfi.basePolytope hf.1.1 hf.2.1,hf.minkowskiIndecomposable,?_,?_⟩
    · exact (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
        (hfg.mono_graph (hH.trans (inducedOn_le G _)))
    · omega
  · obtain ⟨C,hC⟩ := hK
    obtain ⟨hfour,hcl⟩ := (mem_filter.mp hC).2
    obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq (s := C) (n := d+1) (by omega)
    obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness
      (by omega : 2 ≤ D.card) (fun u hu v hv huv => hcl (hDC hu) (hDC hv) huv)
    exact ⟨Q,hQ,hi,hw,by omega⟩

/-- Corollary 6.7's exact dimension and full positive spectrum. Algorithmic
complexity is a separate assertion and is not hidden in this statement. -/
theorem threeTree_dimension_and_spectrum {G : SimpleGraph V} (hG : IsThreeTree G) :
    maximumIndecomposableDimension G = maximumAdmissibleCliqueCount G+2 ∧
      ∀ d : ℕ,1 ≤ d → d ≤ maximumAdmissibleCliqueCount G+2 →
        ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
          IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
          Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  have hp : IsPartialThreeTree G := Or.inr ⟨G,hG,le_rfl⟩
  exact ⟨partial_threeTree_maximum_dimension hp hG.tetrahedra_nonempty,
    partial_threeTree_dimension_spectrum hp hG.tetrahedra_nonempty⟩

end GraphicalZonotopes

end
end
end BundlePart136

section BundlePart137
/- Source: Papers/GraphicalZonotopes/PolytopalDimension.lean -/




/-! # Dimension invariants with the paper's polytopal convention -/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The dimension supremum is unchanged when indecomposability is defined
using only finite polytopal Minkowski decompositions, as in the paper. -/
theorem maximumIndecomposableDimension_eq_polytopal_supremum (G : SimpleGraph V) :
    maximumIndecomposableDimension G =
      sSup {d : ℕ | ∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q)=d} := by
  unfold maximumIndecomposableDimension
  congr 1
  ext d
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hw,hd⟩
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi,hw,hd⟩

theorem supportsFullIndecomposable_iff_polytopal_weak (G : SimpleGraph V) :
    SupportsFullIndecomposable G ↔
      ∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hd,hw⟩
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi,hd,hw⟩

end GraphicalZonotopes

end
end
end BundlePart137

section BundlePart138
/- Source: Papers/GraphicalZonotopes/TreeJoinDimension.lean -/







/-! # Corollary 6.9: the join of K₂ with an arbitrary finite tree

The maximum is over actual finite polytopes in the ambient coordinate space.
Every nonempty tree is covered, including the one-vertex tree. The invariant
s₃ counts vertices in ordinary connected subtrees of maximum degree three;
the equivalence of induced and arbitrary subtree presentations is proved in
TreeJoinSubtrees. The lower bound supplies an actual lattice witness.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.TreeJoin
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def vertexOrder (V : Type*) [Fintype V] [DecidableEq V] : LinearOrder (Vertex V) :=
  let o : LinearOrder (Vertex V) :=
    LinearOrder.lift' (Fintype.equivFin (Vertex V)) (Fintype.equivFin (Vertex V)).injective
  { o with
    toDecidableEq := inferInstance
    compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
    compare_eq_compareOfLessAndEq := by intros; rfl }

local instance : LinearOrder (Vertex V) := vertexOrder V
local instance : DecidableEq (Vertex V) := (vertexOrder V).toDecidableEq

theorem isPartialThreeTree {T : SimpleGraph V} (hT : T.IsTree) :
    IsPartialThreeTree (graph T) := by
  by_cases hn : 2≤ Fintype.card V
  · exact Or.inr ⟨graph T,isThreeTree hT hn,le_rfl⟩
  · apply Or.inl
    simp only [Vertex,Fintype.card_sum,Fintype.card_fin]
    omega

theorem summand_dimension_le {T : SimpleGraph V} (hT : T.IsTree)
    {Q : Set (Vertex V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (graph T))) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤ s3 T+1 := by
  letI : Nonempty V := hT.connected.nonempty
  by_cases hd : 3≤ Module.finrank ℝ (vectorSpan ℝ Q)
  · obtain ⟨S,hcard,hactual,hS,hA,hD⟩ :=
      partial_threeTree_polytope_support (isPartialThreeTree hT) hQ hi hw hd
    obtain ⟨U,hSU,hn,ht,hm⟩ := induced_admissible_subtree hT.isAcyclic hS hA
    have hU := subtree_card_le_s3 ht hm
    rw [hSU,core_card] at hD
    omega
  · have hp := s3_pos T
    omega

theorem lattice_attainment {T : SimpleGraph V} (hT : T.IsTree) :
    ∃ Q : Set (Vertex V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=s3 T+1 := by
  letI : Nonempty V := hT.connected.nonempty
  obtain ⟨U,ht,hm,hU⟩ := s3_attained T
  by_cases hn : 2≤ U.card
  · have htr := (induced_core_threeTree_iff hT.isAcyclic U hn).mpr ht
    have hA := (induced_core_admissible_iff hT.isAcyclic U).mpr hm
    obtain ⟨Q,hQ,hi,hw,ha,hd⟩ := induced_admissible_threeTree_witness htr hA
    refine ⟨Q,hQ,hi,hw,?_⟩
    rw [core_card,hU] at hd
    omega
  · have hpos := s3_pos T
    have hcard : U.card=1 := by omega
    obtain ⟨v,hv⟩ := card_eq_one.mp hcard
    have hc : (graph T).IsClique (core U) := by
      apply (core_clique_iff T U).mpr
      rw [hv]
      simp [SimpleGraph.isClique_singleton]
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness
      (by rw [core_card]; omega : 2≤(core U).card) hc
    refine ⟨Q,hQ,hi,hw,?_⟩
    rw [core_card,hU] at hd
    omega

theorem maximum_dimension {T : SimpleGraph V} (hT : T.IsTree) :
    maximumIndecomposableDimension (graph T)=s3 T+1 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [←hd]
    exact summand_dimension_le hT hQ hi hw
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := lattice_attainment hT
    have h := dimension_le_maximum hQ.finitePolytope hi hw
    rwa [hd] at h

theorem supports_full_iff {T : SimpleGraph V} (hT : T.IsTree) :
    SupportsFullIndecomposable (graph T) ↔ T.maxDegree≤3 := by
  constructor
  · rintro ⟨Q,hQ,hi,hd,hw⟩
    have h := summand_dimension_le hT hQ hi hw
    have hbound := s3_le_card T
    change Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card (Vertex V)-1 at hd
    simp only [Vertex,Fintype.card_sum,Fintype.card_fin] at hd
    have hdim : Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card V+1 := by
      simpa only [Nat.add_sub_cancel] using hd
    rw [hdim] at h
    exact (s3_eq_card_iff hT).mp
      (le_antisymm hbound (Nat.le_of_add_le_add_right h))
  · intro h
    have he := (s3_eq_card_iff hT).mpr h
    obtain ⟨Q,hQ,hi,hw,hd⟩ := lattice_attainment hT
    refine ⟨Q,hQ.finitePolytope,hi,?_,hw⟩
    change Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card (Vertex V)-1
    simp only [Vertex,Fintype.card_sum,Fintype.card_fin]
    rw [hd,he]
    omega

/-- The complete K₂*tree portion of Corollary 6.9, with the paper's ordinary
polytopal indecomposability convention and lattice attainment of the maximum. -/
theorem paper_corollary_6_9_tree_join (T : SimpleGraph V) (hT : T.IsTree) :
    (sSup {d : ℕ | ∃ Q : Set (Vertex V → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d})=s3 T+1 ∧
    ((∃ Q : Set (Vertex V → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T))) ↔ T.maxDegree≤3) ∧
    ∃ Q : Set (Vertex V → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=s3 T+1 := by
  refine ⟨?_,?_,?_⟩
  · rw [←maximumIndecomposableDimension_eq_polytopal_supremum]
    exact maximum_dimension hT
  · rw [←supportsFullIndecomposable_iff_polytopal_weak]
    exact supports_full_iff hT
  · obtain ⟨Q,hQ,hi,hw,hd⟩ := lattice_attainment hT
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,hw,hd⟩

end GraphicalZonotopes.TreeJoin

end
end
end BundlePart138

section BundlePart139
/- Source: Papers/GraphicalZonotopes/LatticeExtremeEmbedding.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- An actual integral extreme graphical set function with exact dimension
and a uniform integral elemental-slack bound. -/
def LatticeExtremeAt (G : SimpleGraph V) (d M : ℕ) : Prop :=
  ∃ f : SetFunction V,TranslationNormalized f ∧ IntegerValued f ∧
    ExtremeSupermodular f ∧ Graphical G f ∧
    Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=d ∧
    ∀ u v,u≠ v → ∀ S,u∉S → v∉S → delta f u v S≤(M : ℝ)

theorem LatticeExtremeAt.of_lattice_complement {G : SimpleGraph V} {f : SetFunction V}
    (hn : TranslationNormalized f) (hi : IntegerValued f) (he : ExtremeSupermodular f)
    (hG : Graphical G f) {d M : ℕ} (hd : Module.finrank ℝ (vectorSpan ℝ (basePolytope f))=d)
    {R : Set (V → ℝ)} (hR : LatticePolytope R) (hRn : R.Nonempty)
    (hsum : basePolytope f+R=(M : ℝ) • graphicalZonotope G) : LatticeExtremeAt G d M := by
  have hsummand : IsMinkowskiSummand (basePolytope f) ((M : ℝ) • graphicalZonotope G) :=
    ⟨R,hR.compact,hR.convex,hRn,hsum⟩
  have hb := ((isMinkowskiSummand_graphical_iff hn.1 he.2.1 (Nat.cast_nonneg M)).mp hsummand).2
  refine ⟨f,hn,hi,he,hG,hd,?_⟩
  intro u v huv S hu hv
  by_cases hedge : G.Adj u v
  · exact hb u v huv hedge S hu hv
  · rw [hG u v huv hedge S hu hv]
    exact Nat.cast_nonneg M

theorem LatticeExtremeAt.mono_dilation {G : SimpleGraph V} {d M N : ℕ}
    (h : LatticeExtremeAt G d M) (hMN : M≤ N) : LatticeExtremeAt G d N := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  exact ⟨f,hn,hi,he,hG,hd,fun u v huv S hu hv =>
    (hb u v huv S hu hv).trans (by exact_mod_cast hMN)⟩

theorem LatticeExtremeAt.embed {G : SimpleGraph V} {H : SimpleGraph W}
    {d M : ℕ} (h : LatticeExtremeAt G d M) (e : V ↪ W) (hGH : G≤ H.comap e) :
    LatticeExtremeAt H d M := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  let g := SetFunctionEmbedding.extend e f
  refine ⟨g,SetFunctionEmbedding.extend_translationNormalized e hn,
    SetFunctionEmbedding.extend_integer e hi,SetFunctionEmbedding.extend_extreme e he,
    SetFunctionEmbedding.extend_graphical e (hG.mono_graph hGH),?_,?_⟩
  · rw [SetFunctionEmbedding.finrank_vectorSpan_extend e hn]
    exact hd
  · intro u v huv S hu hv
    by_cases huR : u∈Set.range e
    · obtain ⟨a,rfl⟩ := huR
      by_cases hvR : v∈Set.range e
      · obtain ⟨b,rfl⟩ := hvR
        rw [SetFunctionEmbedding.delta_extend]
        exact hb a b (fun h => huv (congrArg e h)) _
          (by simpa using hu) (by simpa using hv)
      · rw [delta_comm,SetFunctionEmbedding.delta_extend_not_range e f v (e a) hvR]
        exact Nat.cast_nonneg M
    · rw [SetFunctionEmbedding.delta_extend_not_range e f u v huR]
      exact Nat.cast_nonneg M

theorem LatticeExtremeAt.polytope {G : SimpleGraph V} {d M : ℕ}
    (h : LatticeExtremeAt G d M) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d ∧
      IsMinkowskiSummand Q ((M : ℝ) • graphicalZonotope G) := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  exact ⟨basePolytope f,hi.basePolytope hn.1 he.2.1,he.minkowskiIndecomposable,hd,
    (isMinkowskiSummand_graphical_iff hn.1 he.2.1 (Nat.cast_nonneg M)).mpr
      ⟨hG,fun u v huv _ S hu hv => hb u v huv S hu hv⟩⟩

theorem LatticeExtremeAt.dimension_le_maximum {G : SimpleGraph V} {d M : ℕ}
    (h : LatticeExtremeAt G d M) : d≤ maximumIndecomposableDimension G := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  rw [← hd]
  exact GraphicalZonotopes.dimension_le_maximum (show IsGeneralizedPermutahedron (basePolytope f) from ⟨f,hn.1,he.2.1,rfl⟩).finitePolytope
    he.minkowskiIndecomposable ((isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG)

theorem LatticeExtremeAt.supports_full {G : SimpleGraph V} {M : ℕ}
    (h : LatticeExtremeAt G (Fintype.card V-1) M) : SupportsFullIndecomposable G := by
  obtain ⟨f,hn,hi,he,hG,hd,hb⟩ := h
  exact ⟨basePolytope f,(show IsGeneralizedPermutahedron (basePolytope f) from ⟨f,hn.1,he.2.1,rfl⟩).finitePolytope,
    he.minkowskiIndecomposable,hd,(isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG⟩

end GraphicalZonotopes

end
end
end BundlePart139

section BundlePart140
/- Source: Papers/GraphicalZonotopes/BookEmbeddings.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators

/-- Promoting one outer vertex to a hub preserves all existing edges. -/
def bookPromote (s k : ℕ) : (Fin s⊕Fin (k+1)) ≃ (Fin (s+1)⊕Fin k) where
  toFun
    | .inl i => .inl i.succ
    | .inr j => Fin.cases (.inl 0) (fun i => .inr i) j
  invFun
    | .inl i => Fin.cases (.inr 0) (fun j => .inl j) i
    | .inr j => .inr j.succ
  left_inv x := by
    cases x with
    | inl i => rfl
    | inr j => exact Fin.cases rfl (fun _ => rfl) j
  right_inv x := by
    cases x with
    | inl i => exact Fin.cases rfl (fun _ => rfl) i
    | inr j => rfl

theorem bookPromote_edges (s k : ℕ) :
    cliqueBook s (k+1)≤(cliqueBook (s+1) k).comap (bookPromote s k) := by
  intro u v h
  change u≠ v ∧ (u.isLeft ∨ v.isLeft) at h
  change (bookPromote s k u)≠(bookPromote s k v) ∧
    ((bookPromote s k u).isLeft ∨ (bookPromote s k v).isLeft)
  have hleft : ∀ x : Fin s⊕Fin (k+1),x.isLeft → (bookPromote s k x).isLeft := by
    intro x hx
    cases x with
    | inl i => rfl
    | inr j => exact False.elim (by simpa using hx)
  exact ⟨fun he => h.1 ((bookPromote s k).injective he),h.2.elim
    (fun hu => Or.inl (hleft u hu)) (fun hv => Or.inr (hleft v hv))⟩

def bookOuterEmbedding (s : ℕ) {k l : ℕ} (hkl : k≤ l) : (Fin s⊕Fin k) ↪ (Fin s⊕Fin l) :=
  Function.Embedding.sumMap (Function.Embedding.refl _) (Fin.castLEEmb hkl)

theorem bookOuterEmbedding_edges (s : ℕ) {k l : ℕ} (hkl : k≤ l) :
    cliqueBook s k≤(cliqueBook s l).comap (bookOuterEmbedding s hkl) := by
  intro u v h
  change u≠ v ∧ (u.isLeft ∨ v.isLeft) at h
  change (bookOuterEmbedding s hkl u)≠(bookOuterEmbedding s hkl v) ∧
    ((bookOuterEmbedding s hkl u).isLeft ∨ (bookOuterEmbedding s hkl v).isLeft)
  constructor
  · exact fun he => h.1 ((bookOuterEmbedding s hkl).injective he)
  · cases u <;> cases v <;> simpa [bookOuterEmbedding] using h.2

theorem book_lattice_promote {s k M : ℕ}
    (h : LatticeExtremeAt (cliqueBook s (k+1)) (s+(k+1)-1) M) :
    LatticeExtremeAt (cliqueBook (s+1) k) (s+1+k-1) M := by
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
    h.embed (bookPromote s k).toEmbedding (bookPromote_edges s k)

theorem book_lattice_add_outer {s k l M : ℕ} (hkl : k≤ l)
    (h : LatticeExtremeAt (cliqueBook s k) (s+k-1) M) :
    LatticeExtremeAt (cliqueBook s l) (s+k-1) M :=
  h.embed (bookOuterEmbedding s hkl) (bookOuterEmbedding_edges s hkl)

end GraphicalZonotopes

end
end
end BundlePart140

section BundlePart141
/- Source: Papers/GraphicalZonotopes/BooleanResponseQuotient.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

/-- The paper's rows are unordered hub pairs, each with every conditioning
subset of the remaining hubs. `BoundaryContext` uses the increasing ordering
only to select one representative of each unordered pair. -/
abbrev HubResponseRow (H : Type*) [Fintype H] [LinearOrder H] :=
  BoundaryContext (⊤ : SimpleGraph H)

def centralSlack : graphicalFunctionSpace (⊤ : SimpleGraph H) →ₗ[ℝ]
    (HubResponseRow H → ℝ) := boundarySlackMap ⊤

/-- This is literally the elemental map from all central Möbius coefficients,
including every subset of size at least two. -/
def centralCoefficientSlack : (CliqueIndex (⊤ : SimpleGraph H) → ℝ) →ₗ[ℝ]
    (HubResponseRow H → ℝ) :=
  centralSlack ∘ₗ (graphicalCoordinatesEquiv ⊤).toLinearMap

theorem centralSlack_injective : Function.Injective (centralSlack (H:=H)) :=
  boundarySlackMap_injective ⊤

theorem centralCoefficientSlack_injective :
    Function.Injective (centralCoefficientSlack (H:=H)) :=
  centralSlack_injective.comp (graphicalCoordinatesEquiv ⊤).injective

theorem centralCoefficientSlack_range :
    LinearMap.range (centralCoefficientSlack (H:=H))=
      LinearMap.range (centralSlack (H:=H)) := by
  apply le_antisymm
  · rintro x ⟨c,rfl⟩
    exact ⟨graphicalCoordinatesEquiv ⊤ c,rfl⟩
  · rintro x ⟨z,rfl⟩
    exact ⟨(graphicalCoordinatesEquiv ⊤).symm z,by
      simp only [centralCoefficientSlack,LinearMap.comp_apply,
        LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]⟩

def responseVector (F : SetFunction H) : HubResponseRow H → ℝ :=
  fun r => negativeResponse F r.1.1.1 r.1.1.2 r.2.1

def weightedResponse (F : J → SetFunction H) :
    (J → ℝ) →ₗ[ℝ] (HubResponseRow H → ℝ) where
  toFun w r := ∑ j : J,w j*responseVector (F j) r
  map_add' w t := by ext r; simp [add_mul,sum_add_distrib]
  map_smul' c w := by ext r; simp [mul_assoc,mul_sum]

/-- The complete relation map in the actual response quotient. Its kernel
contains all real relations among the classes, not merely positive ones. -/
def quotientRelation (F : J → SetFunction H) :
    (J → ℝ) →ₗ[ℝ]
      ((HubResponseRow H → ℝ) ⧸ LinearMap.range (centralCoefficientSlack (H:=H))) :=
  (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ ∘ₗ weightedResponse F

theorem negativeResponse_comm (F : SetFunction H) (u v : H) (S : Finset H) :
    negativeResponse F u v S=negativeResponse F v u S := by
  simp only [negativeResponse,delta_comm u v]

theorem central_function {z : SetFunction H} (hz : TranslationNormalized z) :
    z∈graphicalFunctionSpace (⊤ : SimpleGraph H) := by
  refine ⟨hz,?_⟩
  intro u v huv hnon S hu hv
  exact False.elim (hnon ((SimpleGraph.top_adj u v).mpr huv))

theorem remaining_subset_commonNeighbors (u v : H) (S : Finset H)
    (hu : u∉S) (hv : v∉S) : S⊆commonNeighbors (⊤ : SimpleGraph H) u v := by
  intro a ha
  apply (mem_commonNeighbors _ _ _ _).mpr
  constructor
  · apply (SimpleGraph.top_adj u a).mpr
    intro he
    exact hu (he.symm ▸ ha)
  · apply (SimpleGraph.top_adj v a).mpr
    intro he
    exact hv (he.symm ▸ ha)

/-- Quantifying over the row type is equivalent to quantifying over every
actual elemental difference, with no context omitted. -/
theorem compatible_iff_rows {z : SetFunction H} (hz : TranslationNormalized z)
    (F : J → SetFunction H) (w : J → ℝ) :
    Compatible z F w ↔
      centralSlack ⟨z,central_function hz⟩=weightedResponse F w := by
  constructor
  · intro hc
    funext r
    have hu : r.1.1.1∉r.2.1 := by
      intro hm
      exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
    have hv : r.1.1.2∉r.2.1 := by
      intro hm
      exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) hm)
    exact hc _ _ (ne_of_lt r.1.2.1) _ hu hv
  · intro he u v huv S hu hv
    have hordered : ∀ a b,a< b → a∉S → b∉S →
        delta z a b S=∑ j : J,w j*negativeResponse (F j) a b S := by
      intro a b hab ha hb
      let e : OrientedEdge (⊤ : SimpleGraph H):=
        ⟨(a,b),hab,(SimpleGraph.top_adj a b).mpr (ne_of_lt hab)⟩
      let r : HubResponseRow H:=⟨e,⟨S,mem_powerset.mpr
        (remaining_subset_commonNeighbors a b S ha hb)⟩⟩
      exact congrFun he r
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · exact hordered u v hlt hu hv
    · rw [delta_comm u v,hordered v u hgt hv hu]
      apply sum_congr rfl
      intro j hj
      rw [negativeResponse_comm (F j) v u]

theorem mem_quotientRelation_ker_iff (F : J → SetFunction H) (w : J → ℝ) :
    w∈LinearMap.ker (quotientRelation F) ↔
      ∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z F w := by
  change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ
      (weightedResponse F w)=0 ↔ _
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ,centralCoefficientSlack_range]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨z.1,z.2.1,(compatible_iff_rows z.2.1 F w).mpr hz⟩
  · rintro ⟨z,hz,hc⟩
    exact ⟨⟨z,central_function hz⟩,(compatible_iff_rows hz F w).mp hc⟩

/-- The basis-free compatibility formulation used in the zero-equation proof
is exactly the paper's one-dimensional quotient relation condition. -/
theorem uniqueIntegrableRelation_iff_ker_eq_span
    (F : J → SetFunction H) (w : J → ℝ)
    (hw : ∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z F w) :
    UniqueIntegrableRelation F w ↔
      LinearMap.ker (quotientRelation F)=Submodule.span ℝ {w} := by
  have hwm : w∈LinearMap.ker (quotientRelation F):=
    (mem_quotientRelation_ker_iff F w).mpr hw
  constructor
  · intro huniq
    apply le_antisymm
    · intro t ht
      obtain ⟨c,hc⟩:=huniq t ((mem_quotientRelation_ker_iff F t).mp ht)
      exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
    · apply Submodule.span_le.mpr
      intro t ht
      have he : t=w := Set.mem_singleton_iff.mp ht
      subst t
      exact hwm
  · intro hker t ht
    have hm:=(mem_quotientRelation_ker_iff F t).mpr ht
    rw [hker,Submodule.mem_span_singleton] at hm
    obtain ⟨c,hc⟩:=hm
    exact ⟨c,hc.symm⟩

/-- Literal positive-circuit extremality: the relation space is the kernel of
the map to the quotient by the central Möbius image. -/
theorem positive_quotient_circuit_extreme [Nonempty J]
    {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0< w j) (hc : Compatible z F w)
    (hd : Module.finrank ℝ (LinearMap.ker (quotientRelation F))=1) :
    ExtremeSupermodular (assembled z F w) := by
  obtain ⟨j₀⟩:=‹Nonempty J›
  have hne : w≠0 := by
    intro he
    have hj:=hw j₀
    rw [he] at hj
    simp at hj
  have hm : w∈LinearMap.ker (quotientRelation F):=
    (mem_quotientRelation_ker_iff F w).mpr ⟨z,hz,hc⟩
  have hker:=eq_span_singleton_of_mem_of_finrank_eq_one hd hm hne
  exact positive_circuit_extreme hz hF (fun j => (hw j).le)
    ⟨j₀,ne_of_gt (hw j₀)⟩ hc
    ((uniqueIntegrableRelation_iff_ker_eq_span F w ⟨z,hz,hc⟩).mpr hker)

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart141

section BundlePart142
/- Source: Papers/GraphicalZonotopes/BookModuleGeometry.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

/-- An essential Boolean variable is witnessed by an actual cover with
increment one. For a monotone zero-one function this is ordinary dependence
on that variable. -/
def Essential (F : SetFunction H) (a : H) : Prop :=
  ∃ X : Finset H,a∉X ∧ F (insert a X)-F X=1

def essentialSpokeGraph (F : J → SetFunction H) : SimpleGraph (H⊕J) where
  Adj
    | Sum.inl a,Sum.inr j => Essential (F j) a
    | Sum.inr j,Sum.inl a => Essential (F j) a
    | _,_ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> exact not_false⟩

theorem essentialSpokeGraph_connected [Nonempty H] [Nonempty J]
    (F : J → SetFunction H) (hF : ∀ j a,Essential (F j) a) :
    (essentialSpokeGraph F).Connected := by
  obtain ⟨a₀⟩:=‹Nonempty H›
  obtain ⟨j₀⟩:=‹Nonempty J›
  have hcross : ∀ a j,(essentialSpokeGraph F).Adj (Sum.inl a) (Sum.inr j):=
    fun a j => hF j a
  refine ⟨?_⟩
  intro x y
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      exact (hcross a j₀).reachable.trans (hcross b j₀).reachable.symm
    | inr j => exact (hcross a j).reachable
  | inr i =>
    cases y with
    | inl a => exact (hcross a i).reachable.symm
    | inr j =>
      exact (hcross a₀ i).reachable.symm.trans (hcross a₀ j).reachable

theorem essential_spoke_slack {z : SetFunction H} {F : J → SetFunction H}
    {w : J → ℝ} (hw : ∀ j,0< w j) {a b : H⊕J}
    (hab : (essentialSpokeGraph F).Adj a b) :
    ∃ A : Finset (H⊕J),a∉A ∧ b∉A ∧ delta (assembled z F w) a b A≠0 := by
  cases a with
  | inl u =>
    cases b with
    | inl v => exact False.elim hab
    | inr j =>
      obtain ⟨X,hu,hX⟩:=hab
      refine ⟨hubSet X,by simpa using hu,by simp,?_⟩
      rw [delta_assembled_spoke _ _ _ _ _ _ (by simp),hubs_hubSet,hX,mul_one]
      exact ne_of_gt (hw j)
  | inr i =>
    cases b with
    | inl v =>
      obtain ⟨X,hv,hX⟩:=hab
      refine ⟨hubSet X,by simp,by simpa using hv,?_⟩
      rw [delta_swap,delta_assembled_spoke _ _ _ _ _ _ (by simp),hubs_hubSet,hX,mul_one]
      exact ne_of_gt (hw i)
    | inr j => exact False.elim hab

/-- The dimension clause of Lemma7.3 uses the genuine connected spanning
essential-spoke graph, so ignored variables remain present in the ambient
coordinate space and cannot disappear silently. -/
theorem assembled_fullDimension {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0< w j) (hc : Compatible z F w)
    (hconn : (essentialSpokeGraph F).Connected) :
    FullDimension (basePolytope (assembled z F w)) := by
  apply finrank_vectorSpan_eq_of_connected_slacks (assembled_normalized hz F hF w).1
    (assembled_supermodular z F hF w (fun j => (hw j).le) hc) hconn
  intro a b hab
  exact essential_spoke_slack hw hab

theorem assembled_delta_le_weight_sum {z : SetFunction H}
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0≤ w j) (hc : Compatible z F w)
    (a b : H⊕J) (hab : a≠ b) (A : Finset (H⊕J)) (ha : a∉A) (hb : b∉A) :
    delta (assembled z F w) a b A≤∑ j : J,w j := by
  have hsum : 0≤∑ j : J,w j:=sum_nonneg (fun j _ => hw j)
  have hspoke : ∀ u j,Sum.inr j∉A →
      delta (assembled z F w) (Sum.inl u) (Sum.inr j) A≤∑ i : J,w i := by
    intro u j hj
    rw [delta_assembled_spoke _ _ _ _ _ _ hj]
    have hcover : F j (insert u (hubs A))-F j (hubs A)≤1 := by
      rcases cover_values (hF j) u (hubs A) with h | h <;> simp [h]
    exact (mul_le_mul_of_nonneg_left hcover (hw j)).trans
      (by simpa using single_le_sum (fun i _ => hw i) (mem_univ j))
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      rw [assembled_factorization z F w hc u v (fun he => hab (congrArg Sum.inl he)) A ha hb]
      apply sum_le_sum
      intro j hj
      have hx : (if Sum.inr j∈A then (1 : ℝ) else 0)=0 ∨
          (if Sum.inr j∈A then (1 : ℝ) else 0)=1 := by split_ifs <;> simp
      have hle : negativeResponse (F j) u v (hubs A)+
          (if Sum.inr j∈A then 1 else 0)*delta (F j) u v (hubs A)≤1 := by
        rcases response_factor_values (hF j) u v (hubs A) _ hx with h | h <;> rw [h] <;> norm_num
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (hw j)
    | inr j => exact hspoke u j hb
  | inr i =>
    cases b with
    | inl v => rw [delta_swap]; exact hspoke v i ha
    | inr j =>
      rw [delta_assembled_outer _ _ _ _ _ (fun he => hab (congrArg Sum.inr he)) _ ha hb]
      exact hsum

theorem IsMonotoneBoolean.integerValued {F : SetFunction H} (hF : IsMonotoneBoolean F) :
    IntegerValued F := by
  intro X
  rcases hF.values X with h | h
  · exact ⟨0,by simpa using h⟩
  · exact ⟨1,by simpa using h⟩

theorem boundaryLift_integerValued {z : SetFunction H} (hz : IntegerValued z) :
    IntegerValued (boundaryLift (J:=J) z) := fun A => hz (hubs A)

theorem branchLift_integerValued (j : J) {F : SetFunction H} (hF : IntegerValued F) :
    IntegerValued (branchLift j F) := by
  intro A
  by_cases hj : Sum.inr j∈A
  · simpa only [branchLift,if_pos hj] using hF (hubs A)
  · exact ⟨0,by simp only [branchLift,if_neg hj,Int.cast_zero]⟩

theorem assembled_integerValued {z : SetFunction H} (hz : IntegerValued z)
    (F : J → SetFunction H) (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℤ) :
    IntegerValued (assembled z F (fun j => (w j : ℝ))) := by
  apply (boundaryLift_integerValued hz).add
  exact IntegerValued.finset_sum univ _ (fun j _ =>
    (branchLift_integerValued j (hF j).integerValued).int_smul (w j))

/-- The exact slack bound gives an actual Minkowski complement in the sum of
the branch weights times the graphical zonotope. -/
theorem assembled_actual_summand {s k : ℕ} {z : SetFunction (Fin s)}
    (hz : TranslationNormalized z) {F : Fin k → SetFunction (Fin s)}
    (hF : ∀ j,IsMonotoneBoolean (F j)) {w : Fin k → ℝ}
    (hw : ∀ j,0≤ w j) (hc : Compatible z F w) :
    IsMinkowskiSummand (basePolytope (assembled z F w))
      ((∑ j : Fin k,w j) • graphicalZonotope (cliqueBook s k)) := by
  apply (isMinkowskiSummand_graphical_iff (assembled_normalized hz F hF w).1
    (assembled_supermodular z F hF w hw hc) (sum_nonneg (fun j _ => hw j))).mpr
  refine ⟨assembled_graphical z F w,?_⟩
  intro a b hab hedge A ha hb
  exact assembled_delta_le_weight_sum hF hw hc a b hab A ha hb

theorem assembled_lattice_complement {s k : ℕ} {z : SetFunction (Fin s)}
    (hz : TranslationNormalized z) (hzi : IntegerValued z)
    {F : Fin k → SetFunction (Fin s)} (hF : ∀ j,IsMonotoneBoolean (F j))
    (w : Fin k → ℤ) (hw : ∀ j,0≤ w j)
    (hc : Compatible z F (fun j => (w j : ℝ))) :
    LatticePolytope (basePolytope (assembled z F (fun j => (w j : ℝ)))) ∧
    ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
      basePolytope (assembled z F (fun j => (w j : ℝ)))+R=
        ((∑ j : Fin k,(w j : ℝ)) • graphicalZonotope (cliqueBook s k)) := by
  let f:=assembled z F (fun j => (w j : ℝ))
  let a : ℝ:=∑ j : Fin k,(w j : ℝ)
  have hw' : ∀ j,0≤(w j : ℝ):=fun j => by exact_mod_cast hw j
  have hn:=assembled_normalized hz F hF (fun j => (w j : ℝ))
  have hs:=assembled_supermodular z F hF (fun j => (w j : ℝ)) hw' hc
  have hi:=assembled_integerValued hzi F hF w
  have hG:=assembled_graphical z F (fun j => (w j : ℝ))
  have ha : 0≤ a:=sum_nonneg (fun j _ => hw' j)
  have hbound : ∀ u v,u≠ v → (cliqueBook s k).Adj u v → ∀ A,u∉A → v∉A →
      delta f u v A≤ a := by
    intro u v huv hedge A hu hv
    exact assembled_delta_le_weight_sum hF hw' hc u v huv A hu hv
  let g : SetFunction (Fin s⊕Fin k):=a • graphFunction (cliqueBook s k)-f
  have hgn : Normalized g := by
    change a*graphFunction (cliqueBook s k) ∅-f ∅=0
    have hf0 : f ∅=0 := hn.1
    rw [graphFunction_normalized,hf0,mul_zero,sub_self]
  have hgs : Supermodular g:=graphical_complement_supermodular hG ha hbound
  have hgi : IntegerValued g := by
    have hg0:=(graphFunction_integerValued (cliqueBook s k)).int_smul (∑ j : Fin k,w j)
    have he : ((∑ j : Fin k,w j : ℤ) : ℝ)=a := by simp only [Int.cast_sum,a]
    rw [he] at hg0
    exact hg0.sub hi
  exact ⟨hi.basePolytope hn.1 hs,basePolytope g,hgi.basePolytope hgn hgs,
    basePolytope_nonempty hgn hgs,basePolytope_add_graphical_complement hn.1 hs hG ha hbound⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart142

section BundlePart143
/- Source: Papers/GraphicalZonotopes/DisjointMintermModules.lean -/




@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The nonempty, disjoint complements of the minimal winning sets. Their
union may be smaller than `C`; the remaining variables occur in every term. -/
structure ComplementFamily (C : Finset H) (blocks : Finset (Finset H)) : Prop where
  card_two : 2≤ blocks.card
  subsets : ∀ B∈blocks,B⊆C
  nonempty : ∀ B∈blocks,B.Nonempty
  disjoint : ∀ A∈blocks,∀ B∈blocks,A≠ B → Disjoint A B

def complementModule (C : Finset H) (blocks : Finset (Finset H)) : SetFunction H :=
  fun S => if ∃ B∈blocks,C\B⊆S then 1 else 0

theorem complementModule_one_iff (C : Finset H) (blocks : Finset (Finset H)) (S : Finset H) :
    complementModule C blocks S=1 ↔ ∃ B∈blocks,C\B⊆S := by
  classical
  simp [complementModule]

theorem complementModule_zero_iff (C : Finset H) (blocks : Finset (Finset H)) (S : Finset H) :
    complementModule C blocks S=0 ↔ ¬∃ B∈blocks,C\B⊆S := by
  classical
  simp [complementModule]

theorem ComplementFamily.exists_other {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) (A : Finset H) : ∃ B∈blocks,B≠ A := by
  by_contra hn
  push_neg at hn
  have hc : blocks.card≤1:=card_le_one.mpr (fun B hB D hD =>
    (hn B hB).trans (hn D hD).symm)
  have hh:=h.card_two
  omega

theorem ComplementFamily.shared_mem_eq {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {A B : Finset H} (hA : A∈blocks) (hB : B∈blocks)
    {a : H} (ha : a∈A) (hb : a∈B) : A=B := by
  by_contra hne
  exact (disjoint_left.mp (h.disjoint A hA B hB hne)) ha hb

theorem ComplementFamily.module_boolean {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) : IsMonotoneBoolean (complementModule C blocks) := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro S T hST
    by_cases hs : ∃ B∈blocks,C\B⊆S
    · have ht : ∃ B∈blocks,C\B⊆T := by
        obtain ⟨B,hB,hBS⟩:=hs
        exact ⟨B,hB,hBS.trans hST⟩
      simp only [complementModule,if_pos hs,if_pos ht,le_refl]
    · simp only [complementModule,if_neg hs]
      split_ifs <;> norm_num
  · intro S
    unfold complementModule
    split_ifs <;> simp
  · apply (complementModule_zero_iff _ _ _).mpr
    rintro ⟨B,hB,hBE⟩
    obtain ⟨D,hD,hDB⟩:=h.exists_other B
    obtain ⟨a,ha⟩:=h.nonempty D hD
    have haC:=h.subsets D hD ha
    have haB : a∉B:=fun hb => (disjoint_left.mp (h.disjoint D hD B hB hDB)) ha hb
    exact notMem_empty a (hBE (mem_sdiff.mpr ⟨haC,haB⟩))
  · apply (complementModule_one_iff _ _ _).mpr
    obtain ⟨B,hB,_⟩:=h.exists_other ∅
    exact ⟨B,hB,subset_univ _⟩

/-- The complete multipartite graph on the union of the complement blocks;
vertices of `C` outside that union are isolated in this response graph. -/
def Crosses (blocks : Finset (Finset H)) (u v : H) : Prop :=
  ∃ A∈blocks,∃ B∈blocks,A≠ B ∧ u∈A ∧ v∈B

theorem Crosses.symm {blocks : Finset (Finset H)} {u v : H}
    (h : Crosses blocks u v) : Crosses blocks v u := by
  obtain ⟨A,hA,B,hB,hAB,hu,hv⟩:=h
  exact ⟨B,hB,A,hA,hAB.symm,hv,hu⟩

/-- All negative second differences are literal full-context indicators on
the crossing pairs, even when the function ignores hubs outside `C`. -/
theorem complementModule_negative_one_iff {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {u v : H} (huv : u≠ v) {S : Finset H}
    (hu : u∉S) (hv : v∉S) :
    negativeResponse (complementModule C blocks) u v S=1 ↔
      Crosses blocks u v ∧ C⊆insert u (insert v S) := by
  rw [negativeResponse_eq_one_iff h.module_boolean]
  simp only [complementModule_zero_iff,complementModule_one_iff]
  constructor
  · rintro ⟨hn,⟨A,hA,hAu⟩,⟨B,hB,hBv⟩⟩
    have huCA : u∈C\A := by
      by_contra hh
      apply hn
      refine ⟨A,hA,?_⟩
      intro x hx
      rcases mem_insert.mp (hAu hx) with he | he
      · exact False.elim (hh (he ▸ hx))
      · exact he
    have hvCB : v∈C\B := by
      by_contra hh
      apply hn
      refine ⟨B,hB,?_⟩
      intro x hx
      rcases mem_insert.mp (hBv hx) with he | he
      · exact False.elim (hh (he ▸ hx))
      · exact he
    have huC:=(mem_sdiff.mp huCA).1
    have hvC:=(mem_sdiff.mp hvCB).1
    have huA:=(mem_sdiff.mp huCA).2
    have hvB:=(mem_sdiff.mp hvCB).2
    have hvA : v∈A := by
      by_contra hh
      rcases mem_insert.mp (hAu (mem_sdiff.mpr ⟨hvC,hh⟩)) with he | he
      · exact huv he.symm
      · exact hv he
    have huB : u∈B := by
      by_contra hh
      rcases mem_insert.mp (hBv (mem_sdiff.mpr ⟨huC,hh⟩)) with he | he
      · exact huv he
      · exact hu he
    have hBA : B≠ A := fun he => huA (he ▸ huB)
    refine ⟨⟨B,hB,A,hA,hBA,huB,hvA⟩,?_⟩
    intro x hx
    by_cases hxA : x∈A
    · have hxB : x∉B:=fun hxB => (disjoint_left.mp
        (h.disjoint A hA B hB hBA.symm)) hxA hxB
      exact mem_insert_of_mem (hBv (mem_sdiff.mpr ⟨hx,hxB⟩))
    · exact (insert_subset_insert u (subset_insert v S))
        (hAu (mem_sdiff.mpr ⟨hx,hxA⟩))
  · rintro ⟨⟨A,hA,B,hB,hAB,huA,hvB⟩,hCS⟩
    have huC:=h.subsets A hA huA
    have hvC:=h.subsets B hB hvB
    refine ⟨?_,?_,?_⟩
    · rintro ⟨D,hD,hDS⟩
      have huD : u∈D := by
        by_contra hh
        exact hu (hDS (mem_sdiff.mpr ⟨huC,hh⟩))
      have hvD : v∈D := by
        by_contra hh
        exact hv (hDS (mem_sdiff.mpr ⟨hvC,hh⟩))
      exact hAB ((h.shared_mem_eq hA hD huA huD).trans
        (h.shared_mem_eq hD hB hvD hvB))
    · refine ⟨B,hB,?_⟩
      intro x hx
      have hxC:=(mem_sdiff.mp hx).1
      have hxB:=(mem_sdiff.mp hx).2
      rcases mem_insert.mp (hCS hxC) with he | he
      · exact mem_insert.mpr (Or.inl he)
      · rcases mem_insert.mp he with hev | heS
        · exact False.elim (hxB (hev.symm ▸ hvB))
        · exact mem_insert_of_mem heS
    · refine ⟨A,hA,?_⟩
      intro x hx
      have hxC:=(mem_sdiff.mp hx).1
      have hxA:=(mem_sdiff.mp hx).2
      rcases mem_insert.mp (hCS hxC) with he | he
      · exact False.elim (hxA (he.symm ▸ huA))
      · exact he

theorem complementModule_negative {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {u v : H} (huv : u≠ v) {S : Finset H}
    (hu : u∉S) (hv : v∉S) :
    negativeResponse (complementModule C blocks) u v S=
      if Crosses blocks u v ∧ C⊆insert u (insert v S) then 1 else 0 := by
  classical
  by_cases hc : Crosses blocks u v ∧ C⊆insert u (insert v S)
  · rw [if_pos hc]
    exact (complementModule_negative_one_iff h huv hu hv).mpr hc
  · rw [if_neg hc]
    rcases negativeResponse_values h.module_boolean u v S with h0 | h1
    · exact h0
    · exact False.elim (hc ((complementModule_negative_one_iff h huv hu hv).mp h1))

theorem ComplementFamily.essential {C : Finset H} {blocks : Finset (Finset H)}
    (h : ComplementFamily C blocks) {a : H} (ha : a∈C) :
    Essential (complementModule C blocks) a := by
  obtain ⟨A,hA,_⟩:=h.exists_other ∅
  obtain ⟨B,hB,haB⟩ : ∃ B∈blocks,a∉B := by
    by_cases haA : a∈A
    · obtain ⟨B,hB,hBA⟩:=h.exists_other A
      exact ⟨B,hB,fun hb => (disjoint_left.mp (h.disjoint B hB A hA hBA)) hb haA⟩
    · exact ⟨A,hA,haA⟩
  let X:=(C\B).erase a
  have hwin : complementModule C blocks (insert a X)=1 := by
    apply (complementModule_one_iff _ _ _).mpr
    refine ⟨B,hB,?_⟩
    rw [insert_erase (mem_sdiff.mpr ⟨ha,haB⟩)]
  have hlose : complementModule C blocks X=0 := by
    apply (complementModule_zero_iff _ _ _).mpr
    rintro ⟨D,hD,hDX⟩
    by_cases hDB : D=B
    · subst D
      exact notMem_erase a (C\B) (hDX (mem_sdiff.mpr ⟨ha,haB⟩))
    · obtain ⟨b,hb⟩:=h.nonempty B hB
      have hbC:=h.subsets B hB hb
      have hbD : b∉D:=fun hd => (disjoint_left.mp (h.disjoint D hD B hB hDB)) hd hb
      have hbad:=mem_of_mem_erase (hDX (mem_sdiff.mpr ⟨hbC,hbD⟩))
      exact (mem_sdiff.mp hbad).2 hb
  exact ⟨X,notMem_erase _ _,by rw [hwin,hlose,sub_zero]⟩

theorem complementModule_ignores_outside (C : Finset H) (blocks : Finset (Finset H))
    {a : H} (ha : a∉C) (S : Finset H) :
    complementModule C blocks (insert a S)=complementModule C blocks S := by
  classical
  have he : (∃ B∈blocks,C\B⊆insert a S) ↔ ∃ B∈blocks,C\B⊆S := by
    constructor
    · rintro ⟨B,hB,hBS⟩
      refine ⟨B,hB,?_⟩
      intro x hx
      rcases mem_insert.mp (hBS hx) with hxa | hxS
      · exact False.elim (ha (hxa ▸ (mem_sdiff.mp hx).1))
      · exact hxS
    · rintro ⟨B,hB,hBS⟩
      exact ⟨B,hB,hBS.trans (subset_insert _ _)⟩
  simp only [complementModule,he]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart143

section BundlePart144
/- Source: Papers/GraphicalZonotopes/FinitePowersetTransform.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem delta_zeta_reduced {u v : V} (huv : u≠ v) {S : Finset V}
    (hu : u∉S) (hv : v∉S) (y : SetFunction V) :
    delta (zeta y) u v S=∑ T∈S.powerset,y (insert u (insert v T)) := by
  have huvS : u∉insert v S:=by simp only [mem_insert,not_or]; exact ⟨huv,hu⟩
  simp only [delta,zeta,sum_powerset_insert huvS,sum_powerset_insert hu,
    sum_powerset_insert hv]
  ring

namespace PowersetTransform

abbrev SubsetIndex (B : Finset V) := ↥B.powerset

/-- The full lower-set sum on the powerset of a fixed ambient finite set.
The domain is exactly all its subsets; no extension or truncation is used. -/
def lowerSum (B : Finset V) :
    (SubsetIndex B → ℝ) →ₗ[ℝ] (SubsetIndex B → ℝ) where
  toFun y S := ∑ T : SubsetIndex B,if T.1⊆S.1 then y T else 0
  map_add' y z := by
    funext S
    simp only [Pi.add_apply]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro T hT
    split_ifs <;> simp
  map_smul' a y := by
    funext S
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [mul_sum]
    apply sum_congr rfl
    intro T hT
    split_ifs <;> simp

theorem lowerSum_eq_zero_iff (B : Finset V) (y : SubsetIndex B → ℝ) :
    lowerSum B y=0 ↔ y=0 := by
  constructor
  · intro hz
    have hzero : ∀ S : Finset V,∀ hS : S⊆B,y ⟨S,mem_powerset.mpr hS⟩=0 := by
      intro S
      refine Finset.strongInductionOn S ?_
      intro S ih hS
      let s : SubsetIndex B:=⟨S,mem_powerset.mpr hS⟩
      have hs:=congrFun hz s
      change (∑ T : SubsetIndex B,if T.1⊆S then y T else 0)=0 at hs
      rw [sum_eq_single s] at hs
      · simpa only [s,Subset.rfl,ite_true] using hs
      · intro T hT hne
        by_cases hTS : T.1⊆S
        · rw [if_pos hTS]
          have hne' : T.1≠ S := by
            intro he
            apply hne
            exact Subtype.ext he
          exact ih T.1 (Finset.ssubset_iff_subset_ne.mpr ⟨hTS,hne'⟩)
            (mem_powerset.mp T.2)
        · rw [if_neg hTS]
      · simp
    funext S
    exact hzero S.1 (mem_powerset.mp S.2)
  · rintro rfl
    exact (lowerSum B).map_zero

theorem lowerSum_injective (B : Finset V) : Function.Injective (lowerSum B) := by
  intro y z he
  have hz : lowerSum B (y-z)=0 := by rw [map_sub,he,sub_self]
  exact sub_eq_zero.mp ((lowerSum_eq_zero_iff B (y-z)).mp hz)

def lowerEquiv (B : Finset V) :
    (SubsetIndex B → ℝ) ≃ₗ[ℝ] (SubsetIndex B → ℝ) :=
  LinearEquiv.ofInjectiveEndo (lowerSum B) (lowerSum_injective B)

theorem lowerSum_restriction (B : Finset V) (y : SetFunction V) (S : SubsetIndex B) :
    lowerSum B (fun T => y T.1) S=∑ T∈S.1.powerset,y T := by
  change (∑ T : SubsetIndex B,if T.1⊆S.1 then y T.1 else 0)=_
  rw [← sum_filter]
  apply sum_bij (fun T _ => T.1)
  · intro T hT
    exact mem_powerset.mpr (mem_filter.mp hT).2
  · intro T hT U hU he
    exact Subtype.ext he
  · intro T hT
    let t : SubsetIndex B:=⟨T,mem_powerset.mpr
      ((mem_powerset.mp hT).trans (mem_powerset.mp S.2))⟩
    exact ⟨t,mem_filter.mpr ⟨mem_univ t,mem_powerset.mp hT⟩,rfl⟩
  · intro T hT
    rfl

/-- Triangular inversion preserves every coefficient subring, in particular
the integer lattice. This is proved from the inverse equations themselves. -/
theorem lowerEquiv_symm_mem_subring (B : Finset V) (K : Subring ℝ)
    (x : SubsetIndex B → ℝ) (hx : ∀ S,x S∈K) :
    ∀ S,(lowerEquiv B).symm x S∈K := by
  let y:=(lowerEquiv B).symm x
  have he : lowerSum B y=x:=(lowerEquiv B).apply_symm_apply x
  have hmem : ∀ S : Finset V,∀ hS : S⊆B,y ⟨S,mem_powerset.mpr hS⟩∈K := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih hS
    let s : SubsetIndex B:=⟨S,mem_powerset.mpr hS⟩
    have hs:=congrFun he s
    change (∑ T : SubsetIndex B,if T.1⊆S then y T else 0)=x s at hs
    rw [← sum_erase_add _ _ (mem_univ s)] at hs
    have hlast : (if s.1⊆S then y s else 0)=y s:=if_pos Subset.rfl
    rw [hlast] at hs
    have hsum : (∑ T∈(univ : Finset (SubsetIndex B)).erase s,
        if T.1⊆S then y T else 0)∈K := by
      apply K.sum_mem
      intro T hT
      by_cases hTS : T.1⊆S
      · rw [if_pos hTS]
        have hne : T.1≠ S := by
          intro he
          exact (ne_of_mem_erase hT) (Subtype.ext he)
        exact ih T.1 (Finset.ssubset_iff_subset_ne.mpr ⟨hTS,hne⟩) (mem_powerset.mp T.2)
      · rw [if_neg hTS]
        exact K.zero_mem
    have hy : y s=x s-(∑ T∈(univ : Finset (SubsetIndex B)).erase s,
        if T.1⊆S then y T else 0) := by linarith
    rw [hy]
    exact K.sub_mem (hx s) hsum
  intro S
  exact hmem S.1 (mem_powerset.mp S.2)

end PowersetTransform
end GraphicalZonotopes

end
end
end BundlePart144
