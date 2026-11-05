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

public import verified.parts.part004
import all verified.parts.part004

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart48
/- Source: Papers/GraphicalZonotopes/ThreeTreeIncidence.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def triangles (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun T => T.card=3 ∧ G.IsClique T)

theorem mem_triangles {G : SimpleGraph V} {T : Finset V} :
    T∈triangles G ↔ T.card=3 ∧ G.IsClique T := by
  classical
  simp [triangles]

/-- Every triangle of an ordinary 3-tree lies in an actual tetrahedron;
the statement includes triangles created at the last attachment. -/
theorem ThreeTreeOn.triangle_extends {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {T : Finset V} (hT : T.card=3) (hcT : G.IsClique T) :
    ∃ C∈tetrahedra G,T⊆C := by
  classical
  induction h generalizing T with
  | tetrahedron C hC =>
    refine ⟨C,?_,?_⟩
    · rw [tetrahedra_cliqueGraph hC]
      exact mem_singleton_self _
    · exact (ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcT
  | @attach S G h u hu A hA hAS hcA ih =>
    rw [tetrahedra_after_attachment h hu hA hAS hcA]
    by_cases huT : u∈T
    · refine ⟨insert u A,mem_insert_self _ _,?_⟩
      intro v hv
      by_cases hvu : v=u
      · exact mem_insert.mpr (Or.inl hvu)
      · exact mem_insert.mpr (Or.inr
          ((attached_vertex_adj_iff h hu hAS v).mp (hcT huT hv (Ne.symm hvu))))
    · obtain ⟨C,hC,hTC⟩ := ih hT (clique_before_attachment huT hcT)
      exact ⟨C,mem_insert_of_mem hC,hTC⟩

theorem ThreeTreeOn.tetrahedra_nonempty {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (tetrahedra G).Nonempty := by
  classical
  induction h with
  | tetrahedron C hC => rw [tetrahedra_cliqueGraph hC]; exact singleton_nonempty _
  | @attach S G h u hu T hT hTS hcT ih =>
    rw [tetrahedra_after_attachment h hu hT hTS hcT]
    exact insert_nonempty _ _

theorem tetrahedronAdjacency_mono {G H : SimpleGraph V} (h : G≤ H) :
    TriangleComponents.cliqueGraph G≤ TriangleComponents.cliqueGraph H := by
  intro C D hCD
  exact ⟨hCD.1,hCD.2.1,
    fun u hu v hv huv => h (hCD.2.2.1 hu hv huv),
    fun u hu v hv huv => h (hCD.2.2.2.1 hu hv huv),hCD.2.2.2.2⟩

/-- All actual tetrahedra of a 3-tree are joined by shared triangles. This
is a statement about the graph itself, independent of a chosen coefficient
vector or an extreme-ray assumption. -/
theorem ThreeTreeOn.tetrahedra_reachable {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {C D : Finset V}
    (hC : C∈tetrahedra G) (hD : D∈tetrahedra G) :
    (TriangleComponents.cliqueGraph G).Reachable C D := by
  classical
  induction h generalizing C D with
  | tetrahedron A hA =>
    rw [tetrahedra_cliqueGraph hA,mem_singleton] at hC hD
    subst C
    subst D
    exact SimpleGraph.Reachable.rfl
  | @attach S G h u hu T hT hTS hcT ih =>
    have hm := tetrahedronAdjacency_mono
      (show G≤ G⊔attachmentStar u T from le_sup_left)
    obtain ⟨K,hK,hTK⟩ := h.triangle_extends hT hcT
    have hk := (mem_filter.mp hK).2
    have huT : u∉T := fun huT => hu (hTS huT)
    have hnew : (TriangleComponents.cliqueGraph (G⊔attachmentStar u T)).Reachable
        (insert u T) K :=
      TriangleComponents.reachable_of_shared_triangle
        (by rw [card_insert_of_notMem huT,hT]) hk.1
        (attached_tetrahedron_clique h hu hTS hcT)
        (fun a ha b hb hab => Or.inl (hk.2 ha hb hab)) hT (subset_insert _ _) hTK
    rw [tetrahedra_after_attachment h hu hT hTS hcT] at hC hD
    rcases mem_insert.mp hC with rfl | hC
    · rcases mem_insert.mp hD with rfl | hD
      · exact SimpleGraph.Reachable.rfl
      · exact hnew.trans (SimpleGraph.Reachable.mono hm (ih hK hD))
    · rcases mem_insert.mp hD with rfl | hD
      · exact (hnew.trans (SimpleGraph.Reachable.mono hm (ih hK hC))).symm
      · exact SimpleGraph.Reachable.mono hm (ih hC hD)

abbrev CliqueTriangleNode (G : SimpleGraph V) := ↥(tetrahedra G) ⊕ ↥(triangles G)

/-- The literal bipartite clique-triangle incidence graph used to root the
construction in Section 6. Its nodes are all tetrahedra and all triangles,
and its edges express containment. -/
def cliqueTriangleIncidence (G : SimpleGraph V) : SimpleGraph (CliqueTriangleNode G) where
  Adj x y := match x,y with
    | Sum.inl C,Sum.inr T => T.1⊆C.1
    | Sum.inr T,Sum.inl C => T.1⊆C.1
    | _,_ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

instance (G : SimpleGraph V) : DecidableRel (cliqueTriangleIncidence G).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [cliqueTriangleIncidence] <;> infer_instance

/-- A shared triangle gives the actual length-two incidence path. -/
theorem incidence_reachable_of_shared_triangle {G : SimpleGraph V}
    (C D : ↥(tetrahedra G)) (hCD : (TriangleComponents.cliqueGraph G).Adj C.1 D.1) :
    (cliqueTriangleIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  obtain ⟨T,hTsub,hTcard⟩ := exists_subset_card_eq hCD.2.2.2.2.2
  have hTC : T⊆C.1 := hTsub.trans inter_subset_left
  have hTD : T⊆D.1 := hTsub.trans inter_subset_right
  have hT : T∈triangles G := mem_triangles.mpr
    ⟨hTcard,fun u hu v hv huv => hCD.2.2.1 (hTC hu) (hTC hv) huv⟩
  exact (SimpleGraph.Adj.reachable
    (show (cliqueTriangleIncidence G).Adj (Sum.inl C) (Sum.inr ⟨T,hT⟩) from hTC)).trans
      (SimpleGraph.Adj.reachable
        (show (cliqueTriangleIncidence G).Adj (Sum.inr ⟨T,hT⟩) (Sum.inl D) from hTD))

theorem incidence_reachable_of_tetrahedron_reachable {G : SimpleGraph V}
    (C D : ↥(tetrahedra G))
    (hp : (TriangleComponents.cliqueGraph G).Reachable C.1 D.1) :
    (cliqueTriangleIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  have hpath : ∀ E,Relation.ReflTransGen (TriangleComponents.cliqueGraph G).Adj C.1 E →
      ∃ hE : E∈tetrahedra G,
        (cliqueTriangleIncidence G).Reachable (Sum.inl C) (Sum.inl ⟨E,hE⟩) := by
    intro E hE
    induction hE with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hE hEF ih =>
      obtain ⟨hEmem,hreach⟩ := ih
      have hFmem : F∈tetrahedra G := mem_filter.mpr
        ⟨mem_univ _,hEF.2.1,hEF.2.2.2.1⟩
      exact ⟨hFmem,hreach.trans
        (incidence_reachable_of_shared_triangle ⟨E,hEmem⟩ ⟨F,hFmem⟩ hEF)⟩
  obtain ⟨hD,hreach⟩ := hpath _ hp
  exact hreach

theorem ThreeTreeOn.incidence_connected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (cliqueTriangleIncidence G).Connected := by
  classical
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl ⟨C,hC⟩,?_⟩
  intro N
  cases N with
  | inl D =>
    exact incidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ D
      (h.tetrahedra_reachable hC D.2)
  | inr T =>
    have ht := mem_triangles.mp T.2
    obtain ⟨D,hD,hTD⟩ := h.triangle_extends ht.1 ht.2
    exact (incidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ ⟨D,hD⟩
      (h.tetrahedra_reachable hC hD)).trans
        (SimpleGraph.Adj.reachable
          (show (cliqueTriangleIncidence G).Adj (Sum.inl ⟨D,hD⟩) (Sum.inr T) from hTD))

end GraphicalZonotopes

end
end
end BundlePart48

section BundlePart49
/- Source: Papers/GraphicalZonotopes/ThreeTreeEmbedding.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem map_cliqueGraph (e : V ↪ W) (C : Finset V) :
    (cliqueGraph C).map e=cliqueGraph (C.map e) := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a,b,⟨hab,ha,hb⟩,rfl,rfl⟩
    exact ⟨fun he => hab (e.injective he),mem_map.mpr ⟨a,ha,rfl⟩,mem_map.mpr ⟨b,hb,rfl⟩⟩
  · rintro ⟨huv,hu,hv⟩
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hv
    exact ⟨a,b,⟨fun he => huv (congrArg e he),ha,hb⟩,rfl,rfl⟩

theorem map_attachmentStar (e : V ↪ W) (u : V) (T : Finset V) :
    (attachmentStar u T).map e=attachmentStar (e u) (T.map e) := by
  ext a b
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨v,w,⟨hvw,hstar⟩,rfl,rfl⟩
    refine ⟨fun he => hvw (e.injective he),?_⟩
    rcases hstar with ⟨rfl,hw⟩ | ⟨rfl,hv⟩
    · exact Or.inl ⟨rfl,mem_map.mpr ⟨w,hw,rfl⟩⟩
    · exact Or.inr ⟨rfl,mem_map.mpr ⟨v,hv,rfl⟩⟩
  · rintro ⟨hab,hstar⟩
    rcases hstar with ⟨rfl,hb⟩ | ⟨rfl,ha⟩
    · obtain ⟨w,hw,rfl⟩ := mem_map.mp hb
      exact ⟨u,w,⟨fun he => hab (congrArg e he),Or.inl ⟨rfl,hw⟩⟩,rfl,rfl⟩
    · obtain ⟨v,hv,rfl⟩ := mem_map.mp ha
      exact ⟨v,u,⟨fun he => hab (congrArg e he),Or.inr ⟨rfl,hv⟩⟩,rfl,rfl⟩

theorem map_sup_embedding (e : V ↪ W) (G H : SimpleGraph V) :
    (G⊔H).map e=G.map e⊔H.map e := by
  ext u v
  simp only [SimpleGraph.map_adj,SimpleGraph.sup_adj]
  aesop

theorem ThreeTreeOn.map {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (e : V ↪ W) : ThreeTreeOn (S.map e) (G.map e) := by
  induction h with
  | tetrahedron C hC =>
    rw [map_cliqueGraph]
    exact ThreeTreeOn.tetrahedron _ (by simpa only [card_map] using hC)
  | @attach S G h u hu T hT hTS hcl ih =>
    rw [map_insert,map_sup_embedding,map_attachmentStar]
    exact ThreeTreeOn.attach ih (e u) (by simpa using hu) (T.map e)
      (by simpa only [card_map] using hT) (map_subset_map.mpr hTS) hcl.finsetMap

namespace SetFunctionEmbedding

theorem map_pullSet_of_subset (e : V ↪ W) (S : Finset W)
    (hS : ∀ v∈S,v∈Set.range e) : (pullSet e S).map e=S := by
  ext v
  constructor
  · rintro hv
    obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
    exact (mem_pullSet e S w).mp hw
  · intro hv
    obtain ⟨w,rfl⟩ := hS v hv
    exact mem_map.mpr ⟨w,(mem_pullSet e S w).mpr hv,rfl⟩

theorem card_pullSet_of_subset (e : V ↪ W) (S : Finset W)
    (hS : ∀ v∈S,v∈Set.range e) : (pullSet e S).card=S.card := by
  rw [← card_map e, map_pullSet_of_subset e S hS]

end SetFunctionEmbedding

theorem comap_cliqueGraph (e : V ↪ W) (C : Finset W) :
    (cliqueGraph C).comap e=cliqueGraph (SetFunctionEmbedding.pullSet e C) := by
  ext u v
  change (e u≠ e v ∧ e u∈C ∧ e v∈C) ↔
    (u≠ v ∧ u∈SetFunctionEmbedding.pullSet e C ∧ v∈SetFunctionEmbedding.pullSet e C)
  simp [e.injective.eq_iff]

theorem comap_attachmentStar (e : V ↪ W) (u : V) (T : Finset W) :
    (attachmentStar (e u) T).comap e=
      attachmentStar u (SetFunctionEmbedding.pullSet e T) := by
  ext a b
  change (e a≠ e b ∧ ((e a=e u ∧ e b∈T) ∨ (e b=e u ∧ e a∈T))) ↔ _
  simp [attachmentStar,SetFunctionEmbedding.mem_pullSet,e.injective.eq_iff]

theorem ThreeTreeOn.comap {S : Finset W} {G : SimpleGraph W}
    (h : ThreeTreeOn S G) (e : V ↪ W) (hS : ∀ v∈S,v∈Set.range e) :
    ThreeTreeOn (SetFunctionEmbedding.pullSet e S) (G.comap e) := by
  induction h with
  | tetrahedron C hC =>
    rw [comap_cliqueGraph]
    exact ThreeTreeOn.tetrahedron _
      ((SetFunctionEmbedding.card_pullSet_of_subset e C hS).trans hC)
  | @attach S G h u hu T hT hTS hcl ih =>
    have hS' : ∀ v∈S,v∈Set.range e := fun v hv => hS v (mem_insert_of_mem hv)
    have hT' : ∀ v∈T,v∈Set.range e := fun v hv => hS' v (hTS hv)
    obtain ⟨w,hw⟩ := hS u (mem_insert_self _ _)
    subst u
    rw [SetFunctionEmbedding.pullSet_insert_image]
    have hsup : (G⊔attachmentStar (e w) T).comap e=
        G.comap e⊔(attachmentStar (e w) T).comap e := rfl
    rw [hsup,comap_attachmentStar]
    apply ThreeTreeOn.attach (ih hS') w (by simpa using hu)
      (SetFunctionEmbedding.pullSet e T)
      ((SetFunctionEmbedding.card_pullSet_of_subset e T hT').trans hT)
    · intro v hv
      exact (SetFunctionEmbedding.mem_pullSet e S v).mpr
        (hTS ((SetFunctionEmbedding.mem_pullSet e T v).mp hv))
    · intro a ha b hb hab
      exact hcl ((SetFunctionEmbedding.mem_pullSet e T a).mp ha)
        ((SetFunctionEmbedding.mem_pullSet e T b).mp hb) (fun he => hab (e.injective he))

theorem ThreeTreeOn.induce {S : Finset V} {G : SimpleGraph V}
    [DecidableEq S] (h : ThreeTreeOn S G) : IsThreeTree (G.induce (S : Set V)) := by
  let e : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hh := h.comap e (fun v hv => ⟨⟨v,hv⟩,rfl⟩)
  have hset : SetFunctionEmbedding.pullSet e S=univ := by
    ext v
    simp [SetFunctionEmbedding.mem_pullSet,e,v.property]
  rw [hset] at hh
  exact hh

theorem ThreeTreeOn.reachable_active {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : ∀ u∈S,∀ v∈S,G.Reachable u v := by
  induction h with
  | tetrahedron C hC =>
    intro u hu v hv
    by_cases huv : u=v
    · subst v; exact SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable ⟨huv,hu,hv⟩
  | @attach S G h w hw T hT hTS hcl ih =>
    obtain ⟨a,ha⟩ := card_pos.mp (show 0< T.card by omega)
    have hwa : (G⊔attachmentStar w T).Reachable w a :=
      SimpleGraph.Adj.reachable ((attached_vertex_adj_iff h hw hTS a).mpr ha)
    intro u hu v hv
    rcases mem_insert.mp hu with hue | huS
    · subst u
      rcases mem_insert.mp hv with hve | hvS
      · subst v; exact SimpleGraph.Reachable.rfl
      · exact hwa.trans ((ih a (hTS ha) v hvS).mono le_sup_left)
    · rcases mem_insert.mp hv with hve | hvS
      · subst v
        exact ((ih u huS a (hTS ha)).mono le_sup_left).trans hwa.symm
      · exact (ih u huS v hvS).mono le_sup_left

theorem IsThreeTree.connected {G : SimpleGraph V} (h : IsThreeTree G) : G.Connected := by
  obtain ⟨v,hv⟩ := card_pos.mp (show 0<(univ : Finset V).card from lt_of_lt_of_le (by norm_num) h.active_card_ge_four)
  letI : Nonempty V := ⟨v⟩
  exact ⟨fun u v => h.reachable_active u (mem_univ _) v (mem_univ _)⟩

@[simp] theorem mem_tetrahedra_iff (G : SimpleGraph V) (C : Finset V) :
    C∈tetrahedra G ↔ C.card=4 ∧ G.IsClique C := by
  classical
  simp only [tetrahedra,mem_filter,mem_univ,true_and]

theorem tetrahedra_map (e : V ↪ W) (G : SimpleGraph V) :
    tetrahedra (G.map e)=(tetrahedra G).image (fun C => C.map e) := by
  classical
  ext D
  constructor
  · intro hD
    obtain ⟨hd,hcl⟩ := (mem_tetrahedra_iff (G.map e) D).mp hD
    obtain ⟨C,hC,rfl⟩ := (SimpleGraph.isClique_map_finset_iff_of_nontrivial
      (G := G) (f := e) (show D.Nontrivial from one_lt_card_iff_nontrivial.mp (by omega))).mp hcl
    refine mem_image.mpr ⟨C,(mem_tetrahedra_iff G C).mpr ⟨?_,hC⟩,rfl⟩
    simpa only [card_map] using hd
  · intro hD
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hD
    obtain ⟨hc,hcl⟩ := (mem_tetrahedra_iff G C).mp hC
    exact (mem_tetrahedra_iff (G.map e) (C.map e)).mpr
      ⟨by simpa only [card_map] using hc,hcl.finsetMap⟩

theorem triangleMultiplicity_map (e : V ↪ W) (G : SimpleGraph V) (T : Finset V) :
    triangleMultiplicity (G.map e) (T.map e)=triangleMultiplicity G T := by
  have he : (tetrahedra (G.map e)).filter (fun C => T.map e⊆C)=
      ((tetrahedra G).filter (fun C => T⊆C)).image (fun C => C.map e) := by
    rw [tetrahedra_map]
    ext D
    simp only [mem_filter,mem_image]
    constructor
    · rintro ⟨⟨C,hC,rfl⟩,hTC⟩
      exact ⟨C,⟨hC,map_subset_map.mp hTC⟩,rfl⟩
    · rintro ⟨C,⟨hC,hTC⟩,rfl⟩
      exact ⟨⟨C,hC,rfl⟩,map_subset_map.mpr hTC⟩
  unfold triangleMultiplicity
  rw [he,card_image_of_injective _ (Finset.map_injective e)]

theorem Admissible.map {G : SimpleGraph V} (h : Admissible G) (e : V ↪ W) :
    Admissible (G.map e) := by
  intro T hT hcl
  obtain ⟨S,hS,rfl⟩ := (SimpleGraph.isClique_map_finset_iff_of_nontrivial
    (G := G) (f := e) (show T.Nontrivial from one_lt_card_iff_nontrivial.mp (by omega))).mp hcl
  rw [triangleMultiplicity_map]
  exact h S (by simpa only [card_map] using hT) hS

theorem Admissible.of_map {G : SimpleGraph V} (e : V ↪ W)
    (h : Admissible (G.map e)) : Admissible G := by
  intro T hT hcl
  have hh := h (T.map e) (by simpa only [card_map] using hT) hcl.finsetMap
  rwa [triangleMultiplicity_map] at hh

theorem IsThreeTree.map_equiv {G : SimpleGraph V} (h : IsThreeTree G) (e : V ≃ W) :
    IsThreeTree (G.map e.toEmbedding) := by
  have hh := h.map e.toEmbedding
  change ThreeTreeOn univ _
  simpa only [Finset.map_univ_equiv] using hh

theorem HasAdmissibleSpanningThreeTree.map_equiv {G : SimpleGraph V}
    (h : HasAdmissibleSpanningThreeTree G) (e : V ≃ W) :
    HasAdmissibleSpanningThreeTree (G.map e.toEmbedding) := by
  obtain ⟨H,hHG,hT,hA⟩ := h
  exact ⟨H.map e.toEmbedding,SimpleGraph.map_monotone e hHG,
    hT.map_equiv e,hA.map e.toEmbedding⟩

theorem ThreeTreeOn.exists_edge {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : ∃ u v,G.Adj u v := by
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  obtain ⟨hc,hcl⟩ := (mem_filter.mp hC).2
  obtain ⟨u,hu⟩ := card_pos.mp (show 0< C.card by omega)
  obtain ⟨v,hv,hvu⟩ := exists_mem_ne (show 1< C.card by omega) u
  exact ⟨u,v,hcl hu hv (Ne.symm hvu)⟩

theorem map_comap_of_supported (e : V ↪ W) (G : SimpleGraph W)
    (hs : ∀ u v,G.Adj u v → u∈Set.range e) : (G.comap e).map e=G := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a,b,hab,rfl,rfl⟩
    exact hab
  · intro huv
    obtain ⟨a,rfl⟩ := hs u v huv
    obtain ⟨b,rfl⟩ := hs v (e a) (G.adj_symm huv)
    exact ⟨a,b,huv,rfl,rfl⟩

end GraphicalZonotopes

end
end
end BundlePart49

section BundlePart50
/- Source: Papers/GraphicalZonotopes/SupportGeometry.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
section Unordered
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Dependence on a displayed set of coordinates is an equality of the
original set function, not an informal support convention. -/
def DependsOn (z : SetFunction V) (S : Finset V) : Prop :=
  ∀ T, z T = z (T ∩ S)

theorem DependsOn.add {f g : SetFunction V} {S : Finset V}
    (hf : DependsOn f S) (hg : DependsOn g S) : DependsOn (f+g) S := by
  intro T
  change f T+g T=f (T∩S)+g (T∩S)
  rw [hf T,hg T]

theorem DependsOn.of_smul {z : SetFunction V} {S : Finset V} {a : ℝ}
    (ha : a ≠ 0) (h : DependsOn (a • z) S) : DependsOn z S := by
  intro T
  exact mul_left_cancel₀ ha (h T)

theorem setMonomial_dependsOn (C : Finset V) : DependsOn (setMonomial C) C := by
  intro T
  simp [setMonomial,subset_inter_iff]

theorem DependsOn.smul {z : SetFunction V} {S : Finset V}
    (h : DependsOn z S) (a : ℝ) : DependsOn (a • z) S := by
  intro T
  change a*z T=a*z (T∩S)
  rw [h T]

theorem zeta_dependsOn {y : SetFunction V} {S : Finset V}
    (hy : ∀ C, ¬ C ⊆ S → y C = 0) : DependsOn (zeta y) S := by
  intro T
  rw [zeta_eq_sum_monomials]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro C hC
  by_cases hCS : C ⊆ S
  · simp [setMonomial,subset_inter_iff,hCS]
  · simp [hy C hCS]

theorem DependsOn.delta_eq_zero {z : SetFunction V} {S : Finset V}
    (h : DependsOn z S) {u v : V} (hu : u ∉ S) (T : Finset V) :
    delta z u v T = 0 := by
  have hi : ∀ A : Finset V, insert u A ∩ S = A ∩ S := by
    intro A
    ext x
    simp only [mem_inter,mem_insert]
    constructor
    · rintro ⟨hx,hxS⟩
      rcases hx with rfl | hx
      · exact False.elim (hu hxS)
      · exact ⟨hx,hxS⟩
    · rintro ⟨hx,hxS⟩
      exact ⟨Or.inr hx,hxS⟩
  unfold delta
  rw [h (insert u (insert v T)),h (insert u T),h (insert v T),h T,hi,hi]
  ring

theorem basePolytope_coordinate_zero_of_dependsOn {z : SetFunction V} {S : Finset V}
    (hn : TranslationNormalized z) (hd : DependsOn z S) {u : V} (hu : u ∉ S)
    {x : V → ℝ} (hx : x ∈ basePolytope z) : x u = 0 := by
  have hl : 0 ≤ x u := by simpa [hn.2 u,subsetSum] using hx.2 {u}
  have he : univ.erase u ∩ S = S := by
    ext v
    simp only [mem_inter,mem_erase,mem_univ,true_and,and_true]
    constructor
    · exact fun h => h.2
    · intro hv
      exact ⟨fun hvu => hu (hvu ▸ hv),hv⟩
  have hz : z (univ.erase u) = z univ := by
    rw [hd (univ.erase u),hd univ,he,univ_inter]
  have hh := hx.2 (univ.erase u)
  rw [hz] at hh
  have hsum : subsetSum x (univ.erase u)+x u=z univ := by
    rw [subsetSum,sum_erase_add _ _ (mem_univ u)]
    exact hx.1
  linarith

def evaluationLinear (u : V) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vectorSpan_le_evaluation_ker_of_dependsOn {z : SetFunction V} {S : Finset V}
    (hn : TranslationNormalized z) (hs : Supermodular z) (hd : DependsOn z S)
    {u : V} (hu : u ∉ S) : vectorSpan ℝ (basePolytope z) ≤ (evaluationLinear u).ker := by
  obtain ⟨p,hp⟩ := basePolytope_nonempty hn.1 hs
  rw [vectorSpan_eq_span_vsub_set_right ℝ hp]
  apply Submodule.span_le.mpr
  rintro x ⟨q,hq,rfl⟩
  change q u-p u=0
  rw [basePolytope_coordinate_zero_of_dependsOn hn hd hu hq,
    basePolytope_coordinate_zero_of_dependsOn hn hd hu hp,sub_self]

/-- Full affine dimension forces every coordinate to be present in any set
on which the normalized function depends. -/
theorem fullDimension_dependsOn_eq_univ {n : ℕ} (hn : 2 ≤ n)
    {z : SetFunction (Fin n)} (hzn : TranslationNormalized z) (hzs : Supermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = n-1)
    {S : Finset (Fin n)} (hdep : DependsOn z S) : S = univ := by
  have hne := basePolytope_nonempty hzn.1 hzs
  have hW : vectorSpan ℝ (basePolytope z) = (totalLinear (V := Fin n)).ker :=
    Submodule.eq_of_le_of_finrank_eq (vectorSpan_basePolytope_le_total_ker hne)
      (hfull.trans (finrank_total_ker (by omega)).symm)
  apply eq_univ_of_forall
  intro u
  by_contra hu
  have hex : ∃ v : Fin n, v ≠ u := by
    by_cases hu0 : u = ⟨0,by omega⟩
    · refine ⟨⟨1,by omega⟩,?_⟩
      rw [hu0]
      intro h
      have hv := congrArg Fin.val h
      change (1 : ℕ)=0 at hv
      omega
    · exact ⟨⟨0,by omega⟩,Ne.symm hu0⟩
  obtain ⟨v,hvu⟩ := hex
  have hroot : basisVector u-basisVector v ∈ (totalLinear (V := Fin n)).ker := by
    change subsetSum (basisVector u-basisVector v) univ=0
    simp
  rw [← hW] at hroot
  have hzero := vectorSpan_le_evaluation_ker_of_dependsOn hzn hzs hdep hu hroot
  change (basisVector u-basisVector v) u=0 at hzero
  simp [basisVector,Pi.single_apply,hvu,Ne.symm hvu] at hzero

theorem TranslationNormalized.finset_sum {I : Type*} (s : Finset I)
    (f : I → SetFunction V) (hf : ∀ i ∈ s, TranslationNormalized (f i)) :
    TranslationNormalized (∑ i ∈ s, f i) := by
  constructor
  · change (∑ i ∈ s, f i) ∅=0
    rw [Finset.sum_apply]
    exact sum_eq_zero fun i hi => (hf i hi).1
  · intro v
    change (∑ i ∈ s, f i) {v}=0
    rw [Finset.sum_apply]
    exact sum_eq_zero fun i hi => (hf i hi).2 v

theorem TranslationNormalized.add {f g : SetFunction V}
    (hf : TranslationNormalized f) (hg : TranslationNormalized g) :
    TranslationNormalized (f+g) := by
  exact ⟨by change f ∅+g ∅=0; rw [hf.1,hg.1,add_zero],
    fun v => by change f {v}+g {v}=0; rw [hf.2 v,hg.2 v,add_zero]⟩

/-- Every nonzero member of an arbitrary finite positive decomposition of an
extreme normalized function is a strictly positive multiple of it. -/
theorem ExtremeSupermodular.finite_summand {I : Type*} [Fintype I]
    {z : SetFunction V} (hz : ExtremeSupermodular z) (f : I → SetFunction V)
    (hn : ∀ i, TranslationNormalized (f i)) (hs : ∀ i, Supermodular (f i))
    (he : ∑ i, f i=z) {i : I} (hi : f i ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ f i=a • z := by
  classical
  let g := ∑ j ∈ univ.erase i, f j
  have hgn : TranslationNormalized g := TranslationNormalized.finset_sum _ _ (fun j hj => hn j)
  have hgs : Supermodular g := Supermodular.finset_sum _ _ (fun j hj => hs j)
  have hsum : f i+g=z := by
    rw [add_comm,show g=∑ j ∈ univ.erase i,f j from rfl,
      sum_erase_add _ _ (mem_univ i),he]
  obtain ⟨a,ha,hf⟩ := hz.2.2.2 (f i) g (hn i) hgn (hs i) hgs hsum
  refine ⟨a,lt_of_le_of_ne ha ?_,hf⟩
  intro hzero
  exact hi (by simpa [← hzero] using hf)

end Unordered

namespace PositiveDecomposition
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem DependsOn.adjusted {z : SetFunction V} {S : Finset V}
    (h : GraphicalZonotopes.DependsOn z S) : GraphicalZonotopes.DependsOn (adjusted z) S := by
  apply h.add
  apply zeta_dependsOn
  intro C hC
  by_cases hcard : C.card = 2
  · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hcard
    rw [allocation_pair z huv]
    have hzero : minimumSlack z u v=0 := by
      by_cases hu : u ∈ S
      · have hv : v ∉ S := fun hv => hC (insert_subset hu (singleton_subset_iff.mpr hv))
        have hz : ∀ T, u ∉ T → v ∉ T → delta z u v T=0 := by
          intro T _ _
          have hcomm : delta z u v T=delta z v u T := by
            unfold delta
            rw [insert_comm]
            ring
          rw [hcomm]
          exact h.delta_eq_zero hv T
        obtain ⟨T,hTu,hTv,hmin⟩ := exists_minimumSlack z u v
        exact hmin.symm.trans (hz T hTu hTv)
      · obtain ⟨T,hTu,hTv,hmin⟩ := exists_minimumSlack z u v
        exact hmin.symm.trans (h.delta_eq_zero hu T)
    simp [hzero]
  · exact allocation_zero z hcard

end PositiveDecomposition
end GraphicalZonotopes

end
end
end BundlePart50

section BundlePart51
/- Source: Papers/GraphicalZonotopes/SetFunctionEmbeddingGeometry.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace GraphicalZonotopes.SetFunctionEmbedding
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

@[simp] theorem pullSet_univ (e : W ↪ V) : pullSet e univ=univ := by
  ext w; simp

theorem reconstruct_of_insert_absent (e : W ↪ V) (f : SetFunction V)
    (hf : ∀ v,v∉Set.range e → ∀ S,f (insert v S)=f S) :
    extend e (restrict e f)=f := by
  have hall : ∀ S : Finset V,∀ f : SetFunction V,
      (∀ v,v∉Set.range e → ∀ T,f (insert v T)=f T) →
      f S=f ((pullSet e S).map e) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro f hf; simp
    | @insert v S hv ih =>
      intro f hf
      by_cases hvR : v∈Set.range e
      · obtain ⟨w,rfl⟩ := hvR
        let g : SetFunction V := fun T => f (insert (e w) T)
        have hg : ∀ v,v∉Set.range e → ∀ T,g (insert v T)=g T := by
          intro v hv T
          dsimp only [g]
          rw [insert_comm,hf v hv]
        simpa only [g,pullSet_insert_image,map_insert] using ih g hg
      · rw [hf v hvR,pullSet_insert_not_range e v hvR]
        exact ih f hf
  funext S
  exact (hall S f hf).symm

theorem insert_absent_of_zero_deltas {f : SetFunction V}
    (hn : TranslationNormalized f) (u : V)
    (hz : ∀ v,u≠ v → ∀ S,u∉S → v∉S → delta f u v S=0) :
    ∀ S,f (insert u S)=f S := by
  intro S
  induction S using Finset.induction_on with
  | empty => change f {u}=f ∅; rw [hn.2 u,hn.1]
  | @insert v S hv ih =>
    by_cases huv : u=v
    · subst v; simp
    · by_cases huS : u∈S
      · simp [insert_eq_of_mem huS,insert_eq_of_mem (mem_insert_of_mem huS)]
      · have hh := hz v huv S huS hv
        dsimp only [delta] at hh
        rw [ih] at hh
        linarith

/-- Adding unused coordinates preserves actual extremality in the full
supermodular cone. Summands are proved to ignore every new coordinate. -/
theorem extend_extreme (e : W ↪ V) {f : SetFunction W}
    (hf : ExtremeSupermodular f) : ExtremeSupermodular (extend e f) := by
  refine ⟨extend_translationNormalized e hf.1,extend_supermodular e hf.2.1,?_,?_⟩
  · intro he
    apply hf.2.2.1
    funext S
    have hh := congrFun he (S.map e)
    simpa only [extend,pullSet_map,Pi.zero_apply] using hh
  · intro g h hgn hhn hgs hhs hsum
    have hgzero : ∀ u,u∉Set.range e → ∀ v,u≠ v → ∀ S,u∉S → v∉S →
        delta g u v S=0 := by
      intro u hu v huv S huS hvS
      have h1 := hgs.elemental u v huv S huS hvS
      have h2 := hhs.elemental u v huv S huS hvS
      have he : delta g u v S+delta h u v S=0 := by
        rw [← delta_add,hsum,delta_extend_not_range e f u v hu]
      linarith
    have hgrec : extend e (restrict e g)=g :=
      reconstruct_of_insert_absent e g (fun u hu =>
        insert_absent_of_zero_deltas hgn u (hgzero u hu))
    have hsum' : restrict e g+restrict e h=f := by
      funext S
      have he := congrFun hsum (S.map e)
      simpa only [restrict,extend,pullSet_map,Pi.add_apply] using he
    obtain ⟨a,ha,hscale⟩ := hf.2.2.2 (restrict e g) (restrict e h)
      (restrict_translationNormalized e hgn) (restrict_translationNormalized e hhn)
      (restrict_supermodular e hgs) (restrict_supermodular e hhs) hsum'
    refine ⟨a,ha,?_⟩
    rw [← hgrec,hscale,extend_smul]

theorem extend_integer (e : W ↪ V) {f : SetFunction W}
    (hf : IntegerValued f) : IntegerValued (extend e f) := fun S => hf (pullSet e S)

theorem extend_dependsOn (e : W ↪ V) (f : SetFunction W) :
    DependsOn (extend e f) (univ.map e) := by
  intro S
  change f (pullSet e S)=f (pullSet e (S∩univ.map e))
  congr 1
  ext w
  simp

/-- The literal linear embedding extends vectors by zero outside the image. -/
def pushVector (e : W ↪ V) : (W → ℝ) →ₗ[ℝ] (V → ℝ) :=
  Fintype.linearCombination ℝ (fun w => basisVector (e w))

@[simp] theorem pushVector_image (e : W ↪ V) (x : W → ℝ) (w : W) :
    pushVector e x (e w)=x w := by
  simp [pushVector,Fintype.linearCombination_apply,basisVector,Pi.single_apply,
    e.injective.eq_iff]

theorem pushVector_outside (e : W ↪ V) (x : W → ℝ) (v : V)
    (hv : v∉Set.range e) : pushVector e x v=0 := by
  have hne : ∀ w,e w≠ v := fun w he => hv ⟨w,he⟩
  simp [pushVector,Fintype.linearCombination_apply,basisVector,Pi.single_apply,
    hne,fun w => Ne.symm (hne w)]

theorem pushVector_injective (e : W ↪ V) : Function.Injective (pushVector e) := by
  intro x y he
  funext w
  have hh := congrFun he (e w)
  simpa only [pushVector_image] using hh

theorem subsetSum_pushVector (e : W ↪ V) (x : W → ℝ) (S : Finset V) :
    subsetSum (pushVector e x) S=subsetSum x (pullSet e S) := by
  change subsetSum (∑ w,x w • basisVector (e w)) S=_
  unfold subsetSum
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [sum_comm]
  simp_rw [← mul_sum]
  change (∑ w,x w*subsetSum (basisVector (e w)) S)=_
  simp only [subsetSum_basisVector]
  simp [subsetSum,pullSet,sum_filter]

/-- The extended base polytope is exactly the zero-coordinate linear image
of the original body, including every point and every defining inequality. -/
theorem basePolytope_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) :
    basePolytope (extend e f)=pushVector e '' basePolytope f := by
  ext x
  constructor
  · intro hx
    let p : W → ℝ := fun w => x (e w)
    have hzero : ∀ v,v∉Set.range e → x v=0 := by
      intro v hv
      apply basePolytope_coordinate_zero_of_dependsOn
        (extend_translationNormalized e hn) (extend_dependsOn e f) (x := x) _ hx
      intro hm
      obtain ⟨w,_,he⟩ := mem_map.mp hm
      exact hv ⟨w,he⟩
    have hpush : pushVector e p=x := by
      funext v
      by_cases hv : v∈Set.range e
      · obtain ⟨w,rfl⟩ := hv
        exact pushVector_image e p w
      · rw [pushVector_outside e p v hv,hzero v hv]
    refine ⟨p,?_,hpush⟩
    constructor
    · have ht := hx.1
      rw [← hpush,subsetSum_pushVector,pullSet_univ] at ht
      simpa only [extend,pullSet_univ] using ht
    · intro T
      have ht := hx.2 (T.map e)
      rw [← hpush,subsetSum_pushVector,pullSet_map] at ht
      simpa only [extend,pullSet_map] using ht
  · rintro ⟨p,hp,rfl⟩
    constructor
    · rw [subsetSum_pushVector,pullSet_univ]
      simpa only [extend,pullSet_univ] using hp.1
    · intro S
      rw [subsetSum_pushVector]
      exact hp.2 (pullSet e S)

/-- Affine dimension is unchanged by an injective extension of the vertex
index set. This is a statement about the genuine base polytopes. -/
theorem finrank_vectorSpan_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope (extend e f)))=
      Module.finrank ℝ (vectorSpan ℝ (basePolytope f)) := by
  rw [basePolytope_extend e hn]
  have he := (pushVector e).toAffineMap.map_vectorSpan (s := basePolytope f)
  change Submodule.map (pushVector e) (vectorSpan ℝ (basePolytope f))=
    vectorSpan ℝ (pushVector e '' basePolytope f) at he
  rw [← he]
  exact (Submodule.equivMapOfInjective (pushVector e) (pushVector_injective e)
    (vectorSpan ℝ (basePolytope f))).finrank_eq.symm

end GraphicalZonotopes.SetFunctionEmbedding

end
end
end BundlePart51

section BundlePart52
/- Source: Papers/GraphicalZonotopes/RefinedTriangleComponents.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace RefinedTriangleComponents
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The actual nonzero four-coefficient family, with no ambient tetrahedron
inserted merely because its vertices form a clique. -/
def family (y : SetFunction V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card=4 ∧ y C≠0)

@[simp] theorem mem_family (y : SetFunction V) (C : Finset V) :
    C∈family y ↔ C.card=4 ∧ y C≠0 := by
  classical
  simp [family]

abbrev FamilyVertex (y : SetFunction V) := {C : Finset V // C∈family y}
abbrev Component (y : SetFunction V) := (tetrahedronGraph (family y)).ConnectedComponent
abbrev ClassIndex (y : SetFunction V) := Component y ⊕ Finset V

noncomputable instance classIndexFintype (y : SetFunction V) : Fintype (ClassIndex y) := by
  classical
  infer_instance

def Incident (y : SetFunction V) (T : Finset V) : Prop :=
  ∃ C : Finset V,C∈family y ∧ T⊆C

def classOf (y : SetFunction V) (C : Finset V) : ClassIndex y := by
  classical
  exact if h3 : C.card=3 then
    if h : Incident y C then
      Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk
        ⟨Classical.choose h,(Classical.choose_spec h).1⟩)
    else Sum.inr C
  else if h : C∈family y then
    Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk ⟨C,h⟩)
  else Sum.inr C

theorem family_reachable_of_triangle {y : SetFunction V}
    (C D : FamilyVertex y) {T : Finset V} (hT : T.card=3)
    (hTC : T⊆C.val) (hTD : T⊆D.val) :
    (tetrahedronGraph (family y)).Reachable C D := by
  by_cases he : C=D
  · subst D
    exact SimpleGraph.Reachable.rfl
  · apply SimpleGraph.Adj.reachable
    refine ⟨he,?_⟩
    have hcard := card_le_card (subset_inter hTC hTD)
    omega

theorem classOf_family {y : SetFunction V} {C : Finset V} (hC : C∈family y) :
    classOf y C=Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk ⟨C,hC⟩) := by
  classical
  have hc := (mem_family y C).mp hC
  have h3 : C.card≠3 := by omega
  simp [classOf,h3,hC]

theorem classOf_triangle {y : SetFunction V} {T C : Finset V}
    (hT : T.card=3) (hC : C∈family y) (hTC : T⊆C) :
    classOf y T=Sum.inl ((tetrahedronGraph (family y)).connectedComponentMk ⟨C,hC⟩) := by
  classical
  have hI : Incident y T := ⟨C,hC,hTC⟩
  simp only [classOf,dif_pos hT,dif_pos hI]
  apply congrArg Sum.inl
  apply SimpleGraph.ConnectedComponent.sound
  exact family_reachable_of_triangle _ _ hT (Classical.choose_spec hI).2 hTC

theorem nonzero_card_le_four {G : SimpleGraph V} (hG : G.CliqueFree 5)
    {y : SetFunction V} (hy : CliqueSupported G y) {C : Finset V} (hC : y C≠0) :
    C.card≤4 := by
  by_contra hcard
  have h5 : 5≤ C.card := by omega
  obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq h5
  apply hG D
  refine ⟨?_,hD⟩
  intro u hu v hv huv
  by_contra hnon
  exact hC (hy.2.2 C u v (hDC hu) (hDC hv) huv hnon)

/-- The refined partition has the exact compatibility needed by the positive
decomposition, because no nonzero coefficient has size greater than four. -/
theorem classOf_compatible {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) :
    PositiveDecomposition.ClassCompatible y (classOf y) := by
  intro C hC hyC T hT hTC
  have hc : C.card=4 := le_antisymm (hdegree C hyC) hC
  have hmem : C∈family y := (mem_family y C).mpr ⟨hc,hyC⟩
  rw [classOf_triangle hT hmem hTC,classOf_family hmem]

theorem right_class_is_triangle {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) {C T : Finset V}
    (hC : 3≤ C.card) (hyC : y C≠0) (ha : classOf y C=Sum.inr T) :
    C.card=3 ∧ C=T := by
  classical
  by_cases h3 : C.card=3
  · refine ⟨h3,?_⟩
    by_cases hi : Incident y C
    · simp [classOf,h3,hi] at ha
    · simpa [classOf,h3,hi] using ha
  · have h4 : C.card=4 := by have h:=hdegree C hyC; omega
    have hm : C∈family y := (mem_family y C).mpr ⟨h4,hyC⟩
    rw [classOf_family hm] at ha
    cases ha

theorem triangle_left_incident {y : SetFunction V} {T : Finset V} (hT : T.card=3)
    {a : Component y} (ha : classOf y T=Sum.inl a) : Incident y T := by
  classical
  by_contra hi
  simp [classOf,hT,hi] at ha

/-- The edge union of the actual nonzero four-coefficient family. -/
def edgeGraph (y : SetFunction V) : SimpleGraph V where
  Adj u v := u≠ v ∧ ∃ C∈family y,u∈C ∧ v∈C
  symm := ⟨by
    rintro u v ⟨huv,C,hC,hu,hv⟩
    exact ⟨Ne.symm huv,C,hC,hv,hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem family_subset_edgeGraph_clique {y : SetFunction V} {C : Finset V}
    (hC : C∈family y) : (edgeGraph y).IsClique C := by
  intro u hu v hv huv
  exact ⟨huv,C,hC,hu,hv⟩

theorem left_coefficients_supported {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (a : Component y) :
    CliqueSupported (edgeGraph y)
      (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a)) := by
  classical
  refine ⟨by simp [PositiveDecomposition.classCoefficients],
    fun v => by simp [PositiveDecomposition.classCoefficients],?_⟩
  intro C u v hu hv huv hnon
  by_contra hz
  obtain ⟨hc,ha,hyC⟩ := PositiveDecomposition.classCoefficients_nonzero hz
  apply hnon
  refine ⟨huv,?_⟩
  by_cases h3 : C.card=3
  · obtain ⟨D,hD,hCD⟩ := triangle_left_incident h3 ha
    exact ⟨D,hD,hCD hu,hCD hv⟩
  · have h4 : C.card=4 := by have h:=hdegree C hyC; omega
    exact ⟨C,(mem_family y C).mpr ⟨h4,hyC⟩,hu,hv⟩

theorem left_coefficients_subset_vertices {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (a : Component y) {C : Finset V}
    (hC : PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C≠0) :
    C⊆(family y).biUnion id := by
  classical
  obtain ⟨hc,ha,hyC⟩ := PositiveDecomposition.classCoefficients_nonzero hC
  by_cases h3 : C.card=3
  · obtain ⟨D,hD,hCD⟩ := triangle_left_incident h3 ha
    intro v hv
    exact mem_biUnion.mpr ⟨D,hD,hCD hv⟩
  · have h4 : C.card=4 := by have h:=hdegree C hyC; omega
    intro v hv
    exact mem_biUnion.mpr ⟨C,(mem_family y C).mpr ⟨h4,hyC⟩,hv⟩

/-- If a nonzero refined positive piece is proportional to the whole
function, every nonzero four-coefficient lies in its one shared-face component. -/
theorem same_component_of_positive_piece {y : SetFunction V} (a : Component y)
    {t : ℝ} (ht : t≠0)
    (he : PositiveDecomposition.adjusted
      (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a))=t • zeta y) :
    ∀ C : FamilyVertex y,
      (tetrahedronGraph (family y)).connectedComponentMk C=a := by
  intro C
  have hC := (mem_family y C.val).mp C.property
  have hcoef := congrArg (fun f : SetFunction V => mobius f C.val) he
  have hmin : PositiveDecomposition.allocation
      (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a)) C.val=0 :=
    PositiveDecomposition.allocation_zero _ (by omega)
  have hleft : mobius (PositiveDecomposition.adjusted
      (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a))) C.val=
      PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C.val := by
    unfold PositiveDecomposition.adjusted PositiveDecomposition.higherClass
    rw [show zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a))+
        zeta (PositiveDecomposition.allocation
          (zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a))))=
        zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a)+
          PositiveDecomposition.allocation
            (zeta (PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a)))) from
      (zetaLinear.map_add _ _).symm,mobius_zeta]
    change PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C.val +
      PositiveDecomposition.allocation
        (PositiveDecomposition.higherClass y (classOf y) (Sum.inl a)) C.val = _
    rw [hmin,add_zero]
  have hright : mobius (t • zeta y) C.val=t*y C.val := by
    have hmap := (zetaEquiv (V:=V)).symm.map_smul t (zeta y)
    have h := congrFun hmap C.val
    change mobius (t • zeta y) C.val=t*mobius (zeta y) C.val at h
    simpa only [mobius_zeta] using h
  rw [hleft,hright] at hcoef
  have hn : PositiveDecomposition.classCoefficients y (classOf y) (Sum.inl a) C.val≠0 := by
    rw [hcoef]
    exact mul_ne_zero ht hC.2
  have hclass := (PositiveDecomposition.classCoefficients_nonzero hn).2.1
  rw [classOf_family C.property] at hclass
  exact Sum.inl.inj hclass

end RefinedTriangleComponents
end GraphicalZonotopes

end
end
end BundlePart52

section BundlePart53
/- Source: Papers/GraphicalZonotopes/RefinedSupport.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace RefinedTriangleComponents
open Finset PositiveDecomposition
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [LinearOrder V]

private theorem adjusted_zero_function : adjusted (0 : SetFunction V)=0 := by
  have ha : allocation (0 : SetFunction V)=0 := by
    funext C
    by_cases hC : C.card=2
    · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
      rw [allocation_pair _ huv]
      have hm : minimumSlack (0 : SetFunction V) u v=0 :=
        minimumSlack_eq_zero (by intros; simp [delta])
      simp [hm]
    · exact allocation_zero _ hC
  rw [adjusted,ha]
  change 0+zetaLinear 0=0
  simp

theorem higher_right_dependsOn {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (T : Finset V) :
    DependsOn (higherClass y (classOf y) (Sum.inr T)) T := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := right_class_is_triangle hdegree hc hyC ha
  exact hC Subset.rfl

theorem higher_right_zero_of_card_ne_three {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) {T : Finset V} (hT : T.card≠3) :
    higherClass y (classOf y) (Sum.inr T)=0 := by
  apply (zeta_eq_zero_iff _).mpr
  funext C
  by_contra he
  obtain ⟨hc,ha,hyC⟩ := classCoefficients_nonzero he
  obtain ⟨h3,rfl⟩ := right_class_is_triangle hdegree hc hyC ha
  exact hT h3

theorem higher_left_dependsOn {y : SetFunction V}
    (hdegree : ∀ C,y C≠0 → C.card≤4) (a : Component y) :
    DependsOn (higherClass y (classOf y) (Sum.inl a)) ((family y).biUnion id) := by
  apply zeta_dependsOn
  intro C hC
  by_contra he
  exact hC (left_coefficients_subset_vertices hdegree a he)

def pieces (y : SetFunction V) : (ClassIndex y ⊕ Finset V) → SetFunction V :=
  Sum.elim (fun a => adjusted (higherClass y (classOf y) a))
    (fun C => residual y (higherClass y (classOf y)) C • setMonomial C)

theorem pieces_positive {y : SetFunction V} (hy : y ∅=0 ∧ ∀ v,y {v}=0)
    (hdegree : ∀ C,y C≠0 → C.card≤4) (hs : Supermodular (zeta y)) :
    (∀ i,TranslationNormalized (pieces y i) ∧ Supermodular (pieces y i)) ∧
    (∑ i,pieces y i)=zeta y := by
  classical
  have hytop : CliqueSupported (⊤ : SimpleGraph V) y := by
    refine ⟨hy.1,hy.2,?_⟩
    intro C u v hu hv huv hnon
    exact False.elim (hnon huv)
  obtain ⟨hp,hr,hrn,hrs,he⟩ := compatible_class_decomposition y hytop hs
    (classOf y) (classOf_compatible hdegree)
  constructor
  · intro i
    cases i with
    | inl a => exact ⟨(hp a).1,(hp a).2.1⟩
    | inr C =>
      refine ⟨?_,(setMonomial_supermodular C).smul (hr C)⟩
      by_cases hC : C.card=2
      · have hn : TranslationNormalized (setMonomial C) := by
          refine ⟨setMonomial_normalized (card_pos.mp (by omega)),?_⟩
          intro v
          have hnot : ¬C⊆{v} := by
            intro hsub
            have hcard:=card_le_card hsub
            simp only [card_singleton] at hcard
            omega
          simp [setMonomial,hnot]
        exact ⟨by change _*setMonomial C ∅=0; rw [hn.1,mul_zero],
          fun v => by change _*setMonomial C {v}=0; rw [hn.2 v,mul_zero]⟩
      · have hz := residual_zero y (higherClass y (classOf y)) hC
        simp only [pieces,Sum.elim_inr,hz,zero_smul]
        exact ⟨rfl,fun _ => rfl⟩
  · rw [Fintype.sum_sum_type]
    change (∑ a,adjusted (higherClass y (classOf y) a))+
      (∑ C,residual y (higherClass y (classOf y)) C • setMonomial C)=_
    rw [← zeta_eq_sum_monomials]
    exact he

theorem extreme_has_positive_component {n : ℕ} (hn : 4≤ n)
    {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1)
    (hdegree : ∀ C,mobius z C≠0 → C.card≤4) :
    ∃ a : Component (mobius z),∃ t : ℝ,0< t ∧
      adjusted (higherClass (mobius z) (classOf (mobius z)) (Sum.inl a))=t • z ∧
      (family (mobius z)).biUnion id=univ := by
  classical
  let y:=mobius z
  have hy : y ∅=0 ∧ ∀ v,y {v}=0 :=
    (zeta_normalized_iff y).mp (by simpa [y] using hz.1)
  obtain ⟨hp,he⟩ := pieces_positive hy hdegree (by simpa [y] using hz.2.1)
  have hez : (∑ i,pieces y i)=z := by simpa [y] using he
  have hex : ∃ i,pieces y i≠0 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i,pieces y i)=0 := sum_eq_zero (fun i hi => h i)
    exact hz.2.2.1 (hez.symm.trans hzero)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨t,ht,hscale⟩ := hz.finite_summand (pieces y)
    (fun i => (hp i).1) (fun i => (hp i).2) hez hi
  have hsupport : ∀ S,DependsOn (pieces y i) S → S=univ := by
    intro S hS
    rw [hscale] at hS
    exact fullDimension_dependsOn_eq_univ (by omega) hz.1 hz.2.1 hfull
      (DependsOn.of_smul (ne_of_gt ht) hS)
  cases i with
  | inr C =>
    have hC : C.card=2 := by
      by_contra hnot
      have hzC := residual_zero y (higherClass y (classOf y)) hnot
      exact hi (by simp [pieces,hzC])
    have hdep : DependsOn (pieces y (Sum.inr C)) C := (setMonomial_dependsOn C).smul _
    have hcard:=congrArg Finset.card (hsupport C hdep)
    simp only [hC,card_univ,Fintype.card_fin] at hcard
    omega
  | inl c =>
    cases c with
    | inr T =>
      have hT : T.card=3 := by
        by_contra hnot
        have hzero:=higher_right_zero_of_card_ne_three hdegree hnot
        exact hi (by simp only [y,pieces,Sum.elim_inl,hzero,adjusted_zero_function])
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_right_dependsOn hdegree T)
      have hcard:=congrArg Finset.card (hsupport T hdep)
      simp only [hT,card_univ,Fintype.card_fin] at hcard
      omega
    | inl a =>
      have hdep := PositiveDecomposition.DependsOn.adjusted
        (higher_left_dependsOn hdegree a)
      exact ⟨a,t,ht,hscale,hsupport _ hdep⟩

theorem actualRootEdge_of_nonzero_coefficient {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) {C : Finset V}
    (hC : mobius z C≠0) {u v : V} (huv : u≠ v) (hu : u∈C) (hv : v∈C) :
    ActualRootEdge (basePolytope z) u v := by
  by_contra he
  have hzero : ∀ S : Finset V,u∉S → v∉S → delta z u v S=0 := by
    intro S hSu hSv
    apply le_antisymm _ (hs.elemental u v huv S hSu hSv)
    by_contra h
    exact he (exposedSegment_of_positive_delta hn hs huv hSu hSv (lt_of_not_ge h))
  have hcoeff := (nonedge_coefficients_zero_iff (mobius z) huv).mp
    (by simpa only [zeta_mobius] using hzero) C hu hv
  exact hC hcoeff

theorem actualRootEdge_of_graphical {z : SetFunction V} {G : SimpleGraph V}
    (hn : Normalized z) (hs : Supermodular z) (hG : Graphical G z)
    {u v : V} (h : ActualRootEdge (basePolytope z) u v) : G.Adj u v := by
  obtain ⟨a,ha,R,_,_,_,he⟩ := (isWeakMinkowskiSummand_graphical_iff hn hs).mpr hG
  exact basePolytope_summand_actualRootEdge hn hs G ha.le R he h

/-- Corollary4.4: for a full-dimensional extreme function in a K5-free graph,
the complete nonzero four-coefficient family is nonempty and triangle
connected, covers every vertex, and has precisely the actual direction graph
as its edge union. No zero tetrahedron is added to this family. -/
theorem full_refined_support {n : ℕ} (hn : 4≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {z : SetFunction (Fin n)} (hz : ExtremeSupermodular z)
    (hgraph : Graphical G z)
    (hfull : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1) :
    (family (mobius z)).Nonempty ∧
      (tetrahedronGraph (family (mobius z))).Preconnected ∧
      (family (mobius z)).biUnion id=univ ∧
      actualDirectionGraph (basePolytope z)=edgeGraph (mobius z) := by
  classical
  let y:=mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hgraph⟩
  have hdegree : ∀ C,y C≠0 → C.card≤4 := fun C hC => nonzero_card_le_four hG hy hC
  obtain ⟨a,t,ht,hscale,hcover⟩ := extreme_has_positive_component hn hz hfull hdegree
  have hcomp := same_component_of_positive_piece a (ne_of_gt ht)
    (by simpa only [zeta_mobius] using hscale)
  have hconnected : (tetrahedronGraph (family y)).Preconnected := by
    intro C D
    exact SimpleGraph.ConnectedComponent.exact ((hcomp C).trans (hcomp D).symm)
  have hne : (family y).Nonempty := by
    have hm : (⟨0,by omega⟩ : Fin n)∈(family y).biUnion id := by
      rw [hcover]
      exact mem_univ _
    obtain ⟨C,hC,hv⟩ := mem_biUnion.mp hm
    exact ⟨C,hC⟩
  refine ⟨hne,hconnected,hcover,?_⟩
  have hpiece : Graphical (edgeGraph y)
      (adjusted (higherClass y (classOf y) (Sum.inl a))) :=
    adjusted_graphical ((cliqueSupported_iff _ _).mp (left_coefficients_supported hdegree a)).2
  have hzedge : Graphical (edgeGraph y) z := by
    intro u v huv hnon S hu hv
    have h:=hpiece u v huv hnon S hu hv
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
end GraphicalZonotopes

end
end
end BundlePart53

section BundlePart54
/- Source: Papers/GraphicalZonotopes/SetFunctionEmbeddingDirections.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes
open Finset

private def missingPairGraph {V : Type*} (u v : V) : SimpleGraph V where
  Adj a b := a≠ b ∧ (a≠ u ∨ b≠ v) ∧ (a≠ v ∨ b≠ u)
  symm := ⟨by intro a b h; tauto⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Actual exposed root edges are precisely the nonzero elemental rows,
with existence of a genuine conditioning context in both directions. -/
theorem actualRootEdge_iff_nonzero_delta {V : Type*} [Fintype V] [LinearOrder V]
    {f : SetFunction V} (hn : Normalized f) (hs : Supermodular f) (u v : V) :
    ActualRootEdge (basePolytope f) u v ↔ u≠ v ∧
      ∃ S : Finset V,u∉S ∧ v∉S ∧ delta f u v S≠0 := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    by_contra hnone
    push_neg at hnone
    have hg : Graphical (missingPairGraph u v) f := by
      intro a b hab hnon S ha hb
      have hp : (a=u ∧ b=v) ∨ (a=v ∧ b=u) := by
        change ¬(a≠ b ∧ (a≠ u ∨ b≠ v) ∧ (a≠ v ∨ b≠ u)) at hnon
        tauto
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnone S ha hb
      · rw [delta_comm]
        exact hnone S hb ha
    have hh := RefinedTriangleComponents.actualRootEdge_of_graphical hn hs hg h
    exact hh.2.1.elim (fun hn => hn rfl) (fun hn => hn rfl)
  · rintro ⟨huv,S,hu,hv,hd⟩
    exact exposedSegment_of_positive_delta hn hs huv hu hv
      (lt_of_le_of_ne (hs.elemental u v huv S hu hv) (Ne.symm hd))

namespace SetFunctionEmbedding
variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]

theorem reconstruct_of_graphical_supported (e : W ↪ V) {G : SimpleGraph V}
    {f : SetFunction V} (hn : TranslationNormalized f) (hG : Graphical G f)
    (hS : ∀ u v,G.Adj u v → u∈Set.range e) : extend e (restrict e f)=f := by
  apply reconstruct_of_insert_absent e f
  intro u hu
  apply insert_absent_of_zero_deltas hn u
  intro v huv S huS hvS
  exact hG u v huv (fun hadj => hu (hS u v hadj)) S huS hvS

theorem extreme_restrict_of_reconstruction (e : W ↪ V) {f : SetFunction V}
    (hf : ExtremeSupermodular f) (hrec : extend e (restrict e f)=f) :
    ExtremeSupermodular (restrict e f) := by
  refine ⟨restrict_translationNormalized e hf.1,restrict_supermodular e hf.2.1,?_,?_⟩
  · intro he
    apply hf.2.2.1
    rw [← hrec,he]
    funext S
    rfl
  · intro g h hgn hhn hgs hhs he
    have hsum : extend e g+extend e h=f := by
      rw [← hrec,← he]
      rfl
    obtain ⟨a,ha,hscale⟩ := hf.2.2.2 (extend e g) (extend e h)
      (extend_translationNormalized e hgn) (extend_translationNormalized e hhn)
      (extend_supermodular e hgs) (extend_supermodular e hhs) hsum
    refine ⟨a,ha,?_⟩
    have hh := congrArg (restrict e) hscale
    simpa only [restrict_extend,restrict_smul] using hh

/-- The complete actual direction graph is transported by the embedding;
new coordinates have no edges, and every retained edge stays exposed. -/
theorem actualDirectionGraph_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) (hs : Supermodular f) :
    actualDirectionGraph (basePolytope (extend e f))=
      (actualDirectionGraph (basePolytope f)).map e := by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · intro huv
    obtain ⟨hne,S,hu,hv,hd⟩ := (actualRootEdge_iff_nonzero_delta
      (extend_translationNormalized e hn).1 (extend_supermodular e hs) u v).mp huv
    have huR : u∈Set.range e := by
      by_contra h
      exact hd (delta_extend_not_range e f u v h S)
    have hvR : v∈Set.range e := by
      by_contra h
      rw [delta_comm] at hd
      exact hd (delta_extend_not_range e f v u h S)
    obtain ⟨a,rfl⟩ := huR
    obtain ⟨b,rfl⟩ := hvR
    refine ⟨a,b,?_,rfl,rfl⟩
    apply (actualRootEdge_iff_nonzero_delta hn.1 hs a b).mpr
    refine ⟨fun he => hne (congrArg e he),pullSet e S,by simpa using hu,by simpa using hv,?_⟩
    simpa only [delta_extend] using hd
  · rintro ⟨a,b,hab,rfl,rfl⟩
    obtain ⟨hne,S,ha,hb,hd⟩ := (actualRootEdge_iff_nonzero_delta hn.1 hs a b).mp hab
    apply (actualRootEdge_iff_nonzero_delta (extend_translationNormalized e hn).1
      (extend_supermodular e hs) (e a) (e b)).mpr
    refine ⟨fun he => hne (e.injective he),S.map e,by simpa using ha,by simpa using hb,?_⟩
    simpa only [delta_extend,pullSet_map] using hd

theorem actualDirectionGraph_restrict (e : W ↪ V) {f : SetFunction V}
    (hn : TranslationNormalized f) (hs : Supermodular f)
    (hrec : extend e (restrict e f)=f) :
    actualDirectionGraph (basePolytope (restrict e f))=
      (actualDirectionGraph (basePolytope f)).comap e := by
  have he := actualDirectionGraph_extend e (restrict_translationNormalized e hn)
    (restrict_supermodular e hs)
  rw [hrec] at he
  have hh := congrArg (fun G : SimpleGraph V => G.comap e) he
  simpa only [SimpleGraph.comap_map_eq] using hh.symm

theorem edgeFamily_map (e : W ↪ V) (G : SimpleGraph W) :
    edgeFamily (G.map e)=(edgeFamily G).image (fun C => C.map e) := by
  ext D
  constructor
  · intro hD
    obtain ⟨hd,hcl⟩ := (mem_edgeFamily _ _).mp hD
    obtain ⟨C,hC,rfl⟩ := (SimpleGraph.isClique_map_finset_iff_of_nontrivial
      (G := G) (f := e) (show D.Nontrivial from one_lt_card_iff_nontrivial.mp (by omega))).mp hcl
    refine mem_image.mpr ⟨C,(mem_edgeFamily G C).mpr ⟨?_,hC⟩,rfl⟩
    simpa only [card_map] using hd
  · intro hD
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hD
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hC
    exact (mem_edgeFamily _ _).mpr ⟨by simpa only [card_map] using hc,
      (show G.IsClique C from hcl).finsetMap⟩

/-- The number of genuine root directions is preserved under every
injective coordinate embedding, including arbitrary coordinate relabelings. -/
theorem directionCount_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) (hs : Supermodular f) :
    directionCount (basePolytope (extend e f))=directionCount (basePolytope f) := by
  unfold directionCount
  rw [actualDirectionGraph_extend e hn hs,edgeFamily_map,
    card_image_of_injective _ (Finset.map_injective e)]

end SetFunctionEmbedding
end GraphicalZonotopes

end
end
end BundlePart54

section BundlePart55
/- Source: Papers/GraphicalZonotopes/ThreeTreeIncidenceTree.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triangles_cliqueGraph {C : Finset V} (hC : C.card=4) :
    triangles (cliqueGraph C)=C.powersetCard 3 := by
  classical
  ext T
  rw [mem_triangles,mem_powersetCard]
  constructor
  · rintro ⟨hT,hcl⟩
    exact ⟨(ThreeTreeOn.tetrahedron C hC).clique_subset_active (by omega) hcl,hT⟩
  · rintro ⟨hTC,hT⟩
    exact ⟨hT,fun u hu v hv huv => ⟨huv,hTC hu,hTC hv⟩⟩

theorem triangles_after_attachment {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {A : Finset V}
    (hA : A.card=3) (hAS : A⊆S) (hcA : G.IsClique A) :
    triangles (G⊔attachmentStar u A)=triangles G∪
      (A.powersetCard 2).image (insert u) := by
  classical
  ext T
  rw [mem_triangles,mem_union,mem_triangles,mem_image]
  constructor
  · rintro ⟨hT,hcl⟩
    by_cases huT : u∈T
    · right
      refine ⟨T.erase u,mem_powersetCard.mpr ⟨?_,?_⟩,insert_erase huT⟩
      · intro v hv
        exact (attached_vertex_adj_iff h hu hAS v).mp
          (hcl huT (mem_of_mem_erase hv) (Ne.symm (ne_of_mem_erase hv)))
      · rw [card_erase_of_mem huT,hT]
    · exact Or.inl ⟨hT,clique_before_attachment huT hcl⟩
  · rintro (⟨hT,hcl⟩ | ⟨B,hB,rfl⟩)
    · exact ⟨hT,fun v hv w hw hvw => Or.inl (hcl hv hw hvw)⟩
    · obtain ⟨hBA,hB⟩ := mem_powersetCard.mp hB
      have huB : u∉B := fun hum => hu (hAS (hBA hum))
      refine ⟨by rw [card_insert_of_notMem huB,hB],?_⟩
      have hcl := attached_tetrahedron_clique h hu hAS hcA
      exact fun v hv w hw hvw => hcl (insert_subset_insert u hBA hv)
        (insert_subset_insert u hBA hw) hvw

theorem triangles_after_attachment_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) {u : V} (hu : u∉S) {A : Finset V}
    (hA : A.card=3) (hAS : A⊆S) (hcA : G.IsClique A) :
    (triangles (G⊔attachmentStar u A)).card=(triangles G).card+3 := by
  classical
  have hdis : Disjoint (triangles G) ((A.powersetCard 2).image (insert u)) := by
    apply disjoint_left.mpr
    intro T hT hnew
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hnew
    obtain ⟨hT,hcl⟩ := mem_triangles.mp hT
    exact hu ((h.clique_subset_active (by omega) hcl) (mem_insert_self _ _))
  have himage : ((A.powersetCard 2).image (insert u)).card=(A.powersetCard 2).card := by
    apply card_image_of_injOn
    intro B hB C hC he
    have huB : u∉B := fun hum => hu (hAS ((mem_powersetCard.mp hB).1 hum))
    have huC : u∉C := fun hum => hu (hAS ((mem_powersetCard.mp hC).1 hum))
    have herase := congrArg (fun D : Finset V => D.erase u) he
    simpa [huB,huC] using herase
  rw [triangles_after_attachment h hu hA hAS hcA,card_union_of_disjoint hdis,
    himage,card_powersetCard,hA]
  norm_num

/-- The exact count includes all graph triangles, not a chosen set of
construction separators. -/
theorem ThreeTreeOn.triangles_card {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (triangles G).card=3*(tetrahedra G).card+1 := by
  classical
  induction h with
  | tetrahedron C hC =>
    rw [triangles_cliqueGraph hC,card_powersetCard,hC,
      tetrahedra_cliqueGraph hC,card_singleton]
    norm_num
  | @attach S G h u hu A hA hAS hcA ih =>
    rw [triangles_after_attachment_card h hu hA hAS hcA,
      tetrahedra_after_attachment h hu hA hAS hcA,
      card_insert_of_notMem (attached_tetrahedron_not_old h hu),ih]
    omega

def incidenceCliqueNeighbors (G : SimpleGraph V) (C : ↥(tetrahedra G)) :
    ↥(C.1.powersetCard 3) ≃ (cliqueTriangleIncidence G).neighborSet (Sum.inl C) := by
  classical
  have hc := (mem_filter.mp C.2).2
  let f : ↥(C.1.powersetCard 3) →
      (cliqueTriangleIncidence G).neighborSet (Sum.inl C) := fun T =>
    ⟨Sum.inr ⟨T.1,mem_triangles.mpr
      ⟨(mem_powersetCard.mp T.2).2,fun u hu v hv huv =>
        hc.2 ((mem_powersetCard.mp T.2).1 hu) ((mem_powersetCard.mp T.2).1 hv) huv⟩⟩,
      (mem_powersetCard.mp T.2).1⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro T U he
    apply Subtype.ext
    simpa only [f, Subtype.mk.injEq, Sum.inr.injEq] using he
  · rintro ⟨N,hN⟩
    cases N with
    | inl D => exact False.elim hN
    | inr T =>
      refine ⟨⟨T.1,mem_powersetCard.mpr ⟨hN,(mem_triangles.mp T.2).1⟩⟩,?_⟩
      rfl

theorem incidence_clique_degree (G : SimpleGraph V) (C : ↥(tetrahedra G)) :
    (cliqueTriangleIncidence G).degree (Sum.inl C)=4 := by
  classical
  have hc := (mem_filter.mp C.2).2.1
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← Fintype.card_congr (incidenceCliqueNeighbors G C)]
  simp only [Fintype.card_coe,card_powersetCard,hc]
  norm_num

theorem incidence_edge_card (G : SimpleGraph V) :
    (cliqueTriangleIncidence G).edgeFinset.card=4*(tetrahedra G).card := by
  classical
  let L : Finset (CliqueTriangleNode G) := univ.image Sum.inl
  let R : Finset (CliqueTriangleNode G) := univ.image Sum.inr
  have hb : (cliqueTriangleIncidence G).IsBipartiteWith L R := by
    constructor
    · apply Set.disjoint_left.mpr
      intro N hL hR
      obtain ⟨C,hC,hCN⟩ := mem_image.mp hL
      obtain ⟨T,hT,hTN⟩ := mem_image.mp hR
      have he := hCN.trans hTN.symm
      cases he
    · intro N M hNM
      cases N <;> cases M
      · exact False.elim hNM
      · exact Or.inl ⟨by simp [L],by simp [R]⟩
      · exact Or.inr ⟨by simp [R],by simp [L]⟩
      · exact False.elim hNM
  calc
    (cliqueTriangleIncidence G).edgeFinset.card=
        ∑ N∈L,(cliqueTriangleIncidence G).degree N :=
      (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hb).symm
    _=∑ C : ↥(tetrahedra G),(4:ℕ) := by
      dsimp [L]
      rw [sum_image (fun C hC D hD hCD => Sum.inl.inj hCD)]
      simp only [incidence_clique_degree]
    _=4*(tetrahedra G).card := by simp [Nat.mul_comm]

/-- The complete literal clique–triangle incidence graph of any 3-tree
is a tree. Connectedness and the exact vertex/edge counts are independently
proved for all actual cliques, so no incidence-tree property is assumed. -/
theorem ThreeTreeOn.incidence_isTree {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (cliqueTriangleIncidence G).IsTree := by
  classical
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨h.incidence_connected,?_⟩
  simp only [Nat.card_eq_fintype_card,CliqueTriangleNode,Fintype.card_sum,Fintype.card_coe]
  rw [← SimpleGraph.edgeFinset_card,incidence_edge_card,h.triangles_card]
  omega

end GraphicalZonotopes

end
end
end BundlePart55

section BundlePart56
/- Source: Papers/GraphicalZonotopes/PrunedIncidence.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def internalTriangles (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact (triangles G).filter (fun T => 2≤ triangleMultiplicity G T)

theorem mem_internalTriangles {G : SimpleGraph V} {T : Finset V} :
    T∈internalTriangles G ↔ T∈triangles G ∧ 2≤ triangleMultiplicity G T := by
  classical
  simp [internalTriangles]

abbrev InternalIncidenceNode (G : SimpleGraph V) :=
  ↥(tetrahedra G) ⊕ ↥(internalTriangles G)

def internalIncidenceEmbedding (G : SimpleGraph V) :
    InternalIncidenceNode G ↪ CliqueTriangleNode G :=
  Function.Embedding.sumMap (Function.Embedding.refl _) {
    toFun := fun T => ⟨T.1,(mem_internalTriangles.mp T.2).1⟩
    inj' := by intro T U he; apply Subtype.ext; simpa only [Subtype.mk.injEq] using he }

/-- The incidence tree with leaf triangles removed. Every remaining
edge carries a nonconstant response, so the local matching property applies
in both directions without a distinguished global root. -/
def internalIncidence (G : SimpleGraph V) : SimpleGraph (InternalIncidenceNode G) :=
  (cliqueTriangleIncidence G).comap (internalIncidenceEmbedding G)

@[simp] theorem internalIncidence_adj_left_right (G : SimpleGraph V)
    (C : ↥(tetrahedra G)) (T : ↥(internalTriangles G)) :
    (internalIncidence G).Adj (Sum.inl C) (Sum.inr T) ↔ T.1⊆C.1 := Iff.rfl

theorem internal_triangle_of_shared {G : SimpleGraph V} {C D T : Finset V}
    (hC : C∈tetrahedra G) (hD : D∈tetrahedra G) (hCD : C≠ D)
    (hT : T.card=3) (hTC : T⊆C) (hTD : T⊆D) : T∈internalTriangles G := by
  classical
  have hc := (mem_filter.mp hC).2.2
  apply mem_internalTriangles.mpr
  refine ⟨mem_triangles.mpr ⟨hT,fun u hu v hv huv => hc (hTC hu) (hTC hv) huv⟩,?_⟩
  unfold triangleMultiplicity
  exact Nat.succ_le_of_lt (one_lt_card.mpr
    ⟨C,mem_filter.mpr ⟨hC,hTC⟩,D,mem_filter.mpr ⟨hD,hTD⟩,hCD⟩)

theorem internalIncidence_reachable_of_shared {G : SimpleGraph V}
    (C D : ↥(tetrahedra G))
    (hCD : (TriangleComponents.cliqueGraph G).Adj C.1 D.1) :
    (internalIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  obtain ⟨T,hTsub,hTcard⟩ := exists_subset_card_eq hCD.2.2.2.2.2
  have hTC : T⊆C.1 := hTsub.trans inter_subset_left
  have hTD : T⊆D.1 := hTsub.trans inter_subset_right
  have hT := internal_triangle_of_shared C.2 D.2 hCD.2.2.2.2.1 hTcard hTC hTD
  exact (SimpleGraph.Adj.reachable
    (show (internalIncidence G).Adj (Sum.inl C) (Sum.inr ⟨T,hT⟩) from hTC)).trans
      (SimpleGraph.Adj.reachable
        (show (internalIncidence G).Adj (Sum.inr ⟨T,hT⟩) (Sum.inl D) from hTD))

theorem internalIncidence_reachable_of_tetrahedron_reachable {G : SimpleGraph V}
    (C D : ↥(tetrahedra G))
    (hp : (TriangleComponents.cliqueGraph G).Reachable C.1 D.1) :
    (internalIncidence G).Reachable (Sum.inl C) (Sum.inl D) := by
  classical
  rw [SimpleGraph.reachable_eq_reflTransGen] at hp
  have hpath : ∀ E,Relation.ReflTransGen (TriangleComponents.cliqueGraph G).Adj C.1 E →
      ∃ hE : E∈tetrahedra G,
        (internalIncidence G).Reachable (Sum.inl C) (Sum.inl ⟨E,hE⟩) := by
    intro E hE
    induction hE with
    | refl => exact ⟨C.2,SimpleGraph.Reachable.rfl⟩
    | @tail E F hE hEF ih =>
      obtain ⟨hEmem,hreach⟩ := ih
      have hFmem : F∈tetrahedra G := mem_filter.mpr
        ⟨mem_univ _,hEF.2.1,hEF.2.2.2.1⟩
      exact ⟨hFmem,hreach.trans
        (internalIncidence_reachable_of_shared ⟨E,hEmem⟩ ⟨F,hFmem⟩ hEF)⟩
  obtain ⟨hD,hreach⟩ := hpath _ hp
  exact hreach

theorem ThreeTreeOn.internalIncidence_connected {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (internalIncidence G).Connected := by
  classical
  obtain ⟨C,hC⟩ := h.tetrahedra_nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inl ⟨C,hC⟩,?_⟩
  intro N
  cases N with
  | inl D =>
    exact internalIncidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ D
      (h.tetrahedra_reachable hC D.2)
  | inr T =>
    have ht := mem_triangles.mp (mem_internalTriangles.mp T.2).1
    obtain ⟨D,hD,hTD⟩ := h.triangle_extends ht.1 ht.2
    exact (internalIncidence_reachable_of_tetrahedron_reachable ⟨C,hC⟩ ⟨D,hD⟩
      (h.tetrahedra_reachable hC hD)).trans
        (SimpleGraph.Adj.reachable
          (show (internalIncidence G).Adj (Sum.inl ⟨D,hD⟩) (Sum.inr T) from hTD))

theorem ThreeTreeOn.internalIncidence_isTree {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (internalIncidence G).IsTree := by
  exact ⟨h.internalIncidence_connected,
    h.incidence_isTree.isAcyclic.of_comap (internalIncidenceEmbedding G)⟩

end GraphicalZonotopes

end
end
end BundlePart56

section BundlePart57
/- Source: Papers/GraphicalZonotopes/RootedResponseAlgebra.lean -/












@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace RootedResponse

/-! The local construction in Lemma 6.2. These finite identities concern
the first tetrahedron of an arbitrary branch. The subsequent branch induction
must establish their application to the actual private-kernel equations. -/

abbrev Row := Fin 3 → Bool

abbrev Nonconstant (v : Row) : Prop :=
  (∃ i,v i=false) ∧ (∃ i,v i=true)

def third : Fin 3 → Fin 3 → Fin 3 :=
  ![![0,2,1],![2,1,0],![1,0,2]]

theorem third_distinct : ∀ i j : Fin 3,i≠ j → third i j≠ i ∧ third i j≠ j := by
  decide

/-- The diagonal is the boundary-edge coordinate. An off-diagonal entry
represents the common edge of two nonboundary faces. -/
def compatibleRows (occupied : Finset (Fin 3)) (v : Row) (i j : Fin 3) : Bool :=
  if i=j then v i
  else if i∈occupied then
    if j∈occupied then
      if occupied=Finset.univ then v (third i j) else !(v (third i j))
    else v j
  else v i

theorem compatibleRows_diagonal : ∀ occupied v i,
    compatibleRows occupied v i i=v i := by
  decide

theorem unoccupied_row_constant : ∀ occupied v i,i∉occupied →
    ∀ j,compatibleRows occupied v i j=v i := by
  decide

/-- This is exactly the simultaneous row choice in equation (6.1), for all
eight occupation patterns and all six permitted boundary response states. -/
theorem occupied_rows_nonconstant : ∀ occupied v,Nonconstant v →
    ∀ i,i∈occupied → Nonconstant (compatibleRows occupied v i) := by
  decide

theorem occupied_intersections_agree : ∀ occupied v i j,i≠ j →
    (i∈occupied ∨ j∈occupied) →
      compatibleRows occupied v i j=compatibleRows occupied v j i := by
  decide

def integerBit (b : Bool) : ℤ := if b then 1 else 0

/-- Equation (6.4), before embedding its integer values into the reals. -/
def coreSlack (a b x y : Bool) : ℤ :=
  max (integerBit a) (integerBit b)-integerBit a*integerBit y-
    integerBit b*integerBit x+integerBit x*integerBit y

theorem coreSlack_nonnegative : ∀ a b x y,0≤ coreSlack a b x y := by decide

theorem coreSlack_has_zero : ∀ a b,∃ x y,coreSlack a b x y=0 := by decide

theorem coreSlack_has_positive : ∀ a b,∃ x y,0< coreSlack a b x y := by decide

/-- Both values of either third-vertex bit remain visible at a reduced
zero when the two rows agree. -/
theorem coreSlack_equal_bits_zero : ∀ a x,coreSlack a a x a=0 := by decide

def boundarySlack (v x p : Bool) : ℤ :=
  -integerBit v*integerBit p+integerBit x*integerBit p

def boundaryMinimum (v x : Bool) : ℤ := integerBit v*(integerBit x-1)

theorem boundaryMinimum_le : ∀ v x p,boundaryMinimum v x≤ boundarySlack v x p := by
  decide

theorem boundaryMinimum_attained : ∀ v x,∃ p,boundarySlack v x p=boundaryMinimum v x := by
  decide

theorem boundaryStrictExcess : ∀ v,∃ x p,boundaryMinimum v x< boundarySlack v x p := by
  decide

theorem boundary_tie : ∀ v p,boundarySlack v v p=boundaryMinimum v v := by decide

/-- Recovering the effective coefficients from the three reduced zero
rows in the zero-bit case. All variation coefficients remain arbitrary real
numbers. -/
theorem recover_zero_effective_row (c A B h : ℝ)
    (h00 : c=0) (h10 : c-B=0) (h01 : c-A=0) :
    c=0 ∧ A=0 ∧ B=0 := by
  exact ⟨h00,by linarith,by linarith⟩

/-- The corresponding three-row recovery for the one-bit case. -/
theorem recover_one_effective_row (c A B h : ℝ)
    (h10 : c-B=0) (h01 : c-A=0) (h11 : c-A-B+h=0) :
    c=h ∧ A=h ∧ B=h := by
  exact ⟨by linarith,by linarith,by linarith⟩

def realBit (b : Bool) : ℝ := if b then 1 else 0

/-- The one-child completion `r=1-b` determines the child scale, rather
than merely asserting that the resulting boundary response vanishes. -/
theorem recover_one_child (b : Row) (hb : Nonconstant b) (d lam h : ℝ)
    (he : ∀ i,d-lam*(1-realBit (b i))=h*realBit (b i)) :
    d=h ∧ lam=h := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := hb
  have h0 := he i
  have h1 := he j
  simp only [hi,hj,realBit,Bool.false_eq_true,ite_false,ite_true] at h0 h1
  constructor <;> nlinarith

def unitResponse (i : Fin 3) (x : Fin 3) : ℝ := if x=i then 1 else 0

/-- Two other unit responses complete a unit row, and equation (6.6)
then fixes both child scales and the triangle coefficient. -/
theorem recover_two_unit_children (i j k : Fin 3)
    (hij : i≠ j) (hik : i≠ k) (hjk : j≠ k) (d lam mu h : ℝ)
    (he : ∀ x,d-lam*unitResponse i x-mu*unitResponse j x=h*unitResponse k x) :
    d=h ∧ lam=h ∧ mu=h := by
  have hi := he i
  have hj := he j
  have hk := he k
  simp only [unitResponse,ite_true,ite_false,hij,hik,hjk,
    Ne.symm hij,Ne.symm hik,Ne.symm hjk,mul_one,mul_zero,sub_zero] at hi hj hk
  exact ⟨by linarith,by linarith,by linarith⟩

/-- The complementary-unit completion gives triangle coefficient `2h`
and fixes the same common scale on both children. -/
theorem recover_two_complement_children (i j k : Fin 3)
    (hij : i≠ j) (hik : i≠ k) (hjk : j≠ k) (d lam mu h : ℝ)
    (he : ∀ x,d-lam*(1-unitResponse i x)-mu*(1-unitResponse j x)=
      h*(1-unitResponse k x)) :
    d=2*h ∧ lam=h ∧ mu=h := by
  have hi := he i
  have hj := he j
  have hk := he k
  simp only [unitResponse,ite_true,ite_false,hij,hik,hjk,
    Ne.symm hij,Ne.symm hik,Ne.symm hjk,mul_one,mul_zero,sub_zero,sub_self] at hi hj hk
  exact ⟨by linarith,by linarith,by linarith⟩

end RootedResponse
end GraphicalZonotopes

end
end BundlePart57

section BundlePart58
/- Source: Papers/GraphicalZonotopes/TetrahedronRows.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 100000
set_option maxRecDepth 4096
namespace GraphicalZonotopes
namespace RootedResponse

/-- Face `i` has coordinates indexed by the other three faces. The entry
at `(i,j)` belongs to their actual common edge. Diagonal entries are unused. -/
abbrev FaceRows := Fin 4 → Fin 4 → Bool

abbrev NonconstantFace (f : Fin 4 → Bool) (i : Fin 4) : Prop :=
  (∃ j,j≠ i ∧ f j=false) ∧ (∃ j,j≠ i ∧ f j=true)

abbrev ConstantFace (f : Fin 4 → Bool) (i : Fin 4) : Prop :=
  ∃ b,∀ j,j≠ i → f j=b

def fourRows (occupied : Finset (Fin 3)) (v : Row) : FaceRows :=
  ![![false,compatibleRows occupied v 0 1,compatibleRows occupied v 0 2,v 0],
    ![compatibleRows occupied v 1 0,false,compatibleRows occupied v 1 2,v 1],
    ![compatibleRows occupied v 2 0,compatibleRows occupied v 2 1,false,v 2],
    ![v 0,v 1,v 2,false]]

abbrev internalFace (occupied : Finset (Fin 3)) (i : Fin 4) : Prop :=
  i=3 ∨ ∃ j : Fin 3,j∈occupied ∧ i=j.castSucc

theorem fourRows_root : ∀ occupied v (i : Fin 3),
    fourRows occupied v 3 i.castSucc=v i := by decide

theorem fourRows_nonconstant : ∀ occupied v,Nonconstant v →
    ∀ i,internalFace occupied i → NonconstantFace (fourRows occupied v i) i := by
  unfold Nonconstant NonconstantFace internalFace
  decide

theorem fourRows_constant : ∀ occupied v i,¬internalFace occupied i →
    ConstantFace (fourRows occupied v i) i := by decide

theorem fourRows_agree : ∀ occupied v i j,i≠ j →
    (internalFace occupied i ∨ internalFace occupied j) →
      fourRows occupied v i j=fourRows occupied v j i := by decide

/-- Relabel the root face by a literal permutation. This construction
works for each of the four possible incoming faces; no preferred vertex is
part of the final local-state predicate. -/
def relabelledRows (internal : Finset (Fin 4)) (r : Fin 4)
    (v : Fin 4 → Bool) : FaceRows :=
  let p := Equiv.swap (3 : Fin 4) r
  let occupied := Finset.univ.filter (fun i : Fin 3 => p i.castSucc∈internal)
  let input : Row := fun i => v (p i.castSucc)
  fun i j => fourRows occupied input (p.symm i) (p.symm j)

/-- The finite local extension theorem for one actual tetrahedron. Every
prescribed nonconstant row on any internal face extends to rows on all four
faces. Internal rows remain nonconstant, leaf rows are constant, and every
edge incident with an internal face has matching rows on its two faces. -/
theorem relabelledRows_spec : ∀ internal r v,r∈internal → NonconstantFace v r →
    (∀ j,j≠ r → relabelledRows internal r v r j=v j) ∧
    (∀ i,i∈internal → NonconstantFace (relabelledRows internal r v i) i) ∧
    (∀ i,i∉internal → ConstantFace (relabelledRows internal r v i) i) ∧
    (∀ i j,i≠ j → (i∈internal ∨ j∈internal) →
      relabelledRows internal r v i j=relabelledRows internal r v j i) := by
  unfold NonconstantFace ConstantFace
  decide

theorem exists_nonconstantFace : ∀ r : Fin 4,∃ v : Fin 4 → Bool,NonconstantFace v r := by decide

end RootedResponse
end GraphicalZonotopes

end
end BundlePart58

section BundlePart59
/- Source: Papers/GraphicalZonotopes/FourState.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace RootedResponse
variable {W : Type*} [Fintype W]

abbrev NonconstantAt (v : W → Bool) (r : W) : Prop :=
  (∃ j,j≠ r ∧ v j=false) ∧ (∃ j,j≠ r ∧ v j=true)

/-- Intrinsic local states on the four vertices of a tetrahedron. A face
is indexed by its missing vertex, and a coordinate on that face is indexed
by the third vertex opposite the corresponding edge. -/
structure FourState (internal : W → Prop) where
  row : W → W → Bool
  nonconstant : ∀ i,internal i → NonconstantAt (row i) i
  constant : ∀ i,¬internal i → ∃ b,∀ j,j≠ i → row i j=b
  agree : ∀ i j,i≠ j → (internal i ∨ internal j) → row i j=row j i

theorem fourState_extend (hcard : Fintype.card W=4) (internal : W → Prop)
    (r : W) (hr : internal r) (v : W → Bool) (hv : NonconstantAt v r) :
    ∃ s : FourState internal,∀ j,j≠ r → s.row r j=v j := by
  classical
  let e := Fintype.equivFinOfCardEq hcard
  let I : Finset (Fin 4) := Finset.univ.filter (fun i => internal (e.symm i))
  let input : Fin 4 → Bool := fun i => v (e.symm i)
  have hroot : e r∈I := by simp [I,hr]
  have hin : NonconstantFace input (e r) := by
    obtain ⟨⟨j,hjr,hj⟩,⟨k,hkr,hk⟩⟩ := hv
    exact ⟨⟨e j,(fun he => hjr (e.injective he)),by simpa [input] using hj⟩,
      ⟨e k,(fun he => hkr (e.injective he)),by simpa [input] using hk⟩⟩
  obtain ⟨hport,hnon,hconst,hagree⟩ := relabelledRows_spec I (e r) input hroot hin
  let rows : W → W → Bool := fun i j => relabelledRows I (e r) input (e i) (e j)
  have hnon' : ∀ i,internal i → NonconstantAt (rows i) i := by
    intro i hi
    obtain ⟨⟨j,hji,hj⟩,⟨k,hki,hk⟩⟩ := hnon (e i) (by simp [I,hi])
    refine ⟨⟨e.symm j,?_,?_⟩,⟨e.symm k,?_,?_⟩⟩
    · intro he
      exact hji (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
    · simpa only [rows,Equiv.apply_symm_apply] using hj
    · intro he
      exact hki (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
    · simpa only [rows,Equiv.apply_symm_apply] using hk
  have hconst' : ∀ i,¬internal i → ∃ b,∀ j,j≠ i → rows i j=b := by
    intro i hi
    obtain ⟨b,hb⟩ := hconst (e i) (by simp [I,hi])
    exact ⟨b,fun j hji => hb (e j) (fun he => hji (e.injective he))⟩
  have hagree' : ∀ i j,i≠ j → (internal i ∨ internal j) → rows i j=rows j i := by
    intro i j hij hi
    apply hagree (e i) (e j) (fun he => hij (e.injective he))
    simpa only [I,Finset.mem_filter,Finset.mem_univ,true_and,
      Equiv.symm_apply_apply] using hi
  refine ⟨⟨rows,hnon',hconst',hagree'⟩,?_⟩
  intro j hjr
  simpa only [rows,input,Equiv.symm_apply_apply] using
    hport (e j) (fun he => hjr (e.injective he))

theorem exists_nonconstantAt (hcard : Fintype.card W=4) (r : W) :
    ∃ v : W → Bool,NonconstantAt v r := by
  classical
  have h := exists_nonconstantFace
  let e := Fintype.equivFinOfCardEq hcard
  obtain ⟨v,⟨⟨j,hjr,hj⟩,⟨k,hkr,hk⟩⟩⟩ := h (e r)
  refine ⟨fun x => v (e x),⟨e.symm j,?_,?_⟩,⟨e.symm k,?_,?_⟩⟩
  · intro he
    exact hjr (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
  · simpa only [Equiv.apply_symm_apply] using hj
  · intro he
    exact hkr (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
  · simpa only [Equiv.apply_symm_apply] using hk

theorem fourState_nonempty (hcard : Fintype.card W=4) (internal : W → Prop) :
    Nonempty (FourState internal) := by
  classical
  by_cases hi : ∃ r,internal r
  · obtain ⟨r,hr⟩ := hi
    obtain ⟨v,hv⟩ := exists_nonconstantAt hcard r
    obtain ⟨s,hs⟩ := fourState_extend hcard internal r hr v hv
    exact ⟨s⟩
  · exact ⟨{
      row := fun _ _ => false
      nonconstant := fun i hi' => False.elim (hi ⟨i,hi'⟩)
      constant := fun _ _ => ⟨false,fun _ _ => rfl⟩
      agree := fun _ _ _ _ => rfl }⟩

end RootedResponse
end GraphicalZonotopes

end
end
end BundlePart59

section BundlePart60
/- Source: Papers/GraphicalZonotopes/TriangleRows.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace RootedResponse
open Finset
open scoped BigOperators

def unitBit (i : Fin 3) (x : Fin 3) : Bool := decide (x=i)

def exceptionalCoordinate (v : Row) : Fin 3 :=
  if v 0=v 1 then 2 else if v 0=v 2 then 1 else 0

/-- Each nonconstant three-bit vector is a unit vector or a complementary
unit vector. The exceptional coordinate is selected by a fixed formula. -/
theorem exceptionalCoordinate_spec : ∀ v,Nonconstant v →
    ∀ x,v x=if v (exceptionalCoordinate v) then
      unitBit (exceptionalCoordinate v) x else !(unitBit (exceptionalCoordinate v) x) := by
  decide

def threeRows (complement : Bool) (p : Equiv.Perm (Fin 3)) (j : Fin 3) : Row :=
  fun x => if complement then !(unitBit (p j) x) else unitBit (p j) x

theorem threeRows_nonconstant (complement : Bool) (p : Equiv.Perm (Fin 3))
    (j : Fin 3) : Nonconstant (threeRows complement p j) := by
  have h : ∀ (complement : Bool) (i : Fin 3),Nonconstant
      (fun x => if complement then !(unitBit i x) else unitBit i x) := by decide
  exact h complement (p j)

/-- Any prescribed nonconstant incoming row can occupy any of the three
branch positions. The other rows have the same unit/complement type. -/
theorem threeRows_extend (j : Fin 3) (v : Row) (hv : Nonconstant v) :
    ∃ complement p,threeRows complement p j=v := by
  let i := exceptionalCoordinate v
  refine ⟨!(v i),Equiv.swap j i,?_⟩
  funext x
  rw [exceptionalCoordinate_spec v hv x]
  simp only [threeRows,Equiv.swap_apply_left]
  change (if !(v i) then !(unitBit i x) else unitBit i x)=
    (if v i then unitBit i x else !(unitBit i x))
  cases v i <;> rfl

theorem weighted_unit_row (p : Equiv.Perm (Fin 3)) (lam : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i,lam i*realBit (unitBit (p i) (p j)))=lam j := by
  rw [sum_eq_single j]
  · simp [unitBit,realBit]
  · intro i hi hij
    have he : p j≠ p i := fun he => hij (p.injective he.symm)
    simp [unitBit,realBit,he]
  · intro hj
    exact False.elim (hj (mem_univ j))

theorem realBit_not (b : Bool) : realBit (!b)=1-realBit b := by
  cases b <;> norm_num [realBit]

theorem weighted_threeRows_at (complement : Bool) (p : Equiv.Perm (Fin 3))
    (lam : Fin 3 → ℝ) (j : Fin 3) :
    (∑ i,lam i*realBit (threeRows complement p i (p j)))=
      if complement then (∑ i,lam i)-lam j else lam j := by
  cases complement
  · simpa only [threeRows,Bool.false_eq_true,ite_false] using weighted_unit_row p lam j
  · simp only [threeRows,ite_true,realBit_not,mul_sub,mul_one]
    rw [sum_sub_distrib,weighted_unit_row]

/-- The quotient response relation is exactly one-dimensional. No
positivity or prior common-scale hypothesis is used to recover the scales. -/
theorem threeRows_relation_kernel (complement : Bool) (p : Equiv.Perm (Fin 3))
    (lam : Fin 3 → ℝ) (d : ℝ)
    (h : ∀ x,(∑ i,lam i*realBit (threeRows complement p i x))=d) :
    (∀ i,lam i=lam 0) ∧ d=(if complement then 2 else 1)*lam 0 := by
  have he : ∀ j,(if complement then (∑ i,lam i)-lam j else lam j)=d := by
    intro j
    rw [← weighted_threeRows_at]
    exact h (p j)
  have hs : ∀ j,lam j=lam 0 := by
    intro j
    have h0 := he 0
    have hj := he j
    cases complement <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h0 hj <;>
      linarith
  refine ⟨hs,?_⟩
  have h0 := he 0
  have hsum : (∑ i,lam i)=3*lam 0 := by
    simp only [hs,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    norm_num
  rw [hsum] at h0
  cases complement <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h0 ⊢ <;>
    linarith

theorem threeRows_sum (complement : Bool) (p : Equiv.Perm (Fin 3)) (x : Fin 3) :
    (∑ i,realBit (threeRows complement p i x))=if complement then 2 else 1 := by
  have h := weighted_threeRows_at complement p (fun _ => 1) (p.symm x)
  have hsum : (∑ _ : Fin 3,(1:ℝ))=3 := by norm_num
  rw [hsum] at h
  simpa only [Equiv.apply_symm_apply,one_mul,show (3:ℝ)-1=2 by norm_num] using h

def twoRows (v : Row) : Fin 2 → Row := ![v,fun x => !(v x)]

theorem twoRows_nonconstant : ∀ v,Nonconstant v → ∀ j,Nonconstant (twoRows v j) := by
  decide

theorem twoRows_sum (v : Row) (x : Fin 3) :
    (∑ i,realBit (twoRows v i x))=1 := by
  rw [Fin.sum_univ_two]
  change realBit (v x) + realBit (!(v x)) = 1
  cases v x <;> norm_num [realBit]

theorem twoRows_relation_kernel (v : Row) (hv : Nonconstant v)
    (lam : Fin 2 → ℝ) (d : ℝ)
    (h : ∀ x,(∑ i,lam i*realBit (twoRows v i x))=d) :
    lam 0=lam 1 ∧ d=lam 0 := by
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := hv
  have h0 := h i
  have h1 := h j
  simp [twoRows,Fin.sum_univ_two,hi,hj,realBit] at h0 h1
  exact ⟨by linarith,by linarith⟩

end RootedResponse
end GraphicalZonotopes

end
end BundlePart60

section BundlePart61
/- Source: Papers/GraphicalZonotopes/TriangleState.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace RootedResponse
open Finset
open scoped BigOperators
variable {J T J' T' : Type*} [Fintype J] [Fintype T] [Fintype J'] [Fintype T']

abbrev NonconstantBits (v : T → Bool) : Prop := (∃ x,v x=false) ∧ (∃ x,v x=true)

theorem nonconstantBits_comp (e : T' ≃ T) (v : T → Bool) :
    NonconstantBits (fun x => v (e x)) ↔ NonconstantBits v := by
  constructor
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    exact ⟨⟨e x,hx⟩,⟨e y,hy⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    exact ⟨⟨e.symm x,by simpa using hx⟩,⟨e.symm y,by simpa using hy⟩⟩

/-- Complete local data at an internal triangle: nonconstant incident
rows, constant column sum one or two, and the full real response-kernel
condition forcing all incident clique scales to agree. -/
structure TriangleState (J T : Type*) [Fintype J] where
  row : J → T → Bool
  degree : ℕ
  degree_mem : degree=1 ∨ degree=2
  nonconstant : ∀ j,NonconstantBits (row j)
  sum_row : ∀ x,(∑ j,realBit (row j x))=(degree : ℝ)
  kernel : ∀ (lam : J → ℝ) (d : ℝ),
    (∀ x,(∑ j,lam j*realBit (row j x))=d) → ∀ i j,lam i=lam j

def TriangleState.relabel (s : TriangleState J T) (e : J' ≃ J) (f : T' ≃ T) :
    TriangleState J' T' where
  row j x := s.row (e j) (f x)
  degree := s.degree
  degree_mem := s.degree_mem
  nonconstant j := (nonconstantBits_comp f _).mpr (s.nonconstant (e j))
  sum_row x := by
    rw [Equiv.sum_comp e (fun j => realBit (s.row j (f x)))]
    exact s.sum_row (f x)
  kernel lam d h i j := by
    let μ : J → ℝ := fun k => lam (e.symm k)
    have hμ : ∀ x,(∑ k,μ k*realBit (s.row k x))=d := by
      intro x
      have hx := h (f.symm x)
      simp only [Equiv.apply_symm_apply] at hx
      rw [← Equiv.sum_comp e (fun k => μ k*realBit (s.row k x))]
      simpa only [μ,Equiv.symm_apply_apply] using hx
    simpa only [μ,Equiv.symm_apply_apply] using s.kernel μ d hμ (e i) (e j)

def threeState (complement : Bool) (p : Equiv.Perm (Fin 3)) :
    TriangleState (Fin 3) (Fin 3) where
  row := threeRows complement p
  degree := if complement then 2 else 1
  degree_mem := by cases complement <;> simp
  nonconstant := threeRows_nonconstant complement p
  sum_row x := by
    cases complement
    · simpa only [Bool.false_eq_true, ite_false, Nat.cast_one] using threeRows_sum false p x
    · simpa only [ite_true, Nat.cast_ofNat] using threeRows_sum true p x
  kernel lam d h i j :=
    (threeRows_relation_kernel complement p lam d h).1 i |>.trans
      ((threeRows_relation_kernel complement p lam d h).1 j).symm

def twoState (v : Row) (hv : Nonconstant v) : TriangleState (Fin 2) (Fin 3) where
  row := twoRows v
  degree := 1
  degree_mem := Or.inl rfl
  nonconstant := twoRows_nonconstant v hv
  sum_row x := by simpa only [Nat.cast_one] using twoRows_sum v x
  kernel lam d h i j := by
    have he := (twoRows_relation_kernel v hv lam d h).1
    fin_cases i <;> fin_cases j
    · rfl
    · exact he
    · exact he.symm
    · rfl

def twoInput (j : Fin 2) (v : Row) : Row := if j=0 then v else fun x => !(v x)

theorem twoInput_nonconstant : ∀ j v,Nonconstant v → Nonconstant (twoInput j v) := by
  decide

theorem twoInput_port : ∀ j v,twoRows (twoInput j v) j=v := by decide

theorem triangleState_extend (hT : Fintype.card T=3)
    (hJ : Fintype.card J=2 ∨ Fintype.card J=3) (j : J)
    (v : T → Bool) (hv : NonconstantBits v) :
    ∃ s : TriangleState J T,s.row j=v := by
  classical
  let f := Fintype.equivFinOfCardEq hT
  let input : Row := fun x => v (f.symm x)
  have hin : Nonconstant input := (nonconstantBits_comp f.symm v).mpr hv
  rcases hJ with hJ | hJ
  · let e := Fintype.equivFinOfCardEq hJ
    let s := twoState (twoInput (e j) input) (twoInput_nonconstant _ _ hin)
    refine ⟨s.relabel e f,?_⟩
    funext x
    change twoRows (twoInput (e j) input) (e j) (f x)=v x
    rw [twoInput_port]
    exact congrArg v (f.symm_apply_apply x)
  · let e := Fintype.equivFinOfCardEq hJ
    obtain ⟨complement,p,hport⟩ := threeRows_extend (e j) input hin
    refine ⟨(threeState complement p).relabel e f,?_⟩
    funext x
    change threeRows complement p (e j) (f x)=v x
    rw [hport]
    exact congrArg v (f.symm_apply_apply x)

theorem triangleState_nonempty (hT : Fintype.card T=3)
    (hJ : Fintype.card J=2 ∨ Fintype.card J=3) :
    Nonempty (TriangleState J T) := by
  classical
  have hpos : 0< Fintype.card J := by rcases hJ with hJ | hJ <;> omega
  letI : Nonempty J := Fintype.card_pos_iff.mp hpos
  let f := Fintype.equivFinOfCardEq hT
  let input : T → Bool := fun x => unitBit 0 (f x)
  have hv : NonconstantBits input := (nonconstantBits_comp f (unitBit 0)).mpr ⟨⟨1, rfl⟩, ⟨0, rfl⟩⟩
  obtain ⟨s,hs⟩ := triangleState_extend hT hJ (Classical.arbitrary J) input hv
  exact ⟨s⟩

end RootedResponse
end GraphicalZonotopes

end
end
end BundlePart61

section BundlePart62
/- Source: Papers/GraphicalZonotopes/TreeCompatibility.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
universe u v w

/-- A finite tree of nonempty local state spaces has compatible states if
every state at one end of an edge can be matched at the other end. There
are no compatibility conditions on nonedges and no chosen-root hypothesis.
This is the exact finite constraint-tree gluing step needed for the bit-row
construction, independent of its geometric application. -/
theorem tree_compatible_states {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (State : V → Type v)
    (hne : ∀ v,Nonempty (State v)) (Color : Type w)
    (port : ∀ u v,State u → Color)
    (hextend : ∀ u v,G.Adj u v → ∀ t : State v,
      ∃ s : State u,port u v s=port v u t) :
    ∃ s : ∀ v,State v,∀ u v,G.Adj u v → port u v (s u)=port v u (s v) := by
  classical
  suffices h : ∀ n,∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W),Fintype.card W=n → H.IsTree →
      ∀ (S : W → Type v),(∀ v,Nonempty (S v)) →
      ∀ (p : ∀ u v,S u → Color),
      (∀ u v,H.Adj u v → ∀ t : S v,∃ s : S u,p u v s=p v u t) →
      ∃ s : ∀ v,S v,∀ u v,H.Adj u v → p u v (s u)=p v u (s v) from
    h _ V G rfl hG State hne port hextend
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ H hcard htree S hne p hextend
    by_cases hsub : Subsingleton W
    · letI : Subsingleton W := hsub
      refine ⟨fun v => Classical.choice (hne v),?_⟩
      intro u v huv
      exact False.elim (huv.ne (Subsingleton.elim u v))
    · letI : Nontrivial W := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨r,hdeg⟩ := htree.exists_vert_degree_one_of_nontrivial
      obtain ⟨q,hrq,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
      let W' := {x : W // x≠ r}
      let H' : SimpleGraph W' := H.induce {r}ᶜ
      have htree' : H'.IsTree :=
        ⟨htree.connected.induce_compl_singleton_of_degree_eq_one hdeg,
          htree.isAcyclic.induce _⟩
      have hlt : Fintype.card W'< n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (x:=r) (by simp)
      obtain ⟨s,hs⟩ := ih (Fintype.card W') hlt W' H' rfl htree'
        (fun v => S v.1) (fun v => hne v.1) (fun u v => p u.1 v.1)
        (fun u v huv t => hextend u.1 v.1 huv t)
      have hqr : q≠ r := hrq.ne.symm
      obtain ⟨sr,hsr⟩ := hextend r q hrq (s ⟨q,hqr⟩)
      let t : ∀ x,S x := fun x =>
        if hx : x=r then hx.symm ▸ sr else s ⟨x,hx⟩
      have htroot : t r=sr := by simp only [t,dif_pos rfl]
      have htoff : ∀ x (hx : x≠ r),t x=s ⟨x,hx⟩ := by
        intro x hx
        simp only [t,dif_neg hx]
      refine ⟨t,?_⟩
      intro u v huv
      by_cases hur : u=r
      · subst u
        have hvq : v=q := hunique v huv
        subst v
        rw [htroot,htoff q hqr]
        exact hsr
      · by_cases hvr : v=r
        · subst v
          have huq : u=q := hunique u huv.symm
          subst u
          rw [htroot,htoff q hqr]
          exact hsr.symm
        · rw [htoff u hur,htoff v hvr]
          exact hs ⟨u,hur⟩ ⟨v,hvr⟩ huv

end GraphicalZonotopes

end
end
end BundlePart62
