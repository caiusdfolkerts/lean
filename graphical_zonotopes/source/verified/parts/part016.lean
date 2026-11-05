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

public import verified.parts.part015
import all verified.parts.part015

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart223
/- Source: Papers/GraphicalZonotopes/DiamondBookCapacity.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped BigOperators
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def boundary (k : ℕ) : Finset (Vertex k):={a k,b k,u k,v k}
def privateVertex (k : ℕ) (j : Fin k) : Vertex k:=⟨j.val+4,by omega⟩
def privatePart (k : ℕ) (j : Fin k) : Finset (Vertex k):={privateVertex k j}

theorem boundary_card (k : ℕ) : (boundary k).card=4 := by
  simp [boundary,a,b,u,v,Fin.ext_iff]

theorem mem_boundary_iff (k : ℕ) (x : Vertex k) : x∈boundary k ↔ x.val<4 := by
  simp only [boundary,mem_insert,mem_singleton,Fin.ext_iff,a,b,u,v]
  omega

theorem privateVertex_injective (k : ℕ) : Function.Injective (privateVertex k) := by
  intro i j hij
  apply Fin.ext
  have hh:=congrArg Fin.val hij
  change i.val+4=j.val+4 at hh
  omega

theorem private_part_value (k : ℕ) (j : Fin k) : part k (privateVertex k j)=3 := by
  simp [part,privateVertex]

theorem partition (k : ℕ) : Separator.Partition (graph k) (boundary k) (privatePart k) where
  boundary_disjoint j:=by
    apply disjoint_left.mpr
    intro x hx hxp
    have he:x=privateVertex k j:=mem_singleton.mp hxp
    rw [he,mem_boundary_iff] at hx
    change j.val+4<4 at hx
    omega
  private_disjoint:=by
    intro i j hij
    exact disjoint_singleton.mpr (fun he => hij (privateVertex_injective k he))
  cover x:=by
    by_cases hx:x.val<4
    · exact Or.inl ((mem_boundary_iff k x).mpr hx)
    · apply Or.inr
      let j : Fin k:=⟨x.val-4,by have:=x.isLt; omega⟩
      refine ⟨j,?_⟩
      apply mem_singleton.mpr
      apply Fin.ext
      change x.val=(x.val-4)+4
      omega
  no_cross_edge:=by
    intro i j x y hx hy hxy
    have hx':x=privateVertex k i:=mem_singleton.mp hx
    have hy':y=privateVertex k j:=mem_singleton.mp hy
    subst x
    subst y
    change part k (privateVertex k i)≠ part k (privateVertex k j) at hxy
    rw [private_part_value,private_part_value] at hxy
    exact False.elim (hxy rfl)

theorem boundary_cliques_card (k : ℕ) :
    (Separator.boundaryCliques (graph k) (boundary k)).card=7 := by
  classical
  have hp (x : Vertex k) : ({x} : Finset (Vertex k)).powerset={∅,{x}} := by
    ext S
    simp [Finset.subset_singleton_iff]
  norm_num [Separator.boundaryCliques,boundary,IsCliqueCoordinate,
    SimpleGraph.IsClique,Set.Pairwise,graph,part_a,part_b,part_u,part_v,
    Finset.powerset_insert,hp,Finset.filter_insert,Finset.filter_singleton]
  exact of_decide_eq_true rfl

def boundaryEdges (k : ℕ) : Finset (Vertex k × Vertex k):=
  {(a k,b k),(a k,u k),(a k,v k),(b k,u k),(b k,v k)}

theorem boundary_edge_iff (k : ℕ) (x y : Vertex k) :
    (x< y ∧ (graph k).Adj x y ∧ x∈boundary k ∧ y∈boundary k) ↔
      (x,y)∈boundaryEdges k := by
  constructor
  · rintro ⟨hlt,he,hx,hy⟩
    simp only [boundary,mem_insert,mem_singleton] at hx hy
    rcases hx with rfl|rfl|rfl|rfl <;>
      rcases hy with rfl|rfl|rfl|rfl <;>
      norm_num [boundaryEdges,graph,part,a,b,u,v,Fin.lt_def] at *
  · intro he
    simp only [boundaryEdges,mem_insert,mem_singleton,Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      norm_num [boundary,graph,part,a,b,u,v,Fin.lt_def]

def boundaryEdgeEquiv (k : ℕ) :
    Separator.BoundaryEdge (graph k) (boundary k) ≃ ↥(boundaryEdges k) where
  toFun e:=⟨e.1.1,(boundary_edge_iff k _ _).mp ⟨e.1.2.1,e.1.2.2,e.2⟩⟩
  invFun e:=
    let h:=(boundary_edge_iff k e.1.1 e.1.2).mpr e.2
    ⟨⟨e.1,h.1,h.2.1⟩,h.2.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem common_boundary_ab (k : ℕ) :
    commonNeighbors (graph k) (a k) (b k)∩boundary k={u k,v k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_au (k : ℕ) :
    commonNeighbors (graph k) (a k) (u k)∩boundary k={b k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_av (k : ℕ) :
    commonNeighbors (graph k) (a k) (v k)∩boundary k={b k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_bu (k : ℕ) :
    commonNeighbors (graph k) (b k) (u k)∩boundary k={a k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem common_boundary_bv (k : ℕ) :
    commonNeighbors (graph k) (b k) (v k)∩boundary k={a k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hn,hB⟩:=mem_inter.mp hx
    simp only [boundary,mem_insert,mem_singleton] at hB
    rcases hB with rfl|rfl|rfl|rfl
    all_goals simp_all [mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]
  · intro hx
    simp only [mem_insert,mem_singleton] at hx
    subst x
    all_goals apply mem_inter.mpr
    all_goals constructor
    all_goals simp [boundary,mem_commonNeighbors,graph,part_a,part_b,part_u,part_v]

theorem boundary_rows_count (k : ℕ) :
    (∑ e : Separator.BoundaryEdge (graph k) (boundary k),
      2^(commonNeighbors (graph k) e.1.1.1 e.1.1.2∩boundary k).card)=12 := by
  classical
  have hsum : (∑ e : Separator.BoundaryEdge (graph k) (boundary k),
      2^(commonNeighbors (graph k) e.1.1.1 e.1.1.2∩boundary k).card)=
      ∑ e∈boundaryEdges k,2^(commonNeighbors (graph k) e.1 e.2∩boundary k).card := by
    calc
      _ = ∑ e : ↥(boundaryEdges k),
          (2 : ℕ)^(commonNeighbors (graph k) e.1.1 e.1.2∩boundary k).card :=
        Fintype.sum_equiv (boundaryEdgeEquiv k)
          (fun e : Separator.BoundaryEdge (graph k) (boundary k) =>
            (2 : ℕ)^(commonNeighbors (graph k) e.1.1.1 e.1.1.2∩boundary k).card)
          (fun e : ↥(boundaryEdges k) =>
            (2 : ℕ)^(commonNeighbors (graph k) e.1.1 e.1.2∩boundary k).card)
          (fun _ => rfl)
      _ = _ := sum_coe_sort (boundaryEdges k)
        (fun e : Vertex k × Vertex k =>
          (2 : ℕ)^(commonNeighbors (graph k) e.1 e.2∩boundary k).card)
  rw [hsum]
  simp [boundaryEdges,common_boundary_ab,common_boundary_au,common_boundary_av,
    common_boundary_bu,common_boundary_bv]

/-- The exact diamond separator capacity, independent of the number of
private vertices and allowing every zero private block. -/
theorem active_capacity (k : ℕ) (z : graphicalFunctionSpace (graph k))
    (hz : ExtremeSupermodular z.1) :
    Fintype.card (Gluing.ActiveBranch (((Separator.functionEquiv (partition k)).symm z).2))≤6 := by
  have hb:=Separator.separator_capacity_for_function (partition k) z hz
  rw [boundary_rows_count,boundary_cliques_card] at hb
  exact hb

theorem dimension_le_nine (k : ℕ) (z : graphicalFunctionSpace (graph k))
    (hz : ExtremeSupermodular z.1) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))≤9 := by
  have hb:=Separator.finrank_le_boundary_add_active (partition k)
    (fun j => by simp [privatePart]) z hz.2.1
  rw [boundary_card] at hb
  have ha:=active_capacity k z hz
  omega

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart223

section BundlePart224
/- Source: Papers/GraphicalZonotopes/DiamondBookUpperBound.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset

theorem actual_summand_dimension_bound (k : ℕ) {Q : Set (Vertex k → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (graph k))) :
    Module.finrank ℝ (vectorSpan ℝ Q)≤ min (k+3) 9 := by
  apply le_min
  · have hb:=weak_summand_dimension_le hQ hi hw
    simp only [Fintype.card_fin] at hb
    omega
  · obtain ⟨z,hz,hzero|hext,hd⟩:=weak_summand_extreme_or_zero hQ hi hw
    · rw [hd,hzero,basePolytope_zero,vectorSpan_singleton,finrank_bot]
      norm_num
    · rw [hd]
      exact dimension_le_nine k z hext

/-- The upper half of the paper's complete dimension formula, with its
literal supremum over all actual indecomposable weak polytope summands. -/
theorem maximum_dimension_upper (k : ℕ) :
    maximumIndecomposableDimension (graph k)≤ min (k+3) 9 := by
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  rw [← hd]
  exact actual_summand_dimension_bound k hQ hi hw

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart224

section BundlePart225
/- Source: Papers/GraphicalZonotopes/DiamondBookSmallTrees.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped BigOperators Pointwise
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192

instance decidableCliqueGraph {V : Type*} [DecidableEq V] (C : Finset V) :
    DecidableRel (cliqueGraph C).Adj :=
  fun x y => inferInstanceAs (Decidable (x≠ y ∧ x∈C ∧ y∈C))
instance decidableAttachmentStar {V : Type*} [DecidableEq V] (x : V) (T : Finset V) :
    DecidableRel (attachmentStar x T).Adj :=
  fun y z => inferInstanceAs (Decidable (y≠ z ∧ ((y=x ∧ z∈T) ∨ (z=x ∧ y∈T))))

theorem admissible_of_tetrahedron_list {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V)) (hF : tetrahedra G=F)
    (hcap : ∀ T∈F.biUnion (fun C => C.powerset.filter (fun T => T.card=3)),
      (F.filter (fun C => T⊆C)).card≤3) : Admissible G := by
  classical
  intro T hT hc
  rw [triangleMultiplicity,hF]
  by_cases he : (F.filter (fun C => T⊆C)).Nonempty
  · obtain ⟨C,hC⟩:=he
    obtain ⟨hCF,hTC⟩:=mem_filter.mp hC
    exact hcap T (mem_biUnion.mpr ⟨C,hCF,mem_filter.mpr ⟨mem_powerset.mpr hTC,hT⟩⟩)
  · rw [not_nonempty_iff_eq_empty.mp he,card_empty]
    norm_num

def small1G0 : SimpleGraph (Fin 5) := cliqueGraph {0,1,2,4}
instance small1dec0 : DecidableRel small1G0.Adj := by unfold small1G0; infer_instance
theorem small1tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 5)) small1G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small1F0 : Finset (Finset (Fin 5)) := {{0,1,2,4}}
theorem small1tetra0 : tetrahedra small1G0=small1F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small1G1 : SimpleGraph (Fin 5) := small1G0 ⊔ attachmentStar 3 {0,1,4}
instance small1dec1 : DecidableRel small1G1.Adj := by unfold small1G1; infer_instance
theorem small1clique1 : small1G0.IsClique ({0,1,4} : Finset (Fin 5)) := by
  unfold small1G0
  decide +kernel
theorem small1tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 5)) small1G1 := by
  have h:=ThreeTreeOn.attach small1tree0 (3 : Fin 5) (by decide +kernel)
    ({0,1,4} : Finset (Fin 5)) (by decide +kernel) (by decide +kernel) small1clique1
  simpa only [small1G1,show insert (3 : Fin 5) ({0,1,2,4} : Finset (Fin 5))={0,1,2,4,3} from by decide +kernel] using h
def small1F1 : Finset (Finset (Fin 5)) := insert (insert 3 {0,1,4}) small1F0
theorem small1tetra1 : tetrahedra small1G1=small1F1 := by
  rw [small1G1,tetrahedra_after_attachment small1tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small1clique1,small1tetra0]
  rfl

theorem small1spanning : IsThreeTree small1G1 := by
  change ThreeTreeOn univ small1G1
  have he : ({0,1,2,4,3} : Finset (Fin 5))=univ := by decide +kernel
  simpa only [he] using small1tree1

theorem small1admissible : Admissible small1G1 := by
  apply admissible_of_tetrahedron_list small1G1 small1F1 small1tetra1
  intro T hT
  unfold small1F1 small1F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small1subgraph : small1G1≤ graph 1 := by
  change ∀ x y,small1G1.Adj x y → (graph 1).Adj x y
  unfold small1G1 small1G0
  decide +kernel

def small2G0 : SimpleGraph (Fin 6) := cliqueGraph {0,1,2,4}
instance small2dec0 : DecidableRel small2G0.Adj := by unfold small2G0; infer_instance
theorem small2tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 6)) small2G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small2F0 : Finset (Finset (Fin 6)) := {{0,1,2,4}}
theorem small2tetra0 : tetrahedra small2G0=small2F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small2G1 : SimpleGraph (Fin 6) := small2G0 ⊔ attachmentStar 3 {0,1,4}
instance small2dec1 : DecidableRel small2G1.Adj := by unfold small2G1; infer_instance
theorem small2clique1 : small2G0.IsClique ({0,1,4} : Finset (Fin 6)) := by
  unfold small2G0
  decide +kernel
theorem small2tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 6)) small2G1 := by
  have h:=ThreeTreeOn.attach small2tree0 (3 : Fin 6) (by decide +kernel)
    ({0,1,4} : Finset (Fin 6)) (by decide +kernel) (by decide +kernel) small2clique1
  simpa only [small2G1,show insert (3 : Fin 6) ({0,1,2,4} : Finset (Fin 6))={0,1,2,4,3} from by decide +kernel] using h
def small2F1 : Finset (Finset (Fin 6)) := insert (insert 3 {0,1,4}) small2F0
theorem small2tetra1 : tetrahedra small2G1=small2F1 := by
  rw [small2G1,tetrahedra_after_attachment small2tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small2clique1,small2tetra0]
  rfl

def small2G2 : SimpleGraph (Fin 6) := small2G1 ⊔ attachmentStar 5 {0,1,2}
instance small2dec2 : DecidableRel small2G2.Adj := by unfold small2G2; infer_instance
theorem small2clique2 : small2G1.IsClique ({0,1,2} : Finset (Fin 6)) := by
  unfold small2G1 small2G0
  decide +kernel
theorem small2tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 6)) small2G2 := by
  have h:=ThreeTreeOn.attach small2tree1 (5 : Fin 6) (by decide +kernel)
    ({0,1,2} : Finset (Fin 6)) (by decide +kernel) (by decide +kernel) small2clique2
  simpa only [small2G2,show insert (5 : Fin 6) ({0,1,2,4,3} : Finset (Fin 6))={0,1,2,4,3,5} from by decide +kernel] using h
def small2F2 : Finset (Finset (Fin 6)) := insert (insert 5 {0,1,2}) small2F1
theorem small2tetra2 : tetrahedra small2G2=small2F2 := by
  rw [small2G2,tetrahedra_after_attachment small2tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small2clique2,small2tetra1]
  rfl

theorem small2spanning : IsThreeTree small2G2 := by
  change ThreeTreeOn univ small2G2
  have he : ({0,1,2,4,3,5} : Finset (Fin 6))=univ := by decide +kernel
  simpa only [he] using small2tree2

theorem small2admissible : Admissible small2G2 := by
  apply admissible_of_tetrahedron_list small2G2 small2F2 small2tetra2
  intro T hT
  unfold small2F2 small2F1 small2F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small2subgraph : small2G2≤ graph 2 := by
  change ∀ x y,small2G2.Adj x y → (graph 2).Adj x y
  unfold small2G2 small2G1 small2G0
  decide +kernel

def small3G0 : SimpleGraph (Fin 7) := cliqueGraph {0,1,2,4}
instance small3dec0 : DecidableRel small3G0.Adj := by unfold small3G0; infer_instance
theorem small3tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 7)) small3G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small3F0 : Finset (Finset (Fin 7)) := {{0,1,2,4}}
theorem small3tetra0 : tetrahedra small3G0=small3F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small3G1 : SimpleGraph (Fin 7) := small3G0 ⊔ attachmentStar 3 {0,1,4}
instance small3dec1 : DecidableRel small3G1.Adj := by unfold small3G1; infer_instance
theorem small3clique1 : small3G0.IsClique ({0,1,4} : Finset (Fin 7)) := by
  unfold small3G0
  decide +kernel
theorem small3tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 7)) small3G1 := by
  have h:=ThreeTreeOn.attach small3tree0 (3 : Fin 7) (by decide +kernel)
    ({0,1,4} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) small3clique1
  simpa only [small3G1,show insert (3 : Fin 7) ({0,1,2,4} : Finset (Fin 7))={0,1,2,4,3} from by decide +kernel] using h
def small3F1 : Finset (Finset (Fin 7)) := insert (insert 3 {0,1,4}) small3F0
theorem small3tetra1 : tetrahedra small3G1=small3F1 := by
  rw [small3G1,tetrahedra_after_attachment small3tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small3clique1,small3tetra0]
  rfl

def small3G2 : SimpleGraph (Fin 7) := small3G1 ⊔ attachmentStar 5 {0,1,2}
instance small3dec2 : DecidableRel small3G2.Adj := by unfold small3G2; infer_instance
theorem small3clique2 : small3G1.IsClique ({0,1,2} : Finset (Fin 7)) := by
  unfold small3G1 small3G0
  decide +kernel
theorem small3tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 7)) small3G2 := by
  have h:=ThreeTreeOn.attach small3tree1 (5 : Fin 7) (by decide +kernel)
    ({0,1,2} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) small3clique2
  simpa only [small3G2,show insert (5 : Fin 7) ({0,1,2,4,3} : Finset (Fin 7))={0,1,2,4,3,5} from by decide +kernel] using h
def small3F2 : Finset (Finset (Fin 7)) := insert (insert 5 {0,1,2}) small3F1
theorem small3tetra2 : tetrahedra small3G2=small3F2 := by
  rw [small3G2,tetrahedra_after_attachment small3tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small3clique2,small3tetra1]
  rfl

def small3G3 : SimpleGraph (Fin 7) := small3G2 ⊔ attachmentStar 6 {0,1,2}
instance small3dec3 : DecidableRel small3G3.Adj := by unfold small3G3; infer_instance
theorem small3clique3 : small3G2.IsClique ({0,1,2} : Finset (Fin 7)) := by
  unfold small3G2 small3G1 small3G0
  decide +kernel
theorem small3tree3 : ThreeTreeOn ({0,1,2,4,3,5,6} : Finset (Fin 7)) small3G3 := by
  have h:=ThreeTreeOn.attach small3tree2 (6 : Fin 7) (by decide +kernel)
    ({0,1,2} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) small3clique3
  simpa only [small3G3,show insert (6 : Fin 7) ({0,1,2,4,3,5} : Finset (Fin 7))={0,1,2,4,3,5,6} from by decide +kernel] using h
def small3F3 : Finset (Finset (Fin 7)) := insert (insert 6 {0,1,2}) small3F2
theorem small3tetra3 : tetrahedra small3G3=small3F3 := by
  rw [small3G3,tetrahedra_after_attachment small3tree2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small3clique3,small3tetra2]
  rfl

theorem small3spanning : IsThreeTree small3G3 := by
  change ThreeTreeOn univ small3G3
  have he : ({0,1,2,4,3,5,6} : Finset (Fin 7))=univ := by decide +kernel
  simpa only [he] using small3tree3

theorem small3admissible : Admissible small3G3 := by
  apply admissible_of_tetrahedron_list small3G3 small3F3 small3tetra3
  intro T hT
  unfold small3F3 small3F2 small3F1 small3F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small3subgraph : small3G3≤ graph 3 := by
  change ∀ x y,small3G3.Adj x y → (graph 3).Adj x y
  unfold small3G3 small3G2 small3G1 small3G0
  decide +kernel

def small4G0 : SimpleGraph (Fin 8) := cliqueGraph {0,1,2,4}
instance small4dec0 : DecidableRel small4G0.Adj := by unfold small4G0; infer_instance
theorem small4tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 8)) small4G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small4F0 : Finset (Finset (Fin 8)) := {{0,1,2,4}}
theorem small4tetra0 : tetrahedra small4G0=small4F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small4G1 : SimpleGraph (Fin 8) := small4G0 ⊔ attachmentStar 3 {0,1,4}
instance small4dec1 : DecidableRel small4G1.Adj := by unfold small4G1; infer_instance
theorem small4clique1 : small4G0.IsClique ({0,1,4} : Finset (Fin 8)) := by
  unfold small4G0
  decide +kernel
theorem small4tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 8)) small4G1 := by
  have h:=ThreeTreeOn.attach small4tree0 (3 : Fin 8) (by decide +kernel)
    ({0,1,4} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique1
  simpa only [small4G1,show insert (3 : Fin 8) ({0,1,2,4} : Finset (Fin 8))={0,1,2,4,3} from by decide +kernel] using h
def small4F1 : Finset (Finset (Fin 8)) := insert (insert 3 {0,1,4}) small4F0
theorem small4tetra1 : tetrahedra small4G1=small4F1 := by
  rw [small4G1,tetrahedra_after_attachment small4tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique1,small4tetra0]
  rfl

def small4G2 : SimpleGraph (Fin 8) := small4G1 ⊔ attachmentStar 5 {0,1,2}
instance small4dec2 : DecidableRel small4G2.Adj := by unfold small4G2; infer_instance
theorem small4clique2 : small4G1.IsClique ({0,1,2} : Finset (Fin 8)) := by
  unfold small4G1 small4G0
  decide +kernel
theorem small4tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 8)) small4G2 := by
  have h:=ThreeTreeOn.attach small4tree1 (5 : Fin 8) (by decide +kernel)
    ({0,1,2} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique2
  simpa only [small4G2,show insert (5 : Fin 8) ({0,1,2,4,3} : Finset (Fin 8))={0,1,2,4,3,5} from by decide +kernel] using h
def small4F2 : Finset (Finset (Fin 8)) := insert (insert 5 {0,1,2}) small4F1
theorem small4tetra2 : tetrahedra small4G2=small4F2 := by
  rw [small4G2,tetrahedra_after_attachment small4tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique2,small4tetra1]
  rfl

def small4G3 : SimpleGraph (Fin 8) := small4G2 ⊔ attachmentStar 6 {0,1,2}
instance small4dec3 : DecidableRel small4G3.Adj := by unfold small4G3; infer_instance
theorem small4clique3 : small4G2.IsClique ({0,1,2} : Finset (Fin 8)) := by
  unfold small4G2 small4G1 small4G0
  decide +kernel
theorem small4tree3 : ThreeTreeOn ({0,1,2,4,3,5,6} : Finset (Fin 8)) small4G3 := by
  have h:=ThreeTreeOn.attach small4tree2 (6 : Fin 8) (by decide +kernel)
    ({0,1,2} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique3
  simpa only [small4G3,show insert (6 : Fin 8) ({0,1,2,4,3,5} : Finset (Fin 8))={0,1,2,4,3,5,6} from by decide +kernel] using h
def small4F3 : Finset (Finset (Fin 8)) := insert (insert 6 {0,1,2}) small4F2
theorem small4tetra3 : tetrahedra small4G3=small4F3 := by
  rw [small4G3,tetrahedra_after_attachment small4tree2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique3,small4tetra2]
  rfl

def small4G4 : SimpleGraph (Fin 8) := small4G3 ⊔ attachmentStar 7 {0,1,3}
instance small4dec4 : DecidableRel small4G4.Adj := by unfold small4G4; infer_instance
theorem small4clique4 : small4G3.IsClique ({0,1,3} : Finset (Fin 8)) := by
  unfold small4G3 small4G2 small4G1 small4G0
  decide +kernel
theorem small4tree4 : ThreeTreeOn ({0,1,2,4,3,5,6,7} : Finset (Fin 8)) small4G4 := by
  have h:=ThreeTreeOn.attach small4tree3 (7 : Fin 8) (by decide +kernel)
    ({0,1,3} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique4
  simpa only [small4G4,show insert (7 : Fin 8) ({0,1,2,4,3,5,6} : Finset (Fin 8))={0,1,2,4,3,5,6,7} from by decide +kernel] using h
def small4F4 : Finset (Finset (Fin 8)) := insert (insert 7 {0,1,3}) small4F3
theorem small4tetra4 : tetrahedra small4G4=small4F4 := by
  rw [small4G4,tetrahedra_after_attachment small4tree3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique4,small4tetra3]
  rfl

theorem small4spanning : IsThreeTree small4G4 := by
  change ThreeTreeOn univ small4G4
  have he : ({0,1,2,4,3,5,6,7} : Finset (Fin 8))=univ := by decide +kernel
  simpa only [he] using small4tree4

theorem small4admissible : Admissible small4G4 := by
  apply admissible_of_tetrahedron_list small4G4 small4F4 small4tetra4
  intro T hT
  unfold small4F4 small4F3 small4F2 small4F1 small4F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small4subgraph : small4G4≤ graph 4 := by
  change ∀ x y,small4G4.Adj x y → (graph 4).Adj x y
  unfold small4G4 small4G3 small4G2 small4G1 small4G0
  decide +kernel

def small5G0 : SimpleGraph (Fin 9) := cliqueGraph {0,1,2,4}
instance small5dec0 : DecidableRel small5G0.Adj := by unfold small5G0; infer_instance
theorem small5tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 9)) small5G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small5F0 : Finset (Finset (Fin 9)) := {{0,1,2,4}}
theorem small5tetra0 : tetrahedra small5G0=small5F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small5G1 : SimpleGraph (Fin 9) := small5G0 ⊔ attachmentStar 3 {0,1,4}
instance small5dec1 : DecidableRel small5G1.Adj := by unfold small5G1; infer_instance
theorem small5clique1 : small5G0.IsClique ({0,1,4} : Finset (Fin 9)) := by
  unfold small5G0
  decide +kernel
theorem small5tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 9)) small5G1 := by
  have h:=ThreeTreeOn.attach small5tree0 (3 : Fin 9) (by decide +kernel)
    ({0,1,4} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique1
  simpa only [small5G1,show insert (3 : Fin 9) ({0,1,2,4} : Finset (Fin 9))={0,1,2,4,3} from by decide +kernel] using h
def small5F1 : Finset (Finset (Fin 9)) := insert (insert 3 {0,1,4}) small5F0
theorem small5tetra1 : tetrahedra small5G1=small5F1 := by
  rw [small5G1,tetrahedra_after_attachment small5tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique1,small5tetra0]
  rfl

def small5G2 : SimpleGraph (Fin 9) := small5G1 ⊔ attachmentStar 5 {0,1,2}
instance small5dec2 : DecidableRel small5G2.Adj := by unfold small5G2; infer_instance
theorem small5clique2 : small5G1.IsClique ({0,1,2} : Finset (Fin 9)) := by
  unfold small5G1 small5G0
  decide +kernel
theorem small5tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 9)) small5G2 := by
  have h:=ThreeTreeOn.attach small5tree1 (5 : Fin 9) (by decide +kernel)
    ({0,1,2} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique2
  simpa only [small5G2,show insert (5 : Fin 9) ({0,1,2,4,3} : Finset (Fin 9))={0,1,2,4,3,5} from by decide +kernel] using h
def small5F2 : Finset (Finset (Fin 9)) := insert (insert 5 {0,1,2}) small5F1
theorem small5tetra2 : tetrahedra small5G2=small5F2 := by
  rw [small5G2,tetrahedra_after_attachment small5tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique2,small5tetra1]
  rfl

def small5G3 : SimpleGraph (Fin 9) := small5G2 ⊔ attachmentStar 6 {0,1,2}
instance small5dec3 : DecidableRel small5G3.Adj := by unfold small5G3; infer_instance
theorem small5clique3 : small5G2.IsClique ({0,1,2} : Finset (Fin 9)) := by
  unfold small5G2 small5G1 small5G0
  decide +kernel
theorem small5tree3 : ThreeTreeOn ({0,1,2,4,3,5,6} : Finset (Fin 9)) small5G3 := by
  have h:=ThreeTreeOn.attach small5tree2 (6 : Fin 9) (by decide +kernel)
    ({0,1,2} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique3
  simpa only [small5G3,show insert (6 : Fin 9) ({0,1,2,4,3,5} : Finset (Fin 9))={0,1,2,4,3,5,6} from by decide +kernel] using h
def small5F3 : Finset (Finset (Fin 9)) := insert (insert 6 {0,1,2}) small5F2
theorem small5tetra3 : tetrahedra small5G3=small5F3 := by
  rw [small5G3,tetrahedra_after_attachment small5tree2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique3,small5tetra2]
  rfl

def small5G4 : SimpleGraph (Fin 9) := small5G3 ⊔ attachmentStar 7 {0,1,3}
instance small5dec4 : DecidableRel small5G4.Adj := by unfold small5G4; infer_instance
theorem small5clique4 : small5G3.IsClique ({0,1,3} : Finset (Fin 9)) := by
  unfold small5G3 small5G2 small5G1 small5G0
  decide +kernel
theorem small5tree4 : ThreeTreeOn ({0,1,2,4,3,5,6,7} : Finset (Fin 9)) small5G4 := by
  have h:=ThreeTreeOn.attach small5tree3 (7 : Fin 9) (by decide +kernel)
    ({0,1,3} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique4
  simpa only [small5G4,show insert (7 : Fin 9) ({0,1,2,4,3,5,6} : Finset (Fin 9))={0,1,2,4,3,5,6,7} from by decide +kernel] using h
def small5F4 : Finset (Finset (Fin 9)) := insert (insert 7 {0,1,3}) small5F3
theorem small5tetra4 : tetrahedra small5G4=small5F4 := by
  rw [small5G4,tetrahedra_after_attachment small5tree3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique4,small5tetra3]
  rfl

def small5G5 : SimpleGraph (Fin 9) := small5G4 ⊔ attachmentStar 8 {0,1,3}
instance small5dec5 : DecidableRel small5G5.Adj := by unfold small5G5; infer_instance
theorem small5clique5 : small5G4.IsClique ({0,1,3} : Finset (Fin 9)) := by
  unfold small5G4 small5G3 small5G2 small5G1 small5G0
  decide +kernel
theorem small5tree5 : ThreeTreeOn ({0,1,2,4,3,5,6,7,8} : Finset (Fin 9)) small5G5 := by
  have h:=ThreeTreeOn.attach small5tree4 (8 : Fin 9) (by decide +kernel)
    ({0,1,3} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique5
  simpa only [small5G5,show insert (8 : Fin 9) ({0,1,2,4,3,5,6,7} : Finset (Fin 9))={0,1,2,4,3,5,6,7,8} from by decide +kernel] using h
def small5F5 : Finset (Finset (Fin 9)) := insert (insert 8 {0,1,3}) small5F4
theorem small5tetra5 : tetrahedra small5G5=small5F5 := by
  rw [small5G5,tetrahedra_after_attachment small5tree4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique5,small5tetra4]
  rfl

theorem small5spanning : IsThreeTree small5G5 := by
  change ThreeTreeOn univ small5G5
  have he : ({0,1,2,4,3,5,6,7,8} : Finset (Fin 9))=univ := by decide +kernel
  simpa only [he] using small5tree5

theorem small5admissible : Admissible small5G5 := by
  apply admissible_of_tetrahedron_list small5G5 small5F5 small5tetra5
  intro T hT
  unfold small5F5 small5F4 small5F3 small5F2 small5F1 small5F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small5subgraph : small5G5≤ graph 5 := by
  change ∀ x y,small5G5.Adj x y → (graph 5).Adj x y
  unfold small5G5 small5G4 small5G3 small5G2 small5G1 small5G0
  decide +kernel

/-- Every member below the diamond threshold has an admissible spanning
3-tree. The finite cases exhaust the exact parameter range1≤k≤5. -/
theorem admissible_spanning_small (k : ℕ) (hk : 1≤ k) (hmax : k≤5) :
    HasAdmissibleSpanningThreeTree (graph k) := by
  interval_cases k
  · exact ⟨small1G1,small1subgraph,small1spanning,small1admissible⟩
  · exact ⟨small2G2,small2subgraph,small2spanning,small2admissible⟩
  · exact ⟨small3G3,small3subgraph,small3spanning,small3admissible⟩
  · exact ⟨small4G4,small4subgraph,small4spanning,small4admissible⟩
  · exact ⟨small5G5,small5subgraph,small5spanning,small5admissible⟩

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart225

section BundlePart226
/- Source: Papers/GraphicalZonotopes/DiamondBookSmallDimension.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped Pointwise

/-- The checked3-tree construction yields a full-dimensional extreme
function on every graph containing an admissible spanning3-tree. -/
theorem full_support_of_admissible_spanning_threeTree {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : HasAdmissibleSpanningThreeTree G) :
    ∃ z : SetFunction (Fin n),ExtremeSupermodular z ∧
      FullDimension (basePolytope z) ∧ Graphical G z := by
  obtain ⟨H,hHG,hH,hA⟩:=hG
  obtain ⟨z,hz,hi,hfour,hthree,hd,hdir,hsum⟩:=admissible_threeTree_construction hn hH hA
  have hgraph:=((isMinkowskiSummand_graphical_iff hz.1.1 hz.2.1
    (Nat.cast_nonneg (n-3))).mp hsum).1
  exact ⟨z,hz,hd,hgraph.mono_graph hHG⟩

namespace DiamondBook

theorem small_dimension_lower (k : ℕ) (hk : 1≤ k) (hmax : k≤5) :
    k+3≤ maximumIndecomposableDimension (graph k) := by
  obtain ⟨z,hz,hd,hgraph⟩:=full_support_of_admissible_spanning_threeTree
    (by omega : 4≤ k+4) (admissible_spanning_small k hk hmax)
  have hw:=(isWeakMinkowskiSummand_graphical_iff hz.1.1 hz.2.1).mpr hgraph
  have hfinite : IsFinitePolytope (basePolytope z):=
    (show IsGeneralizedPermutahedron (basePolytope z) from ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope
  have hle:=dimension_le_maximum hfinite hz.minkowskiIndecomposable hw
  change Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=Fintype.card (Fin (k+4))-1 at hd
  rw [hd,Fintype.card_fin] at hle
  omega

end DiamondBook
end GraphicalZonotopes

end
end
end BundlePart226

section BundlePart227
/- Source: Papers/GraphicalZonotopes/DiamondBookLargeDimension.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped Pointwise

def largeEmbedding (k : ℕ) (hk : 6≤ k) : Fin 10 ↪ Vertex k where
  toFun x:=⟨x.val,by have:=x.isLt; omega⟩
  inj' x y h:=Fin.ext (congrArg (fun z : Vertex k => z.val) h)

theorem large_graph_comap (k : ℕ) (hk : 6≤ k) :
    (graph k).comap (largeEmbedding k hk)=graph 6 := by
  apply SimpleGraph.ext
  funext x y
  rfl

theorem diamond_support_subgraph : DiamondGeometry.graph≤ graph 6 := by
  change ∀ x y,DiamondGeometry.graph.Adj x y → (graph 6).Adj x y
  decide +kernel

theorem large_dimension_lower (k : ℕ) (hk : 6≤ k) :
    9≤ maximumIndecomposableDimension (graph k) := by
  let e:=largeEmbedding k hk
  let z:=SetFunctionEmbedding.extend e DiamondGeometry.function
  have hz : ExtremeSupermodular z:=SetFunctionEmbedding.extend_extreme e DiamondGeometry.extreme
  have hgraph0 : Graphical ((graph k).comap e) DiamondGeometry.function := by
    rw [large_graph_comap]
    exact DiamondGeometry.graphical.mono_graph diamond_support_subgraph
  have hgraph : Graphical (graph k) z:=SetFunctionEmbedding.extend_graphical e hgraph0
  have hd : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=9 := by
    rw [SetFunctionEmbedding.finrank_vectorSpan_extend e DiamondGeometry.normalized]
    exact DiamondGeometry.full_dimension
  have hfinite : IsFinitePolytope (basePolytope z):=
    (show IsGeneralizedPermutahedron (basePolytope z) from ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope
  have hle:=dimension_le_maximum hfinite hz.minkowskiIndecomposable
    ((isWeakMinkowskiSummand_graphical_iff hz.1.1 hz.2.1).mpr hgraph)
  rwa [hd] at hle

theorem diamond_witness :
    ∃ Q : Set (Fin 10 → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      FullDimension Q ∧ IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (graph 6)) ∧
      directionCount Q=25 ∧ ¬HasAdmissibleSpanningThreeTree (graph 6) := by
  refine ⟨basePolytope DiamondGeometry.function,DiamondGeometry.lattice,
    DiamondGeometry.indecomposable,DiamondGeometry.full_dimension,?_,
    DiamondGeometry.direction_count,no_admissible_spanning_threeTree 6 (by norm_num)⟩
  apply (isMinkowskiSummand_graphical_iff DiamondGeometry.normalized.1
    DiamondGeometry.supermodular (by norm_num : (0 : ℝ)≤4)).mpr
  exact ⟨DiamondGeometry.graphical.mono_graph diamond_support_subgraph,
    fun _ _ huv _ _ hu hv => (DiamondGeometry.elemental_bounds huv hu hv).2⟩

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart227

section BundlePart228
/- Source: Papers/GraphicalZonotopes/DiamondPrincipal.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook

/-- The unbounded maximum-dimension formula for every positive private-part
size. All lower witnesses and the upper supremum bound refer to actual
indecomposable Minkowski summands. -/
theorem maximum_dimension (k : ℕ) (hk : 1≤ k) :
    maximumIndecomposableDimension (graph k)=min (k+3) 9 := by
  apply le_antisymm (maximum_dimension_upper k)
  by_cases hs:k≤5
  · exact (min_le_left _ _).trans (small_dimension_lower k hk hs)
  · exact (min_le_right _ _).trans (large_dimension_lower k (by omega))

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart228

section BundlePart229
/- Source: Papers/GraphicalZonotopes/DiamondBookIsomorphism.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open scoped BigOperators

abbrev MultipartiteVertex (k : ℕ) := Σ i : Fin 4,Fin (![1,1,2,k] i)

/-- The literal coordinate numbering: singleton parts at0,1; the two-element
part at2,3; and the last part at4 throughk+3. -/
def sigmaToVertex (k : ℕ) (x : MultipartiteVertex k) : Vertex k :=
  ⟨if x.1.val=0 then 0 else if x.1.val=1 then 1 else
    if x.1.val=2 then x.2.val+2 else x.2.val+4,by
    rcases x with ⟨i,j⟩
    have hj := j.isLt
    fin_cases i <;> norm_num at hj ⊢ <;> omega⟩

@[simp] theorem part_sigmaToVertex (k : ℕ) (x : MultipartiteVertex k) :
    part k (sigmaToVertex k x)=x.1 := by
  rcases x with ⟨i,j⟩
  have hj := j.isLt
  fin_cases i
  · rfl
  · rfl
  · have hj' : j.val<2 := by simpa using hj
    have h0 : j.val+2≠0 := by omega
    have h1 : j.val+2≠1 := by omega
    have h4 : j.val+2<4 := by omega
    simp [part,sigmaToVertex,h0,h1,h4]
  · have h0 : j.val+4≠0 := by omega
    have h1 : j.val+4≠1 := by omega
    have h4 : ¬j.val+4<4 := by omega
    simp [part,sigmaToVertex,h0,h1,h4]

theorem sigmaToVertex_injective (k : ℕ) : Function.Injective (sigmaToVertex k) := by
  intro x y he
  have hi := congrArg (part k) he
  rw [part_sigmaToVertex,part_sigmaToVertex] at hi
  rcases x with ⟨i,j⟩
  rcases y with ⟨l,m⟩
  change i=l at hi
  subst l
  apply congrArg (Sigma.mk i)
  apply Fin.ext
  have hj := j.isLt
  have hm := m.isLt
  have hv := congrArg Fin.val he
  fin_cases i <;> norm_num [sigmaToVertex] at hj hm hv ⊢ <;> omega

def sigmaEquiv (k : ℕ) : MultipartiteVertex k ≃ Vertex k :=
  Equiv.ofBijective (sigmaToVertex k)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨sigmaToVertex_injective k,by
        simp [MultipartiteVertex,Vertex,Fintype.card_sigma,Fin.sum_univ_succ,
          Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]⟩)

def sigmaGraphIso (k : ℕ) : twoSingletonGraph 2 k ≃g graph k where
  toEquiv := sigmaEquiv k
  map_rel_iff' := by
    intro x y
    change (part k (sigmaToVertex k x)≠ part k (sigmaToVertex k y)) ↔ x.1≠ y.1
    rw [part_sigmaToVertex,part_sigmaToVertex]

/-- The model used for the explicit certificate is exactly the paper's
graph, under an actual bijection of all coordinates for everyk. -/
def graphIso (k : ℕ) : graph k ≃g twoSingletonGraph 2 k := (sigmaGraphIso k).symm

theorem maximum_dimension_model_eq (k : ℕ) :
    maximumIndecomposableDimension (graph k)=
      maximumIndecomposableDimension (twoSingletonGraph 2 k) :=
  maximumIndecomposableDimension_iso (graphIso k)

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart229

section BundlePart230
/- Source: Papers/GraphicalZonotopes/DiamondPaper.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset SetFunctionEmbedding
open scoped Pointwise

/-- The obstruction survives the exact bijection to the paper's four-part
coordinate type. The transported object is an actual spanning 3-tree. -/
theorem no_spanning_six_multipartite :
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph 2 6) := by
  classical
  rintro ⟨H,hH,hTree,hAdm⟩
  let e := (sigmaGraphIso 6).toEquiv.toEmbedding
  have hsub : H.map e≤ graph 6 := by
    intro x y hxy
    obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj e H x y).mp hxy
    exact (sigmaGraphIso 6).map_adj_iff.mpr (hH hab)
  have htree : IsThreeTree (H.map e) := by
    change ThreeTreeOn univ (H.map e)
    have ht := hTree.map e
    simpa only [e,Finset.map_univ_equiv] using ht
  exact no_admissible_spanning_threeTree 6 (by norm_num)
    ⟨H.map e,hsub,htree,hAdm.map e⟩

/-- Every geometric property of the diamond witness is transported to the
literal multipartite coordinates used in the paper's statement. -/
theorem diamond_witness_multipartite :
    ∃ Q : Set (MultipartiteVertex 6 → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
      directionCount Q=25 ∧ ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph 2 6) := by
  classical
  let o : LinearOrder (MultipartiteVertex 6) :=
    LinearOrder.lift' (Fintype.equivFin (MultipartiteVertex 6))
      (Fintype.equivFin (MultipartiteVertex 6)).injective
  letI : LinearOrder (MultipartiteVertex 6) :=
    { o with
      toDecidableEq := inferInstance
      compare := fun x y => @compareOfLessAndEq _ x y o.toLT (o.toDecidableLT x y) inferInstance
      compare_eq_compareOfLessAndEq := by intros;rfl }
  let e := (graphIso 6).toEquiv.toEmbedding
  let z := extend e DiamondGeometry.function
  have hz : ExtremeSupermodular z := extend_extreme e DiamondGeometry.extreme
  have hi : IntegerValued z := extend_integer e DiamondGeometry.integerValued
  have hcomap : (twoSingletonGraph 2 6).comap e=graph 6 := by
    ext a b
    exact (graphIso 6).map_adj_iff
  have hg : Graphical (twoSingletonGraph 2 6) z := by
    apply extend_graphical e
    rw [hcomap]
    exact DiamondGeometry.graphical.mono_graph diamond_support_subgraph
  have hd : FullDimension (basePolytope z) := by
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=
      Fintype.card (MultipartiteVertex 6)-1
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope
      (extend e DiamondGeometry.function)))=_
    rw [finrank_vectorSpan_extend e DiamondGeometry.normalized]
    have hh := DiamondGeometry.full_dimension
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope DiamondGeometry.function))=9 at hh
    rw [hh]
    norm_num [MultipartiteVertex,Fintype.card_sigma,Fin.sum_univ_succ]
  have hsum : IsMinkowskiSummand (basePolytope z)
      ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) := by
    apply (isMinkowskiSummand_graphical_iff hz.1.1 hz.2.1
      (by norm_num : (0 : ℝ)≤4)).mpr
    refine ⟨hg,?_⟩
    intro u v huv _ S hu hv
    have heval (x : Vertex 6) : e x=(graphIso 6).toEquiv x := rfl
    have hsurj : Function.Surjective e := by
      intro y
      obtain ⟨x,hx⟩ := (graphIso 6).toEquiv.surjective y
      exact ⟨x,(heval x).trans hx⟩
    obtain ⟨a,rfl⟩ := hsurj u
    obtain ⟨b,rfl⟩ := hsurj v
    change delta (extend e DiamondGeometry.function) (e a) (e b) S≤4
    rw [delta_extend]
    exact (DiamondGeometry.elemental_bounds
      (fun he => huv (congrArg e he))
      (by simpa only [mem_pullSet] using hu)
      (by simpa only [mem_pullSet] using hv)).2
  refine ⟨basePolytope z,hi.basePolytope hz.1.1 hz.2.1,
    hz.minkowskiIndecomposable,hd,hsum,?_,no_spanning_six_multipartite⟩
  change directionCount (basePolytope (extend e DiamondGeometry.function))=25
  rw [directionCount_extend e DiamondGeometry.normalized DiamondGeometry.supermodular]
  exact DiamondGeometry.direction_count

/-- Theorem 8.1 in the paper's exact vertex model, with both the unrestricted
dimension formula and every property of the extremal six-branch witness. -/
theorem paper_theorem_8_1 : Targets.DiamondBookClassification := by
  refine ⟨?_,diamond_witness_multipartite⟩
  intro k hk
  rw [← maximum_dimension_model_eq]
  exact maximum_dimension k hk

end GraphicalZonotopes.DiamondBook

end
end
end BundlePart230

section BundlePart231
/- Source: Papers/GraphicalZonotopes/DiamondGeometricObstruction.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset SetFunctionEmbedding
open scoped Pointwise
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Coordinate relabelling preserves the actual full-dimensional weak-summand
existence assertion. No direction graph is assigned by definition. -/
theorem SupportsFullIndecomposable.map_equiv {G : SimpleGraph V}
    (e : V ≃ W) (hn : 2≤ Fintype.card V) (h : SupportsFullIndecomposable G) :
    SupportsFullIndecomposable (G.map e.toEmbedding) := by
  obtain ⟨Q,hQ,hi,hd,hw⟩ := h
  obtain ⟨z,hz,he,hzd⟩ := weak_summand_extreme_or_zero hQ hi hw
  have hdf : Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1))=Fintype.card V-1 := by
    rw [←hzd]
    exact hd
  rcases he with he | he
  · rw [he,basePolytope_zero,_root_.vectorSpan_singleton,_root_.finrank_bot] at hdf
    omega
  · have hfe := extend_extreme e.toEmbedding he
    have hsub : G≤(G.map e.toEmbedding).comap e.toEmbedding := by
      intro u v huv
      exact (SimpleGraph.map_adj e.toEmbedding G (e u) (e v)).mpr ⟨u,v,huv,rfl,rfl⟩
    have hgg : Graphical (G.map e.toEmbedding) (extend e.toEmbedding z.1) :=
      extend_graphical e.toEmbedding (Graphical.mono_graph hsub z.2.2)
    have hp : IsGeneralizedPermutahedron (basePolytope (extend e.toEmbedding z.1)) :=
      ⟨_,hfe.1.1,hfe.2.1,rfl⟩
    refine ⟨_,hp.finitePolytope,hfe.minkowskiIndecomposable,?_,
      (isWeakMinkowskiSummand_graphical_iff hfe.1.1 hfe.2.1).mpr hgg⟩
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (extend e.toEmbedding z.1)))=
      Fintype.card W-1
    rw [finrank_vectorSpan_extend e.toEmbedding z.2.1,hdf,Fintype.card_congr e]

namespace DiamondBook

/-- The literal geometric obstruction in Theorem 8.1: no spanning 3-tree
contained in the prescribed graph supports a full-dimensional indecomposable
weak Minkowski summand. -/
theorem no_supporting_spanning_threeTree :
    ¬∃ H : SimpleGraph (MultipartiteVertex 6),
      H≤ twoSingletonGraph 2 6 ∧ IsThreeTree H ∧ SupportsFullIndecomposable H := by
  classical
  rintro ⟨H,hsub,htree,hsupport⟩
  let e := (sigmaGraphIso 6).toEquiv
  have hm : IsThreeTree (H.map e.toEmbedding) := by
    change ThreeTreeOn univ (H.map e.toEmbedding)
    simpa only [Finset.map_univ_equiv] using htree.map e.toEmbedding
  have hc : 2≤ Fintype.card (MultipartiteVertex 6) := by
    norm_num [MultipartiteVertex,Fintype.card_sigma,Fin.sum_univ_succ]
  have hs := hsupport.map_equiv e hc
  have ha := (threeTree_supports_iff_admissible (by decide : 4≤10) hm).mp hs
  exact no_spanning_six_multipartite
    ⟨H,hsub,htree,Admissible.of_map e.toEmbedding ha⟩

/-- Both clauses of Theorem 8.1 with the second clause phrased directly in
terms of actual geometric supporting polytopes, in the paper's vertex model. -/
theorem paper_theorem_8_1_literal :
    (∀ k : ℕ,1≤ k → maximumIndecomposableDimension (twoSingletonGraph 2 k)=min (k+3) 9) ∧
    (∃ Q : Set (MultipartiteVertex 6 → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
      directionCount Q=25) ∧
    ¬∃ H : SimpleGraph (MultipartiteVertex 6),
      H≤ twoSingletonGraph 2 6 ∧ IsThreeTree H ∧ SupportsFullIndecomposable H := by
  obtain ⟨Q,hQ,hi,hd,hs,he,_⟩ := diamond_witness_multipartite
  exact ⟨paper_theorem_8_1.1,⟨Q,hQ,hi,hd,hs,he⟩,no_supporting_spanning_threeTree⟩

end DiamondBook
end GraphicalZonotopes

end
end
end BundlePart231

section BundlePart232
/- Source: Papers/GraphicalZonotopes/DiamondPolytopalCompletion.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- On every actual finite weak summand, ordinary polytopal and compact-convex
indecomposability agree. No full-dimension hypothesis is needed. -/
theorem minkowskiIndecomposable_iff_polytopal_of_weak_summand
    {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    MinkowskiIndecomposable Q ↔ PolytopalMinkowskiIndecomposable Q := by
  constructor
  · intro hi
    exact ⟨hi.1,fun P R hP hR he =>
      hi.2 P R hP.compact hR.compact hP.convex hR.convex he⟩
  · intro hi
    obtain ⟨a,ha,R,hR,hcR,hnR,he⟩ := hw
    have hzn : Normalized (a • graphFunction G) := by
      change a * graphFunction G ∅=0
      rw [graphFunction_normalized,mul_zero]
    have hzs : Supermodular (a • graphFunction G) :=
      (graphFunction_supermodular G).smul ha.le
    have hsum : Q+R=basePolytope (a • graphFunction G) := by
      rw [basePolytope_smul (graphFunction_normalized G)
        (graphFunction_supermodular G) ha.le,baseGraphFunction_eq_graphicalZonotope]
      exact he
    have hn := lowerSupport_normalized hQ.compact hi.1
    have hsm := summand_lowerSupport_supermodular hzn hzs hQ.compact hR hi.1 hnR hsum
    have hbody := summand_eq_basePolytope hzn hzs hQ.compact hR hQ.convex hi.1 hnR hsum
    exact (minkowskiIndecomposable_iff_polytopal
      ⟨lowerSupport Q,hn,hsm,hbody⟩).mpr hi

/-- The literal dimension supremum with ordinary polytopal decompositions. -/
def maximumPolytopalIndecomposableDimension (G : SimpleGraph V) : ℕ :=
  sSup {d : ℕ | ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    PolytopalMinkowskiIndecomposable Q ∧
    IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    Module.finrank ℝ (vectorSpan ℝ Q)=d}

/-- Equality of the two dimension invariants, for every finite graph. -/
theorem maximumIndecomposableDimension_eq_polytopal (G : SimpleGraph V) :
    maximumIndecomposableDimension G=maximumPolytopalIndecomposableDimension G := by
  unfold maximumIndecomposableDimension maximumPolytopalIndecomposableDimension
  congr 1
  ext d
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal_of_weak_summand hQ hw).mp hi,hw,hd⟩
  · rintro ⟨Q,hQ,hi,hw,hd⟩
    exact ⟨Q,hQ,(minkowskiIndecomposable_iff_polytopal_of_weak_summand hQ hw).mpr hi,hw,hd⟩

/-- Allowing zero as a dilation factor adds no full-dimensional lattice
witness when there are at least two coordinates. -/
theorem not_fullLatticeSummandAt_zero (G : SimpleGraph V)
    (hn : 2≤ Fintype.card V) : ¬FullLatticeSummandAt G 0 := by
  rintro ⟨Q,_,hi,hd,R,_,_,hnR,he⟩
  obtain ⟨r,hr⟩ := hnR
  have hpoint : ∀ q∈Q,q= -r := by
    intro q hq
    have hm : q+r∈(0 : ℝ) • graphicalZonotope G :=
      he ▸ (show q+r∈Q+R from ⟨q,hq,r,hr,rfl⟩)
    obtain ⟨z,_,hz⟩ := hm
    have hqr : q+r=0 := by simpa only [zero_smul] using hz.symm
    calc
      q=q+r-r := by abel
      _= -r := by rw [hqr];simp
  have hQ : Q={-r} := by
    ext q
    constructor
    · intro hq
      exact Set.mem_singleton_iff.mpr (hpoint q hq)
    · intro hq
      have heq := Set.mem_singleton_iff.mp hq
      obtain ⟨q₀,hq₀⟩ := hi.1
      simpa only [heq,hpoint q₀ hq₀] using hq₀
  change Module.finrank ℝ (vectorSpan ℝ Q)=Fintype.card V-1 at hd
  rw [hQ,_root_.vectorSpan_singleton,_root_.finrank_bot] at hd
  omega

namespace DiamondBook

/-- The entire diamond theorem with ordinary polytopal indecomposability
in both its dimension invariant and its literal geometric obstruction. -/
theorem paper_theorem_8_1_polytopal :
    (∀ k : ℕ,1≤ k → maximumPolytopalIndecomposableDimension (twoSingletonGraph 2 k)=
      min (k+3) 9) ∧
    (∃ Q : Set (MultipartiteVertex 6 → ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
      directionCount Q=25) ∧
    ¬∃ H : SimpleGraph (MultipartiteVertex 6),
      H≤ twoSingletonGraph 2 6 ∧ IsThreeTree H ∧
      ∃ Q : Set (MultipartiteVertex 6 → ℝ), IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope H) := by
  obtain ⟨hm,⟨Q,hQ,hi,hd,hs,he⟩,ho⟩ := paper_theorem_8_1_literal
  refine ⟨?_,⟨Q,hQ,?_,hd,hs,he⟩,?_⟩
  · intro k hk
    rw [←maximumIndecomposableDimension_eq_polytopal]
    exact hm k hk
  · exact ⟨hi.1,fun P R hP hR heq =>
      hi.2 P R hP.compact hR.compact hP.convex hR.convex heq⟩
  · rintro ⟨H,hsub,htree,Q,hfin,hind,hfull,hweak⟩
    apply ho
    exact ⟨H,hsub,htree,Q,hfin,
      (minkowskiIndecomposable_iff_polytopal_of_weak_summand hfin hweak).mpr hind,
      hfull,hweak⟩

end DiamondBook
end GraphicalZonotopes

end
end
end BundlePart232

section BundlePart233
/- Source: Papers/GraphicalZonotopes/GraphFunctionTwins.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices with identical open neighborhoods have identical induced-edge
marginals in every subset avoiding them. -/
theorem graphFunction_insert_twins (G : SimpleGraph V) {u v : V}
    (htwin : ∀ w,G.Adj u w↔G.Adj v w) (S : Finset V) (hu : u∉S) (hv : v∉S) :
    graphFunction G (insert u S)=graphFunction G (insert v S) := by
  classical
  revert hu hv
  induction S using Finset.induction_on with
  | empty =>
    intro hu hv
    simp only [insert_empty_eq,(graphFunction_translationNormalized G).2]
  | @insert w S hw ih =>
    intro hu hv
    have huS : u∉S := fun h => hu (mem_insert_of_mem h)
    have hvS : v∉S := fun h => hv (mem_insert_of_mem h)
    have huw : u≠ w := fun h => hu (by simp [h])
    have hvw : v≠ w := fun h => hv (by simp [h])
    have h1 := graphFunction_delta G huw huS hw
    have h2 := graphFunction_delta G hvw hvS hw
    rw [htwin w] at h1
    have he := ih huS hvS
    unfold delta at h1 h2
    linarith

end GraphicalZonotopes

end
end
end BundlePart233

section BundlePart234
/- Source: Papers/GraphicalZonotopes/FloorHalf.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace GraphicalZonotopes
namespace FloorHalf
open Finset
open scoped BigOperators

/-- The exact carry identity behind every graphical Boolean slack. -/
theorem edge_boolean (m a b : ℤ) :
    (m+a+b+1)/2+m/2-(m+a)/2-(m+b)/2=0 ∨
    (m+a+b+1)/2+m/2-(m+a)/2-(m+b)/2=1 := by omega

theorem edge_boolean_of_mixed (m mu mv muv : ℤ) (h : muv+m-mu-mv=1) :
    muv/2+m/2-mu/2-mv/2=0 ∨ muv/2+m/2-mu/2-mv/2=1 := by omega

/-- Nonadjacent paired vertices have consecutive unrounded marginals, whose
rounding errors cancel exactly. -/
theorem twins_zero (m mu mv muv : ℤ) (hm : muv+m-mu-mv=0)
    (ht : mu+1=mv ∨ mv+1=mu) : muv/2+m/2-mu/2-mv/2=0 := by omega

/-- Four-variable quadratic-phase Möbius coefficient with arbitrary linear
part. This finite identity is later applied through an arbitrary four-clique
restriction; it is not used as a bounded replacement for a graph theorem. -/
def fourPhaseMobius (b : Fin 4 → Bool) : ℤ :=
  ∑ S : Finset (Fin 4),(-1 : ℤ)^(4-S.card)*
    (-1 : ℤ)^(S.card.choose 2+(S.filter (fun i => b i=false)).card)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem fourPhaseMobius_values :
    ∀ b : Fin 4 → Bool,fourPhaseMobius b=4 ∨ fourPhaseMobius b= -4 := by decide

end FloorHalf
end GraphicalZonotopes

end
end BundlePart234

section BundlePart235
/- Source: Papers/GraphicalZonotopes/DoubledPartsBoolean.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The ordinary complete multipartite graph with a pair in each part. -/
def graph (I : Type*) : SimpleGraph (I×Fin 2) where
  Adj u v := u.1≠ v.1
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

def integerGraphCount (S : Finset (I×Fin 2)) : ℤ :=
  ∑ C∈edgeFamily (graph I),if C⊆S then 1 else 0

def firstWeight (v : I×Fin 2) : ℤ := if v.2=0 then 1 else 0

def integerData (S : Finset (I×Fin 2)) : ℤ :=
  integerGraphCount S+∑ v∈S,firstWeight v

/-- An explicit uniform integral function for all even and odd numbers of
parts: the floor of half the induced-edge count plus first-vertex count. -/
def setFunction (S : Finset (I×Fin 2)) : ℝ := ((integerData S/2 : ℤ) : ℝ)

theorem delta_setFunction (u v : I×Fin 2) (S : Finset (I×Fin 2)) :
    delta setFunction u v S=
      ((integerData (insert u (insert v S))/2+integerData S/2-
        integerData (insert u S)/2-integerData (insert v S)/2 : ℤ) : ℝ) := by
  simp only [delta,setFunction,Int.cast_sub,Int.cast_add]
  ring

theorem cast_integerGraphCount (S : Finset (I×Fin 2)) :
    (integerGraphCount S : ℝ)=graphFunction (graph I) S := by
  simp [integerGraphCount,graphFunction,setMonomial,Finset.sum_apply]

theorem cast_integerData (S : Finset (I×Fin 2)) :
    (integerData S : ℝ)=graphFunction (graph I) S+
      modular (fun v : I×Fin 2 => (firstWeight v : ℝ)) S := by
  simp only [integerData,Int.cast_add,Int.cast_sum,cast_integerGraphCount,modular,subsetSum]

@[simp] theorem integerGraphCount_empty : integerGraphCount (I := I) ∅=0 := by
  apply Int.cast_injective (α := ℝ)
  rw [cast_integerGraphCount,(graphFunction_translationNormalized (graph I)).1]
  norm_num

@[simp] theorem integerGraphCount_singleton (v : I×Fin 2) : integerGraphCount {v}=0 := by
  apply Int.cast_injective (α := ℝ)
  rw [cast_integerGraphCount,(graphFunction_translationNormalized (graph I)).2]
  norm_num

theorem setFunction_translationNormalized : TranslationNormalized (setFunction (I := I)) := by
  constructor
  · change setFunction ∅ = 0
    simp [setFunction, integerData]
  · intro v
    simp only [setFunction, integerData, integerGraphCount_singleton, sum_singleton, zero_add]
    by_cases h : v.2=0 <;> norm_num [firstWeight,h]

theorem integerData_mixed {u v : I×Fin 2} (huv : u≠ v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    integerData (insert u (insert v S))+integerData S-
      integerData (insert u S)-integerData (insert v S)=
      if (graph I).Adj u v then 1 else 0 := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  simp only [cast_integerData]
  have hg := graphFunction_delta (graph I) huv hu hv
  have hm := delta_modular (fun v : I×Fin 2 => (firstWeight v : ℝ)) huv hu hv
  unfold delta at hg hm
  split_ifs with h
  · rw [if_pos h] at hg
    linarith
  · rw [if_neg h] at hg
    linarith

theorem integerData_twins_consecutive {u v : I×Fin 2} (huv : u≠ v)
    (hnon : ¬(graph I).Adj u v) {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    integerData (insert u S)+1=integerData (insert v S) ∨
    integerData (insert v S)+1=integerData (insert u S) := by
  have hp : u.1=v.1 := Classical.not_not.mp hnon
  have ht : ∀ w,(graph I).Adj u w↔(graph I).Adj v w := by
    intro w
    change u.1≠ w.1 ↔ v.1≠ w.1
    rw [hp]
  have hg : integerGraphCount (insert u S)=integerGraphCount (insert v S) := by
    apply Int.cast_injective (α := ℝ)
    rw [cast_integerGraphCount,cast_integerGraphCount]
    exact graphFunction_insert_twins (graph I) ht S hu hv
  have hside : u.2≠ v.2 := fun he => huv (Prod.ext hp he)
  have hw : firstWeight u+1=firstWeight v ∨ firstWeight v+1=firstWeight u := by
    rcases u with ⟨i,a⟩
    rcases v with ⟨j,b⟩
    fin_cases a <;> fin_cases b <;> simp_all [firstWeight]
  simp only [integerData,sum_insert hu,sum_insert hv]
  rcases hw with hw | hw
  · left
    linarith
  · right
    linarith

theorem setFunction_graphical : Graphical (graph I) (setFunction (I := I)) := by
  intro u v huv hnon S hu hv
  have hm := integerData_mixed huv hu hv
  rw [if_neg hnon] at hm
  have ht := integerData_twins_consecutive huv hnon hu hv
  have hh := FloorHalf.twins_zero _ _ _ _ hm ht
  rw [delta_setFunction]
  exact_mod_cast hh

/-- Every original elemental slack is Boolean, uniformly in the number of
parts and in every conditioning subset. -/
theorem setFunction_boolean {u v : I×Fin 2} (huv : u≠ v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta (setFunction (I := I)) u v S=0 ∨ delta (setFunction (I := I)) u v S=1 := by
  by_cases hadj : (graph I).Adj u v
  · have hm := integerData_mixed huv hu hv
    rw [if_pos hadj] at hm
    have hh := FloorHalf.edge_boolean_of_mixed _ _ _ _ hm
    rcases hh with hh | hh
    · left
      rw [delta_setFunction]
      exact_mod_cast hh
    · right
      rw [delta_setFunction]
      exact_mod_cast hh
  · exact Or.inl (setFunction_graphical u v huv hadj S hu hv)

theorem setFunction_supermodular : Supermodular (setFunction (I := I)) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rcases setFunction_boolean huv hu hv with he | he <;> rw [he] <;> norm_num

theorem setFunction_integerValued : IntegerValued (setFunction (I := I)) :=
  fun S => ⟨integerData S/2,rfl⟩

def complementFunction : SetFunction (I×Fin 2) := graphFunction (graph I)-setFunction

theorem complementFunction_translationNormalized :
    TranslationNormalized (complementFunction (I := I)) := by
  constructor
  · change graphFunction (graph I) ∅-setFunction ∅=0
    rw [(graphFunction_translationNormalized _).1,setFunction_translationNormalized.1,sub_self]
  · intro v
    change graphFunction (graph I) {v}-setFunction {v}=0
    rw [(graphFunction_translationNormalized _).2 v,setFunction_translationNormalized.2 v,sub_self]

theorem complementFunction_supermodular : Supermodular (complementFunction (I := I)) := by
  have h := graphical_complement_supermodular (G := graph I) (z := setFunction) setFunction_graphical (show (0 : ℝ)≤1 by norm_num)
    (fun u v huv _ S hu hv => by
      rcases setFunction_boolean huv hu hv with he | he <;> rw [he] <;> norm_num)
  simpa only [complementFunction,one_smul] using h

theorem complementFunction_integerValued : IntegerValued (complementFunction (I := I)) :=
  (graphFunction_integerValued _).sub setFunction_integerValued

def polytope : Set ((I×Fin 2) → ℝ) := basePolytope setFunction
def complementPolytope : Set ((I×Fin 2) → ℝ) := basePolytope complementFunction

theorem polytope_lattice : LatticePolytope (polytope (I := I)) :=
  setFunction_integerValued.basePolytope setFunction_translationNormalized.1 setFunction_supermodular

theorem complementPolytope_lattice : LatticePolytope (complementPolytope (I := I)) :=
  complementFunction_integerValued.basePolytope complementFunction_translationNormalized.1
    complementFunction_supermodular

theorem polytope_add_complement :
    polytope (I := I)+complementPolytope=graphicalZonotope (graph I) := by
  rw [polytope,complementPolytope,←basePolytope_add setFunction_translationNormalized.1
    complementFunction_translationNormalized.1 setFunction_supermodular complementFunction_supermodular]
  rw [show (setFunction (I := I)+complementFunction)=graphFunction (graph I) by
    unfold complementFunction
    abel,baseGraphFunction_eq_graphicalZonotope]

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart235

section BundlePart236
/- Source: Papers/GraphicalZonotopes/QuadraticSignAlgebra.lean -/














@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace QuadraticSign
open Finset
open scoped symmDiff

/-- The real sign of a parity, written over the natural numbers so that no
representative of an element of `𝔽₂` is chosen implicitly. -/
def parity (n : ℕ) : ℝ := (-1 : ℝ)^n

def triangle (n : ℕ) : ℝ := parity (n.choose 2)

@[simp] theorem parity_zero : parity 0=1 := by simp [parity]
@[simp] theorem parity_one : parity 1=-1 := by simp [parity]
@[simp] theorem parity_add (m n : ℕ) : parity (m+n)=parity m*parity n := by
  simp only [parity,pow_add]
@[simp] theorem parity_square (n : ℕ) : parity n*parity n=1 := by
  simp [parity,← mul_pow]
theorem parity_ne_zero (n : ℕ) : parity n≠0 := pow_ne_zero _ (by norm_num)

theorem parity_mod_two (n : ℕ) : parity n=parity (n%2) :=
  neg_one_pow_eq_pow_mod_two n

theorem parity_mul (m n : ℕ) :
    parity (m*n)=if Even m then 1 else parity n := by
  rw [parity,pow_mul,neg_one_pow_eq_ite]
  split_ifs <;> simp [parity]

@[simp] theorem triangle_zero : triangle 0=1 := by simp [triangle]
@[simp] theorem triangle_one : triangle 1=1 := by simp [triangle]
@[simp] theorem triangle_square (n : ℕ) : triangle n*triangle n=1 := by
  exact parity_square _
theorem triangle_ne_zero (n : ℕ) : triangle n≠0 := parity_ne_zero _

theorem triangle_succ (n : ℕ) : triangle (n+1)=triangle n*parity n := by
  change parity ((n+1).choose (1+1))=triangle n*parity n
  rw [Nat.choose_succ_succ',Nat.choose_one_right,parity_add]
  exact mul_comm _ _

theorem triangle_add (m n : ℕ) :
    triangle (m+n)=triangle m*triangle n*parity (m*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m+(n+1)=(m+n)+1 by omega,triangle_succ,ih,
      triangle_succ,parity_add,show m*(n+1)=m*n+m by ring,parity_add]
    ring

theorem triangle_add_two (n : ℕ) : triangle (n+2)= -triangle n := by
  rw [show n+2=(n+1)+1 by omega,triangle_succ,triangle_succ,parity_add]
  simp only [parity_one]
  calc
    triangle n*parity n*(parity n*(-1)) =
        -(triangle n*(parity n*parity n)) := by ring
    _ = -triangle n := by rw [parity_square,mul_one]

theorem triangle_add_twice (n k : ℕ) :
    triangle (n+2*k)=triangle n*parity k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show n+2*(k+1)=(n+2*k)+2 by omega,triangle_add_two,ih,parity_add]
    simp

variable {I : Type*} [DecidableEq I]

theorem card_symmDiff_add_twice_inter (A B : Finset I) :
    (A∆B).card+2*(A∩B).card=A.card+B.card := by
  have hd : Disjoint (A\B) (B\A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  rw [Finset.symmDiff_def,card_union_of_disjoint hd]
  have ha := card_sdiff_add_card_inter A B
  have hb := card_sdiff_add_card_inter B A
  rw [inter_comm B A] at hb
  omega

/-- The complete quadratic form on subsets. Its exponent is precisely the
number of unordered pairs of chosen coordinates. -/
def complete (A : Finset I) : ℝ := triangle A.card

/-- The ordinary Boolean character pairing. -/
def pairing (A B : Finset I) : ℝ := parity (A∩B).card

@[simp] theorem complete_empty : complete (∅ : Finset I)=1 := by simp [complete]
@[simp] theorem complete_square (A : Finset I) : complete A*complete A=1 :=
  triangle_square _
theorem complete_ne_zero (A : Finset I) : complete A≠0 := triangle_ne_zero _
@[simp] theorem pairing_empty_left (A : Finset I) : pairing ∅ A=1 := by simp [pairing]
@[simp] theorem pairing_empty_right (A : Finset I) : pairing A ∅=1 := by simp [pairing]
@[simp] theorem pairing_square (A B : Finset I) : pairing A B*pairing A B=1 :=
  parity_square _
theorem pairing_comm (A B : Finset I) : pairing A B=pairing B A := by
  simp only [pairing,inter_comm]

/-- Polarization of the complete Boolean quadratic form, with every sign
identity proved over the real numbers. -/
theorem complete_symmDiff (A B : Finset I) :
    complete (A∆B)=complete A*complete B*parity (A.card*B.card)*pairing A B := by
  have h := congrArg triangle (card_symmDiff_add_twice_inter A B)
  rw [triangle_add_twice,triangle_add] at h
  calc
    complete (A∆B) =
        (triangle (A∆B).card*parity (A∩B).card)*parity (A∩B).card := by
      rw [mul_assoc,parity_square,mul_one]
      rfl
    _ = (triangle A.card*triangle B.card*parity (A.card*B.card))*
        parity (A∩B).card := by rw [h]
    _ = _ := rfl

/-- The parity of symmetric-difference cardinality is the product of the two
parities; the intersection contributes twice and therefore cancels. -/
theorem parity_card_symmDiff (A B : Finset I) :
    parity (A∆B).card=parity A.card*parity B.card := by
  have h := congrArg parity (card_symmDiff_add_twice_inter A B)
  rw [parity_add,parity_add] at h
  have htwo : parity (2*(A∩B).card)=1 := by
    rw [parity_mul]
    simp
  simpa only [htwo,mul_one] using h

theorem pairing_symmDiff_right (A B C : Finset I) :
    pairing A (B∆C)=pairing A B*pairing A C := by
  have hset : A∩(B∆C)=(A∩B)∆(A∩C) := by
    ext i
    simp only [mem_inter,mem_symmDiff]
    tauto
  change parity (A∩(B∆C)).card=_
  rw [hset,parity_card_symmDiff]
  rfl

theorem pairing_symmDiff_left (A B C : Finset I) :
    pairing (A∆B) C=pairing A C*pairing B C := by
  rw [pairing_comm,pairing_symmDiff_right,pairing_comm C A,pairing_comm C B]

variable [Fintype I]

/-- The bilinear map `I+J` on Boolean subsets. -/
def polar (A : Finset I) : Finset I := if Even A.card then A else Aᶜ

theorem pairing_compl_left (A B : Finset I) :
    pairing Aᶜ B=parity B.card*pairing A B := by
  have hcard : (Aᶜ∩B).card+(A∩B).card=B.card := by
    have hs : Aᶜ∩B=B\A := by ext i; simp [and_comm]
    rw [hs,inter_comm A B]
    exact card_sdiff_add_card_inter B A
  have h := congrArg parity hcard
  rw [parity_add] at h
  calc
    pairing Aᶜ B=(pairing Aᶜ B*pairing A B)*pairing A B := by
      rw [mul_assoc,pairing_square,mul_one]
    _ = parity B.card*pairing A B := by change _ = _; rw [show pairing Aᶜ B * pairing A B = parity B.card from h]

theorem pairing_polar (A B : Finset I) :
    pairing (polar A) B=parity (A.card*B.card)*pairing A B := by
  rw [polar,parity_mul]
  split_ifs with h
  · simp
  · exact pairing_compl_left A B

theorem complete_polarization (A B : Finset I) :
    complete (A∆B)=complete A*complete B*pairing (polar A) B := by
  rw [complete_symmDiff,pairing_polar]
  ring

theorem even_card_compl_iff (hI : Even (Fintype.card I)) (A : Finset I) :
    Even Aᶜ.card ↔ Even A.card := by
  rw [card_compl,Nat.even_iff,Nat.even_iff] 
  have hle := card_le_univ A
  have he := Nat.even_iff.mp hI
  omega

theorem polar_involutive (hI : Even (Fintype.card I)) :
    Function.Involutive (polar (I := I)) := by
  intro A
  by_cases h : Even A.card
  · simp [polar,h]
  · have hc : ¬Even Aᶜ.card := by simpa only [even_card_compl_iff hI A] using h
    simp [polar,h,hc]

theorem polar_eq_empty_iff (hI : Even (Fintype.card I)) (A : Finset I) :
    polar A=∅ ↔ A=∅ := by
  constructor
  · intro h
    have he := congrArg polar h
    rw [polar_involutive hI A] at he
    simpa [polar] using he
  · rintro rfl
    simp [polar]

end QuadraticSign
end GraphicalZonotopes

end
end
end BundlePart236

section BundlePart237
/- Source: Papers/GraphicalZonotopes/PairCounting.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators symmDiff
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary marginal of the induced-edge count. -/
theorem graphFunction_insert (G : SimpleGraph V) (u : V) (S : Finset V) (hu : u∉S) :
    graphFunction G (insert u S)=graphFunction G S+
      ∑ w∈S,if G.Adj u w then (1 : ℝ) else 0 := by
  revert hu
  induction S using Finset.induction_on with
  | empty =>
    intro hu
    simp only [insert_empty_eq, sum_empty, add_zero, (graphFunction_translationNormalized G).2]
    exact (graphFunction_translationNormalized G).1.symm
  | @insert w S hw ih =>
    intro hu
    have huS : u∉S := fun h => hu (mem_insert_of_mem h)
    have huw : u≠ w := fun h => hu (by simp [h])
    have hd := graphFunction_delta G huw huS hw
    have hm := ih huS
    rw [sum_insert hw]
    unfold delta at hd
    linarith

namespace DoubledParts
variable {I : Type*} [Fintype I] [DecidableEq I]

def firstSet (S : Finset (I×Fin 2)) : Finset I := univ.filter fun i => (i,0)∈S
def secondSet (S : Finset (I×Fin 2)) : Finset I := univ.filter fun i => (i,1)∈S

@[simp] theorem mem_firstSet (S : Finset (I×Fin 2)) (i : I) : i∈firstSet S ↔ (i,0)∈S := by
  simp [firstSet]
@[simp] theorem mem_secondSet (S : Finset (I×Fin 2)) (i : I) : i∈secondSet S ↔ (i,1)∈S := by
  simp [secondSet]

theorem subset_eq_two_images (S : Finset (I×Fin 2)) :
    S=(firstSet S).image (fun i => (i,0)) ∪ (secondSet S).image (fun i => (i,1)) := by
  ext v
  rcases v with ⟨i,b⟩
  fin_cases b <;> simp

theorem card_eq_first_add_second (S : Finset (I×Fin 2)) :
    S.card=(firstSet S).card+(secondSet S).card := by
  have hd : Disjoint ((firstSet S).image (fun i => (i,(0 : Fin 2))))
      ((secondSet S).image (fun i => (i,(1 : Fin 2)))) := by
    apply disjoint_left.mpr
    rintro w hw₀ hw₁
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hw₀
    obtain ⟨j,hj,he⟩ := mem_image.mp hw₁
    have hh := congrArg Prod.snd he
    norm_num at hh
  conv_lhs => rw [subset_eq_two_images S]
  rw [card_union_of_disjoint hd,
    card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h),
    card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]

/-- Pairs internal to one doubled part. -/
def internalPairFunction : SetFunction (I×Fin 2) :=
  ∑ i : I,setMonomial {(i,0),(i,1)}

theorem internalPairFunction_eq (S : Finset (I×Fin 2)) :
    internalPairFunction S=((firstSet S∩secondSet S).card : ℝ) := by
  simp only [internalPairFunction,Finset.sum_apply,setMonomial,Finset.insert_subset_iff,Finset.singleton_subset_iff]
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  congr 1
  apply congrArg Finset.card
  ext i
  simp

def allPairFunction (S : Finset (I×Fin 2)) : ℝ := (S.card.choose 2 : ℝ)

theorem allPairFunction_delta {u v : I×Fin 2} (huv : u≠ v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta allPairFunction u v S=1 := by
  have huvS : u∉insert v S := by simp [huv,hu]
  simp only [delta,allPairFunction,card_insert_of_notMem hu,card_insert_of_notMem hv,
    card_insert_of_notMem huvS]
  have h1 : (S.card+1).choose 2=S.card.choose 2+S.card := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' S.card 1
  have h2 : (S.card+1+1).choose 2=(S.card+1).choose 2+(S.card+1) := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' (S.card+1) 1
  rw [h2,h1]
  push_cast
  ring

theorem internalPairFunction_delta {u v : I×Fin 2} (huv : u≠ v)
    {S : Finset (I×Fin 2)} (hu : u∉S) (hv : v∉S) :
    delta internalPairFunction u v S=if u.1=v.1 then 1 else 0 := by
  rw [internalPairFunction,delta_sum]
  simp_rw [delta_setMonomial huv hu hv]
  by_cases hp : u.1=v.1
  · rw [if_pos hp,sum_eq_single u.1]
    · rcases u with ⟨i,a⟩
      rcases v with ⟨j,b⟩
      dsimp at hp
      subst j
      fin_cases a <;> fin_cases b <;> simp_all [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    · intro i hi hne
      have hn : u∉({(i,0),(i,1)} : Finset (I×Fin 2)) := by
        intro hm
        simp only [mem_insert,mem_singleton] at hm
        rcases hm with he | he <;> exact hne (congrArg Prod.fst he).symm
      simp [hn]
    · simp
  · rw [if_neg hp]
    apply sum_eq_zero
    intro i hi
    have hn : ¬(u∈({(i,0),(i,1)} : Finset (I×Fin 2)) ∧
        v∈({(i,0),(i,1)} : Finset (I×Fin 2))) := by
      rintro ⟨hu',hv'⟩
      simp only [mem_insert,mem_singleton] at hu' hv'
      rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;>
        exact hp ((congrArg Prod.fst hu').trans (congrArg Prod.fst hv').symm)
    simp only [ite_eq_right_iff,one_ne_zero,imp_false,not_and]
    intro hu' hv'
    exact False.elim (hn ⟨hu',hv'⟩)

/-- The exact induced-edge formula in all dimensions. Both sides are
identified by their complete elemental rows and normalization. -/
theorem graphFunction_eq_allPairs_sub_internal :
    graphFunction (graph I)=allPairFunction-internalPairFunction := by
  have hnorm : TranslationNormalized
      (graphFunction (graph I)-(allPairFunction-internalPairFunction)) := by
    constructor
    · change graphFunction (graph I) ∅ - (allPairFunction ∅ - internalPairFunction ∅) = 0
      rw [(graphFunction_translationNormalized (graph I)).1]
      simp [allPairFunction,internalPairFunction,setMonomial]
    · intro v
      have hp : ∀ i : I,¬({(i,0),(i,1)} : Finset (I×Fin 2))⊆{v} := by
        intro i h
        have h0 := h (by simp : (i,0)∈({(i,0),(i,1)} : Finset (I×Fin 2)))
        have h1 := h (by simp : (i,1)∈({(i,0),(i,1)} : Finset (I×Fin 2)))
        simp only [mem_singleton] at h0 h1
        have h01 := congrArg Prod.snd (h0.trans h1.symm)
        norm_num at h01
      simp [allPairFunction,internalPairFunction,setMonomial,hp,
        (graphFunction_translationNormalized _).2]
  apply sub_eq_zero.mp
  apply normalized_zero_elemental_eq_zero hnorm
  intro u v huv S hu hv
  rw [delta_sub,delta_sub,graphFunction_delta _ huv hu hv,
    allPairFunction_delta huv hu hv,internalPairFunction_delta huv hu hv]
  by_cases hp : u.1=v.1 <;> simp [graph,hp]

theorem firstWeight_sum (S : Finset (I×Fin 2)) :
    (∑ v∈S,firstWeight v : ℤ)=((firstSet S).card : ℤ) := by
  rw [show (∑ v∈S,firstWeight v : ℤ)=
      ∑ v∈S.filter (fun v => v.2=0),(1 : ℤ) by simp [firstWeight,sum_filter]]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  congr 1
  apply card_bij (fun v _ => v.1)
  · intro v hv
    rcases mem_filter.mp hv with ⟨hv,hv0⟩
    apply (mem_firstSet S v.1).mpr
    have he : (v.1, (0 : Fin 2)) = v := Prod.ext rfl hv0.symm
    rwa [he]
  · intro v hv w hw h
    apply Prod.ext h
    exact (mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm
  · intro i hi
    exact ⟨(i,0),by simpa using hi,rfl⟩

theorem integerData_count_identity (S : Finset (I×Fin 2)) :
    integerData S+((firstSet S∩secondSet S).card : ℤ)=
      (S.card.choose 2 : ℤ)+((firstSet S).card : ℤ) := by
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [cast_integerData,graphFunction_eq_allPairs_sub_internal]
  simp only [modular,subsetSum,← Int.cast_sum]
  change (allPairFunction S-internalPairFunction S)+
    ((∑ v∈S,firstWeight v : ℤ) : ℝ)+((firstSet S∩secondSet S).card : ℝ)=_
  rw [internalPairFunction_eq,firstWeight_sum]
  change (S.card.choose 2 : ℝ)-_+_+_= _
  push_cast
  ring

/-- Exact parity of the defining integer quadratic form: its quadratic part
is the complete form on the symmetric difference of the two selected sets. -/
theorem integerData_phase (S : Finset (I×Fin 2)) :
    (-1 : ℝ)^(integerData S)=
      QuadraticSign.parity (firstSet S).card *
        QuadraticSign.complete (firstSet S ∆ secondSet S) := by
  have hc : S.card=(firstSet S∆secondSet S).card+2*(firstSet S∩secondSet S).card := by
    rw [card_eq_first_add_second]
    exact (QuadraticSign.card_symmDiff_add_twice_inter _ _).symm
  have hi := congrArg (fun n : ℤ => (-1 : ℝ)^n) (integerData_count_identity S)
  rw [zpow_add₀ (by norm_num),zpow_add₀ (by norm_num)] at hi
  simp only [zpow_natCast] at hi
  change (-1 : ℝ)^integerData S*QuadraticSign.parity (firstSet S∩secondSet S).card=
    QuadraticSign.triangle S.card*QuadraticSign.parity (firstSet S).card at hi
  rw [hc,QuadraticSign.triangle_add_twice] at hi
  apply mul_right_cancel₀ (QuadraticSign.parity_ne_zero (firstSet S∩secondSet S).card)
  calc
    (-1 : ℝ)^integerData S*QuadraticSign.parity (firstSet S∩secondSet S).card =
        (QuadraticSign.triangle (firstSet S∆secondSet S).card*
          QuadraticSign.parity (firstSet S∩secondSet S).card)*
          QuadraticSign.parity (firstSet S).card := hi
    _ = _ := by unfold QuadraticSign.complete; ring

end DoubledParts
end GraphicalZonotopes

end
end
end BundlePart237

section BundlePart238
/- Source: Papers/GraphicalZonotopes/BooleanFourier.lean -/











@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Cube (I : Type*) := I → Bool

def spin (b : Bool) : ℝ := if b then -1 else 1

theorem spin_isSign (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

@[simp] theorem spin_mul_self (b : Bool) : spin b*spin b=1 := by
  cases b <;> norm_num [spin]

theorem spin_ne_zero (b : Bool) : spin b ≠ 0 := by
  cases b <;> norm_num [spin]

def character (A : Finset I) (u : Cube I) : ℝ :=
  ∏ i, if i∈A then spin (u i) else 1

@[simp] theorem character_empty (u : Cube I) : character ∅ u=1 := by
  simp [character]

@[simp] theorem character_univ (u : Cube I) :
    character univ u=∏ i,spin (u i) := by
  simp [character]

theorem character_ne_zero (A : Finset I) (u : Cube I) : character A u≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs <;> simp [spin_ne_zero]

@[simp] theorem character_square (A : Finset I) (u : Cube I) :
    character A u*character A u=1 := by
  simp only [character,← prod_mul_distrib]
  have h : ∀ i : I,(if i∈A then spin (u i) else 1)*
      (if i∈A then spin (u i) else 1)=1 := by
    intro i
    split_ifs <;> simp
  simp only [h,prod_const_one]

theorem character_compl (A : Finset I) (u : Cube I) :
    character univ u*character A u=character Aᶜ u := by
  simp only [character,mem_univ,ite_true,← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  by_cases h : i∈A <;> simp [h]

theorem character_orthogonality (A B : Finset I) :
    (∑ u : Cube I,character A u*character B u)=
      if A=B then (2 : ℝ)^Fintype.card I else 0 := by
  simp only [character,← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    (if i∈A then spin b else 1)*(if i∈B then spin b else 1))]
  have hlocal : ∀ i : I,
      (∑ b : Bool,(if i∈A then spin b else 1)*(if i∈B then spin b else 1))=
      if (i∈A ↔ i∈B) then (2 : ℝ) else 0 := by
    intro i
    by_cases ha : i∈A <;> by_cases hb : i∈B <;> norm_num [ha,hb,spin]
  simp_rw [hlocal]
  by_cases h : A=B
  · subst B
    simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ : ∃ i : I,¬(i∈A ↔ i∈B) := by
      by_contra! hh
      exact h (Finset.ext hh)
    exact prod_eq_zero (mem_univ i) (if_neg hi)

theorem coefficient_extraction (c : Finset I → ℝ) (B : Finset I) :
    (∑ u : Cube I,character B u*(∑ A : Finset I,c A*character A u))=
      (2 : ℝ)^Fintype.card I*c B := by
  simp_rw [mul_sum]
  rw [sum_comm]
  have hterm : ∀ A : Finset I,
      (∑ u : Cube I,character B u*(c A*character A u))=
      c A*(∑ u : Cube I,character B u*character A u) := by
    intro A
    rw [mul_sum]
    apply sum_congr rfl
    intro u hu
    ring
  simp_rw [hterm,character_orthogonality]
  simp [mul_comm]

theorem character_linearIndependent : LinearIndependent ℝ (character (I := I)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc B
  have hz : ∀ u : Cube I,(∑ A : Finset I,c A*character A u)=0 := by
    intro u
    have h := congrFun hc u
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using h
  have h := coefficient_extraction c B
  simp only [hz,mul_zero,sum_const_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (by norm_num))

theorem character_span : Submodule.span ℝ (Set.range (character (I := I)))=⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card character_linearIndependent,Module.finrank_pi,
    Fintype.card_finset,Fintype.card_fun]
  simp

theorem exists_character_expansion (f : Cube I → ℝ) :
    ∃ c : Finset I → ℝ,∀ u,f u=∑ A : Finset I,c A*character A u := by
  have h : f∈Submodule.span ℝ (Set.range (character (I := I))) := by
    rw [character_span]
    trivial
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp h
  refine ⟨c,fun u => ?_⟩
  have hcu := congrFun hc u
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hcu.symm

/-- A function depends on the indicated coordinates, with no representation
or regularity assumption on the remaining coordinates. -/
def DependsOn (A : Finset I) (f : Cube I → ℝ) : Prop :=
  ∀ u v : Cube I,(∀ i∈A,u i=v i) → f u=f v

theorem dependsOn_const (A : Finset I) (c : ℝ) : DependsOn A (fun _ => c) :=
  fun _ _ _ => rfl

theorem dependsOn_univ (f : Cube I → ℝ) : DependsOn univ f := by
  intro u v h
  congr 1
  exact funext fun i => h i (mem_univ i)

theorem dependsOn_character (A : Finset I) : DependsOn A (character A) := by
  intro u v h
  apply prod_congr rfl
  intro i hi
  by_cases hia : i∈A
  · simp [hia,h i hia]
  · simp [hia]

theorem DependsOn.add {A : Finset I} {f g : Cube I → ℝ}
    (hf : DependsOn A f) (hg : DependsOn A g) : DependsOn A (f+g) := by
  intro u v h
  change f u+g u=f v+g v
  rw [hf u v h,hg u v h]

theorem DependsOn.smul {A : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn A f) (c : ℝ) : DependsOn A (c • f) := by
  intro u v h
  change c*f u=c*f v
  rw [hf u v h]

theorem DependsOn.mono {A B : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn A f) (hAB : A⊆B) : DependsOn B f :=
  fun u v h => hf u v fun i hi => h i (hAB hi)

theorem dependsOn_empty_iff (f : Cube I → ℝ) :
    DependsOn ∅ f ↔ ∃ c : ℝ,∀ u,f u=c := by
  constructor
  · intro h
    exact ⟨f (fun _ => false),fun u => h u (fun _ => false) (by simp)⟩
  · rintro ⟨c,hc⟩ u v huv
    rw [hc u,hc v]

def mix (A : Finset I) (u v : Cube I) : Cube I :=
  fun i => if i∈A then u i else v i

theorem DependsOn.mix_left {A : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn A f) (u v : Cube I) : f (mix A u v)=f u := by
  apply hf
  intro i hi
  simp [mix,hi]

theorem DependsOn.mix_right {A : Finset I} {f : Cube I → ℝ}
    (hf : DependsOn Aᶜ f) (u v : Cube I) : f (mix A u v)=f v := by
  apply hf
  intro i hi
  simp only [mem_compl] at hi
  simp [mix,hi]

end BooleanFourier
end GraphicalZonotopes

end
end
end BundlePart238
