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

public import verified.parts.part020
import all verified.parts.part020

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart298
/- Source: Papers/GraphicalZonotopes/PathJoinTransitions.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def transitionSet {n : ℕ} (S : Finset (Vertex n)) : Finset (Fin (n+1)) :=
  univ.filter (fun i => vertex i.castSucc∉S ∧ vertex i.succ∈S)

theorem transition_endpoints_disjoint {n : ℕ} (S : Finset (Vertex n)) :
    Disjoint ((transitionSet S).image Fin.castSucc) ((transitionSet S).image Fin.succ) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
  obtain ⟨j,hj,hji⟩ := mem_image.mp hy
  have hzero := (mem_filter.mp hi).2.1
  have hone := (mem_filter.mp hj).2.2
  apply hzero
  simpa only [hji] using hone

theorem transition_card_le {n : ℕ} (S : Finset (Vertex n)) :
    (transitionSet S).card≤(n+2)/2 := by
  have hl : ((transitionSet S).image Fin.castSucc).card=(transitionSet S).card :=
    card_image_of_injective _ (Fin.castSucc_injective (n+1))
  have hr : ((transitionSet S).image Fin.succ).card=(transitionSet S).card :=
    card_image_of_injective _ (Fin.succ_injective (n+1))
  have hc := card_le_card (subset_univ
    (((transitionSet S).image Fin.castSucc)∪((transitionSet S).image Fin.succ)))
  rw [card_union_of_disjoint (transition_endpoints_disjoint S),hl,hr,
    card_univ,Fintype.card_fin] at hc
  omega

theorem transition_sum_eq_card {n : ℕ} (S : Finset (Vertex n)) :
    (∑ i : Fin (n+1),(1-bit (vertex i.castSucc) S)*bit (vertex i.succ) S) =
      ((transitionSet S).card : ℝ) := by
  have he (i : Fin (n+1)) :
      (1-bit (vertex i.castSucc) S)*bit (vertex i.succ) S =
      if vertex i.castSucc∉S ∧ vertex i.succ∈S then (1 : ℝ) else 0 := by
    by_cases hl : vertex i.castSucc∈S <;> by_cases hr : vertex i.succ∈S <;>
      simp [bit,hl,hr]
  simp_rw [he]
  simp [transitionSet]

theorem delta_hub_bounds {n : ℕ} (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    0≤ delta (setFunction n) (hubA n) (hubB n) S ∧
      delta (setFunction n) (hubA n) (hubB n) S≤((n+2)/2 : ℕ) := by
  rw [delta_hub S ha hb,transition_sum_eq_card]
  have hc : ((transitionSet S).card : ℝ)≤((n+2)/2 : ℕ) := by
    exact_mod_cast transition_card_le S
  have hn : (0 : ℝ)≤((transitionSet S).card : ℝ) := Nat.cast_nonneg _
  constructor <;> linarith

def alternatingSet (n : ℕ) : Finset (Vertex n) :=
  univ.filter (fun v => 2≤ v.val ∧ v.val%2=1)

@[simp] theorem hubA_notMem_alternatingSet (n : ℕ) : hubA n∉alternatingSet n := by
  simp [alternatingSet,hubA]
@[simp] theorem hubB_notMem_alternatingSet (n : ℕ) : hubB n∉alternatingSet n := by
  simp [alternatingSet,hubB]
@[simp] theorem vertex_mem_alternatingSet {n : ℕ} (i : Fin (n+2)) :
    vertex i∈alternatingSet n ↔ i.val%2=1 := by
  simp [alternatingSet,vertex,Nat.add_mod]

def evenEdgeEquiv (n : ℕ) : {i : Fin (n+1) // i.val%2=0} ≃ Fin ((n+2)/2) where
  toFun i := ⟨i.1.val/2,by have := i.1.isLt; have := i.2; omega⟩
  invFun j := ⟨⟨2*j.val,by have := j.isLt; omega⟩,by change (2*j.val)%2=0; omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    change 2*(i.1.val/2)=i.1.val
    have := i.2
    omega
  right_inv j := by
    apply Fin.ext
    change (2*j.val)/2=j.val
    omega

theorem alternating_transitions (n : ℕ) :
    transitionSet (alternatingSet n)=univ.filter (fun i : Fin (n+1) => i.val%2=0) := by
  ext i
  simp only [transitionSet,mem_filter,mem_univ,true_and,vertex_mem_alternatingSet,
    Fin.val_castSucc,Fin.val_succ]
  omega

theorem alternating_transition_card (n : ℕ) :
    (transitionSet (alternatingSet n)).card=(n+2)/2 := by
  rw [alternating_transitions,← Fintype.card_subtype]
  exact (Fintype.card_congr (evenEdgeEquiv n)).trans (Fintype.card_fin _)

theorem delta_hub_alternating (n : ℕ) :
    delta (setFunction n) (hubA n) (hubB n) (alternatingSet n)=0 := by
  rw [delta_hub _ (hubA_notMem_alternatingSet n) (hubB_notMem_alternatingSet n),
    transition_sum_eq_card,alternating_transition_card,sub_self]

end GraphicalZonotopes.PathJoin

end
end
end BundlePart298

section BundlePart299
/- Source: Papers/GraphicalZonotopes/PathJoinSpokes.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def neighborBit {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1))
    (S : Finset (Vertex n)) : ℝ :=
  if i=j.castSucc then bit (vertex j.succ) S
  else if i=j.succ then bit (vertex j.castSucc) S else 0

@[simp] theorem edge_castSucc_ne_succ {n : ℕ} (j : Fin (n+1)) :
    j.castSucc ≠ j.succ := by
  intro h
  have := congrArg Fin.val h
  simp at this

@[simp] theorem edge_succ_ne_castSucc {n : ℕ} (j : Fin (n+1)) :
    j.succ ≠ j.castSucc := (edge_castSucc_ne_succ j).symm

theorem delta_clique_a {n : ℕ} (s : Slot n) (i : Fin (n+2))
    (S : Finset (Vertex n)) (ha : hubA n∉S) (hi : vertex i∉S) :
    delta (setMonomial (clique s)) (hubA n) (vertex i) S =
      match s with
      | .inl _ => 0
      | .inr (.inl (r,j)) =>
        if j=i then if r=0 then 1 else if r=2 then bit (hubB n) S else 0 else 0
      | .inr (.inr (r,j)) =>
        if r=1 then neighborBit i j S
        else if r=3 then neighborBit i j S*bit (hubB n) S else 0 := by
  rw [delta_setMonomial (vertex_ne_hubA i).symm ha hi]
  rcases s with u | ⟨r,j⟩ | ⟨r,j⟩
  · simp [clique]
  · by_cases hj : j=i
    · subst j
      fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    · fin_cases r <;> simp [clique,hj,Ne.symm hj]
  · by_cases hl : i=j.castSucc
    · subst i
      fin_cases r <;> simp [clique,neighborBit,bit,Finset.insert_subset_iff,
        Finset.singleton_subset_iff]
      by_cases hb : hubB n∈S <;> by_cases hr : vertex j.succ∈S <;> simp [hb,hr]
    · by_cases hr : i=j.succ
      · subst i
        fin_cases r <;> simp [clique,neighborBit,hl,bit,Finset.insert_subset_iff,
          Finset.singleton_subset_iff]
        by_cases hb : hubB n∈S <;> by_cases he : vertex j.castSucc∈S <;> simp [hb,he]
      · fin_cases r <;> simp [clique,neighborBit,hl,hr]

theorem delta_clique_b {n : ℕ} (s : Slot n) (i : Fin (n+2))
    (S : Finset (Vertex n)) (hb : hubB n∉S) (hi : vertex i∉S) :
    delta (setMonomial (clique s)) (hubB n) (vertex i) S =
      match s with
      | .inl _ => 0
      | .inr (.inl (r,j)) =>
        if j=i then if r=1 then 1 else if r=2 then bit (hubA n) S else 0 else 0
      | .inr (.inr (r,j)) =>
        if r=2 then neighborBit i j S
        else if r=3 then neighborBit i j S*bit (hubA n) S else 0 := by
  rw [delta_setMonomial (vertex_ne_hubB i).symm hb hi]
  rcases s with u | ⟨r,j⟩ | ⟨r,j⟩
  · simp [clique]
  · by_cases hj : j=i
    · subst j
      fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    · fin_cases r <;> simp [clique,hj,Ne.symm hj]
  · by_cases hl : i=j.castSucc
    · subst i
      fin_cases r <;> simp [clique,neighborBit,bit,Finset.insert_subset_iff,
        Finset.singleton_subset_iff]
      by_cases ha : hubA n∈S <;> by_cases hr : vertex j.succ∈S <;> simp [ha,hr]
    · by_cases hr : i=j.succ
      · subst i
        fin_cases r <;> simp [clique,neighborBit,hl,bit,Finset.insert_subset_iff,
          Finset.singleton_subset_iff]
        by_cases ha : hubA n∈S <;> by_cases he : vertex j.castSucc∈S <;> simp [ha,he]
      · fin_cases r <;> simp [clique,neighborBit,hl,hr]

theorem delta_polynomial_a {n : ℕ} (x : Slot n → ℝ) (i : Fin (n+2))
    (S : Finset (Vertex n)) (ha : hubA n∉S) (hi : vertex i∉S) :
    delta (FiniteMonomial.polynomial clique x) (hubA n) (vertex i) S =
      x (.inr (.inl (0,i))) + x (.inr (.inl (2,i)))*bit (hubB n) S +
      ∑ j : Fin (n+1), neighborBit i j S *
        (x (.inr (.inr (1,j)))+x (.inr (.inr (3,j)))*bit (hubB n) S) := by
  rw [FiniteMonomial.polynomial,delta_sum]
  simp only [delta_smul]
  simp_rw [delta_clique_a _ _ _ ha hi]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three,
    Fin.sum_univ_four,Fin.isValue,Fin.reduceEq,ite_true,ite_false,mul_zero,
    Finset.sum_const_zero,add_zero,zero_add,Fintype.sum_unique,mul_ite,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem delta_polynomial_b {n : ℕ} (x : Slot n → ℝ) (i : Fin (n+2))
    (S : Finset (Vertex n)) (hb : hubB n∉S) (hi : vertex i∉S) :
    delta (FiniteMonomial.polynomial clique x) (hubB n) (vertex i) S =
      x (.inr (.inl (1,i))) + x (.inr (.inl (2,i)))*bit (hubA n) S +
      ∑ j : Fin (n+1), neighborBit i j S *
        (x (.inr (.inr (2,j)))+x (.inr (.inr (3,j)))*bit (hubA n) S) := by
  rw [FiniteMonomial.polynomial,delta_sum]
  simp only [delta_smul]
  simp_rw [delta_clique_b _ _ _ hb hi]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three,
    Fin.sum_univ_four,Fin.isValue,Fin.reduceEq,ite_true,ite_false,mul_zero,
    Finset.sum_const_zero,add_zero,zero_add,Fintype.sum_unique,mul_ite,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

end GraphicalZonotopes.PathJoin

end
end
end BundlePart299

section BundlePart300
/- Source: Papers/GraphicalZonotopes/PathJoinSpokeBounds.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def incidentParity {n : ℕ} (p : ℕ) (i : Fin (n+2)) : Finset (Fin (n+1)) :=
  univ.filter (fun j => j.val%2=p ∧ (i=j.castSucc ∨ i=j.succ))

def coloredNeighbor {n : ℕ} (p : ℕ) (i : Fin (n+2)) (S : Finset (Vertex n)) : ℝ :=
  ∑ j∈incidentParity p i, neighborBit i j S

theorem incidentParity_card_le_one {n : ℕ} (p : ℕ) (i : Fin (n+2)) :
    (incidentParity p i).card≤1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [incidentParity,mem_filter,mem_univ,true_and,Fin.ext_iff,
    Fin.val_castSucc,Fin.val_succ] at ha hb
  apply Fin.ext
  omega

theorem neighborBit_cases {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1))
    (S : Finset (Vertex n)) : neighborBit i j S=0 ∨ neighborBit i j S=1 := by
  by_cases hl : i=j.castSucc
  · simpa [neighborBit,hl] using bit_cases (vertex j.succ) S
  · by_cases hr : i=j.succ
    · simpa [neighborBit,hl,hr] using bit_cases (vertex j.castSucc) S
    · simp [neighborBit,hl,hr]

theorem coloredNeighbor_bounds {n : ℕ} (p : ℕ) (i : Fin (n+2))
    (S : Finset (Vertex n)) : 0≤ coloredNeighbor p i S ∧ coloredNeighbor p i S≤1 := by
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    rcases neighborBit_cases i j S with h | h <;> rw [h] <;> norm_num
  · calc
      coloredNeighbor p i S ≤ ∑ _j∈incidentParity p i,(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rcases neighborBit_cases i j S with h | h <;> rw [h] <;> norm_num
      _ = ((incidentParity p i).card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast incidentParity_card_le_one p i

theorem coloredNeighbor_eq_sum {n : ℕ} (p : ℕ) (i : Fin (n+2))
    (S : Finset (Vertex n)) :
    coloredNeighbor p i S = ∑ j : Fin (n+1),if j.val%2=p then neighborBit i j S else 0 := by
  rw [coloredNeighbor,incidentParity,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hp : j.val%2=p <;> by_cases hl : i=j.castSucc <;>
    by_cases hr : i=j.succ <;> simp [hp,hl,hr,neighborBit]

theorem coloredNeighbor_first_odd {n : ℕ} (S : Finset (Vertex n)) :
    coloredNeighbor 1 (0 : Fin (n+2)) S=0 := by
  have h : incidentParity 1 (0 : Fin (n+2))=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    simp only [incidentParity,mem_filter,mem_univ,true_and,Fin.ext_iff,
      Fin.val_zero,Fin.val_castSucc,Fin.val_succ] at hj
    omega
  simp [coloredNeighbor,h]

theorem delta_a_colored {n : ℕ} (i : Fin (n+2)) (S : Finset (Vertex n))
    (ha : hubA n∉S) (hi : vertex i∉S) :
    delta (setFunction n) (hubA n) (vertex i) S =
      1-(if i=0 then 0 else 1)*bit (hubB n) S-coloredNeighbor 0 i S+
        bit (hubB n) S*(coloredNeighbor 0 i S+coloredNeighbor 1 i S) := by
  rw [setFunction,delta_polynomial_a _ _ _ ha hi]
  simp only [coefficient,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
  rw [coloredNeighbor_eq_sum,coloredNeighbor_eq_sum]
  have hs : (∑ j : Fin (n+1), neighborBit i j S *
      ((if j.val%2=0 then -1 else 0)+1*bit (hubB n) S)) =
      -(∑ j : Fin (n+1),if j.val%2=0 then neighborBit i j S else 0)+
      bit (hubB n) S*((∑ j : Fin (n+1),if j.val%2=0 then neighborBit i j S else 0)+
        ∑ j : Fin (n+1),if j.val%2=1 then neighborBit i j S else 0) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_neg_distrib]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : j.val%2=0
    · have ho : j.val%2≠1 := by omega
      simp [he,ho]; ring
    · have ho : j.val%2=1 := by omega
      simp [he,ho]; ring
  rw [hs]
  by_cases hi0 : i=0 <;> simp [hi0] <;> ring

theorem delta_b_colored {n : ℕ} (i : Fin (n+2)) (S : Finset (Vertex n))
    (hb : hubB n∉S) (hi : vertex i∉S) :
    delta (setFunction n) (hubB n) (vertex i) S =
      (if i=0 then 0 else 1)-(if i=0 then 0 else 1)*bit (hubA n) S-
        coloredNeighbor 1 i S+
        bit (hubA n) S*(coloredNeighbor 0 i S+coloredNeighbor 1 i S) := by
  rw [setFunction,delta_polynomial_b _ _ _ hb hi]
  simp only [coefficient,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
  rw [coloredNeighbor_eq_sum,coloredNeighbor_eq_sum]
  have hs : (∑ j : Fin (n+1), neighborBit i j S *
      ((if j.val%2=0 then 0 else -1)+1*bit (hubA n) S)) =
      -(∑ j : Fin (n+1),if j.val%2=1 then neighborBit i j S else 0)+
      bit (hubA n) S*((∑ j : Fin (n+1),if j.val%2=0 then neighborBit i j S else 0)+
        ∑ j : Fin (n+1),if j.val%2=1 then neighborBit i j S else 0) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_neg_distrib]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : j.val%2=0
    · have ho : j.val%2≠1 := by omega
      simp [he,ho]; ring
    · have ho : j.val%2=1 := by omega
      simp [he,ho]; ring
  rw [hs]
  by_cases hi0 : i=0 <;> simp [hi0] <;> ring

theorem delta_a_bounds {n : ℕ} (i : Fin (n+2)) (S : Finset (Vertex n))
    (ha : hubA n∉S) (hi : vertex i∉S) :
    0≤ delta (setFunction n) (hubA n) (vertex i) S ∧
      delta (setFunction n) (hubA n) (vertex i) S≤1 := by
  rw [delta_a_colored i S ha hi]
  have he := coloredNeighbor_bounds 0 i S
  have ho := coloredNeighbor_bounds 1 i S
  by_cases hi0 : i=0
  · subst i
    rw [coloredNeighbor_first_odd]
    rcases bit_cases (hubB n) S with h | h <;> simp only [h,ite_true] <;>
      constructor <;> nlinarith
  · rcases bit_cases (hubB n) S with h | h <;> simp only [h,hi0,ite_false] <;>
      constructor <;> nlinarith

theorem delta_b_bounds {n : ℕ} (i : Fin (n+2)) (S : Finset (Vertex n))
    (hb : hubB n∉S) (hi : vertex i∉S) :
    0≤ delta (setFunction n) (hubB n) (vertex i) S ∧
      delta (setFunction n) (hubB n) (vertex i) S≤1 := by
  rw [delta_b_colored i S hb hi]
  have he := coloredNeighbor_bounds 0 i S
  have ho := coloredNeighbor_bounds 1 i S
  by_cases hi0 : i=0
  · subst i
    rw [coloredNeighbor_first_odd]
    rcases bit_cases (hubA n) S with h | h <;> simp only [h,ite_true] <;>
      constructor <;> nlinarith
  · rcases bit_cases (hubA n) S with h | h <;> simp only [h,hi0,ite_false] <;>
      constructor <;> nlinarith

end GraphicalZonotopes.PathJoin

end
end
end BundlePart300

section BundlePart301
/- Source: Papers/GraphicalZonotopes/PathJoinSupermodular.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

theorem delta_swap {n : ℕ} (f : SetFunction (Vertex n)) (u v : Vertex n)
    (S : Finset (Vertex n)) : delta f u v S=delta f v u S := by
  unfold delta
  rw [insert_comm]
  ring

theorem dilation_ge_one (n : ℕ) : (1 : ℝ)≤((n+2)/2 : ℕ) := by
  have h : 1≤(n+2)/2 := by omega
  exact_mod_cast h

theorem delta_private_bounds {n : ℕ} (i j : Fin (n+2)) (hij : i≠ j)
    (S : Finset (Vertex n)) (hi : vertex i∉S) (hj : vertex j∉S) :
    0≤ delta (setFunction n) (vertex i) (vertex j) S ∧
      delta (setFunction n) (vertex i) (vertex j) S≤1 := by
  by_cases hadj : (graph n).Adj (vertex i) (vertex j)
  · rcases (graph_vertices i j).mp hadj with h | h
    · let k : Fin (n+1) := ⟨i.val,by omega⟩
      have hk0 : k.castSucc=i := Fin.ext rfl
      have hk1 : k.succ=j := Fin.ext h
      rw [←hk0] at hi ⊢
      rw [←hk1] at hj ⊢
      rcases delta_path_boolean k S hi hj with h | h <;> rw [h] <;> norm_num
    · let k : Fin (n+1) := ⟨j.val,by omega⟩
      have hk0 : k.castSucc=j := Fin.ext rfl
      have hk1 : k.succ=i := Fin.ext h
      rw [delta_swap]
      rw [←hk0] at hj ⊢
      rw [←hk1] at hi ⊢
      rcases delta_path_boolean k S hj hi with h | h <;> rw [h] <;> norm_num
  · rw [graphical n _ _ (by simpa using hij) hadj S hi hj]
    norm_num

theorem slack_bounds {n : ℕ} (u v : Vertex n) (huv : u≠ v)
    (S : Finset (Vertex n)) (hu : u∉S) (hv : v∉S) :
    0≤ delta (setFunction n) u v S ∧
      delta (setFunction n) u v S≤((n+2)/2 : ℕ) := by
  have hbound : ∀ x : ℝ,0≤ x ∧ x≤1 → 0≤ x ∧ x≤((n+2)/2 : ℕ) :=
    fun x hx => ⟨hx.1,hx.2.trans (dilation_ge_one n)⟩
  rcases vertex_cases u with rfl | rfl | ⟨i,rfl⟩
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · exact (huv rfl).elim
    · exact delta_hub_bounds S hu hv
    · exact hbound _ (delta_a_bounds j S hu hv)
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · rw [delta_swap]; exact delta_hub_bounds S hv hu
    · exact (huv rfl).elim
    · exact hbound _ (delta_b_bounds j S hu hv)
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · rw [delta_swap]; exact hbound _ (delta_a_bounds i S hv hu)
    · rw [delta_swap]; exact hbound _ (delta_b_bounds i S hv hu)
    · exact hbound _ (delta_private_bounds i j (by simpa using huv) S hu hv)

theorem supermodular (n : ℕ) : Supermodular (setFunction n) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  exact (slack_bounds u v huv S hu hv).1

@[simp] theorem neighborBit_empty {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) :
    neighborBit i j ∅=0 := by simp [neighborBit,bit]

@[simp] theorem coloredNeighbor_empty {n : ℕ} (p : ℕ) (i : Fin (n+2)) :
    coloredNeighbor p i ∅=0 := by simp [coloredNeighbor]

theorem delta_a_empty {n : ℕ} (i : Fin (n+2)) :
    delta (setFunction n) (hubA n) (vertex i) ∅=1 := by
  rw [delta_a_colored i ∅ (notMem_empty _) (notMem_empty _)]
  simp [bit]

theorem function_ne_zero (n : ℕ) : setFunction n≠0 := by
  intro h
  have he := delta_a_empty (0 : Fin (n+2))
  rw [h] at he
  norm_num [delta] at he

end GraphicalZonotopes.PathJoin

end
end
end BundlePart301

section BundlePart302
/- Source: Papers/GraphicalZonotopes/PathJoinCoordinateRows.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

theorem mobius_setMonomial {n : ℕ} (C : Finset (Vertex n)) :
    mobius (setMonomial C)=Pi.single C 1 := by
  apply zeta_injective
  rw [zeta_mobius,zeta_eq_sum_monomials]
  simp

theorem mobius_polynomial_clique {n : ℕ} (x : Slot n → ℝ) (s : Slot n) :
    mobius (FiniteMonomial.polynomial clique x) (clique s)=x s := by
  change zetaEquiv.symm (∑ i : Slot n,x i • setMonomial (clique i)) (clique s)=x s
  rw [map_sum]
  simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change (∑ i : Slot n,x i*mobius (setMonomial (clique i)) (clique s))=x s
  simp_rw [mobius_setMonomial]
  have he (i : Slot n) : (clique i=clique s) ↔ i=s :=
    ⟨fun h => clique_injective h,fun h => congrArg clique h⟩
  have he' (i : Slot n) : (clique s=clique i) ↔ s=i :=
    ⟨fun h => clique_injective h,fun h => congrArg clique h⟩
  simp only [Pi.single_apply,he']
  simp

def coordinate {n : ℕ} (f : SetFunction (Vertex n)) (s : Slot n) : ℝ :=
  mobius f (clique s)

@[simp] theorem coordinate_setFunction {n : ℕ} (s : Slot n) :
    coordinate (setFunction n) s=coefficient n s :=
  mobius_polynomial_clique (coefficient n) s

def aCoeff {n : ℕ} (f : SetFunction (Vertex n)) (i : Fin (n+2)) :=
  coordinate f (.inr (.inl (0,i)))
def bCoeff {n : ℕ} (f : SetFunction (Vertex n)) (i : Fin (n+2)) :=
  coordinate f (.inr (.inl (1,i)))
def eCoeff {n : ℕ} (f : SetFunction (Vertex n)) (i : Fin (n+2)) :=
  coordinate f (.inr (.inl (2,i)))
def dCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  coordinate f (.inr (.inr (0,j)))
def taCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  coordinate f (.inr (.inr (1,j)))
def tbCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  coordinate f (.inr (.inr (2,j)))
def hCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  coordinate f (.inr (.inr (3,j)))
def nCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  if j.val%2=0 then taCoeff f j else tbCoeff f j
def zCoeff {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :=
  if j.val%2=0 then tbCoeff f j else taCoeff f j

theorem delta_a_hub {n : ℕ} (f : SetFunction (Vertex n)) (i : Fin (n+2)) :
    delta f (hubA n) (vertex i) {hubB n}=aCoeff f i+eCoeff f i := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubA_ne_vertex i)
    (hubA_ne_hubB n) (vertex_ne_hubB i)]
  simp [aCoeff,eCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]

theorem delta_b_hub {n : ℕ} (f : SetFunction (Vertex n)) (i : Fin (n+2)) :
    delta f (hubB n) (vertex i) {hubA n}=bCoeff f i+eCoeff f i := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubB_ne_vertex i)
    (hubB_ne_hubA n) (vertex_ne_hubA i)]
  simp [bCoeff,eCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]
  congr 1
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

theorem delta_a_right {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubA n) (vertex j.succ) {vertex j.castSucc}=
      aCoeff f j.succ+taCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubA_ne_vertex j.succ)
    (hubA_ne_vertex j.castSucc) (vertex_right_ne_left j)]
  simp [aCoeff,taCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]

theorem delta_b_right {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubB n) (vertex j.succ) {vertex j.castSucc}=
      bCoeff f j.succ+tbCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubB_ne_vertex j.succ)
    (hubB_ne_vertex j.castSucc) (vertex_right_ne_left j)]
  simp [bCoeff,tbCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]

theorem delta_a_left {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubA n) (vertex j.castSucc) {vertex j.succ}=
      aCoeff f j.castSucc+taCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubA_ne_vertex j.castSucc)
    (hubA_ne_vertex j.succ) (vertex_left_ne_right j)]
  simp [aCoeff,taCoeff,coordinate,clique]

theorem delta_b_left {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubB n) (vertex j.castSucc) {vertex j.succ}=
      bCoeff f j.castSucc+tbCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (hubB_ne_vertex j.castSucc)
    (hubB_ne_vertex j.succ) (vertex_left_ne_right j)]
  simp [bCoeff,tbCoeff,coordinate,clique]

theorem delta_a_right_hub {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubA n) (vertex j.succ) {hubB n,vertex j.castSucc}=
      aCoeff f j.succ+eCoeff f j.succ+taCoeff f j+hCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_pair (mobius f) (hubA_ne_vertex j.succ)
    (hubA_ne_hubB n) (hubA_ne_vertex j.castSucc)
    (vertex_ne_hubB j.succ) (vertex_right_ne_left j) (hubB_ne_vertex j.castSucc)]
  simp [aCoeff,eCoeff,taCoeff,hCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]
  congr 1
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

theorem delta_b_right_hub {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (hubB n) (vertex j.succ) {hubA n,vertex j.castSucc}=
      bCoeff f j.succ+eCoeff f j.succ+tbCoeff f j+hCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_pair (mobius f) (hubB_ne_vertex j.succ)
    (hubB_ne_hubA n) (hubB_ne_vertex j.castSucc)
    (vertex_ne_hubA j.succ) (vertex_right_ne_left j) (hubA_ne_vertex j.castSucc)]
  simp [bCoeff,eCoeff,tbCoeff,hCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]
  have he : mobius f {hubB n,vertex j.succ,hubA n}=
      mobius f {hubA n,vertex j.succ,hubB n} := by
    congr 1
    ext x
    simp only [mem_insert,mem_singleton]
    tauto
  have hh : mobius f {hubB n,vertex j.castSucc,vertex j.succ,hubA n}=
      mobius f {hubA n,hubB n,vertex j.succ,vertex j.castSucc} := by
    congr 1
    ext x
    simp only [mem_insert,mem_singleton]
    tauto
  rw [he,hh]

theorem delta_path_a {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (vertex j.castSucc) (vertex j.succ) {hubA n}=
      dCoeff f j+taCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (vertex_left_ne_right j)
    (vertex_ne_hubA j.castSucc) (vertex_ne_hubA j.succ)]
  simp [dCoeff,taCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]
  congr 1
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

theorem delta_path_b {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) :
    delta f (vertex j.castSucc) (vertex j.succ) {hubB n}=
      dCoeff f j+tbCoeff f j := by
  rw [←zeta_mobius f,delta_zeta_singleton (mobius f) (vertex_left_ne_right j)
    (vertex_ne_hubB j.castSucc) (vertex_ne_hubB j.succ)]
  simp [dCoeff,tbCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]
  congr 1
  ext x
  simp only [mem_insert,mem_singleton]
  tauto

theorem consecutive_middle {n : ℕ} (j : Fin n) :
    j.castSucc.succ=j.succ.castSucc := Fin.ext rfl

theorem consecutive_endpoints_ne {n : ℕ} (j : Fin n) :
    vertex j.castSucc.castSucc≠ vertex j.succ.succ := by
  simp [vertex,Fin.ext_iff]

theorem consecutive_endpoints_nonadj {n : ℕ} (j : Fin n) :
    ¬(graph n).Adj (vertex j.castSucc.castSucc) (vertex j.succ.succ) := by
  rw [graph_vertices]
  simp only [Fin.val_castSucc,Fin.val_succ]
  omega

theorem delta_a_two_neighbors {n : ℕ} (f : SetFunction (Vertex n))
    (hn : TranslationNormalized f) (hg : Graphical (graph n) f) (j : Fin n) :
    delta f (hubA n) (vertex j.castSucc.succ)
      {vertex j.castSucc.castSucc,vertex j.succ.succ}=
      aCoeff f j.castSucc.succ+taCoeff f j.castSucc+taCoeff f j.succ := by
  have hy := (mobius_cliqueSupported_iff (graph n) f).mpr ⟨hn,hg⟩
  have hz : mobius f {hubA n,vertex j.castSucc.succ,
      vertex j.castSucc.castSucc,vertex j.succ.succ}=0 :=
    hy.2.2 _ _ _ (by simp) (by simp) (consecutive_endpoints_ne j)
      (consecutive_endpoints_nonadj j)
  rw [←zeta_mobius f,delta_zeta_pair (mobius f) (hubA_ne_vertex j.castSucc.succ)
    (hubA_ne_vertex j.castSucc.castSucc) (hubA_ne_vertex j.succ.succ)
    (vertex_right_ne_left j.castSucc)
    (by rw [consecutive_middle]; exact vertex_left_ne_right j.succ)
    (consecutive_endpoints_ne j),hz,add_zero]
  simp [aCoeff,taCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]

theorem delta_b_two_neighbors {n : ℕ} (f : SetFunction (Vertex n))
    (hn : TranslationNormalized f) (hg : Graphical (graph n) f) (j : Fin n) :
    delta f (hubB n) (vertex j.castSucc.succ)
      {vertex j.castSucc.castSucc,vertex j.succ.succ}=
      bCoeff f j.castSucc.succ+tbCoeff f j.castSucc+tbCoeff f j.succ := by
  have hy := (mobius_cliqueSupported_iff (graph n) f).mpr ⟨hn,hg⟩
  have hz : mobius f {hubB n,vertex j.castSucc.succ,
      vertex j.castSucc.castSucc,vertex j.succ.succ}=0 :=
    hy.2.2 _ _ _ (by simp) (by simp) (consecutive_endpoints_ne j)
      (consecutive_endpoints_nonadj j)
  rw [←zeta_mobius f,delta_zeta_pair (mobius f) (hubB_ne_vertex j.castSucc.succ)
    (hubB_ne_vertex j.castSucc.castSucc) (hubB_ne_vertex j.succ.succ)
    (vertex_right_ne_left j.castSucc)
    (by rw [consecutive_middle]; exact vertex_left_ne_right j.succ)
    (consecutive_endpoints_ne j),hz,add_zero]
  simp [bCoeff,tbCoeff,coordinate,clique,Finset.insert_comm,Finset.pair_comm]

end GraphicalZonotopes.PathJoin

end
end
end BundlePart302

section BundlePart303
/- Source: Papers/GraphicalZonotopes/PathJoinTightEquations.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def TightOn {n : ℕ} (f : SetFunction (Vertex n)) : Prop :=
  ∀ u v,u≠ v → ∀ S,u∉S → v∉S → delta (setFunction n) u v S=0 → delta f u v S=0

theorem tight_graphical {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f) :
    Graphical (graph n) f := by
  intro u v huv hadj S hu hv
  exact h u v huv S hu hv (graphical n u v huv hadj S hu hv)

@[simp] theorem aCoeff_paper {n : ℕ} (i : Fin (n+2)) : aCoeff (setFunction n) i=1 := by
  simp [aCoeff,coefficient]
@[simp] theorem bCoeff_paper {n : ℕ} (i : Fin (n+2)) :
    bCoeff (setFunction n) i=if i=0 then 0 else 1 := by simp [bCoeff,coefficient]
@[simp] theorem eCoeff_paper {n : ℕ} (i : Fin (n+2)) :
    eCoeff (setFunction n) i=if i=0 then 0 else -1 := by simp [eCoeff,coefficient]
@[simp] theorem dCoeff_paper {n : ℕ} (i : Fin (n+1)) : dCoeff (setFunction n) i=1 := by
  simp [dCoeff,coefficient]
@[simp] theorem taCoeff_paper {n : ℕ} (i : Fin (n+1)) :
    taCoeff (setFunction n) i=if i.val%2=0 then -1 else 0 := by simp [taCoeff,coefficient]
@[simp] theorem tbCoeff_paper {n : ℕ} (i : Fin (n+1)) :
    tbCoeff (setFunction n) i=if i.val%2=0 then 0 else -1 := by simp [tbCoeff,coefficient]
@[simp] theorem hCoeff_paper {n : ℕ} (i : Fin (n+1)) : hCoeff (setFunction n) i=1 := by
  simp [hCoeff,coefficient]

def nearSpoke {n : ℕ} (f : SetFunction (Vertex n)) (j : Fin (n+1)) (i : Fin (n+2)) :=
  if j.val%2=0 then aCoeff f i else bCoeff f i

theorem tight_a_e {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (i : Fin (n+2)) (hi : i≠0) : aCoeff f i+eCoeff f i=0 := by
  have hz := h (hubA n) (vertex i) (hubA_ne_vertex i) {hubB n}
    (by simp) (by simp) (by rw [delta_a_hub]; simp [hi])
  rwa [delta_a_hub] at hz

theorem tight_b_e {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (i : Fin (n+2)) (hi : i≠0) : bCoeff f i+eCoeff f i=0 := by
  have hz := h (hubB n) (vertex i) (hubB_ne_vertex i) {hubA n}
    (by simp) (by simp) (by rw [delta_b_hub]; simp [hi])
  rwa [delta_b_hub] at hz

theorem tight_a_eq_b {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (i : Fin (n+2)) (hi : i≠0) : aCoeff f i=bCoeff f i := by
  have ha := tight_a_e h i hi
  have hb := tight_b_e h i hi
  linarith

theorem nearSpoke_eq_a {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) (i : Fin (n+2)) (hi : i≠0) : nearSpoke f j i=aCoeff f i := by
  unfold nearSpoke
  split_ifs
  · rfl
  · exact (tight_a_eq_b h i hi).symm

theorem tight_near_right {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) : nearSpoke f j j.succ+nCoeff f j=0 := by
  by_cases he : j.val%2=0
  · have hz := h (hubA n) (vertex j.succ) (hubA_ne_vertex j.succ) {vertex j.castSucc}
      (by simp) (by simp) (by rw [delta_a_right]; simp [he])
    simpa only [delta_a_right,nearSpoke,nCoeff,he,ite_true] using hz
  · have hz := h (hubB n) (vertex j.succ) (hubB_ne_vertex j.succ) {vertex j.castSucc}
      (by simp) (by simp) (by rw [delta_b_right]; simp [he])
    simpa only [delta_b_right,nearSpoke,nCoeff,he,ite_false] using hz

theorem tight_near_left {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) : nearSpoke f j j.castSucc+nCoeff f j=0 := by
  by_cases he : j.val%2=0
  · have hz := h (hubA n) (vertex j.castSucc) (hubA_ne_vertex j.castSucc) {vertex j.succ}
      (by simp) (by simp) (by rw [delta_a_left]; simp [he])
    simpa only [delta_a_left,nearSpoke,nCoeff,he,ite_true] using hz
  · have hj : j.castSucc≠0 := by
      intro hz
      have hz' := congrArg Fin.val hz
      simp only [Fin.val_castSucc,Fin.val_zero] at hz'
      omega
    have hz := h (hubB n) (vertex j.castSucc) (hubB_ne_vertex j.castSucc) {vertex j.succ}
      (by simp) (by simp) (by rw [delta_b_left]; simp [he,hj])
    simpa only [delta_b_left,nearSpoke,nCoeff,he,ite_false] using hz

theorem tight_near_right_hub {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) :
    nearSpoke f j j.succ+eCoeff f j.succ+nCoeff f j+hCoeff f j=0 := by
  by_cases he : j.val%2=0
  · have hz := h (hubA n) (vertex j.succ) (hubA_ne_vertex j.succ)
      {hubB n,vertex j.castSucc} (by simp) (by simp)
      (by rw [delta_a_right_hub]; simp [he])
    simpa only [delta_a_right_hub,nearSpoke,nCoeff,he,ite_true] using hz
  · have hz := h (hubB n) (vertex j.succ) (hubB_ne_vertex j.succ)
      {hubA n,vertex j.castSucc} (by simp) (by simp)
      (by rw [delta_b_right_hub]; simp [he])
    simpa only [delta_b_right_hub,nearSpoke,nCoeff,he,ite_false] using hz

theorem tight_path_near {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) : dCoeff f j+nCoeff f j=0 := by
  by_cases he : j.val%2=0
  · have hz := h (vertex j.castSucc) (vertex j.succ) (vertex_left_ne_right j) {hubA n}
      (by simp) (by simp) (by rw [delta_path_a]; simp [he])
    simpa only [delta_path_a,nCoeff,he,ite_true] using hz
  · have hz := h (vertex j.castSucc) (vertex j.succ) (vertex_left_ne_right j) {hubB n}
      (by simp) (by simp) (by rw [delta_path_b]; simp [he])
    simpa only [delta_path_b,nCoeff,he,ite_false] using hz

theorem tight_first_b {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f) :
    bCoeff f (0 : Fin (n+2))=0 := by
  have hdelta (g : SetFunction (Vertex n)) :
      delta g (hubB n) (vertex (0 : Fin (n+2))) ∅=bCoeff g 0 := by
    rw [←zeta_mobius g,delta_zeta_empty (mobius g) (hubB_ne_vertex _)]
    simp [bCoeff,coordinate,clique]
  have hz := h (hubB n) (vertex (0 : Fin (n+2))) (hubB_ne_vertex _) ∅
    (by simp) (by simp) (by rw [hdelta]; simp)
  rwa [hdelta] at hz

theorem tight_first_e {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f) :
    eCoeff f (0 : Fin (n+2))=0 := by
  have hz := h (hubB n) (vertex (0 : Fin (n+2))) (hubB_ne_vertex _) {hubA n}
    (by simp) (by simp) (by rw [delta_b_hub]; simp)
  rw [delta_b_hub,tight_first_b h,zero_add] at hz
  exact hz

theorem tight_first_z {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f) :
    zCoeff f (0 : Fin (n+1))=0 := by
  have hz := h (hubB n) (vertex (0 : Fin (n+1)).castSucc) (hubB_ne_vertex _)
    {vertex (0 : Fin (n+1)).succ} (by simp) (by simp)
    (by rw [delta_b_left]; simp)
  rw [delta_b_left] at hz
  simpa [zCoeff,tight_first_b h] using hz

theorem tight_two_neighbors {n : ℕ} {f : SetFunction (Vertex n)}
    (hn : TranslationNormalized f) (h : TightOn f) (j : Fin n) :
    nearSpoke f j.castSucc j.castSucc.succ+nCoeff f j.castSucc+zCoeff f j.succ=0 := by
  have hne : vertex j.castSucc.succ≠ vertex j.succ.succ := by
    rw [consecutive_middle]
    exact vertex_left_ne_right j.succ
  by_cases he : j.val%2=0
  · have ho : (j.val+1)%2≠0 := by omega
    have hz := h (hubA n) (vertex j.castSucc.succ) (hubA_ne_vertex _)
      {vertex j.castSucc.castSucc,vertex j.succ.succ} (by simp) (by simp [hne])
      (by rw [delta_a_two_neighbors _ (normalized n) (graphical n)]; simp [he,ho])
    rw [delta_a_two_neighbors _ hn (tight_graphical h)] at hz
    simpa [nearSpoke,nCoeff,zCoeff,he,ho] using hz
  · have ho : (j.val+1)%2=0 := by omega
    have hz := h (hubB n) (vertex j.castSucc.succ) (hubB_ne_vertex _)
      {vertex j.castSucc.castSucc,vertex j.succ.succ} (by simp) (by simp [hne])
      (by rw [delta_b_two_neighbors _ (normalized n) (graphical n)]; simp [he,ho])
    rw [delta_b_two_neighbors _ hn (tight_graphical h)] at hz
    simpa [nearSpoke,nCoeff,zCoeff,he,ho] using hz

end GraphicalZonotopes.PathJoin

end
end
end BundlePart303

section BundlePart304
/- Source: Papers/GraphicalZonotopes/PathJoinTightKernel.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

theorem tight_n_constant {n : ℕ} {f : SetFunction (Vertex n)} (h : TightOn f)
    (j : Fin (n+1)) : nCoeff f j=nCoeff f 0 := by
  refine Fin.induction rfl (fun k ih => ?_) j
  have hr := tight_near_right h k.castSucc
  have hl := tight_near_left h k.succ
  have hk : k.succ.castSucc≠0 := by simp [Fin.ext_iff]
  rw [nearSpoke_eq_a h _ _ (Fin.succ_ne_zero _)] at hr
  rw [nearSpoke_eq_a h _ _ hk,←consecutive_middle] at hl
  linarith

theorem tight_z_zero {n : ℕ} {f : SetFunction (Vertex n)}
    (hn : TranslationNormalized f) (h : TightOn f) (j : Fin (n+1)) : zCoeff f j=0 := by
  refine Fin.cases (tight_first_z h) (fun k => ?_) j
  have htwo := tight_two_neighbors hn h k
  have hone := tight_near_right h k.castSucc
  linarith

theorem tight_nonhub_coordinates {n : ℕ} {f : SetFunction (Vertex n)}
    (hn : TranslationNormalized f) (h : TightOn f) :
    ∃ t : ℝ,
      (∀ i : Fin (n+2),aCoeff f i=t ∧
        bCoeff f i=(if i=0 then 0 else t) ∧ eCoeff f i=(if i=0 then 0 else -t)) ∧
      (∀ j : Fin (n+1),dCoeff f j=t ∧
        taCoeff f j=(if j.val%2=0 then -t else 0) ∧
        tbCoeff f j=(if j.val%2=0 then 0 else -t) ∧ hCoeff f j=t) := by
  let t := -nCoeff f (0 : Fin (n+1))
  have hnval (j : Fin (n+1)) : nCoeff f j= -t := by
    rw [tight_n_constant h]
    dsimp [t]
    ring
  have hpos (i : Fin (n+2)) (hi : i≠0) :
      aCoeff f i=t ∧ bCoeff f i=t ∧ eCoeff f i= -t := by
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr hi
    have hr := tight_near_right h j
    rw [nearSpoke_eq_a h _ _ (Fin.succ_ne_zero _),hnval] at hr
    have hae := tight_a_e h j.succ (Fin.succ_ne_zero _)
    have hbe := tight_b_e h j.succ (Fin.succ_ne_zero _)
    constructor
    · linarith
    constructor <;> linarith
  have ha0 : aCoeff f (0 : Fin (n+2))=t := by
    have hl := tight_near_left h (0 : Fin (n+1))
    rw [hnval] at hl
    simp only [nearSpoke,Fin.val_zero,Nat.zero_mod,ite_true,Fin.castSucc_zero] at hl
    linarith
  refine ⟨t,?_,?_⟩
  · intro i
    by_cases hi : i=0
    · subst i
      simp only [ite_true]
      exact ⟨ha0,tight_first_b h,tight_first_e h⟩
    · simpa only [hi,ite_false] using hpos i hi
  · intro j
    have hd := tight_path_near h j
    rw [hnval] at hd
    have hr := tight_near_right_hub h j
    rw [nearSpoke_eq_a h _ _ (Fin.succ_ne_zero _),
      (hpos j.succ (Fin.succ_ne_zero _)).1,
      (hpos j.succ (Fin.succ_ne_zero _)).2.2,hnval] at hr
    have hz := tight_z_zero hn h j
    have hv := hnval j
    refine ⟨by linarith,?_,?_,by linarith⟩
    all_goals by_cases he : j.val%2=0 <;>
      simp only [nCoeff,zCoeff,he,ite_true,ite_false] at hv hz ⊢ <;> assumption

theorem polynomial_add {n : ℕ} (x y : Slot n → ℝ) :
    FiniteMonomial.polynomial clique (x+y)=
      FiniteMonomial.polynomial clique x+FiniteMonomial.polynomial clique y := by
  simp only [FiniteMonomial.polynomial,Pi.add_apply,add_smul,Finset.sum_add_distrib]

theorem polynomial_single {n : ℕ} (s : Slot n) (a : ℝ) :
    FiniteMonomial.polynomial clique (Pi.single s a)=a • setMonomial (clique s) := by
  classical
  unfold FiniteMonomial.polynomial
  rw [Finset.sum_eq_single s]
  · simp
  · intro j hj hjs
    simp [Pi.single_apply,hjs,Ne.symm hjs]
  · simp

/-- Every solution of all tight equations is a scalar multiple of the
displayed polynomial. The quantified test function is arbitrary; its
graphical support is derived from the nonedge tight equations.
-/
theorem complete_tight_kernel {n : ℕ} (f : SetFunction (Vertex n))
    (hn : TranslationNormalized f) (h : TightOn f) :
    ∃ t : ℝ,f=t • setFunction n := by
  obtain ⟨t,hv,he⟩ := tight_nonhub_coordinates hn h
  let x : Slot n → ℝ := coordinate f
  let a : ℝ := x (.inl ())-t*coefficient n (.inl ())
  have hx : x=t • coefficient n+Pi.single (.inl ()) a := by
    funext s
    rcases s with u | ⟨r,i⟩ | ⟨r,j⟩
    · cases u
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same]
      dsimp [a]
      ring
    · fin_cases r
      · change aCoeff f i=_
        rw [(hv i).1]
        simp [coefficient]
      · change bCoeff f i=_
        rw [(hv i).2.1]
        by_cases hi : i=0 <;> simp [coefficient,hi]
      · change eCoeff f i=_
        rw [(hv i).2.2]
        by_cases hi : i=0 <;> simp [coefficient,hi]
    · fin_cases r
      · change dCoeff f j=_
        rw [(he j).1]
        simp [coefficient]
      · change taCoeff f j=_
        rw [(he j).2.1]
        by_cases hj : j.val%2=0 <;> simp [coefficient,hj]
      · change tbCoeff f j=_
        rw [(he j).2.2.1]
        by_cases hj : j.val%2=0 <;> simp [coefficient,hj]
      · change hCoeff f j=_
        rw [(he j).2.2.2]
        simp [coefficient]
  have hf : f=FiniteMonomial.polynomial clique x := graphical_coordinates hn (tight_graphical h)
  have hsplit : f=t • setFunction n+a • setMonomial (clique (.inl () : Slot n)) := by
    rw [hf,hx,polynomial_add,FiniteMonomial.polynomial_smul,polynomial_single]
    rfl
  have hzero := h (hubA n) (hubB n) (hubA_ne_hubB n) (alternatingSet n)
    (hubA_notMem_alternatingSet n) (hubB_notMem_alternatingSet n) (delta_hub_alternating n)
  rw [hsplit,delta_add,delta_smul,delta_smul,delta_hub_alternating,
    delta_clique_hub _ _ (hubA_notMem_alternatingSet n) (hubB_notMem_alternatingSet n)] at hzero
  have ha : a=0 := by simpa using hzero
  refine ⟨t,?_⟩
  simpa only [ha,zero_smul,add_zero] using hsplit

theorem extreme (n : ℕ) : ExtremeSupermodular (setFunction n) :=
  extremeSupermodular_of_tightEquations (normalized n) (supermodular n) (function_ne_zero n)
    (fun f hn h => complete_tight_kernel f hn h)

end GraphicalZonotopes.PathJoin

end
end
end BundlePart304

section BundlePart305
/- Source: Papers/GraphicalZonotopes/PathJoinGeometry.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators Pointwise

def polytope (n : ℕ) : Set (Vertex n → ℝ) := basePolytope (setFunction n)
def complement (n : ℕ) : Set (Vertex n → ℝ) :=
  basePolytope ((((n+2)/2 : ℕ) : ℝ) • graphFunction (graph n)-setFunction n)

theorem graph_connected (n : ℕ) : (graph n).Connected := by
  apply (graph n).connected_iff_exists_forall_reachable.mpr
  refine ⟨hubA n,fun v => ?_⟩
  by_cases hv : v=hubA n
  · subst v; exact SimpleGraph.Reachable.refl _
  · exact ((graph_hubA).mpr (Ne.symm hv)).reachable

theorem neighborBit_first {n : ℕ} (j : Fin (n+1)) (S : Finset (Vertex n)) :
    neighborBit (0 : Fin (n+2)) j S =
      if j=0 then bit (vertex (0 : Fin (n+1)).succ) S else 0 := by
  by_cases hj : j=0
  · subst j
    simp [neighborBit]
  · have hl : (0 : Fin (n+2))≠ j.castSucc := by
      intro h
      apply hj
      apply Fin.ext
      have he := congrArg Fin.val h
      simpa only [Fin.val_castSucc,Fin.val_zero] using he.symm
    have hr : (0 : Fin (n+2))≠ j.succ := Ne.symm (Fin.succ_ne_zero _)
    simp [neighborBit,hj,hl,hr]

theorem delta_b_first_positive (n : ℕ) :
    delta (setFunction n) (hubB n) (vertex (0 : Fin (n+2)))
      {hubA n,vertex (0 : Fin (n+1)).succ}=1 := by
  rw [setFunction,delta_polynomial_b _ _ _ (by simp) (by simp)]
  simp [coefficient,neighborBit_first,bit]

theorem positive_slack {n : ℕ} (u v : Vertex n) (huv : (graph n).Adj u v) :
    ∃ S : Finset (Vertex n),u∉S ∧ v∉S ∧ 0< delta (setFunction n) u v S := by
  have hab : 0< delta (setFunction n) (hubA n) (hubB n) ∅ := by
    rw [delta_hub _ (by simp) (by simp)]
    simp only [bit,notMem_empty,ite_false,sub_zero,mul_zero,sum_const_zero]
    exact lt_of_lt_of_le zero_lt_one (dilation_ge_one n)
  have ha (i : Fin (n+2)) : 0< delta (setFunction n) (hubA n) (vertex i) ∅ := by
    rw [delta_a_empty]; norm_num
  have hb (i : Fin (n+2)) : ∃ S : Finset (Vertex n),hubB n∉S ∧ vertex i∉S ∧
      0< delta (setFunction n) (hubB n) (vertex i) S := by
    by_cases hi : i=0
    · subst i
      exact ⟨{hubA n,vertex (0 : Fin (n+1)).succ},by simp,by simp,
        by rw [delta_b_first_positive]; norm_num⟩
    · refine ⟨∅,by simp,by simp,?_⟩
      rw [delta_b_colored _ _ (by simp) (by simp)]
      simp [bit,hi]
  have hpath (i j : Fin (n+2)) (hij : (graph n).Adj (vertex i) (vertex j)) :
      0< delta (setFunction n) (vertex i) (vertex j) ∅ := by
    rcases (graph_vertices i j).mp hij with h | h
    · let k : Fin (n+1) := ⟨i.val,by omega⟩
      have hk0 : k.castSucc=i := Fin.ext rfl
      have hk1 : k.succ=j := Fin.ext h
      rw [←hk0,←hk1,delta_path _ _ (by simp) (by simp)]
      simp [bit]
    · let k : Fin (n+1) := ⟨j.val,by omega⟩
      have hk0 : k.castSucc=j := Fin.ext rfl
      have hk1 : k.succ=i := Fin.ext h
      rw [delta_swap,←hk0,←hk1,delta_path _ _ (by simp) (by simp)]
      simp [bit]
  rcases vertex_cases u with rfl | rfl | ⟨i,rfl⟩
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · exact ((graph n).irrefl huv).elim
    · exact ⟨∅,by simp,by simp,hab⟩
    · exact ⟨∅,by simp,by simp,ha j⟩
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · exact ⟨∅,by simp,by simp,by rw [delta_swap]; exact hab⟩
    · exact ((graph n).irrefl huv).elim
    · exact hb j
  · rcases vertex_cases v with rfl | rfl | ⟨j,rfl⟩
    · exact ⟨∅,by simp,by simp,by rw [delta_swap]; exact ha i⟩
    · obtain ⟨S,hs,hi,hd⟩ := hb i
      exact ⟨S,hi,hs,by rw [delta_swap]; exact hd⟩
    · exact ⟨∅,by simp,by simp,hpath i j huv⟩

theorem full_dimension (n : ℕ) : FullDimension (polytope n) :=
  finrank_vectorSpan_eq_of_connected_slacks (normalized n).1 (supermodular n)
    (graph_connected n) (fun u v huv => by
      obtain ⟨S,hu,hv,hd⟩ := positive_slack u v huv
      exact ⟨S,hu,hv,ne_of_gt hd⟩)

theorem indecomposable (n : ℕ) : MinkowskiIndecomposable (polytope n) :=
  (extreme n).minkowskiIndecomposable

def integerCoefficient (n : ℕ) : Slot n → ℤ
  | .inl _ => (((n+2)/2 : ℕ) : ℤ)
  | .inr (.inl (r,i)) =>
    if r=0 then 1 else if r=1 then (if i=0 then 0 else 1) else if i=0 then 0 else -1
  | .inr (.inr (r,i)) =>
    if r=0 then 1 else if r=1 then (if i.val%2=0 then -1 else 0)
    else if r=2 then (if i.val%2=0 then 0 else -1) else 1

theorem coefficient_integral (n : ℕ) (s : Slot n) : ∃ a : ℤ,coefficient n s=(a : ℝ) := by
  refine ⟨integerCoefficient n s,?_⟩
  rcases s with u | ⟨r,i⟩ | ⟨r,j⟩
  · change (((n+2)/2 : ℕ) : ℝ)=((((n+2)/2 : ℕ) : ℤ) : ℝ)
    rw [Int.cast_natCast]
  · dsimp only [coefficient,integerCoefficient]
    split_ifs <;> norm_num
  · dsimp only [coefficient,integerCoefficient]
    split_ifs <;> norm_num

theorem integerValued (n : ℕ) : IntegerValued (setFunction n) := by
  unfold setFunction FiniteMonomial.polynomial
  apply IntegerValued.finset_sum
  intro s hs
  obtain ⟨a,ha⟩ := coefficient_integral n s
  rw [ha]
  exact (setMonomial_integerValued (clique s)).int_smul a

theorem lattice (n : ℕ) : LatticePolytope (polytope n) :=
  (integerValued n).basePolytope (normalized n).1 (supermodular n)

theorem complement_normalized (n : ℕ) :
    Normalized ((((n+2)/2 : ℕ) : ℝ) • graphFunction (graph n)-setFunction n) := by
  change _*graphFunction (graph n) ∅-setFunction n ∅=0
  rw [graphFunction_normalized,(normalized n).1]
  ring

theorem complement_supermodular (n : ℕ) :
    Supermodular ((((n+2)/2 : ℕ) : ℝ) • graphFunction (graph n)-setFunction n) :=
  graphical_complement_supermodular (graphical n) (Nat.cast_nonneg _)
    (fun u v huv hadj S hu hv => (slack_bounds u v huv S hu hv).2)

theorem complement_lattice (n : ℕ) : LatticePolytope (complement n) := by
  have hz := (graphFunction_integerValued (graph n)).int_smul (((n+2)/2 : ℕ) : ℤ)
  have hi : IntegerValued ((((n+2)/2 : ℕ) : ℝ) • graphFunction (graph n)-setFunction n) := by
    simpa only [Int.cast_natCast] using hz.sub (integerValued n)
  exact hi.basePolytope (complement_normalized n) (complement_supermodular n)

theorem add_complement (n : ℕ) :
    polytope n+complement n=(((n+2)/2 : ℕ) : ℝ) • graphicalZonotope (graph n) :=
  basePolytope_add_graphical_complement (normalized n).1 (supermodular n) (graphical n)
    (Nat.cast_nonneg _) (fun u v huv hadj S hu hv => (slack_bounds u v huv S hu hv).2)

theorem actual_direction_graph (n : ℕ) : actualDirectionGraph (polytope n)=graph n := by
  ext u v
  constructor
  · exact basePolytope_summand_actualRootEdge (normalized n).1 (supermodular n)
      (graph n) (Nat.cast_nonneg _) (complement n) (add_complement n)
  · intro huv
    obtain ⟨S,hu,hv,hd⟩ := positive_slack u v huv
    exact exposedSegment_of_positive_delta (normalized n).1 (supermodular n)
      ((graph n).ne_of_adj huv) hu hv hd

/-- The actual full-dimensional lattice summand and actual lattice
complement asserted in Appendix B, for every path length at least two.
-/
theorem appendix_B_one (n : ℕ) :
    LatticePolytope (polytope n) ∧ MinkowskiIndecomposable (polytope n) ∧
      FullDimension (polytope n) ∧ LatticePolytope (complement n) ∧
      polytope n+complement n=(((n+2)/2 : ℕ) : ℝ) • graphicalZonotope (graph n) ∧
      actualDirectionGraph (polytope n)=graph n :=
  ⟨lattice n,indecomposable n,full_dimension n,complement_lattice n,add_complement n,
    actual_direction_graph n⟩

end GraphicalZonotopes.PathJoin

end
end
end BundlePart305

section BundlePart306
/- Source: Papers/GraphicalZonotopes/PathJoinThreeTree.lean -/








@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped Classical
attribute [local instance] Classical.propDecidable

def vertexPrefix (n k : ℕ) : Finset (Vertex n) := univ.filter (fun v => v.val< k)

@[simp] theorem mem_prefix {n k : ℕ} {v : Vertex n} : v∈vertexPrefix n k ↔ v.val< k := by
  simp [vertexPrefix]

theorem prefix_card (n k : ℕ) (hk : k≤ n+4) : (vertexPrefix n k).card=k := by
  rw [vertexPrefix,Fin.card_filter_val_lt,Nat.min_eq_right hk]

theorem prefix_four_clique (n : ℕ) : (graph n).IsClique (vertexPrefix n 4) := by
  intro u hu v hv huv
  have hu' := mem_prefix.mp hu
  have hv' := mem_prefix.mp hv
  change u≠ v ∧ _
  refine ⟨huv,?_⟩
  have hne : u.val≠ v.val := fun h => huv (Fin.ext h)
  omega

theorem prefix_step {n k : ℕ} (hk : k< n+4) :
    vertexPrefix n (k+1)=insert (⟨k,hk⟩ : Vertex n) (vertexPrefix n k) := by
  ext v
  simp only [mem_prefix,mem_insert,Fin.ext_iff]
  omega

def attachmentTriangle (n k : ℕ) (hk : k< n+4) : Finset (Vertex n) :=
  {hubA n,hubB n,⟨k-1,by omega⟩}

theorem attachmentTriangle_card {n k : ℕ} (hk0 : 4≤ k) (hk : k< n+4) :
    (attachmentTriangle n k hk).card=3 := by
  simp [attachmentTriangle,hubA,hubB,Fin.ext_iff,show k-1≠0 by omega,
    show k-1≠1 by omega,show 0≠ k-1 by omega,show 1≠ k-1 by omega]

theorem attachmentTriangle_subset {n k : ℕ} (hk0 : 4≤ k) (hk : k< n+4) :
    attachmentTriangle n k hk⊆vertexPrefix n k := by
  intro v hv
  simp only [attachmentTriangle,mem_insert,mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> simp only [mem_prefix,hubA,hubB] <;> omega

theorem attachmentTriangle_clique {n k : ℕ} (hk0 : 4≤ k) (hk : k< n+4) :
    (inducedOn (graph n) (vertexPrefix n k)).IsClique (attachmentTriangle n k hk) := by
  intro u hu v hv huv
  refine ⟨?_,attachmentTriangle_subset hk0 hk hu,attachmentTriangle_subset hk0 hk hv⟩
  change u∈attachmentTriangle n k hk at hu
  change v∈attachmentTriangle n k hk at hv
  simp only [attachmentTriangle,mem_insert,mem_singleton] at hu hv
  change u≠ v ∧ _
  refine ⟨huv,?_⟩
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    simp only [hubA,hubB] at * <;> try omega
  exact (huv rfl).elim

theorem induced_prefix_step {n k : ℕ} (hk0 : 4≤ k) (hk : k< n+4) :
    inducedOn (graph n) (vertexPrefix n (k+1))=
      inducedOn (graph n) (vertexPrefix n k) ⊔ attachmentStar (⟨k,hk⟩ : Vertex n)
        (attachmentTriangle n k hk) := by
  ext u v
  change ((u≠ v ∧ (u.val<2 ∨ v.val<2 ∨ u.val+1=v.val ∨ v.val+1=u.val)) ∧
      u∈vertexPrefix n (k+1) ∧ v∈vertexPrefix n (k+1)) ↔
    ((u≠ v ∧ (u.val<2 ∨ v.val<2 ∨ u.val+1=v.val ∨ v.val+1=u.val)) ∧
      u∈vertexPrefix n k ∧ v∈vertexPrefix n k) ∨
    (u≠ v ∧ ((u=⟨k,hk⟩ ∧ v∈attachmentTriangle n k hk) ∨
      (v=⟨k,hk⟩ ∧ u∈attachmentTriangle n k hk)))
  simp only [mem_prefix,attachmentTriangle,mem_insert,mem_singleton,ne_eq,Fin.ext_iff,hubA,hubB]
  omega

theorem prefix_threeTree (n t : ℕ) (ht : t≤ n) :
    ThreeTreeOn (vertexPrefix n (t+4)) (inducedOn (graph n) (vertexPrefix n (t+4))) := by
  induction t with
  | zero =>
      rw [Nat.zero_add,inducedOn_clique (prefix_four_clique n)]
      exact ThreeTreeOn.tetrahedron _ (prefix_card n 4 (by omega))
  | succ t ih =>
      have hk : t+4< n+4 := by omega
      have hs := ThreeTreeOn.attach (ih (by omega)) (⟨t+4,hk⟩ : Vertex n)
        (by simp) (attachmentTriangle n (t+4) hk) (attachmentTriangle_card (by omega) hk)
        (attachmentTriangle_subset (by omega) hk) (attachmentTriangle_clique (by omega) hk)
      have he : t+1+4=(t+4)+1 := by omega
      simpa only [Nat.succ_eq_add_one,he,←prefix_step hk,←induced_prefix_step (by omega) hk] using hs

theorem graph_isThreeTree (n : ℕ) : IsThreeTree (graph n) := by
  have h := prefix_threeTree n n le_rfl
  have hp : vertexPrefix n (n+4)=univ := by ext v; simp [mem_prefix,v.isLt]
  rw [hp] at h
  have he : inducedOn (graph n) univ=graph n := by ext u v; simp [inducedOn]
  rwa [he] at h

theorem tetrahedra_contain_hubs {n : ℕ} {C : Finset (Vertex n)}
    (hC : C∈tetrahedra (graph n)) : {hubA n,hubB n}⊆C := by
  simp only [tetrahedra,mem_filter,mem_univ,true_and] at hC
  obtain ⟨hc,hcl⟩ := hC
  obtain ⟨s,hs⟩ := clique_covers C ⟨by omega,hcl⟩
  rw [←hs] at hc ⊢
  rcases s with u | ⟨r,i⟩ | ⟨r,i⟩
  · simp [clique]
  · fin_cases r <;> simp [clique] at hc
  · fin_cases r <;> simp [clique,Finset.card_pair (vertex_left_ne_right i)] at hc ⊢

theorem tetrahedra_hub_filter (n : ℕ) :
    (tetrahedra (graph n)).filter (fun C => ({hubA n,hubB n} : Finset (Vertex n))⊆C)=
      tetrahedra (graph n) := by
  apply filter_eq_self.mpr
  intro C hC
  exact tetrahedra_contain_hubs hC

theorem tetrahedra_count (n : ℕ) : (tetrahedra (graph n)).card=n+1 := by
  have h := (graph_isThreeTree n).tetrahedra_card
  simp only [card_univ,Fintype.card_fin] at h
  omega

end GraphicalZonotopes.PathJoin

end
end
end BundlePart306

section BundlePart307
/- Source: Papers/GraphicalZonotopes/PathJoinLatticeDilation.lean -/







/-! # The sharp real lattice dilation for every two-hub path join -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped Classical
attribute [local instance] Classical.propDecidable
open scoped BigOperators Pointwise

/-- The lower bound concerns every actual lattice indecomposable summand,
not only the explicit Appendix B construction. The index n means m=n+2.
-/
theorem lattice_dilation_lower_bound (n : ℕ)
    {Q : Set (Vertex n → ℝ)} (hQ : LatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0< a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope (graph n))) :
    (((n+2)/2 : ℕ) : ℝ)≤ a := by
  classical
  have hG := graph_isThreeTree n
  have hcoeff := threeTree_lattice_four_coefficients (by omega : 4≤ n+4) hG hQ hi hd ha hsum
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := (hQ.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical (graph n) z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hzy : CliqueSupported (graph n) (mobius z) :=
    (mobius_cliqueSupported_iff (graph n) z).mpr ⟨hzn,hzg⟩
  have hzb : ∀ u v,u≠ v → (graph n).Adj u v → ∀ S,u∉S → v∉S → delta z u v S≤ a := by
    intro u v huv hadj S hu hv
    rw [delta_normalize f huv hu hv]
    exact hbound u v huv hadj S hu hv
  have hb := threeTree_integral_slack_bound hG hzs hzi hzy hzb
    (graph_hubA.mpr (hubA_ne_hubB n))
  rw [tetrahedra_hub_filter] at hb
  have hsumlower : ((n+1 : ℕ) : ℝ)≤∑ C∈tetrahedra (graph n),|mobius z C| := by
    calc
      ((n+1 : ℕ) : ℝ)=((tetrahedra (graph n)).card : ℝ) := by rw [tetrahedra_count]
      _ = ∑ C∈tetrahedra (graph n),(1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro C hC
        obtain ⟨k,hk,hvalue⟩ := hcoeff C hC
        have hc : C.card=4 := by
          have hC' := hC
          simp only [tetrahedra,mem_filter,mem_univ,true_and] at hC'
          exact hC'.1
        rw [mobius_four_normalize hc,hvalue]
        have hpos : (0 : ℤ)< abs k := abs_pos.mpr hk
        have hone : (1 : ℤ)≤ abs k := by omega
        exact_mod_cast hone
  have hnat : 2*((n+2)/2)≤ n+2 := Nat.mul_div_le n.succ.succ 2
  have hreal : (2 : ℝ)*(((n+2)/2 : ℕ) : ℝ)≤(n : ℝ)+2 := by exact_mod_cast hnat
  have hceil : ((((n+2)/2 : ℕ) : ℤ) : ℤ)≤
      Int.ceil ((1/2 : ℝ)*∑ C∈tetrahedra (graph n),|mobius z C|) := by
    have hx : ((((n+2)/2 : ℕ) : ℤ)-1)<
        Int.ceil ((1/2 : ℝ)*∑ C∈tetrahedra (graph n),|mobius z C|) :=
      Int.lt_ceil.mpr (by
        simp only [Int.cast_sub,Int.cast_natCast,Int.cast_one]
        norm_num only [Nat.cast_add,Nat.cast_one] at hsumlower
        linarith)
    omega
  have hc : (((n+2)/2 : ℕ) : ℝ)≤
      (Int.ceil ((1/2 : ℝ)*∑ C∈tetrahedra (graph n),|mobius z C|) : ℝ) := by
    have hh : (((((n+2)/2 : ℕ) : ℤ)) : ℝ)≤
        (Int.ceil ((1/2 : ℝ)*∑ C∈tetrahedra (graph n),|mobius z C|) : ℝ) := Int.cast_le.mpr hceil
    simpa only [Int.cast_natCast] using hh
  exact hc.trans hb

theorem full_lattice_summand_at (n : ℕ) :
    FullLatticeSummandAt (graph n) (((n+2)/2 : ℕ) : ℝ) := by
  refine ⟨polytope n,lattice n,indecomposable n,full_dimension n,complement n,?_,?_,?_,add_complement n⟩
  · exact (complement_lattice n).compact
  · exact (complement_lattice n).convex
  · exact basePolytope_nonempty (complement_normalized n) (complement_supermodular n)

/-- Corollary 9.4, the path-join assertion, including every real positive
dilation and every path length at least two. -/
theorem least_lattice_dilation (n : ℕ) :
    LeastFullLatticeDilation (graph n) (((n+2)/2 : ℕ) : ℝ) := by
  refine ⟨lt_of_lt_of_le zero_lt_one (dilation_ge_one n),full_lattice_summand_at n,?_⟩
  intro a ha hQ
  obtain ⟨Q,hQ,hi,hd,hs⟩ := hQ
  exact lattice_dilation_lower_bound n hQ hi hd ha hs

/-- Reindexing to the paper's unrestricted m≥2 convention is explicit. -/
theorem paper_path_join (m : ℕ) (hm : 2≤ m) :
    LeastFullLatticeDilation (graph (m-2)) ((m/2 : ℕ) : ℝ) := by
  have h := least_lattice_dilation (m-2)
  simpa only [Nat.sub_add_cancel hm] using h

end GraphicalZonotopes.PathJoin

end
end
end BundlePart307

section BundlePart308
/- Source: Papers/GraphicalZonotopes/PathJoinPathCube.lean -/







/-! # Corollary 9.4, including both small path cubes and every larger one -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.PathJoin
open Finset SetFunctionEmbedding
open scoped Pointwise

/-- Canonical coordinate relabelling of the actual Appendix B summand. -/
theorem relabelled_summand (n : ℕ) {W : Type*} [Fintype W] [DecidableEq W]
    (e : W ≃ Vertex n) :
    FullLatticeSummandAt ((graph n).comap e) (((n+2)/2 : ℕ) : ℝ) := by
  let f := restrict e.toEmbedding (setFunction n)
  have hext : ExtremeSupermodular f := extreme_restrict_equiv e (extreme n)
  have hi : IntegerValued f := integerValued_restrict e.toEmbedding (integerValued n)
  have hg : Graphical ((graph n).comap e) f := restrict_graphical e.toEmbedding (graphical n)
  let E : ((graph n).comap e) ≃g graph n := {toEquiv := e,map_rel_iff' := by intros;rfl}
  have hconn : ((graph n).comap e).Connected := E.connected_iff.mpr (graph_connected n)
  have hpositive : ∀ u v,((graph n).comap e).Adj u v →
      ∃ S : Finset W,u∉S ∧ v∉S ∧ delta f u v S≠0 := by
    intro u v huv
    obtain ⟨S,hu,hv,hd⟩ := positive_slack (e u) (e v) huv
    refine ⟨S.map e.symm.toEmbedding,by simpa using hu,by simpa using hv,?_⟩
    rw [delta_restrict]
    have hS : (S.map e.symm.toEmbedding).map e.toEmbedding=S := by ext x; simp
    rw [hS]
    exact ne_of_gt hd
  have hb : ∀ u v,u≠ v → ((graph n).comap e).Adj u v → ∀ S : Finset W,
      u∉S → v∉S → delta f u v S≤(((n+2)/2 : ℕ) : ℝ) := by
    intro u v huv hadj S hu hv
    rw [delta_restrict]
    exact (slack_bounds (e u) (e v) (fun h => huv (e.injective h)) _
      (by simpa using hu) (by simpa using hv)).2
  refine ⟨basePolytope f,hi.basePolytope hext.1.1 hext.2.1,
    hext.minkowskiIndecomposable,?_,?_⟩
  · exact finrank_vectorSpan_eq_of_connected_slacks hext.1.1 hext.2.1 hconn hpositive
  · exact (isMinkowskiSummand_graphical_iff hext.1.1 hext.2.1 (Nat.cast_nonneg _)).mpr ⟨hg,hb⟩

theorem pathCube_four_unit : FullLatticeSummandAt (Path.graph 4) 1 := by
  have h := relabelled_summand 0 (Equiv.refl (Fin 4))
  have he : (graph 0).comap (Equiv.refl (Fin 4))=Path.graph 4 := by
    ext u v
    fin_cases u <;> fin_cases v <;> decide
  simpa only [he,show ((0+2)/2 : ℕ)=1 by decide,Nat.cast_one] using h

theorem pathCube_five_unit : FullLatticeSummandAt (Path.graph 5) 1 := by
  have h := relabelled_summand 1 (Equiv.swap (0 : Fin 5) 2)
  have he : (graph 1).comap (Equiv.swap (0 : Fin 5) 2)=Path.graph 5 := by
    ext u v
    fin_cases u <;> fin_cases v <;> decide
  simpa only [he,show ((1+2)/2 : ℕ)=1 by decide,Nat.cast_one] using h

/-- The path-cube clause of Corollary 9.4, with its entire stated range. -/
theorem pathCube_least_dilation (n : ℕ) (hn : 4≤ n) :
    LeastFullLatticeDilation (Path.graph n) (if n≤5 then 1 else 2) := by
  by_cases hsmall : n≤5
  · have hunit : FullLatticeSummandAt (Path.graph n) 1 := by
      have hc : n=4 ∨ n=5 := by omega
      rcases hc with rfl | rfl
      · exact pathCube_four_unit
      · exact pathCube_five_unit
    rw [if_pos hsmall]
    refine ⟨by norm_num,hunit,?_⟩
    intro a ha hQ
    obtain ⟨Q,hQ,hi,hd,hs⟩ := hQ
    exact UnitLatticeDilation.dilation_at_least_one (by omega) hQ hi.1 hd ha hs
  · rw [if_neg hsmall]
    refine ⟨by norm_num,(threeTree_lattice_dilation_sharp.2 n (by omega)).2,?_⟩
    intro a ha hQ
    obtain ⟨Q,hQ,hi,hd,hs⟩ := hQ
    exact (threeTree_lattice_lower_bound (by omega) (Path.graph_isThreeTree hn) hQ hi hd ha hs).1

/-- Every clause of the paper's Corollary 9.4. -/
theorem corollary_nine_four :
    (∀ m : ℕ,2≤ m → LeastFullLatticeDilation (graph (m-2)) ((m/2 : ℕ) : ℝ)) ∧
    (∀ n : ℕ,4≤ n → LeastFullLatticeDilation (Path.graph n) (if n≤5 then 1 else 2)) :=
  ⟨paper_path_join,pathCube_least_dilation⟩

end GraphicalZonotopes.PathJoin

end
end
end BundlePart308

section BundlePart309
/- Source: Papers/GraphicalZonotopes/BoundaryCapacityStrict.lean -/




/-! # Strict maximality of complete-graph boundary capacity

This is Lemma 7.13. Missing cliques inject into missing boundary rows;
when there are at least three vertices an additional missing row proves
strictness. The proof counts the actual boundary contexts used by the
separator theorem.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BoundaryCapacity
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq

abbrev TopContext (V : Type*) [Fintype V] [LinearOrder V] :=
  BoundaryContext (⊤ : SimpleGraph V)

def Valid (G : SimpleGraph V) (r : TopContext V) : Prop :=
  G.Adj r.1.1.1 r.1.1.2 ∧ r.2.1 ⊆ commonNeighbors G r.1.1.1 r.1.1.2

abbrev MissingRow (G : SimpleGraph V) := {r : TopContext V // ¬Valid G r}
abbrev MissingClique (G : SimpleGraph V) :=
  {C : CliqueIndex (⊤ : SimpleGraph V) // ¬G.IsClique C.1}

def contextSet (r : TopContext V) : Finset V := insert r.1.1.1 (insert r.1.1.2 r.2.1)

def contextOfPair (C : Finset V) (u v : V) (huv : u< v) : TopContext V :=
  ⟨⟨(u,v),huv,by simpa only [SimpleGraph.top_adj] using ne_of_lt huv⟩,
    ⟨(C.erase u).erase v,mem_powerset.mpr (by
      intro w hw
      simp only [mem_erase] at hw
      simp only [mem_commonNeighbors,SimpleGraph.top_adj]
      exact ⟨Ne.symm hw.2.1,Ne.symm hw.1⟩)⟩⟩

theorem contextSet_pair (C : Finset V) (u v : V) (huv : u< v)
    (hu : u∈C) (hv : v∈C) : contextSet (contextOfPair C u v huv)=C := by
  ext w
  simp only [contextSet,contextOfPair,mem_insert,mem_erase]
  constructor
  · rintro (rfl|rfl|⟨hwv,hwu,hw⟩)
    · exact hu
    · exact hv
    · exact hw
  · intro hw
    by_cases hwu : w=u
    · exact Or.inl hwu
    · by_cases hwv : w=v
      · exact Or.inr (Or.inl hwv)
      · exact Or.inr (Or.inr ⟨hwv,hwu,hw⟩)

theorem missing_pair (G : SimpleGraph V) (C : MissingClique G) :
    ∃ u∈C.1.1,∃ v∈C.1.1,u< v ∧ ¬G.Adj u v := by
  by_contra hn
  apply C.2
  intro u hu v hv huv
  by_contra hnon
  apply hn
  rcases lt_or_gt_of_ne huv with hlt|hgt
  · exact ⟨u,hu,v,hv,hlt,hnon⟩
  · exact ⟨v,hv,u,hu,hgt,fun h => hnon (G.adj_symm h)⟩

noncomputable def missingLeft (G : SimpleGraph V) (C : MissingClique G) : V :=
  (missing_pair G C).choose
noncomputable def missingRight (G : SimpleGraph V) (C : MissingClique G) : V :=
  (missing_pair G C).choose_spec.2.choose

theorem missingLeft_mem (G : SimpleGraph V) (C : MissingClique G) : missingLeft G C∈C.1.1 :=
  (missing_pair G C).choose_spec.1

theorem missingRight_mem (G : SimpleGraph V) (C : MissingClique G) : missingRight G C∈C.1.1 :=
  (missing_pair G C).choose_spec.2.choose_spec.1

theorem missing_lt (G : SimpleGraph V) (C : MissingClique G) : missingLeft G C < missingRight G C :=
  (missing_pair G C).choose_spec.2.choose_spec.2.1

theorem missing_nonadj (G : SimpleGraph V) (C : MissingClique G) :
    ¬G.Adj (missingLeft G C) (missingRight G C) :=
  (missing_pair G C).choose_spec.2.choose_spec.2.2

def missingInjection (G : SimpleGraph V) (C : MissingClique G) : MissingRow G :=
  ⟨contextOfPair C.1.1 (missingLeft G C) (missingRight G C) (missing_lt G C),
    fun h => missing_nonadj G C h.1⟩

@[simp] theorem contextSet_missingInjection (G : SimpleGraph V) (C : MissingClique G) :
    contextSet (missingInjection G C).1=C.1.1 :=
  contextSet_pair _ _ _ (missing_lt G C) (missingLeft_mem G C) (missingRight_mem G C)

theorem missingInjection_injective (G : SimpleGraph V) : Function.Injective (missingInjection G) := by
  intro C D he
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (fun r : MissingRow G => contextSet r.1) he
  simpa only [contextSet_missingInjection] using h

theorem top_not_clique (G : SimpleGraph V) (hG : G≠⊤) : ¬G.IsClique (univ : Finset V) := by
  intro h
  apply hG
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro h
    exact (SimpleGraph.top_adj _ _).mpr h.ne
  · intro huv
    exact h (mem_univ _) (mem_univ _) ((SimpleGraph.top_adj _ _).mp huv)

def fullMissingClique (G : SimpleGraph V) (hn : 3≤ Fintype.card V) (hG : G≠⊤) : MissingClique G :=
  ⟨⟨univ,by simp only [IsCliqueCoordinate,card_univ]; exact ⟨by omega,fun u hu v hv huv => huv⟩⟩,
    top_not_clique G hG⟩

theorem exists_third (hn : 3≤ Fintype.card V) (u v : V) : ∃ w : V,w≠ u ∧ w≠ v := by
  by_contra h
  push_neg at h
  have he : (univ : Finset V)⊆{u,v} := by
    intro w hw
    by_cases hwu : w=u
    · simp [hwu]
    · simp [h w hwu]
  have hc := card_le_card he
  have hp : ({u,v} : Finset V).card≤2 := by exact card_insert_le _ _ |>.trans (by simp)
  simp only [card_univ] at hc
  omega

/-- Every proper graph has strictly more missing contexts than missing
cliques when the vertex set has cardinality at least three. -/
theorem missing_card_lt (G : SimpleGraph V) (hn : 3≤ Fintype.card V) (hG : G≠⊤) :
    Fintype.card (MissingClique G)< Fintype.card (MissingRow G) := by
  apply Fintype.card_lt_of_injective_not_surjective (missingInjection G) (missingInjection_injective G)
  intro hsurj
  let C := fullMissingClique G hn hG
  let u := missingLeft G C
  let v := missingRight G C
  have huv : u< v := missing_lt G C
  have hnon : ¬G.Adj u v := missing_nonadj G C
  obtain ⟨w,hwu,hwv⟩ := exists_third hn u v
  have huC : u∈(univ : Finset V) := mem_univ _
  have hwC : w∈(univ : Finset V) := mem_univ _
  rcases lt_or_gt_of_ne (Ne.symm hwu) with huw|hwu'
  · let r := contextOfPair univ u w huw
    have hr : ¬Valid G r := by
      intro hr
      have hvS : v∈r.2.1 := by simp [r,contextOfPair,ne_of_gt huv,Ne.symm hwv]
      have hvN := hr.2 hvS
      exact hnon ((mem_commonNeighbors _ _ _ _).mp hvN).1
    obtain ⟨D,hD⟩ := hsurj ⟨r,hr⟩
    have hDC : D=C := by
      apply Subtype.ext
      apply Subtype.ext
      have h := congrArg (fun a : MissingRow G => contextSet a.1) hD
      simpa only [contextSet_missingInjection,r,C,fullMissingClique,
        contextSet_pair univ u w huw huC hwC] using h
    subst D
    have he := congrArg (fun a : MissingRow G => a.1.1.1.2) hD
    change v=w at he
    exact hwv he.symm
  · let r := contextOfPair univ w u hwu'
    have hr : ¬Valid G r := by
      intro hr
      have hvS : v∈r.2.1 := by simp [r,contextOfPair,ne_of_gt huv,Ne.symm hwv]
      have hvN := hr.2 hvS
      exact hnon ((mem_commonNeighbors _ _ _ _).mp hvN).2
    obtain ⟨D,hD⟩ := hsurj ⟨r,hr⟩
    have hDC : D=C := by
      apply Subtype.ext
      apply Subtype.ext
      have h := congrArg (fun a : MissingRow G => contextSet a.1) hD
      simpa only [contextSet_missingInjection,r,C,fullMissingClique,
        contextSet_pair univ w u hwu' hwC huC] using h
    subst D
    have he := congrArg (fun a : MissingRow G => a.1.1.1.1) hD
    change u=w at he
    exact hwu he.symm

def validContextEquiv (G : SimpleGraph V) :
    BoundaryContext G ≃ {r : TopContext V // Valid G r} where
  toFun r := ⟨⟨⟨r.1.1,r.1.2.1,by simpa only [SimpleGraph.top_adj] using r.1.2.2.ne⟩,
    ⟨r.2.1,mem_powerset.mpr (by
      intro w hw
      have h := (mem_commonNeighbors _ _ _ _).mp ((mem_powerset.mp r.2.2) hw)
      simpa only [mem_commonNeighbors,SimpleGraph.top_adj] using And.intro h.1.ne h.2.ne)⟩⟩,
    r.1.2.2,mem_powerset.mp r.2.2⟩
  invFun r := ⟨⟨r.1.1.1,r.1.1.2.1,r.2.1⟩,⟨r.1.2.1,mem_powerset.mpr r.2.2⟩⟩
  left_inv r := by cases r; rfl
  right_inv r := by cases r; rfl

def validCliqueEquiv (G : SimpleGraph V) :
    CliqueIndex G ≃ {C : CliqueIndex (⊤ : SimpleGraph V) // G.IsClique C.1} where
  toFun C := ⟨⟨C.1,C.2.1,fun u hu v hv huv => huv⟩,C.2.2⟩
  invFun C := ⟨C.1.1,C.1.2.1,C.2⟩
  left_inv C := rfl
  right_inv C := rfl

/-- The complete graph uniquely maximizes m(G)-d(G), exactly for the
actual boundary-row and clique-coordinate counts of Lemma 7.13. -/
theorem proper_capacity_lt (G : SimpleGraph V) (hn : 3≤ Fintype.card V) (hG : G≠⊤) :
    Fintype.card (BoundaryContext G)-Fintype.card (CliqueIndex G)<
      Fintype.card (BoundaryContext (⊤ : SimpleGraph V))-
        Fintype.card (CliqueIndex (⊤ : SimpleGraph V)) := by
  have h := missing_card_lt G hn hG
  have hr : Fintype.card (MissingRow G)=
      Fintype.card (TopContext V)-Fintype.card (BoundaryContext G) := by
    rw [Fintype.card_subtype_compl,←Fintype.card_congr (validContextEquiv G)]
  have hc : Fintype.card (MissingClique G)=
      Fintype.card (CliqueIndex (⊤ : SimpleGraph V))-Fintype.card (CliqueIndex G) := by
    rw [Fintype.card_subtype_compl,←Fintype.card_congr (validCliqueEquiv G)]
  rw [hr,hc] at h
  have hmr : Fintype.card (BoundaryContext G)≤ Fintype.card (TopContext V) := by
    rw [Fintype.card_congr (validContextEquiv G)]
    exact Fintype.card_subtype_le _
  have hmc : Fintype.card (CliqueIndex G)≤ Fintype.card (CliqueIndex (⊤ : SimpleGraph V)) := by
    rw [Fintype.card_congr (validCliqueEquiv G)]
    exact Fintype.card_subtype_le _
  have hle := clique_count_le_boundary_context_count G
  have htop := clique_count_le_boundary_context_count (⊤ : SimpleGraph V)
  change Fintype.card (CliqueIndex (⊤ : SimpleGraph V))-Fintype.card (CliqueIndex G)<
      Fintype.card (BoundaryContext (⊤ : SimpleGraph V))-Fintype.card (BoundaryContext G) at h
  change Fintype.card (BoundaryContext G)≤ Fintype.card (BoundaryContext (⊤ : SimpleGraph V)) at hmr
  omega

end GraphicalZonotopes.BoundaryCapacity

end
end
end BundlePart309

section BundlePart310
/- Source: Papers/GraphicalZonotopes/BoundaryInducedCounting.lean -/





/-! # Boundary counts are counts in the actual induced graph -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.Separator
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [LinearOrder V]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable (G : SimpleGraph V) (B : Finset V)

def inducedBoundaryGraph : SimpleGraph B := G.comap Subtype.val

def inducedContextToBoundary (r : BoundaryContext (inducedBoundaryGraph G B)) : BoundaryRow G B :=
  ⟨⟨⟨(r.1.1.1.1,r.1.1.2.1),r.1.2.1,r.1.2.2⟩,
    ⟨r.2.1.map (Function.Embedding.subtype _),mem_powerset.mpr (by
      intro w hw
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
      have h := (mem_commonNeighbors (inducedBoundaryGraph G B) _ _ v).mp
        ((mem_powerset.mp r.2.2) hv)
      exact (mem_commonNeighbors G _ _ _).mpr h)⟩⟩,
    r.1.1.1.2,r.1.1.2.2,by
      intro w hw
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
      exact v.2⟩

def boundaryContextToInduced (r : BoundaryRow G B) : BoundaryContext (inducedBoundaryGraph G B) :=
  ⟨⟨(⟨r.1.1.1.1,r.2.1⟩,⟨r.1.1.1.2,r.2.2.1⟩),r.1.1.2.1,r.1.1.2.2⟩,
    ⟨r.1.2.1.subtype (·∈B),mem_powerset.mpr (by
      intro w hw
      have h := (mem_commonNeighbors G _ _ _).mp
        ((mem_powerset.mp r.1.2.2) (mem_subtype.mp hw))
      exact (mem_commonNeighbors (inducedBoundaryGraph G B) _ _ w).mpr h)⟩⟩

def inducedBoundaryContextEquiv : BoundaryContext (inducedBoundaryGraph G B) ≃ BoundaryRow G B where
  toFun := inducedContextToBoundary G B
  invFun := boundaryContextToInduced G B
  left_inv r := by
    rcases r with ⟨⟨⟨u,v⟩,huv,hadj⟩,⟨S,hS⟩⟩
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    apply Subtype.ext
    ext w
    simp [boundaryContextToInduced,inducedContextToBoundary]
  right_inv r := by
    apply Subtype.ext
    apply Sigma.ext (by rfl)
    apply heq_of_eq
    apply Subtype.ext
    exact subtype_map_of_mem r.2.2.2

def inducedBoundaryCliqueEquiv : CliqueIndex (inducedBoundaryGraph G B) ≃ boundaryIndex G B where
  toFun C := ⟨⟨C.1.map (Function.Embedding.subtype _),by
      refine ⟨by simpa only [card_map] using C.2.1,?_⟩
      intro u hu v hv huv
      obtain ⟨u',hu',rfl⟩ := mem_map.mp hu
      obtain ⟨v',hv',rfl⟩ := mem_map.mp hv
      exact C.2.2 hu' hv' (fun h => huv (congrArg Subtype.val h))⟩,by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
    exact v.2⟩
  invFun C := ⟨C.1.1.subtype (·∈B),by
    have he := subtype_map_of_mem C.2
    refine ⟨?_,?_⟩
    · have hc := congrArg Finset.card he
      rw [card_map] at hc
      rw [hc]
      exact C.1.2.1
    · intro u hu v hv huv
      exact C.1.2.2 (mem_subtype.mp hu) (mem_subtype.mp hv)
        (fun h => huv (Subtype.ext h))⟩
  left_inv C := by
    apply Subtype.ext
    ext w
    simp
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    exact subtype_map_of_mem C.2

/-- A nonclique boundary has strictly less capacity than the complete
boundary on the same vertex set, with the actual induced rows and cliques. -/
theorem boundary_capacity_lt_of_not_clique (hs : 3≤ B.card) (hB : ¬G.IsClique B) :
    Fintype.card (BoundaryRow G B)-(boundaryCliques G B).card+1< cliqueCapacity B.card := by
  have hnot : inducedBoundaryGraph G B≠⊤ := by
    intro he
    apply hB
    intro u hu v hv huv
    have ht : (⊤ : SimpleGraph B).Adj ⟨u,hu⟩ ⟨v,hv⟩ :=
      (SimpleGraph.top_adj _ _).mpr (fun h => huv (congrArg Subtype.val h))
    rw [←he] at ht
    exact ht
  have h := BoundaryCapacity.proper_capacity_lt (inducedBoundaryGraph G B)
    (by simpa only [Fintype.card_coe] using hs) hnot
  rw [Fintype.card_congr (inducedBoundaryContextEquiv G B),
    Fintype.card_congr (inducedBoundaryCliqueEquiv G B),boundaryIndex_card] at h
  have htop : inducedBoundaryGraph (⊤ : SimpleGraph V) B=⊤ := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    simp only [inducedBoundaryGraph,SimpleGraph.comap_adj,SimpleGraph.top_adj]
    exact not_congr Subtype.val_inj
  rw [←htop,Fintype.card_congr (inducedBoundaryContextEquiv (⊤ : SimpleGraph V) B),
    Fintype.card_congr (inducedBoundaryCliqueEquiv (⊤ : SimpleGraph V) B),
    boundaryIndex_card,
    boundaryRow_card_of_clique (G := (⊤ : SimpleGraph V)) (by intro u hu v hv huv; exact huv),
    boundaryCliques_card_of_clique (G := (⊤ : SimpleGraph V)) (by intro u hu v hv huv; exact huv)] at h
  exact Nat.add_lt_add_right h 1

end GraphicalZonotopes.Separator

end
end
end BundlePart310

section BundlePart311
/- Source: Papers/GraphicalZonotopes/SaturatedSeparatorBounds.lean -/





/-! # Full-dimensional separator bounds on arbitrary finite vertex types

These are the separator consequences used for the sharp actual-direction
bound in Theorem 7.12. The private pieces are genuine Möbius-coordinate
blocks, and the boundary is the induced graph, including missing edges.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.Separator
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V J : Type*} [Fintype V] [LinearOrder V] [Fintype J] [DecidableEq J]
local instance : DecidableEq V := LinearOrder.toDecidableEq
variable {G : SimpleGraph V} {B : Finset V} {A : J → Finset V}

/-- Full dimension makes every nonempty private piece active. -/
theorem private_block_nonzero_full (hn : 2 ≤ Fintype.card V) (h : Partition G B A)
    (z : graphicalFunctionSpace G) (hz : Supermodular z.1)
    (hd : FullDimension (basePolytope z.1)) (j : J) (hAj : (A j).Nonempty) :
    ((functionEquiv h).symm z).2 j ≠ 0 := by
  intro hzero
  obtain ⟨v,hvj⟩ := hAj
  have hvB : v ∉ B := fun hvB =>
    disjoint_left.mp (h.boundary_disjoint j) hvB hvj
  have hy := (mobius_cliqueSupported_iff G z.1).mpr z.2
  have hkill : ∀ C : Finset V,v ∈ C → mobius z.1 C = 0 := by
    intro C hvC
    by_cases hC : IsCliqueCoordinate G C
    · have hCB : ¬C ⊆ B := fun hCB => hvB (hCB hvC)
      obtain ⟨k,hCk,hunique⟩ := h.clique_unique_branch ⟨C,hC⟩ hCB
      have hvk : v ∈ A k := (mem_union.mp (hCk hvC)).resolve_left hvB
      have hkj : k = j := by
        by_contra hkj
        exact disjoint_left.mp (h.private_disjoint hkj) hvk hvj
      subst k
      let D : privateIndex G B A j := ⟨⟨C,hC⟩,hCB,hCk⟩
      have he := congrFun hzero D
      exact (private_coordinate_eq_mobius h z j D).symm.trans he
    · exact coefficient_zero_of_not_clique hy C hC
  have hdep : DependsOn z.1 (univ.erase v) := by
    rw [← zeta_mobius z.1]
    apply zeta_dependsOn
    intro C hC
    apply hkill C
    by_contra hvC
    apply hC
    intro w hw
    exact mem_erase.mpr ⟨fun he => hvC (he ▸ hw),mem_univ _⟩
  have hb := finrank_vectorSpan_le_support z.2.1 hz hdep
  rw [card_erase_of_mem (mem_univ v),card_univ] at hb
  change Module.finrank ℝ (vectorSpan ℝ (basePolytope z.1)) = Fintype.card V-1 at hd
  rw [hd] at hb
  omega

theorem full_partition_capacity (hn : 2 ≤ Fintype.card V) (h : Partition G B A)
    (hA : ∀ j,(A j).Nonempty) (z : graphicalFunctionSpace G)
    (hz : ExtremeSupermodular z.1) (hd : FullDimension (basePolytope z.1)) :
    Fintype.card J ≤ Fintype.card (BoundaryRow G B) - Fintype.card (boundaryIndex G B) + 1 := by
  let x := (functionEquiv h).symm z
  have hactive : ∀ j,x.2 j ≠ 0 := fun j =>
    private_block_nonzero_full hn h z hz.2.1 hd j (hA j)
  let e : Gluing.ActiveBranch x.2 ≃ J := {
    toFun := Subtype.val
    invFun := fun j => ⟨j,hactive j⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hb := separator_capacity_for_function h z hz
  rw [←boundaryRow_card,←boundaryIndex_card] at hb
  exact (Fintype.card_congr e).symm ▸ hb

theorem full_partition_clique_capacity (hn : 2 ≤ Fintype.card V) (h : Partition G B A)
    (hA : ∀ j,(A j).Nonempty) (hB : G.IsClique B)
    (z : graphicalFunctionSpace G) (hz : ExtremeSupermodular z.1)
    (hd : FullDimension (basePolytope z.1)) : Fintype.card J ≤ cliqueCapacity B.card := by
  have hb := full_partition_capacity hn h hA z hz hd
  rw [boundaryRow_card_of_clique hB,boundaryIndex_card,boundaryCliques_card_of_clique hB] at hb
  exact hb

/-- A proper induced boundary has strictly smaller capacity than the clique
on the same boundary vertices. -/
theorem proper_boundary_capacity_lt (G : SimpleGraph V) (B : Finset V)
    (hB : 3 ≤ B.card) (hnclique : ¬G.IsClique B) :
    Fintype.card (BoundaryRow G B) - Fintype.card (boundaryIndex G B) + 1 <
      cliqueCapacity B.card := by
  rw [boundaryIndex_card]
  exact boundary_capacity_lt_of_not_clique G B hB hnclique

end GraphicalZonotopes.Separator

end
end
end BundlePart311

section BundlePart312
/- Source: Papers/GraphicalZonotopes/SaturatedBookLower.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SaturatedDirections
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance {V : Type*} [LinearOrder V] : DecidableEq V := LinearOrder.toDecidableEq

variable {s k : ℕ}
abbrev Vertex (s k : ℕ) := Fin s ⊕ Fin k
local instance vertexOrder (s k : ℕ) : LinearOrder (Vertex s k) :=
  inferInstanceAs (LinearOrder (Fin s ⊕ₗ Fin k))
local instance vertexDecidableEq (s k : ℕ) : DecidableEq (Vertex s k) :=
  (vertexOrder s k).toDecidableEq

def bookPartition {H : SimpleGraph (Vertex s k)} (hH : H ≤ cliqueBook s k) :
    Separator.Partition H (BookDimension.boundary s k) (BookDimension.privatePart s k) where
  boundary_disjoint := (BookDimension.partition s k).boundary_disjoint
  private_disjoint := (BookDimension.partition s k).private_disjoint
  cover := (BookDimension.partition s k).cover
  no_cross_edge := fun i j u v hu hv hadj =>
    (BookDimension.partition s k).no_cross_edge i j u v hu hv (hH hadj)

/-- At separator saturation no hub edge can be missing. -/
theorem hubs_clique (hs : 3 ≤ s) {H : SimpleGraph (Vertex s (cliqueCapacity s))}
    (hH : H ≤ cliqueBook s (cliqueCapacity s))
    (z : graphicalFunctionSpace H) (hz : ExtremeSupermodular z.1)
    (hd : FullDimension (basePolytope z.1)) : H.IsClique (BookDimension.boundary s (cliqueCapacity s)) := by
  by_contra hnon
  have hb := Separator.full_partition_capacity
    (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
    (bookPartition hH) (fun j => singleton_nonempty _) z hz hd
  have hstrict := Separator.proper_boundary_capacity_lt H
    (BookDimension.boundary s (cliqueCapacity s))
    (by simpa only [BookDimension.boundary_card] using hs) hnon
  rw [BookDimension.boundary_card] at hstrict
  simp only [Fintype.card_fin] at hb
  omega

def outerNeighbors (H : SimpleGraph (Vertex s k)) (i : Fin s) : Finset (Fin k) :=
  univ.filter (fun j => H.Adj (.inl i) (.inr j))

def outerNonneighbors (H : SimpleGraph (Vertex s k)) (i : Fin s) : Finset (Fin k) :=
  univ.filter (fun j => ¬H.Adj (.inl i) (.inr j))

def smallerBoundary (i : Fin s) : Finset (Vertex s k) :=
  (BookDimension.boundary s k).erase (.inl i)

def hubPrivate (H : SimpleGraph (Vertex s k)) (i : Fin s) :
    Option {j : Fin k // ¬H.Adj (.inl i) (.inr j)} → Finset (Vertex s k)
  | none => insert (.inl i) ((outerNeighbors H i).image Sum.inr)
  | some j => {Sum.inr j.1}

@[simp] theorem mem_outerNeighbors (H : SimpleGraph (Vertex s k)) (i : Fin s) (j : Fin k) :
    j ∈ outerNeighbors H i ↔ H.Adj (.inl i) (.inr j) := by
  simp only [outerNeighbors,mem_filter,mem_univ,true_and]

theorem hubPrivate_nonempty (H : SimpleGraph (Vertex s k)) (i : Fin s)
    (j : Option {j : Fin k // ¬H.Adj (.inl i) (.inr j)}) : (hubPrivate H i j).Nonempty := by
  cases j with
  | none => exact insert_nonempty _ _
  | some j => exact singleton_nonempty _

@[simp] theorem mem_smallerBoundary (i : Fin s) (v : Vertex s k) :
    v ∈ smallerBoundary (k := k) i ↔ ∃ a : Fin s,a ≠ i ∧ v = .inl a := by
  simp only [smallerBoundary,mem_erase,BookDimension.boundary,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨hne,a,rfl⟩
    exact ⟨a,fun h => hne (congrArg Sum.inl h),rfl⟩
  · rintro ⟨a,hai,rfl⟩
    exact ⟨fun h => hai (Sum.inl_injective h),a,rfl⟩

theorem no_outer_adj {H : SimpleGraph (Vertex s k)} (hH : H ≤ cliqueBook s k)
    (i j : Fin k) : ¬H.Adj (.inr i) (.inr j) := by
  intro h
  have hh := hH h
  simpa only [cliqueBook,Sum.isLeft_inr,Bool.false_eq_true,or_self,and_false] using hh

def hubPartition {H : SimpleGraph (Vertex s k)} (hH : H ≤ cliqueBook s k) (i : Fin s) :
    Separator.Partition H (smallerBoundary i) (hubPrivate H i) where
  boundary_disjoint j := by
    apply disjoint_left.mpr
    intro v hv hp
    obtain ⟨a,hai,rfl⟩ := (mem_smallerBoundary i v).mp hv
    cases j with
    | none =>
      simp only [hubPrivate,mem_insert,mem_image] at hp
      rcases hp with he | ⟨j,hj,he⟩
      · exact hai (Sum.inl_injective he)
      · exact Sum.inr_ne_inl he
    | some j => exact Sum.inl_ne_inr (mem_singleton.mp hp)
  private_disjoint := by
    intro j l hjl
    apply disjoint_left.mpr
    intro v hvj hvl
    cases j with
    | none =>
      cases l with
      | none => exact hjl rfl
      | some l =>
        have hv : v = Sum.inr l.1 := mem_singleton.mp hvl
        subst v
        simp only [hubPrivate,mem_insert,Sum.inr.injEq,Sum.inr_ne_inl,mem_image,false_or] at hvj
        obtain ⟨a,ha,he⟩ := hvj
        subst a
        exact l.2 ((mem_outerNeighbors _ _ _).mp ha)
    | some j =>
      cases l with
      | none =>
        have hv : v = Sum.inr j.1 := mem_singleton.mp hvj
        subst v
        simp only [hubPrivate,mem_insert,Sum.inr.injEq,Sum.inr_ne_inl,mem_image,false_or] at hvl
        obtain ⟨a,ha,he⟩ := hvl
        subst a
        exact j.2 ((mem_outerNeighbors _ _ _).mp ha)
      | some l =>
        have he : j.1 = l.1 := Sum.inr_injective ((mem_singleton.mp hvj).symm.trans (mem_singleton.mp hvl))
        exact hjl (congrArg Option.some (Subtype.ext he))
  cover v := by
    cases v with
    | inl a =>
      by_cases hai : a = i
      · subst a
        exact Or.inr ⟨none,mem_insert_self _ _⟩
      · exact Or.inl ((mem_smallerBoundary _ _).mpr ⟨a,hai,rfl⟩)
    | inr j =>
      by_cases hadj : H.Adj (.inl i) (.inr j)
      · exact Or.inr ⟨none,mem_insert_of_mem (mem_image.mpr ⟨j,(mem_outerNeighbors _ _ _).mpr hadj,rfl⟩)⟩
      · exact Or.inr ⟨some ⟨j,hadj⟩,mem_singleton_self _⟩
  no_cross_edge := by
    intro j l u v hu hv hadj
    cases j with
    | none =>
      cases l with
      | none => rfl
      | some l =>
        have hv' : v = Sum.inr l.1 := mem_singleton.mp hv
        subst v
        rcases mem_insert.mp hu with rfl | hu
        · exact False.elim (l.2 hadj)
        · obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
          exact False.elim (no_outer_adj hH _ _ hadj)
    | some j =>
      have hu' : u = Sum.inr j.1 := mem_singleton.mp hu
      subst u
      cases l with
      | none =>
        rcases mem_insert.mp hv with rfl | hv
        · exact False.elim (j.2 (H.adj_symm hadj))
        · obtain ⟨a,ha,rfl⟩ := mem_image.mp hv
          exact False.elim (no_outer_adj hH _ _ hadj)
      | some l =>
        have hv' : v = Sum.inr l.1 := mem_singleton.mp hv
        subst v
        exact False.elim (no_outer_adj hH _ _ hadj)

/-- Deleting all other hubs counts each outer nonneighbor separately,
plus the component containing the selected hub. -/
theorem outer_neighbors_lower (hs : 3 ≤ s)
    {H : SimpleGraph (Vertex s (cliqueCapacity s))}
    (hH : H ≤ cliqueBook s (cliqueCapacity s))
    (z : graphicalFunctionSpace H) (hz : ExtremeSupermodular z.1)
    (hd : FullDimension (basePolytope z.1)) (i : Fin s) :
    saturatedHubNeighbors s ≤ (outerNeighbors H i).card := by
  have hcl := hubs_clique hs hH z hz hd
  have hsm : H.IsClique (smallerBoundary (k := cliqueCapacity s) i) :=
    fun u hu v hv huv => hcl (mem_of_mem_erase hu) (mem_of_mem_erase hv) huv
  have hb := Separator.full_partition_clique_capacity
    (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
    (hubPartition hH i) (hubPrivate_nonempty H i) hsm z hz hd
  have hcard : (smallerBoundary (k := cliqueCapacity s) i).card = s-1 := by
    rw [smallerBoundary,card_erase_of_mem,BookDimension.boundary_card]
    exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  rw [hcard,Fintype.card_option,Fintype.card_subtype] at hb
  have hp := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin (cliqueCapacity s))))
    (p := fun j => H.Adj (.inl i) (.inr j))
  simp only [card_univ,Fintype.card_fin] at hp
  change (outerNeighbors H i).card + (outerNonneighbors H i).card = cliqueCapacity s at hp
  change (outerNonneighbors H i).card + 1 ≤ cliqueCapacity (s-1) at hb
  have hmono := BooleanModule.cliqueCapacity_pred_le (show 1 ≤ s by omega)
  unfold saturatedHubNeighbors
  rw [if_neg (by omega : s ≠ 2)]
  omega

/-- A full-dimensional indecomposable deformation on three coordinates has
all three directions.  A missing pair would give two nonzero private blocks
over a singleton boundary, whose separator capacity is only one. -/
theorem three_vertex_complete {V : Type*} [Fintype V] [LinearOrder V]
    (hV : Fintype.card V = 3) (H : SimpleGraph V)
    (z : graphicalFunctionSpace H) (hz : ExtremeSupermodular z.1)
    (hd : FullDimension (basePolytope z.1)) : H = ⊤ := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro h
    exact (SimpleGraph.top_adj _ _).mpr h.ne
  · intro htop
    have huv : u ≠ v := (SimpleGraph.top_adj _ _).mp htop
    by_contra hnon
    let B : Finset V := (univ.erase u).erase v
    let A : Fin 2 → Finset V := fun j => if j = 0 then {u} else {v}
    have hA : ∀ j,(A j).Nonempty := by
      intro j
      fin_cases j <;> simp [A]
    have hp : Separator.Partition H B A := {
      boundary_disjoint := by
        intro j
        fin_cases j <;> simp [A,B,disjoint_singleton_left,disjoint_singleton_right]
      private_disjoint := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [A,disjoint_singleton,ne_comm]
      cover := by
        intro w
        by_cases hwu : w = u
        · subst w
          exact Or.inr ⟨0,by simp [A]⟩
        by_cases hwv : w = v
        · subst w
          exact Or.inr ⟨1,by simp [A]⟩
        exact Or.inl (by simp [B,hwu,hwv])
      no_cross_edge := by
        intro i j a b ha hb hab
        fin_cases i <;> fin_cases j
        · rfl
        · have ha' : a = u := by simpa [A] using ha
          have hb' : b = v := by simpa [A] using hb
          exact False.elim (hnon (ha' ▸ hb' ▸ hab))
        · have ha' : a = v := by simpa [A] using ha
          have hb' : b = u := by simpa [A] using hb
          exact False.elim (hnon (H.adj_symm (ha' ▸ hb' ▸ hab)))
        · rfl }
    have hBcard : B.card = 1 := by
      dsimp only [B]
      rw [card_erase_of_mem (by simp [Ne.symm huv]),
        card_erase_of_mem (mem_univ u),card_univ,hV]
    have hB : H.IsClique B :=
      SimpleGraph.IsClique.of_subsingleton (Finset.card_le_one.mp hBcard.le)
    have hbound := Separator.full_partition_clique_capacity
      (by omega : 2 ≤ Fintype.card V) hp hA hB z hz hd
    rw [hBcard] at hbound
    norm_num [cliqueCapacity,Nat.choose] at hbound

end GraphicalZonotopes.SaturatedDirections

end
end
end BundlePart312

section BundlePart313
/- Source: Papers/GraphicalZonotopes/BookEdgeCounting.lean -/






/-! # Actual edge counts for every subgraph of a clique book -/

@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BookEdges
open Finset
open scoped BigOperators
variable {s k : ℕ}

abbrev Vertex (s k : ℕ) := Fin s ⊕ Fin k

def outerNeighbors (G : SimpleGraph (Vertex s k)) (i : Fin s) : Finset (Fin k) := by
  classical
  exact univ.filter (fun j => G.Adj (Sum.inl i) (Sum.inr j))

@[simp] theorem mem_outerNeighbors (G : SimpleGraph (Vertex s k)) (i : Fin s) (j : Fin k) :
    j∈outerNeighbors G i ↔ G.Adj (Sum.inl i) (Sum.inr j) := by
  classical
  simp [outerNeighbors]

private theorem degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v=∑ w : V,if G.Adj v w then 1 else 0 := by
  classical
  have he : G.neighborFinset v=univ.filter (G.Adj v) := by ext w; simp
  rw [←SimpleGraph.card_neighborFinset_eq_degree,he,Finset.card_eq_sum_ones,Finset.sum_filter]

/-- Exact edge decomposition into all hub pairs and actual private spokes.
It applies to every subgraph, with no extremality or lattice assumption. -/
theorem edge_count (G : SimpleGraph (Vertex s k))
    (hsub : G≤ cliqueBook s k)
    (hhub : ∀ i j : Fin s,i≠ j → G.Adj (Sum.inl i) (Sum.inl j)) :
    (edgeFamily G).card=s.choose 2+∑ i : Fin s,(outerNeighbors G i).card := by
  classical
  have hleft (i j : Fin s) : G.Adj (Sum.inl i) (Sum.inl j) ↔ i≠ j := by
    constructor
    · intro h he
      exact h.ne (congrArg Sum.inl he)
    · exact hhub i j
  have hright (i j : Fin k) : ¬G.Adj (Sum.inr i) (Sum.inr j) := by
    intro h
    have hh := hsub h
    simpa only [cliqueBook,Sum.isLeft_inr,Bool.false_eq_true,or_self,and_false] using hh
  have hspokes (i : Fin s) : (outerNeighbors G i).card=
      ∑ j : Fin k,if G.Adj (Sum.inl i) (Sum.inr j) then 1 else 0 := by
    rw [outerNeighbors,Finset.card_eq_sum_ones,Finset.sum_filter]
  have htop := (⊤ : SimpleGraph (Fin s)).sum_degrees_eq_twice_card_edges
  simp only [degree_sum,SimpleGraph.top_adj,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin] at htop
  have hall := G.sum_degrees_eq_twice_card_edges
  simp only [degree_sum,Fintype.sum_sum_type,hleft,hright,if_false,sum_const_zero,
    add_zero,Finset.sum_add_distrib] at hall
  have htranspose : (∑ j : Fin k,∑ i : Fin s,if G.Adj (Sum.inr j) (Sum.inl i) then 1 else 0)=
      ∑ i : Fin s,∑ j : Fin k,if G.Adj (Sum.inl i) (Sum.inr j) then 1 else 0 := by
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [G.adj_comm]
  rw [htranspose,htop] at hall
  have he : (edgeFamily G).card=G.edgeFinset.card := by
    rw [edgeFamily_eq_image_edgeFinset,card_image_of_injective _ sym2_toFinset_injective]
  rw [he]
  simp only [hspokes]
  omega

/-- A uniform lower bound at each hub gives the paper's direction bound. -/
theorem edge_count_lower (G : SimpleGraph (Vertex s k)) (hsub : G≤ cliqueBook s k)
    (hhub : ∀ i j : Fin s,i≠ j → G.Adj (Sum.inl i) (Sum.inl j))
    (u : ℕ) (hdegree : ∀ i : Fin s,u≤(outerNeighbors G i).card) :
    s.choose 2+s*u≤(edgeFamily G).card := by
  rw [edge_count G hsub hhub]
  apply Nat.add_le_add_left
  have h : (∑ _i : Fin s,u) ≤ ∑ i : Fin s,(outerNeighbors G i).card :=
    sum_le_sum (fun i _ => hdegree i)
  simpa only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] using h

/-- Exact uniform spoke counts give equality, without an extra graphical
assumption hidden in the numerical statement. -/
theorem edge_count_eq (G : SimpleGraph (Vertex s k)) (hsub : G≤ cliqueBook s k)
    (hhub : ∀ i j : Fin s,i≠ j → G.Adj (Sum.inl i) (Sum.inl j))
    (u : ℕ) (hdegree : ∀ i : Fin s,(outerNeighbors G i).card=u) :
    (edgeFamily G).card=s.choose 2+s*u := by
  rw [edge_count G hsub hhub]
  simp only [hdegree,sum_const,card_univ,Fintype.card_fin,smul_eq_mul]

end GraphicalZonotopes.BookEdges

end
end
end BundlePart313
