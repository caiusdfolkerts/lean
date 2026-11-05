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

public import verified.parts.part018
import all verified.parts.part018

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart268
/- Source: Papers/GraphicalZonotopes/PathSlacks.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators

/-- A window bound proved directly in natural arithmetic, without an inline
reflection proof in a dependent finite-index expression. -/
theorem window_index_bound {n p k : ℕ} (i : Fin (n-p)) (hk : k ≤ p) :
    i.val+k< n :=
  (Nat.add_le_add_left hk i.val).trans_lt (Nat.lt_sub_iff_add_lt.mp i.isLt)

theorem eq_vertex_iff_integer {n i a : ℕ} (h : i+a< n) (u : Fin n) :
    u = vertex n i a h ↔ (u.val : ℤ) = (i : ℤ)+a := by
  constructor
  · rintro rfl
    simp [vertex]
  · intro he
    apply Fin.ext
    dsimp [vertex]
    exact_mod_cast he

theorem membershipBit_vertex {n i a : ℕ} (h : i+a< n) (S : Finset (Fin n)) :
    membershipBit S (vertex n i a h) = integerBit S ((i : ℤ)+a) := by
  rw [← integerBit_cast]
  simp [vertex]

theorem sum_window_pair_single {n p a b c : ℕ}
    (ha : a ≤ p) (hb : b ≤ p) (hc : c ≤ p)
    (u v : Fin n) (S : Finset (Fin n))
    (hsupport : (v.val : ℤ) = u.val + ((b : ℤ)-a) →
      integerBit S ((u.val : ℤ)-a+c) ≠ 0 →
      0 ≤ (u.val : ℤ)-a ∧ (u.val : ℤ)-a < ((n-p : ℕ) : ℤ)) :
    (∑ i : Fin (n-p),
      if u = vertex n i.val a (by omega) ∧ v = vertex n i.val b (by omega)
      then membershipBit S (vertex n i.val c (by omega)) else 0) =
      if (v.val : ℤ) = u.val + ((b : ℤ)-a)
      then integerBit S ((u.val : ℤ)-a+c) else 0 := by
  simp_rw [eq_vertex_iff_integer, membershipBit_vertex]
  exact sum_pair_start (n-p) a b u.val v.val (fun j => integerBit S (j+c)) hsupport

theorem sum_window_pair_double {n p a b c d : ℕ}
    (ha : a ≤ p) (hb : b ≤ p) (hc : c ≤ p) (hd : d ≤ p)
    (u v : Fin n) (S : Finset (Fin n))
    (hsupport : (v.val : ℤ) = u.val + ((b : ℤ)-a) →
      integerBit S ((u.val : ℤ)-a+c) * integerBit S ((u.val : ℤ)-a+d) ≠ 0 →
      0 ≤ (u.val : ℤ)-a ∧ (u.val : ℤ)-a < ((n-p : ℕ) : ℤ)) :
    (∑ i : Fin (n-p),
      if u = vertex n i.val a (by omega) ∧ v = vertex n i.val b (by omega)
      then membershipBit S (vertex n i.val c (by omega)) *
        membershipBit S (vertex n i.val d (by omega)) else 0) =
      if (v.val : ℤ) = u.val + ((b : ℤ)-a)
      then integerBit S ((u.val : ℤ)-a+c) * integerBit S ((u.val : ℤ)-a+d) else 0 := by
  simp_rw [eq_vertex_iff_integer, membershipBit_vertex]
  exact sum_pair_start (n-p) a b u.val v.val
    (fun j => integerBit S (j+c) * integerBit S (j+d)) hsupport

/-- The complete contribution of all consecutive triples, including those
adjacent to the two ends of the finite path. -/
theorem delta_consecutive_triples {n : ℕ} {u v : Fin n} {S : Finset (Fin n)}
    (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (∑ i : Fin (n-2), setMonomial (window n i.val {0,1,2})) u v S =
      (if (v.val : ℤ) = u.val+1 then integerBit S (u.val+2) else 0) +
      (if (v.val : ℤ) = u.val+2 then integerBit S (u.val+1) else 0) +
      (if (v.val : ℤ) = u.val+1 then integerBit S ((u.val : ℤ)-1) else 0) := by
  rw [delta_sum]
  have hrow (i : Fin (n-2)) :
      delta (setMonomial (window n i.val {0,1,2})) u v S =
        (if u = vertex n i.val 0 (window_index_bound (n := n) (p := 2) i (by decide)) ∧ v = vertex n i.val 1 (window_index_bound (n := n) (p := 2) i (by decide))
          then membershipBit S (vertex n i.val 2 (window_index_bound (n := n) (p := 2) i (by decide))) else 0) +
        (if u = vertex n i.val 0 (window_index_bound (n := n) (p := 2) i (by decide)) ∧ v = vertex n i.val 2 (window_index_bound (n := n) (p := 2) i (by decide))
          then membershipBit S (vertex n i.val 1 (window_index_bound (n := n) (p := 2) i (by decide))) else 0) +
        (if u = vertex n i.val 1 (window_index_bound (n := n) (p := 2) i (by decide)) ∧ v = vertex n i.val 2 (window_index_bound (n := n) (p := 2) i (by decide))
          then membershipBit S (vertex n i.val 0 (window_index_bound (n := n) (p := 2) i (by decide))) else 0) := by
    rw [window_triple_eq (window_index_bound (n := n) (p := 2) i (by decide))
      (window_index_bound (n := n) (p := 2) i (by decide)) (window_index_bound (n := n) (p := 2) i (by decide))]
    exact delta_monomial_three (by change (i.val + 0 : ℕ) < (i.val + 1 : ℕ); omega)
      (by change (i.val + 1 : ℕ) < (i.val + 2 : ℕ); omega) huv hu hv
  simp_rw [hrow]
  rw [sum_add_distrib, sum_add_distrib]
  rw [sum_window_pair_single (by decide : 0 ≤ 2) (by decide : 1 ≤ 2) (by decide : 2 ≤ 2) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_single (by decide : 0 ≤ 2) (by decide : 2 ≤ 2) (by decide : 1 ≤ 2) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_single (by decide : 1 ≤ 2) (by decide : 2 ≤ 2) (by decide : 0 ≤ 2) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  norm_num

/-- The complete contribution of all `023` triples. -/
theorem delta_skipped_triples {n : ℕ} {u v : Fin n} {S : Finset (Fin n)}
    (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (∑ i : Fin (n-3), setMonomial (window n i.val {0,2,3})) u v S =
      (if (v.val : ℤ) = u.val+2 then integerBit S (u.val+3) else 0) +
      (if (v.val : ℤ) = u.val+3 then integerBit S (u.val+2) else 0) +
      (if (v.val : ℤ) = u.val+1 then integerBit S ((u.val : ℤ)-2) else 0) := by
  rw [delta_sum]
  have hrow (i : Fin (n-3)) :
      delta (setMonomial (window n i.val {0,2,3})) u v S =
        (if u = vertex n i.val 0 (window_index_bound (n := n) (p := 3) i (by decide)) ∧ v = vertex n i.val 2 (window_index_bound (n := n) (p := 3) i (by decide))
          then membershipBit S (vertex n i.val 3 (window_index_bound (n := n) (p := 3) i (by decide))) else 0) +
        (if u = vertex n i.val 0 (window_index_bound (n := n) (p := 3) i (by decide)) ∧ v = vertex n i.val 3 (window_index_bound (n := n) (p := 3) i (by decide))
          then membershipBit S (vertex n i.val 2 (window_index_bound (n := n) (p := 3) i (by decide))) else 0) +
        (if u = vertex n i.val 2 (window_index_bound (n := n) (p := 3) i (by decide)) ∧ v = vertex n i.val 3 (window_index_bound (n := n) (p := 3) i (by decide))
          then membershipBit S (vertex n i.val 0 (window_index_bound (n := n) (p := 3) i (by decide))) else 0) := by
    rw [window_triple_eq (window_index_bound (n := n) (p := 3) i (by decide))
      (window_index_bound (n := n) (p := 3) i (by decide)) (window_index_bound (n := n) (p := 3) i (by decide))]
    exact delta_monomial_three (by change (i.val + 0 : ℕ) < (i.val + 2 : ℕ); omega)
      (by change (i.val + 2 : ℕ) < (i.val + 3 : ℕ); omega) huv hu hv
  simp_rw [hrow]
  rw [sum_add_distrib, sum_add_distrib]
  rw [sum_window_pair_single (by decide : 0 ≤ 3) (by decide : 2 ≤ 3) (by decide : 3 ≤ 3) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_single (by decide : 0 ≤ 3) (by decide : 3 ≤ 3) (by decide : 2 ≤ 3) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_single (by decide : 2 ≤ 3) (by decide : 3 ≤ 3) (by decide : 0 ≤ 3) u v S (by
    intro hdist hr
    have hb := integerBit_bounds_of_ne_zero hr
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  norm_num

/-- All six pair contributions of the four-vertex windows. -/
theorem delta_tetrahedra {n : ℕ} {u v : Fin n} {S : Finset (Fin n)}
    (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (∑ i : Fin (n-3), setMonomial (window n i.val {0,1,2,3})) u v S =
      (if (v.val : ℤ) = u.val+1 then integerBit S (u.val+2) * integerBit S (u.val+3) else 0) +
      (if (v.val : ℤ) = u.val+2 then integerBit S (u.val+1) * integerBit S (u.val+3) else 0) +
      (if (v.val : ℤ) = u.val+3 then integerBit S (u.val+1) * integerBit S (u.val+2) else 0) +
      (if (v.val : ℤ) = u.val+1 then integerBit S ((u.val : ℤ)-1) * integerBit S (u.val+2) else 0) +
      (if (v.val : ℤ) = u.val+2 then integerBit S ((u.val : ℤ)-1) * integerBit S (u.val+1) else 0) +
      (if (v.val : ℤ) = u.val+1 then integerBit S ((u.val : ℤ)-2) * integerBit S ((u.val : ℤ)-1) else 0) := by
  rw [delta_sum]
  have hrow (i : Fin (n-3)) := delta_monomial_four
    (a := vertex n i.val 0 (window_index_bound (n := n) (p := 3) i (by decide))) (b := vertex n i.val 1 (window_index_bound (n := n) (p := 3) i (by decide)))
    (c := vertex n i.val 2 (window_index_bound (n := n) (p := 3) i (by decide))) (d := vertex n i.val 3 (window_index_bound (n := n) (p := 3) i (by decide)))
    (by change (i.val + 0 : ℕ) < (i.val + 1 : ℕ); omega) (by change (i.val + 1 : ℕ) < (i.val + 2 : ℕ); omega)
    (by change (i.val + 2 : ℕ) < (i.val + 3 : ℕ); omega) huv hu hv
  have hw (i : Fin (n-3)) : window n i.val {0,1,2,3} =
      {vertex n i.val 0 (window_index_bound (n := n) (p := 3) i (by decide)), vertex n i.val 1 (window_index_bound (n := n) (p := 3) i (by decide)),
       vertex n i.val 2 (window_index_bound (n := n) (p := 3) i (by decide)), vertex n i.val 3 (window_index_bound (n := n) (p := 3) i (by decide))} :=
    window_quad_eq (window_index_bound (n := n) (p := 3) i (by decide))
      (window_index_bound (n := n) (p := 3) i (by decide)) (window_index_bound (n := n) (p := 3) i (by decide))
      (window_index_bound (n := n) (p := 3) i (by decide))
  simp_rw [hw, hrow]
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  rw [sum_window_pair_double (by decide : 0 ≤ 3) (by decide : 1 ≤ 3)
    (by decide : 2 ≤ 3) (by decide : 3 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_double (by decide : 0 ≤ 3) (by decide : 2 ≤ 3)
    (by decide : 1 ≤ 3) (by decide : 3 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_double (by decide : 0 ≤ 3) (by decide : 3 ≤ 3)
    (by decide : 1 ≤ 3) (by decide : 2 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_double (by decide : 1 ≤ 3) (by decide : 2 ≤ 3)
    (by decide : 0 ≤ 3) (by decide : 3 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_double (by decide : 1 ≤ 3) (by decide : 3 ≤ 3)
    (by decide : 0 ≤ 3) (by decide : 2 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  rw [sum_window_pair_double (by decide : 2 ≤ 3) (by decide : 3 ≤ 3)
    (by decide : 0 ≤ 3) (by decide : 1 ≤ 3) u v S (by
    intro hdist hr
    obtain ⟨h1,h2⟩ := mul_ne_zero_iff.mp hr
    have hb1 := integerBit_bounds_of_ne_zero h1
    have hb2 := integerBit_bounds_of_ne_zero h2
    have hu' := u.isLt
    have hv' := v.isLt
    omega)]
  have h13 : (u.val : ℤ)-1+3=u.val+2 := by omega
  have h12 : (u.val : ℤ)-1+2=u.val+1 := by omega
  have h21 : (u.val : ℤ)-2+1=(u.val : ℤ)-1 := by omega
  norm_num [h13,h12,h21]

/-- Exact arbitrary-length slack formula, with no omitted endpoint cases. -/
theorem delta_formula {n : ℕ} {u v : Fin n} {S : Finset (Fin n)}
    (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (setFunction n) u v S =
      if (v.val : ℤ) = u.val+1 then
        integerBit S ((u.val : ℤ)-2) * (1-integerBit S ((u.val : ℤ)-1)) +
        integerBit S ((u.val : ℤ)-1) * (1-integerBit S (u.val+2)) +
        integerBit S (u.val+2) * (1-integerBit S (u.val+3))
      else if (v.val : ℤ) = u.val+2 then
        integerBit S (u.val+1) * (1-integerBit S ((u.val : ℤ)-1)) +
        integerBit S (u.val+3) * (1-integerBit S (u.val+1))
      else if (v.val : ℤ) = u.val+3 then
        integerBit S (u.val+2) * (1-integerBit S (u.val+1))
      else 0 := by
  rw [setFunction_expansion, delta_sub, delta_add,
    delta_consecutive_triples huv hu hv, delta_skipped_triples huv hu hv,
    delta_tetrahedra huv hu hv]
  by_cases h1 : (v.val : ℤ) = u.val+1
  · have h2 : ¬(v.val : ℤ) = u.val+2 := by omega
    have h3 : ¬(v.val : ℤ) = u.val+3 := by omega
    simp only [if_pos h1, if_neg h2, if_neg h3]
    ring
  · by_cases h2 : (v.val : ℤ) = u.val+2
    · have h3 : ¬(v.val : ℤ) = u.val+3 := by omega
      simp only [if_neg h1, if_pos h2, if_neg h3]
      ring
    · by_cases h3 : (v.val : ℤ) = u.val+3
      · simp only [if_neg h1, if_neg h2, if_pos h3]
        ring
      · simp [h1,h2,h3]

theorem delta_symm {V : Type*} [Fintype V] [DecidableEq V]
    (f : SetFunction V) (u v : V) (S : Finset V) : delta f u v S = delta f v u S := by
  unfold delta
  rw [insert_comm]
  ring

theorem slack_bounds {n : ℕ} {u v : Fin n} (huv : u ≠ v) {S : Finset (Fin n)}
    (hu : u ∉ S) (hv : v ∉ S) :
    0 ≤ delta (setFunction n) u v S ∧ delta (setFunction n) u v S ≤ 2 := by
  have hordered : ∀ a b : Fin n, a < b → a ∉ S → b ∉ S →
      0 ≤ delta (setFunction n) a b S ∧ delta (setFunction n) a b S ≤ 2 := by
    intro a b hab ha hb
    rw [delta_formula hab ha hb]
    split
    · exact path_boolean_slack_one (integerBit_zero_or_one _ _) (integerBit_zero_or_one _ _)
        (integerBit_zero_or_one _ _) (integerBit_zero_or_one _ _)
    · split
      · have h := path_boolean_slack_two (integerBit_zero_or_one S ((a.val : ℤ)-1))
          (integerBit_zero_or_one S (a.val+1)) (integerBit_zero_or_one S (a.val+3))
        exact ⟨h.1, h.2.trans (by norm_num)⟩
      · split
        · have h := path_boolean_slack_three (integerBit_zero_or_one S (a.val+1))
            (integerBit_zero_or_one S (a.val+2))
          exact ⟨h.1, h.2.trans (by norm_num)⟩
        · norm_num
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact hordered u v hlt hu hv
  · rw [delta_symm]
    exact hordered v u hgt hv hu

theorem setFunction_supermodular (n : ℕ) : Supermodular (setFunction n) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  exact (slack_bounds huv hu hv).1

end Path
end GraphicalZonotopes

end
end
end BundlePart268

section BundlePart269
/- Source: Papers/GraphicalZonotopes/PathPolytope.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators Pointwise

/-- The paper's actual lower base polytope. -/
def polytope (n : ℕ) : Set (Fin n → ℝ) := basePolytope (setFunction n)

/-- The actual complement at dilation two, with integral lower-support data. -/
def complement (n : ℕ) : Set (Fin n → ℝ) :=
  basePolytope ((2 : ℝ) • graphFunction (graph n) - setFunction n)

/-- The defining affine hyperplane is exactly the paper's total n−2. -/
theorem setFunction_univ (n : ℕ) :
    setFunction n Finset.univ = ((n-2 : ℕ) : ℝ) := by
  rw [setFunction_expansion]
  simp [setMonomial]

/-- Exact set equality with the displayed definition (3.1), using zero-based
labels for the n standard coordinates. -/
theorem polytope_defining_equations (n : ℕ) :
    polytope n = {x : Fin n → ℝ | subsetSum x Finset.univ = ((n-2 : ℕ) : ℝ) ∧
      ∀ S, setFunction n S ≤ subsetSum x S} := by
  unfold polytope basePolytope
  rw [setFunction_univ]

theorem setFunction_ne_zero {n : ℕ} (hn : 4 ≤ n) : setFunction n ≠ 0 := by
  intro he
  have hz : coefficients n = 0 := (zeta_eq_zero_iff _).mp he
  have hc := congrFun (congrArg Coordinates.tri012 (coordinates_coefficients n))
    (⟨0, by omega⟩ : Fin (n-2))
  change coefficients n _ = 1 at hc
  rw [hz] at hc
  norm_num at hc

theorem setFunction_extreme {n : ℕ} (hn : 4 ≤ n) :
    ExtremeSupermodular (setFunction n) :=
  extremeSupermodular_of_tightEquations (setFunction_normalized n)
    (setFunction_supermodular n) (setFunction_ne_zero hn) (complete_tight_kernel hn)

theorem polytope_indecomposable {n : ℕ} (hn : 4 ≤ n) :
    MinkowskiIndecomposable (polytope n) :=
  (setFunction_extreme hn).minkowskiIndecomposable

theorem setFunction_integerValued (n : ℕ) : IntegerValued (setFunction n) := by
  rw [setFunction_expansion]
  apply IntegerValued.sub
  · apply IntegerValued.add
    · exact IntegerValued.finset_sum _ _ (fun _ _ => setMonomial_integerValued _)
    · exact IntegerValued.finset_sum _ _ (fun _ _ => setMonomial_integerValued _)
  · exact IntegerValued.finset_sum _ _ (fun _ _ => setMonomial_integerValued _)

theorem polytope_lattice (n : ℕ) : LatticePolytope (polytope n) :=
  (setFunction_integerValued n).basePolytope (setFunction_normalized n).1
    (setFunction_supermodular n)

theorem complement_normalized (n : ℕ) :
    Normalized ((2 : ℝ) • graphFunction (graph n) - setFunction n) := by
  change 2 * graphFunction (graph n) ∅ - setFunction n ∅ = 0
  rw [graphFunction_normalized, (setFunction_normalized n).1]
  ring

theorem complement_supermodular (n : ℕ) :
    Supermodular ((2 : ℝ) • graphFunction (graph n) - setFunction n) :=
  graphical_complement_supermodular (setFunction_graphical n) (by norm_num)
    (fun u v huv _ S hu hv => (slack_bounds huv hu hv).2)

theorem complement_lattice (n : ℕ) : LatticePolytope (complement n) := by
  have hZ := (graphFunction_integerValued (graph n)).int_smul 2
  have hz : IntegerValued ((2 : ℝ) • graphFunction (graph n)-setFunction n) := by
    simpa using hZ.sub (setFunction_integerValued n)
  exact hz.basePolytope (complement_normalized n) (complement_supermodular n)

/-- The claimed dilation is an equality of genuine sets under Minkowski
addition; it is stronger than membership in a formally defined deformation cone. -/
theorem polytope_add_complement (n : ℕ) :
    polytope n + complement n = (2 : ℝ) • graphicalZonotope (graph n) :=
  basePolytope_add_graphical_complement (setFunction_normalized n).1
    (setFunction_supermodular n) (setFunction_graphical n) (by norm_num)
    (fun u v huv _ S hu hv => (slack_bounds huv hu hv).2)

theorem polytope_compact (n : ℕ) : IsCompact (polytope n) :=
  basePolytope_compact (setFunction_normalized n).1 (setFunction_supermodular n)

theorem polytope_nonempty (n : ℕ) : (polytope n).Nonempty :=
  basePolytope_nonempty (setFunction_normalized n).1 (setFunction_supermodular n)

theorem complement_compact (n : ℕ) : IsCompact (complement n) :=
  basePolytope_compact (complement_normalized n) (complement_supermodular n)

end Path
end GraphicalZonotopes

end
end
end BundlePart269

section BundlePart270
/- Source: Papers/GraphicalZonotopes/PathDimension.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators Pointwise

@[simp] theorem integerBit_singleton {n : ℕ} (v : Fin n) (k : ℤ) :
    integerBit {v} k = if (v.val : ℤ) = k then 1 else 0 := by
  simp [integerBit]

/-- Each consecutive path edge has a positive slack, including the final edge. -/
theorem consecutive_positive_slack {n : ℕ} (hn : 4 ≤ n) (i : Fin (n-1)) :
    ∃ S : Finset (Fin n),
      (⟨i.val, by omega⟩ : Fin n) ∉ S ∧ (⟨i.val+1, by omega⟩ : Fin n) ∉ S ∧
      delta (setFunction n) ⟨i.val, by omega⟩ ⟨i.val+1, by omega⟩ S = 1 := by
  let u : Fin n := ⟨i.val, by omega⟩
  let v : Fin n := ⟨i.val+1, by omega⟩
  have huv : u < v := by
    change (i.val : ℕ) < i.val + 1
    omega
  by_cases hlast : i.val+2< n
  · let w : Fin n := ⟨i.val+2,hlast⟩
    have hu : u ∉ ({w} : Finset (Fin n)) := by simp [u,w,Fin.ext_iff]
    have hv : v ∉ ({w} : Finset (Fin n)) := by simp [v,w,Fin.ext_iff]
    refine ⟨{w},hu,hv,?_⟩
    rw [delta_formula huv hu hv]
    have hd : (v.val : ℤ) = u.val+1 := by simp [u,v]
    rw [if_pos hd]
    have ha : integerBit {w} ((u.val : ℤ)-2) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    have hb : integerBit {w} ((u.val : ℤ)-1) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    have hc : integerBit {w} (u.val+2) = 1 := by simp [u,w]
    have hd : integerBit {w} (u.val+3) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    rw [ha,hb,hc,hd]
    norm_num
  · have hi2 : 2 ≤ i.val := by omega
    let w : Fin n := ⟨i.val-2,by omega⟩
    have hu : u ∉ ({w} : Finset (Fin n)) := by
      simp only [mem_singleton, Fin.ext_iff]
      dsimp [u,w]
      omega
    have hv : v ∉ ({w} : Finset (Fin n)) := by
      simp only [mem_singleton, Fin.ext_iff]
      dsimp [v,w]
      omega
    refine ⟨{w},hu,hv,?_⟩
    rw [delta_formula huv hu hv]
    have hd : (v.val : ℤ) = u.val+1 := by simp [u,v]
    rw [if_pos hd]
    have ha : integerBit {w} ((u.val : ℤ)-2) = 1 := by
      rw [integerBit_singleton, if_pos]
      dsimp [u,w]
      omega
    have hb : integerBit {w} ((u.val : ℤ)-1) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    have hc : integerBit {w} (u.val+2) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    have hd : integerBit {w} (u.val+3) = 0 := by
      rw [integerBit_singleton, if_neg]
      dsimp [u,w]
      omega
    rw [ha,hb,hc,hd]
    norm_num

/-- Full affine dimension is proved in the ambient standard coordinate space. -/
theorem polytope_dimension {n : ℕ} (hn : 4 ≤ n) :
    Module.finrank ℝ (vectorSpan ℝ (polytope n)) = n-1 := by
  apply finrank_vectorSpan_eq_of_consecutive_roots (by omega) (polytope_nonempty n)
  intro i
  obtain ⟨S,hu,hv,hδ⟩ := consecutive_positive_slack hn i
  exact root_mem_vectorSpan_of_delta_ne_zero (setFunction_normalized n).1
    (setFunction_supermodular n) (by simp [Fin.ext_iff]) hu hv (by rw [hδ]; norm_num)

end Path
end GraphicalZonotopes

end
end
end BundlePart270

section BundlePart271
/- Source: Papers/GraphicalZonotopes/PathEdges.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset

theorem delta_swap {V : Type*} [Fintype V] [DecidableEq V]
    (f : SetFunction V) (u v : V) (S : Finset V) :
    delta f u v S = delta f v u S := by
  unfold delta
  rw [insert_comm u v]
  ring

/-- All three permitted edge lengths have a positive slack, including the
boundary positions of the path. -/
theorem edge_positive_slack {n : ℕ} (hn : 4 ≤ n) {u v : Fin n}
    (hadj : (graph n).Adj u v) :
    ∃ S : Finset (Fin n), u ∉ S ∧ v ∉ S ∧ delta (setFunction n) u v S = 1 := by
  suffices h : ∀ (u v : Fin n), u < v → v.val ≤ u.val+3 →
      ∃ S : Finset (Fin n), u ∉ S ∧ v ∉ S ∧ delta (setFunction n) u v S = 1 by
    rcases lt_or_gt_of_ne hadj.1 with huv | hvu
    · exact h u v huv hadj.2.2
    · obtain ⟨S,hv,hu,hδ⟩ := h v u hvu hadj.2.1
      exact ⟨S,hu,hv,(delta_swap _ _ _ _).trans hδ⟩
  intro u v huv hdist
  have hlt : u.val < v.val := huv
  by_cases h1 : v.val = u.val+1
  · have hi : u.val < n-1 := by omega
    obtain ⟨S,hu,hv,hδ⟩ := consecutive_positive_slack hn (⟨u.val,hi⟩ : Fin (n-1))
    have hu' : (⟨u.val, by omega⟩ : Fin n) = u := Fin.ext rfl
    have hv' : (⟨u.val+1, by omega⟩ : Fin n) = v := Fin.ext h1.symm
    refine ⟨S, ?_, ?_, ?_⟩
    · simpa only [hu'] using hu
    · simpa only [hv'] using hv
    · simpa only [hu',hv'] using hδ
  · by_cases h2 : v.val = u.val+2
    · let w : Fin n := ⟨u.val+1,by omega⟩
      have hu : u ∉ ({w} : Finset (Fin n)) := by
        simp only [mem_singleton, Fin.ext_iff]
        dsimp [w]
        omega
      have hv : v ∉ ({w} : Finset (Fin n)) := by
        simp only [mem_singleton, Fin.ext_iff]
        dsimp [w]
        omega
      refine ⟨{w},hu,hv,?_⟩
      rw [delta_formula huv hu hv]
      have h1z : (v.val : ℤ) ≠ (u.val : ℤ)+1 := by omega
      have h2z : (v.val : ℤ) = (u.val : ℤ)+2 := by omega
      rw [if_neg h1z,if_pos h2z]
      have ha : integerBit {w} ((u.val : ℤ)+1) = 1 := by simp [w]
      have hb : integerBit {w} ((u.val : ℤ)-1) = 0 := by
        rw [integerBit_singleton,if_neg]
        dsimp [w]
        omega
      have hc : integerBit {w} ((u.val : ℤ)+3) = 0 := by
        rw [integerBit_singleton,if_neg]
        dsimp [w]
        omega
      rw [ha,hb,hc]
      norm_num
    · have h3 : v.val = u.val+3 := by omega
      let w : Fin n := ⟨u.val+2,by omega⟩
      have hu : u ∉ ({w} : Finset (Fin n)) := by
        simp only [mem_singleton, Fin.ext_iff]
        dsimp [w]
        omega
      have hv : v ∉ ({w} : Finset (Fin n)) := by
        simp only [mem_singleton, Fin.ext_iff]
        dsimp [w]
        omega
      refine ⟨{w},hu,hv,?_⟩
      rw [delta_formula huv hu hv]
      have h1z : (v.val : ℤ) ≠ (u.val : ℤ)+1 := by omega
      have h2z : (v.val : ℤ) ≠ (u.val : ℤ)+2 := by omega
      have h3z : (v.val : ℤ) = (u.val : ℤ)+3 := by omega
      rw [if_neg h1z,if_neg h2z,if_pos h3z]
      have ha : integerBit {w} ((u.val : ℤ)+2) = 1 := by simp [w]
      have hb : integerBit {w} ((u.val : ℤ)+1) = 0 := by
        rw [integerBit_singleton,if_neg]
        dsimp [w]
        omega
      rw [ha,hb]
      norm_num

/-- Every edge of the path cube is realized by a genuine exposed edge of Q_n. -/
theorem graph_edge_is_actual {n : ℕ} (hn : 4 ≤ n) {u v : Fin n}
    (hadj : (graph n).Adj u v) : ActualRootEdge (polytope n) u v := by
  obtain ⟨S,hu,hv,hδ⟩ := edge_positive_slack hn hadj
  exact exposedSegment_of_positive_delta (setFunction_normalized n).1
    (setFunction_supermodular n) hadj.1 hu hv (by rw [hδ]; norm_num)

end Path
end GraphicalZonotopes

end
end
end BundlePart271

section BundlePart272
/- Source: Papers/GraphicalZonotopes/PathActualGraph.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open scoped Pointwise

/-- Exact equality of the actual exposed-edge direction graph with the third
power of the path, in both directions and for every n ≥ 4. -/
theorem actual_direction_graph {n : ℕ} (hn : 4 ≤ n) (u v : Fin n) :
    ActualRootEdge (polytope n) u v ↔ (graph n).Adj u v := by
  constructor
  · exact basePolytope_summand_actualRootEdge (setFunction_normalized n).1
      (setFunction_supermodular n) (graph n) (by norm_num : (0 : ℝ) ≤ 2)
      (complement n) (polytope_add_complement n)
  · exact graph_edge_is_actual hn

/-- In addition, every exposed edge is parallel to one of those roots; the
direction graph does not omit non-root exposed edges. -/
theorem every_exposed_edge_is_graph_direction {n : ℕ} (hn : 4 ≤ n)
    {p q : Fin n → ℝ} (hex : IsExposedSegment (polytope n) p q) :
    ∃ u v, (graph n).Adj u v ∧ ∃ t : ℝ, t ≠ 0 ∧
      q-p = t • (basisVector v-basisVector u) :=
  basePolytope_summand_exposed_edge (setFunction_normalized n).1
    (setFunction_supermodular n) (graph n) (by norm_num : (0 : ℝ) ≤ 2)
    (complement n) (polytope_add_complement n) hex

end Path
end GraphicalZonotopes

end
end
end BundlePart272

section BundlePart273
/- Source: Papers/GraphicalZonotopes/PathPlaneGeometry.lean -/









@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace PathDrawing

abbrev Space := Fin 3 → ℝ

def unit (i : Fin 3) : Space := fun j => if j = i then 1 else 0

def rotate : Space →ₗ[ℝ] Space where
  toFun x i := if i = 0 then x 1-x 0 else if i = 1 then x 2-x 0 else 3*x 0
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

def point : ℕ → Space
  | 0 => unit 0
  | 1 => unit 1
  | 2 => unit 2
  | n+3 => (1/3 : ℝ) • (point n + point (n+1) + point (n+2))
termination_by n => n
decreasing_by all_goals omega

theorem point_step (n : ℕ) :
    point (n+3) = (1/3 : ℝ) • (point n+point (n+1)+point (n+2)) := by
  rw [point]

def frame : ℕ → Space →ₗ[ℝ] Space
  | 0 => LinearMap.id
  | n+1 => rotate ∘ₗ frame n

@[simp] theorem rotate_unit_one : rotate (unit 1) = unit 0 := by
  funext i
  fin_cases i <;> norm_num [rotate,unit]

@[simp] theorem rotate_unit_two : rotate (unit 2) = unit 1 := by
  funext i
  fin_cases i <;> norm_num [rotate,unit]

@[simp] theorem rotate_average :
    rotate ((1/3 : ℝ) • (unit 0+unit 1+unit 2)) = unit 2 := by
  funext i
  fin_cases i <;> norm_num [rotate,unit]

theorem frame_vertices (n : ℕ) :
    frame n (point n) = unit 0 ∧
      frame n (point (n+1)) = unit 1 ∧ frame n (point (n+2)) = unit 2 := by
  induction n with
  | zero => simp [frame,point]
  | succ n ih =>
    constructor
    · change rotate (frame n (point (n+1))) = unit 0
      rw [ih.2.1,rotate_unit_one]
    · constructor
      · change rotate (frame n (point (n+2))) = unit 1
        rw [ih.2.2,rotate_unit_two]
      · change rotate (frame n (point (n+3))) = unit 2
        rw [point_step,map_smul,map_add,map_add,ih.1,ih.2.1,ih.2.2,rotate_average]

@[simp] theorem frame_point_self (n : ℕ) : frame n (point n) = unit 0 :=
  (frame_vertices n).1

@[simp] theorem frame_point_next (n : ℕ) : frame n (point (n+1)) = unit 1 :=
  (frame_vertices n).2.1

@[simp] theorem frame_point_next_two (n : ℕ) : frame n (point (n+2)) = unit 2 :=
  (frame_vertices n).2.2

@[simp] theorem frame_point_next_three (n : ℕ) :
    frame n (point (n+3)) = (1/3 : ℝ) • (unit 0+unit 1+unit 2) := by
  rw [point_step,map_smul,map_add,map_add,frame_point_self,frame_point_next,
    frame_point_next_two]

def tailCone (n : ℕ) : Set Space := {x | ∀ i, 0 ≤ frame n x i}

theorem tailCone_convex (n : ℕ) : Convex ℝ (tailCone n) := by
  intro x hx y hy a b ha hb hab
  intro i
  simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem point_offset_mem (n d : ℕ) : point (n+d) ∈ tailCone n := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d < 3
    · rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
      · simp [tailCone,unit]; intro i; split <;> norm_num
      · simp [tailCone,unit]; intro i; split <;> norm_num
      · simp [tailCone,unit]; intro i; split <;> norm_num
    · have h3 : 3 ≤ d := by omega
      have h0 := ih (d-3) (by omega)
      have h1 := ih (d-2) (by omega)
      have h2 := ih (d-1) (by omega)
      have he : n+d = (n+(d-3))+3 := by omega
      have he1 : n+(d-3)+1 = n+(d-2) := by omega
      have he2 : n+(d-3)+2 = n+(d-1) := by omega
      rw [he,point_step,he1,he2]
      intro i
      simp only [map_smul,map_add,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
      exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (h0 i) (h1 i)) (h2 i))

theorem point_later_mem {n m : ℕ} (h : n ≤ m) : point m ∈ tailCone n := by
  simpa only [Nat.add_sub_of_le h] using point_offset_mem n (m-n)

theorem point_not_nextCone (n : ℕ) : point n ∉ tailCone (n+1) := by
  intro h
  have h0 := h (0 : Fin 3)
  change 0 ≤ rotate (frame n (point n)) 0 at h0
  rw [frame_point_self] at h0
  norm_num [rotate,unit] at h0

theorem point_injective : Function.Injective point := by
  intro n m hnm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := point_later_mem (show n+1 ≤ m by omega)
    rw [← hnm] at h
    exact point_not_nextCone n h
  · have h := point_later_mem (show m+1 ≤ n by omega)
    rw [hnm] at h
    exact point_not_nextCone m h

def total (x : Space) : ℝ := x 0+x 1+x 2

theorem total_rotate (x : Space) : total (rotate x) = total x := by
  simp [total,rotate]
  ring

theorem total_frame (n : ℕ) (x : Space) : total (frame n x) = total x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (total_rotate (frame n x)).trans ih

theorem point_total (n : ℕ) : total (point n) = 1 := by
  have h := congrArg total (frame_point_self n)
  rw [total_frame] at h
  simpa [total,unit] using h

/-- Every edge from the oldest vertex to one of its three successors enters
the next tail cone only at its other endpoint. This is the separation statement
that prevents edges added later from crossing it. -/
theorem segment_meets_tail_at_endpoint {n m : ℕ} (hnm : n < m) (hm : m ≤ n+3)
    {x : Space} (hx : x ∈ segment ℝ (point n) (point m))
    (ht : x ∈ tailCone (n+1)) : x = point m := by
  obtain ⟨a,b,ha,hb,hab,hx⟩ := hx
  have hold : frame (n+1) (point n) = rotate (unit 0) := by
    change rotate (frame n (point n)) = _
    rw [frame_point_self]
  have hcases : m = n+1 ∨ m = n+2 ∨ m = n+3 := by omega
  rcases hcases with hm1 | hm2 | hm3
  · subst m
    have h := ht (1 : Fin 3)
    rw [← hx,map_add,map_smul,map_smul,hold,frame_point_self] at h
    norm_num [rotate,unit,Pi.add_apply,Pi.smul_apply] at h
    have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    simpa [ha0,hb1] using hx.symm
  · subst m
    have h := ht (0 : Fin 3)
    have hnext : frame (n+1) (point (n+2)) = unit 1 := by
      simpa only [Nat.add_assoc] using frame_point_next (n+1)
    rw [← hx,map_add,map_smul,map_smul,hold,hnext] at h
    norm_num [rotate,unit,Pi.add_apply,Pi.smul_apply] at h
    have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    simpa [ha0,hb1] using hx.symm
  · subst m
    have h := ht (0 : Fin 3)
    have hnext : frame (n+1) (point (n+3)) = unit 2 := by
      simpa only [Nat.add_assoc] using frame_point_next_two (n+1)
    rw [← hx,map_add,map_smul,map_smul,hold,hnext] at h
    norm_num [rotate,unit,Pi.add_apply,Pi.smul_apply] at h
    have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    simpa [ha0,hb1] using hx.symm

theorem vertex_not_on_edge {i j k : ℕ} (hij : i < j) (hj : j ≤ i+3)
    (hki : k ≠ i) (hkj : k ≠ j) : point k ∉ segment ℝ (point i) (point j) := by
  intro hmem
  rcases lt_or_gt_of_ne hki with hki' | hik
  · have hi := point_later_mem (show k+1 ≤ i by omega)
    have hj' := point_later_mem (show k+1 ≤ j by omega)
    exact point_not_nextCone k ((tailCone_convex (k+1)).segment_subset hi hj' hmem)
  · have ht := point_later_mem (show i+1 ≤ k by omega)
    exact hkj (point_injective (segment_meets_tail_at_endpoint hij hj hmem ht))

def coordinate (n : ℕ) (i : Fin 3) : Space →ₗ[ℝ] ℝ where
  toFun x := frame n x i
  map_add' x y := by simp
  map_smul' a x := by simp

theorem segment_meet_start_of_linear {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p q r x : E} (l : E →ₗ[ℝ] ℝ) (hp : l p = 0) (hq : l q = 0)
    (hr : l r ≠ 0) (hx : x ∈ segment ℝ p q) (hy : x ∈ segment ℝ p r) : x = p := by
  obtain ⟨a,b,ha,hb,hab,he⟩ := hx
  have hlx : l x = 0 := by
    rw [← he,map_add,map_smul,map_smul,hp,hq]
    simp
  obtain ⟨c,d,hc,hd,hcd,he'⟩ := hy
  have h := congrArg l he'
  simp only [map_add,map_smul,smul_eq_mul,hp,hlx,mul_zero,zero_add] at h
  have hd0 : d = 0 := (mul_eq_zero.mp h).resolve_right hr
  have hc1 : c = 1 := by linarith
  simpa [hd0,hc1] using he'.symm

theorem common_start_ordered {n m l : ℕ} (hnm : n < m) (hml : m < l)
    (hl : l ≤ n+3) {x : Space} (hx : x ∈ segment ℝ (point n) (point m))
    (hy : x ∈ segment ℝ (point n) (point l)) : x = point n := by
  by_cases hm : m = n+1
  · subst m
    apply segment_meet_start_of_linear (coordinate n 2) _ _ _ hx hy
    · simp [coordinate,unit]
    · simp [coordinate,unit]
    · rcases (show l = n+2 ∨ l = n+3 by omega) with rfl | rfl
      · norm_num [coordinate,unit]
      · norm_num [coordinate,unit]
  · have hm2 : m = n+2 := by omega
    have hl3 : l = n+3 := by omega
    subst m
    subst l
    apply segment_meet_start_of_linear (coordinate n 1) _ _ _ hx hy
    · simp [coordinate,unit]
    · simp [coordinate,unit]
    · norm_num [coordinate,unit]

theorem common_start {n m l : ℕ} (hnm : n < m) (hnl : n < l)
    (hm : m ≤ n+3) (hl : l ≤ n+3) (hml : m ≠ l)
    {x : Space} (hx : x ∈ segment ℝ (point n) (point m))
    (hy : x ∈ segment ℝ (point n) (point l)) : x = point n := by
  rcases lt_or_gt_of_ne hml with h | h
  · exact common_start_ordered hnm h hl hx hy
  · exact common_start_ordered hnl h hm hy hx

theorem ordered_edges_meet {i j k l : ℕ} (hij : i < j) (hj : j ≤ i+3)
    (hkl : k < l) (hl : l ≤ k+3) {x : Space}
    (hx : x ∈ segment ℝ (point i) (point j))
    (hy : x ∈ segment ℝ (point k) (point l)) :
    (i = k ∧ j = l) ∨
      ∃ w, (w = i ∨ w = j) ∧ (w = k ∨ w = l) ∧ x = point w := by
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · exact Or.inl ⟨rfl,hjl⟩
    · exact Or.inr ⟨i,Or.inl rfl,Or.inl rfl,common_start hij hkl hj hl hjl hx hy⟩
  · rcases lt_or_gt_of_ne hik with hik' | hki
    · have hk := point_later_mem (show i+1 ≤ k by omega)
      have hl' := point_later_mem (show i+1 ≤ l by omega)
      have ht := (tailCone_convex (i+1)).segment_subset hk hl' hy
      have hxj := segment_meets_tail_at_endpoint hij hj hx ht
      have hjmem : point j ∈ segment ℝ (point k) (point l) := hxj ▸ hy
      have hjends : j = k ∨ j = l := by
        by_contra hn
        push_neg at hn
        exact vertex_not_on_edge hkl hl hn.1 hn.2 hjmem
      exact Or.inr ⟨j,Or.inr rfl,hjends,hxj⟩
    · have hi := point_later_mem (show k+1 ≤ i by omega)
      have hj' := point_later_mem (show k+1 ≤ j by omega)
      have ht := (tailCone_convex (k+1)).segment_subset hi hj' hx
      have hxl := segment_meets_tail_at_endpoint hkl hl hy ht
      have hlmem : point l ∈ segment ℝ (point i) (point j) := hxl ▸ hx
      have hlends : l = i ∨ l = j := by
        by_contra hn
        push_neg at hn
        exact vertex_not_on_edge hij hj hn.1 hn.2 hlmem
      exact Or.inr ⟨l,hlends,Or.inr rfl,hxl⟩

abbrev Plane := Fin 2 → ℝ

def project (x : Space) : Plane := fun i => x (Fin.castLE (by decide : 2 ≤ 3) i)

def planePoint (n : ℕ) : Plane := project (point n)

theorem project_injective_on_plane {x y : Space} (hx : total x = 1) (hy : total y = 1)
    (he : project x = project y) : x = y := by
  have h0 := congrFun he (0 : Fin 2)
  have h1 := congrFun he (1 : Fin 2)
  change x 0 = y 0 at h0
  change x 1 = y 1 at h1
  have h2 : x 2 = y 2 := by
    unfold total at hx hy
    linarith
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem planePoint_injective : Function.Injective planePoint := by
  intro n m h
  exact point_injective (project_injective_on_plane (point_total n) (point_total m) h)

@[simp] theorem total_add (x y : Space) : total (x+y) = total x+total y := by
  simp [total]
  ring

@[simp] theorem total_smul (a : ℝ) (x : Space) : total (a • x) = a * total x := by
  simp [total]
  ring

theorem total_segment {p q x : Space} (hp : total p = 1) (hq : total q = 1)
    (hx : x ∈ segment ℝ p q) : total x = 1 := by
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hx
  simpa [hp,hq] using hab

theorem plane_segment_preimage {p q : Space} {x : Plane}
    (hx : x ∈ segment ℝ (project p) (project q)) :
    ∃ y ∈ segment ℝ p q, project y = x := by
  obtain ⟨a,b,ha,hb,hab,he⟩ := hx
  exact ⟨a • p+b • q,⟨a,b,ha,hb,hab,rfl⟩,he⟩

theorem plane_vertex_not_on_edge {i j k : ℕ} (hij : i < j) (hj : j ≤ i+3)
    (hki : k ≠ i) (hkj : k ≠ j) : planePoint k ∉ segment ℝ (planePoint i) (planePoint j) := by
  intro h
  obtain ⟨x,hx,hxp⟩ := plane_segment_preimage h
  have hx' := project_injective_on_plane
    (total_segment (point_total i) (point_total j) hx) (point_total k) hxp
  rw [hx'] at hx
  exact vertex_not_on_edge hij hj hki hkj hx

theorem plane_ordered_edges_meet {i j k l : ℕ} (hij : i < j) (hj : j ≤ i+3)
    (hkl : k < l) (hl : l ≤ k+3) {x : Plane}
    (hx : x ∈ segment ℝ (planePoint i) (planePoint j))
    (hy : x ∈ segment ℝ (planePoint k) (planePoint l)) :
    (i = k ∧ j = l) ∨
      ∃ w, (w = i ∨ w = j) ∧ (w = k ∨ w = l) ∧ x = planePoint w := by
  obtain ⟨p,hp,hpx⟩ := plane_segment_preimage hx
  obtain ⟨q,hq,hqx⟩ := plane_segment_preimage hy
  have hpq : p = q := project_injective_on_plane
    (total_segment (point_total i) (point_total j) hp)
    (total_segment (point_total k) (point_total l) hq) (hpx.trans hqx.symm)
  rw [← hpq] at hq
  rcases ordered_edges_meet hij hj hkl hl hp hq with he | ⟨w,hw,hv,hpw⟩
  · exact Or.inl he
  · refine Or.inr ⟨w,hw,hv,?_⟩
    rw [hpw] at hpx
    exact hpx.symm

end PathDrawing
end GraphicalZonotopes

end
end
end BundlePart273

section BundlePart274
/- Source: Papers/GraphicalZonotopes/PathGraph.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset
open scoped BigOperators

instance graph_decidableAdj (n : ℕ) : DecidableRel (graph n).Adj := by
  dsimp [graph]
  infer_instance

theorem clique_card_le_four {n : ℕ} {C : Finset (Fin n)}
    (hcl : (graph n).IsClique C) : C.card ≤ 4 := by
  by_cases hc : 2 ≤ C.card
  · obtain ⟨i,T,hT,hbound,rfl⟩ := clique_window_classification hc
      (fun u hu v hv huv => hcl hu hv huv)
    rw [window_card T hbound]
    simp only [masks, mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · omega

theorem graph_cliqueFree_five (n : ℕ) : (graph n).CliqueFree 5 := by
  intro C hC
  have h := clique_card_le_four hC.isClique
  rw [hC.card_eq] at h
  omega

abbrev EdgeIndex (n : ℕ) := Fin (n-1) ⊕ (Fin (n-2) ⊕ Fin (n-3))

def indexedEdge (n : ℕ) : EdgeIndex n → Finset (Fin n)
  | Sum.inl i => window n i.val {0,1}
  | Sum.inr (Sum.inl i) => window n i.val {0,2}
  | Sum.inr (Sum.inr i) => window n i.val {0,3}

theorem indexedEdge_mem (n : ℕ) (i : EdgeIndex n) : indexedEdge n i ∈ edgeFamily (graph n) := by
  rw [mem_edgeFamily]
  rcases i with i | i | i
  all_goals
    refine ⟨?_, ?_⟩
    · rw [indexedEdge, window_card _ (by
        intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)]
      norm_num
    · apply window_clique
      intro k hk
      simp only [mem_insert, mem_singleton] at hk ⊢
      tauto

theorem indexedEdge_injective (n : ℕ) : Function.Injective (indexedEdge n) := by
  intro i j he
  rcases i with i | i | i <;> rcases j with j | j | j
  all_goals
    dsimp [indexedEdge] at he
    have h := (window_eq_iff (by simp) (by simp)
      (by intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)
      (by intro k hk; simp only [mem_insert, mem_singleton] at hk; omega)).mp he
    first
    | have hval : i = j := Fin.ext h.1
      subst j
      rfl
    | have hbad := h.2
      exfalso
      revert hbad
      decide

theorem indexedEdge_surjective (n : ℕ) {C : Finset (Fin n)}
    (hC : C ∈ edgeFamily (graph n)) : ∃ i, indexedEdge n i = C := by
  obtain ⟨hc,hcl⟩ := (mem_edgeFamily _ _).mp hC
  obtain ⟨i,T,hT,hbound,rfl⟩ := clique_window_classification (by omega) hcl
  have hcard := window_card T hbound
  simp only [masks, mem_insert, mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h := hbound 1 (by simp)
    exact ⟨Sum.inl ⟨i,by omega⟩,rfl⟩
  · have h := hbound 2 (by simp)
    exact ⟨Sum.inr (Sum.inl ⟨i,by omega⟩),rfl⟩
  · have h := hbound 3 (by simp)
    exact ⟨Sum.inr (Sum.inr ⟨i,by omega⟩),rfl⟩
  all_goals norm_num at hcard; omega

theorem edgeFamily_card (n : ℕ) :
    (edgeFamily (graph n)).card = (n-1)+(n-2)+(n-3) := by
  let f : EdgeIndex n → {C : Finset (Fin n) // C ∈ edgeFamily (graph n)} :=
    fun i => ⟨indexedEdge n i,indexedEdge_mem n i⟩
  have hfinj : Function.Injective f := by
    intro i j he
    exact indexedEdge_injective n (congrArg Subtype.val he)
  have hfsurj : Function.Surjective f := by
    intro C
    obtain ⟨i,hi⟩ := indexedEdge_surjective n C.2
    exact ⟨i,Subtype.ext hi⟩
  have h := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj,hfsurj⟩)
  simpa only [Fintype.card_coe, EdgeIndex, Fintype.card_sum, Fintype.card_fin, Nat.add_assoc] using h.symm

theorem graph_edge_count {n : ℕ} (hn : 4 ≤ n) :
    (edgeFamily (graph n)).card = 3*n-6 := by
  rw [edgeFamily_card]
  omega

abbrev NeighborIndex {n : ℕ} (u : Fin n) :=
  Fin (min u.val 3) ⊕ Fin (min (n-1-u.val) 3)

def indexedNeighbor {n : ℕ} (u : Fin n) : NeighborIndex u → Fin n
  | Sum.inl i => ⟨u.val-(i.val+1),by have h := u.isLt; omega⟩
  | Sum.inr i => ⟨u.val+i.val+1,by have h := u.isLt; omega⟩

theorem indexedNeighbor_adj {n : ℕ} (u : Fin n) (i : NeighborIndex u) :
    (graph n).Adj u (indexedNeighbor u i) := by
  rcases i with i | i
  all_goals
    change u ≠ _ ∧ u.val ≤ _ + 3 ∧ _ ≤ u.val + 3
    dsimp only [indexedNeighbor, Fin.val_mk]
    refine ⟨?_,by omega,by omega⟩
    intro he
    have h := congrArg Fin.val he
    simp only [Fin.val_mk] at h
    omega

theorem indexedNeighbor_injective {n : ℕ} (u : Fin n) :
    Function.Injective (indexedNeighbor u) := by
  intro i j he
  have hv := congrArg Fin.val he
  rcases i with i | i <;> rcases j with j | j
  all_goals
    dsimp [indexedNeighbor] at hv
    first
    | have h : i = j := Fin.ext (by omega)
      subst j
      rfl
    | omega

theorem indexedNeighbor_surjective {n : ℕ} (u v : Fin n)
    (hadj : (graph n).Adj u v) : ∃ i, indexedNeighbor u i = v := by
  obtain ⟨hne,hlo,hhi⟩ := hadj
  have hval : u.val ≠ v.val := by intro h; exact hne (Fin.ext h)
  by_cases hlt : v.val < u.val
  · refine ⟨Sum.inl ⟨u.val-v.val-1,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [indexedNeighbor]
    omega
  · refine ⟨Sum.inr ⟨v.val-u.val-1,by have h := v.isLt; omega⟩,?_⟩
    apply Fin.ext
    dsimp [indexedNeighbor]
    omega

theorem graph_degree {n : ℕ} (u : Fin n) :
    (graph n).degree u = min u.val 3 + min (n-1-u.val) 3 := by
  let f : NeighborIndex u → (graph n).neighborSet u :=
    fun i => ⟨indexedNeighbor u i,indexedNeighbor_adj u i⟩
  have hfinj : Function.Injective f := by
    intro i j he
    exact indexedNeighbor_injective u (congrArg Subtype.val he)
  have hfsurj : Function.Surjective f := by
    intro v
    obtain ⟨i,hi⟩ := indexedNeighbor_surjective u v.1 v.2
    exact ⟨i,Subtype.ext hi⟩
  have h := Fintype.card_congr (Equiv.ofBijective f ⟨hfinj,hfsurj⟩)
  rw [SimpleGraph.card_neighborSet_eq_degree] at h
  simpa [NeighborIndex] using h.symm

theorem graph_maxDegree {n : ℕ} (hn : 4 ≤ n) :
    (graph n).maxDegree = min (n-1) 6 := by
  apply le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro u
    rw [graph_degree]
    have h := u.isLt
    omega
  · have h := (graph n).degree_le_maxDegree (⟨3,by omega⟩ : Fin n)
    rw [graph_degree] at h
    simp only [Fin.val_mk] at h
    convert h using 1 <;> omega

end Path
end GraphicalZonotopes

end
end
end BundlePart274

section BundlePart275
/- Source: Papers/GraphicalZonotopes/PathPlanarity.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes

/-- An actual straight-line drawing in the real plane: vertices are distinct,
no vertex lies on an unrelated edge, and two different edges intersect only at
a common endpoint. This gives a concrete plane embedding, not a combinatorial
proxy for planarity. -/
def HasPlaneStraightLineDrawing {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p : V → (Fin 2 → ℝ), Function.Injective p ∧
    (∀ u v w, G.Adj u v → w ≠ u → w ≠ v →
      p w ∉ segment ℝ (p u) (p v)) ∧
    ∀ u v a b, G.Adj u v → G.Adj a b → ∀ x : Fin 2 → ℝ,
      x ∈ segment ℝ (p u) (p v) → x ∈ segment ℝ (p a) (p b) →
      (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
        ∃ w, (w = u ∨ w = v) ∧ (w = a ∨ w = b) ∧ x = p w

namespace PathDrawing

theorem ordered_plane_segment (i j : ℕ) :
    segment ℝ (planePoint (min i j)) (planePoint (max i j)) =
      segment ℝ (planePoint i) (planePoint j) := by
  by_cases h : i ≤ j
  · simp [min_eq_left h,max_eq_right h]
  · have h' : j ≤ i := by omega
    rw [min_eq_right h',max_eq_left h']
    exact segment_symm ℝ _ _

theorem path_plane_drawing (n : ℕ) : HasPlaneStraightLineDrawing (Path.graph n) := by
  let p : Fin n → Plane := fun v => planePoint v.val
  refine ⟨p,?_,?_,?_⟩
  · intro u v h
    exact Fin.ext (planePoint_injective h)
  · intro u v w huv hwu hwv
    have huv' : u.val ≠ v.val := fun h => huv.1 (Fin.ext h)
    have hwu' : w.val ≠ u.val := fun h => hwu (Fin.ext h)
    have hwv' : w.val ≠ v.val := fun h => hwv (Fin.ext h)
    have huBound := huv.2.1
    have hvBound := huv.2.2
    have h1 : min u.val v.val < max u.val v.val := by omega
    have h2 : max u.val v.val ≤ min u.val v.val+3 := by omega
    have h3 : w.val ≠ min u.val v.val := by omega
    have h4 : w.val ≠ max u.val v.val := by omega
    have h := plane_vertex_not_on_edge h1 h2 h3 h4
    rw [ordered_plane_segment] at h
    exact h
  · intro u v a b huv hab x hx hy
    have huv' : u.val ≠ v.val := fun h => huv.1 (Fin.ext h)
    have hab' : a.val ≠ b.val := fun h => hab.1 (Fin.ext h)
    have huBound := huv.2.1
    have hvBound := huv.2.2
    have haBound := hab.2.1
    have hbBound := hab.2.2
    have h1 : min u.val v.val < max u.val v.val := by omega
    have h2 : max u.val v.val ≤ min u.val v.val+3 := by omega
    have h3 : min a.val b.val < max a.val b.val := by omega
    have h4 : max a.val b.val ≤ min a.val b.val+3 := by omega
    have hx' : x ∈ segment ℝ (planePoint (min u.val v.val))
        (planePoint (max u.val v.val)) := by
      rw [ordered_plane_segment]
      exact hx
    have hy' : x ∈ segment ℝ (planePoint (min a.val b.val))
        (planePoint (max a.val b.val)) := by
      rw [ordered_plane_segment]
      exact hy
    rcases plane_ordered_edges_meet h1 h2 h3 h4 hx' hy' with ⟨hmin,hmax⟩ | ⟨w,hw,hz,he⟩
    · have h : (u.val = a.val ∧ v.val = b.val) ∨
          (u.val = b.val ∧ v.val = a.val) := by omega
      rcases h with ⟨hua,hvb⟩ | ⟨hub,hva⟩
      · exact Or.inl ⟨Fin.ext hua,Fin.ext hvb⟩
      · exact Or.inr (Or.inl ⟨Fin.ext hub,Fin.ext hva⟩)
    · have hw' : w = u.val ∨ w = v.val := by omega
      have hz' : w = a.val ∨ w = b.val := by omega
      have hwn : w < n := by rcases hw' with h | h <;> omega
      let W : Fin n := ⟨w,hwn⟩
      refine Or.inr (Or.inr ⟨W,?_,?_,he⟩)
      · rcases hw' with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      · rcases hz' with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)

end PathDrawing
end GraphicalZonotopes

end
end
end BundlePart275

section BundlePart276
/- Source: Papers/GraphicalZonotopes/PathPrincipal.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open scoped Pointwise

/-- The complete content of Theorem 3.1 for the explicitly defined Q_n.
Planarity is witnessed by a noncrossing straight-line embedding in R². -/
def PrincipalPathClaim (n : ℕ) : Prop :=
  LatticePolytope (polytope n) ∧
  MinkowskiIndecomposable (polytope n) ∧
  Module.finrank ℝ (vectorSpan ℝ (polytope n)) = n-1 ∧
  polytope n + complement n = (2 : ℝ) • graphicalZonotope (graph n) ∧
  (∀ u v, ActualRootEdge (polytope n) u v ↔ (graph n).Adj u v) ∧
  (∀ p q, IsExposedSegment (polytope n) p q →
    ∃ u v, (graph n).Adj u v ∧ ∃ t : ℝ, t ≠ 0 ∧
      q-p = t • (basisVector v-basisVector u)) ∧
  HasPlaneStraightLineDrawing (graph n) ∧
  (graph n).CliqueFree 5 ∧
  (edgeFamily (graph n)).card = 3*n-6 ∧
  (graph n).maxDegree = min (n-1) 6

/-- Theorem 3.1, with all n ≥ 4, actual Minkowski summation, actual exposed
directions, full affine dimension, and an actual geometric plane drawing. -/
theorem principal_path_theorem {n : ℕ} (hn : 4 ≤ n) : PrincipalPathClaim n :=
  ⟨polytope_lattice n, polytope_indecomposable hn, polytope_dimension hn,
    polytope_add_complement n, actual_direction_graph hn,
    fun _ _ h => every_exposed_edge_is_graph_direction hn h,
    PathDrawing.path_plane_drawing n, graph_cliqueFree_five n,
    graph_edge_count hn, graph_maxDegree hn⟩

end Path
end GraphicalZonotopes

end
end
end BundlePart276

section BundlePart277
/- Source: Papers/GraphicalZonotopes/PathThreeTree.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace Path
open Finset

def initialVertices (n k : ℕ) : Finset (Fin n) := univ.filter (fun v => v.val< k)

@[simp] theorem mem_initialVertices (n k : ℕ) (v : Fin n) :
    v∈initialVertices n k ↔ v.val< k := by simp [initialVertices]

theorem initialVertices_four (n : ℕ) :
    initialVertices n 4=window n 0 {0,1,2,3} := by
  ext v
  simp only [mem_initialVertices,mem_window,Nat.zero_le,Nat.sub_zero,true_and,
    mem_insert,mem_singleton]
  omega

theorem initialVertices_next {n k : ℕ} (hk : k< n) :
    initialVertices n (k+1)=insert (⟨k,hk⟩ : Fin n) (initialVertices n k) := by
  ext v
  simp only [mem_initialVertices,mem_insert,Fin.ext_iff]
  omega

/-- The actual path cube has a tetrahedral growth at every prefix: the next
vertex attaches to its three immediate predecessors. -/
theorem initialVertices_growth (n t : ℕ) (hbound : t+4≤ n) :
    TetrahedralGrowth (graph n) (initialVertices n (t+4)) := by
  revert hbound
  induction t with
  | zero =>
    intro hbound
    rw [Nat.zero_add,initialVertices_four]
    apply TetrahedralGrowth.base
    · rw [window_card _ (by
        intro k hk
        simp only [mem_insert,mem_singleton] at hk
        omega)]
      decide
    · intro u hu v hv huv
      exact window_clique (subset_refl _) u hu v hv huv
  | succ t ih =>
    intro hbound
    have ht : t+4< n := by omega
    have hg := ih (by omega)
    let w : Fin n:=⟨t+4,ht⟩
    let T:=window n (t+1) {0,1,2}
    have hTcard : T.card=3 := by
      rw [window_card _ (by
        intro k hk
        simp only [mem_insert,mem_singleton] at hk
        omega)]
      decide
    have hTS : T⊆initialVertices n (t+4) := by
      intro v hv
      have hv' := (mem_window _ _ _ v).mp hv
      simp only [mem_insert,mem_singleton] at hv'
      apply (mem_initialVertices _ _ _).mpr
      omega
    have hTcl : (graph n).IsClique T := by
      intro u hu v hv huv
      exact window_clique (by simp) u hu v hv huv
    have hAdj : ∀ v∈T,(graph n).Adj w v := by
      intro v hv
      have hv' := (mem_window _ _ _ v).mp hv
      simp only [mem_insert,mem_singleton] at hv'
      refine ⟨?_,?_,?_⟩
      · intro he
        have he' := congrArg Fin.val he
        change t+4=v.val at he'
        omega
      · change t+4≤ v.val+3
        omega
      · change v.val≤ t+4+3
        omega
    have hg' := TetrahedralGrowth.attach hg w (by simp [w]) T hTcard hTS hTcl hAdj
    have he : t+1+4=(t+4)+1 := by omega
    simpa only [Nat.succ_eq_add_one,he,initialVertices_next ht,w] using hg'

/-- The equality witness used in Theorem9.1 really belongs to the class of
3-trees; this is proved independently of the lower dilation conclusion. -/
theorem graph_isThreeTree {n : ℕ} (hn : 4≤ n) : IsThreeTree (graph n) := by
  have hg := initialVertices_growth n (n-4) (by omega)
  have he : n-4+4=n := by omega
  have hu : initialVertices n n=univ := by ext v; simp [v.isLt]
  rw [he,hu] at hg
  have hc := hg.edge_bound_and_equality.2
  simp only [inducedOn_univ,card_univ,Fintype.card_fin] at hc
  exact hc (graph_edge_count hn)

end Path
end GraphicalZonotopes

end
end
end BundlePart277

section BundlePart278
/- Source: Papers/GraphicalZonotopes/ThreeTreeLatticeDilation.lean -/









@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open RefinedTriangleComponents
open scoped BigOperators Pointwise

/-- The full quantified lower bound of Theorem9.1: the summand is an actual
lattice polytope, the ambient3-tree is arbitrary, every tetrahedral coefficient
is a nonzero integer, and every edge has the exact ceiling bound. -/
theorem threeTree_lattice_lower_bound {n : ℕ} (hn : 6≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0< a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    2≤ a ∧ (∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k) ∧
      ∀ e∈edgeFamily G,
        (Int.ceil ((1/2 : ℝ)*
          ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius (lowerSupport Q) C|) : ℝ)≤ a := by
  classical
  have hcoeff := threeTree_lattice_four_coefficients (by omega : 4≤ n) hG hQ hi hd ha hsum
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
  let f:=lowerSupport Q
  let z:=normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := (hQ.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hzy : CliqueSupported G (mobius z) := (mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩
  have hzb : ∀ u v,u≠ v → G.Adj u v → ∀ S,u∉S → v∉S → delta z u v S≤ a := by
    intro u v huv hadj S hu hv
    rw [delta_normalize f huv hu hv]
    exact hbound u v huv hadj S hu hv
  have hedge : ∀ e∈edgeFamily G,
      (Int.ceil ((1/2 : ℝ)*
        ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) : ℝ)≤ a := by
    intro e he
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily G e).mp he
    obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hc
    have hadj := (pair_mem_edgeFamily G huv).mp he
    have hb := threeTree_integral_slack_bound hG hzs hzi hzy hzb hadj
    have hs : (∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset (Fin n))⊆C),
        |mobius z C|)=
        ∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset (Fin n))⊆C),|mobius f C| := by
      apply sum_congr rfl
      intro C hC
      have hc : C.card=4 := (mem_filter.mp (mem_filter.mp hC).1).2.1
      rw [mobius_four_normalize hc]
    rwa [hs] at hb
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : z≠0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hall⟩ := threeTree_all_tetrahedra_nonzero (by omega : 4≤ n) hG hext hzg hdim
  have hconn := (full_refined_support (by omega : 4≤ n) hG.cliqueFree_five hext hzg hdim).2.1
  rw [hF] at hconn
  have hnum : 3≤(tetrahedra G).card := by
    have hc:=hG.tetrahedra_card
    simp only [card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨e,hecard,hemany⟩ := connected_tetrahedra_pair_multiplicity (tetrahedra G)
    (fun C hC => (mem_filter.mp hC).2.1) hconn hnum
  have heG : e∈edgeFamily G := by
    obtain ⟨C,hC⟩ := card_pos.mp (show 0<((tetrahedra G).filter (fun C => e⊆C)).card by omega)
    obtain ⟨hC,heC⟩ := mem_filter.mp hC
    have hc := (mem_filter.mp hC).2.2
    exact (mem_edgeFamily G e).mpr ⟨hecard,fun u hu v hv huv => hc (heC hu) (heC hv) huv⟩
  have hsum : (3 : ℝ)≤
      ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C| := by
    calc
      (3 : ℝ)≤(((tetrahedra G).filter (fun C => e⊆C)).card : ℝ) := by exact_mod_cast hemany
      _ = ∑ C∈(tetrahedra G).filter (fun C => e⊆C),(1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro C hC
        obtain ⟨k,hk,hvalue⟩ := hcoeff C (mem_filter.mp hC).1
        rw [hvalue]
        have hpos : (0 : ℤ) < abs k := abs_pos.mpr hk
        have hone : (1 : ℤ) ≤ abs k := by omega
        exact_mod_cast hone
  have hceil : (2 : ℤ)≤ Int.ceil ((1/2 : ℝ)*
      ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) := by
    have hh : (1 : ℤ)< Int.ceil ((1/2 : ℝ)*
        ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) :=
      Int.lt_ceil.mpr (by norm_num; linarith)
    omega
  have hcast : (2 : ℝ)≤(Int.ceil ((1/2 : ℝ)*
      ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) : ℝ) := by exact_mod_cast hceil
  exact ⟨hcast.trans (hedge e heG),hcoeff,hedge⟩

/-- The traditional formulation, quantifying indecomposability only over
polytope summands, is equivalent here; the compact-convex convention imposes
no additional mathematical restriction on the original theorem. -/
theorem threeTree_lattice_lower_bound_polytopal {n : ℕ} (hn : 6≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0< a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    2≤ a ∧ (∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k) ∧
      ∀ e∈edgeFamily G,
        (Int.ceil ((1/2 : ℝ)*
          ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius (lowerSupport Q) C|) : ℝ)≤ a := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hfn,hfs,hbody⟩
  exact threeTree_lattice_lower_bound hn hG hQ
    ((minkowskiIndecomposable_iff_polytopal hgp).mpr hi) hd ha ⟨R,hR,hcR,hnR,he⟩

/-- The full principal statement includes the explicit equality witnesses
at every n≥6, rather than recording sharpness only as an informal remark. -/
theorem threeTree_lattice_dilation : Targets.ThreeTreeLatticeDilation := by
  constructor
  · intro n hn G hG Q hQ hi hd a ha hsum
    exact threeTree_lattice_lower_bound hn hG hQ hi hd ha hsum
  · intro n hn
    refine ⟨Path.polytope n,Path.polytope_lattice n,Path.polytope_indecomposable (by omega),
      ?_,Path.complement n,?_,?_,?_,Path.polytope_add_complement n⟩
    · simpa only [FullDimension,Fintype.card_fin] using Path.polytope_dimension (by omega : 4≤ n)
    · exact basePolytope_compact (Path.complement_normalized n) (Path.complement_supermodular n)
    · exact basePolytope_convex _
    · exact basePolytope_nonempty (Path.complement_normalized n) (Path.complement_supermodular n)

/-- The equality witnesses lie in the original3-tree class and attain the
sharp dilation for every parameter in the theorem. -/
theorem threeTree_lattice_dilation_sharp :
    Targets.ThreeTreeLatticeDilation ∧
      ∀ n : ℕ,6≤ n → IsThreeTree (Path.graph n) ∧ FullLatticeSummandAt (Path.graph n) 2 := by
  refine ⟨threeTree_lattice_dilation,?_⟩
  intro n hn
  exact ⟨Path.graph_isThreeTree (by omega),threeTree_lattice_dilation.2 n hn⟩

end GraphicalZonotopes

end
end
end BundlePart278

section BundlePart279
/- Source: Papers/GraphicalZonotopes/OptimalK5FreeWitnesses.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise

/-- Four actual color classes exclude a five-clique, independently of the
sizes of those classes. -/
theorem cliqueFree_five_of_four_coloring {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (c : V → Fin 4)
    (hc : ∀ u v,G.Adj u v → c u≠ c v) : G.CliqueFree 5 := by
  intro C hC
  have hinj : Set.InjOn c (C : Set V) := by
    intro u hu v hv he
    by_contra hne
    exact hc u v (hC.isClique hu hv hne) he
  have hcard : C.card≤4 := by
    calc
      C.card=(C.image c).card := (card_image_of_injOn hinj).symm
      _≤(univ : Finset (Fin 4)).card := card_le_card (subset_univ _)
      _=4 := by simp
  rw [hC.card_eq] at hcard
  omega

/-- Every vertex cardinality from four through eight has an actual
full-dimensional unit lattice summand of a K5-free graphical zonotope. The
five cases are exactly the bounded branch of the optimal-dilation theorem. -/
theorem unit_lattice_witness_four_to_eight {n : ℕ} (hn : 4≤ n) (hn8 : n≤8) :
    ∃ G : SimpleGraph (Fin n),G.CliqueFree 5 ∧ FullLatticeSummandAt G 1 := by
  let a : Fin 4 → ℕ := fun i => if i.val< n-4 then 2 else 1
  have ha : ∀ i,a i=1 ∨ a i=2 := by intro i;dsimp [a];split_ifs <;> simp
  have hc : Fintype.card (Σ i : Fin 4,Fin (a i))=n := by
    change Fintype.card (Σ i : Fin 4, Fin (if i.val < n - 4 then 2 else 1)) = n
    interval_cases n <;> decide
  let e : Fin n ≃ (Σ i : Fin 4,Fin (a i)) := Fintype.equivOfCardEq (by simpa using hc.symm)
  let H := (fourPartite a).comap e
  let D : BooleanPairData (fourPartite a) := by
    simpa only [FourSmallParts.graph_partSizeEquiv] using
      (FourSmallParts.pairData (FourSmallParts.doubledParts a)).relabel
        (FourSmallParts.partSizeEquiv a ha)
  let E : H ≃g fourPartite a := {toEquiv := e,map_rel_iff' := by intros;rfl}
  have hconn : H.Connected := E.connected_iff.mpr
    (FourSmallParts.fourPartite_connected a (fun i => by rcases ha i with h | h <;> omega))
  let D' : BooleanPairData H := D.relabel e
  have hpair := D'.geometric_pair hconn
  refine ⟨H,cliqueFree_five_of_four_coloring (fun v => (e v).1) (by intros;assumption),
    basePolytope D'.left,hpair.1,hpair.2.2.1,hpair.2.2.2.2.1,?_⟩
  refine ⟨basePolytope D'.right,
    basePolytope_compact D'.right_extreme.1.1 D'.right_extreme.2.1,
    basePolytope_convex _,basePolytope_nonempty D'.right_extreme.1.1 D'.right_extreme.2.1,?_⟩
  simpa only [one_smul] using hpair.2.2.2.2.2.2.1

/-- The attainment half of Corollary 9.12, with no restriction on the vertex
count beyond the paper's n≥4 hypothesis. -/
theorem optimal_k5_free_dilation_attained {n : ℕ} (hn : 4≤ n) :
    ∃ G : SimpleGraph (Fin n),G.CliqueFree 5 ∧
      FullLatticeSummandAt G (if n≤8 then 1 else 2) := by
  by_cases hn8 : n≤8
  · simpa only [if_pos hn8] using unit_lattice_witness_four_to_eight hn hn8
  · have h := threeTree_lattice_dilation_sharp.2 n (by omega)
    exact ⟨Path.graph n,h.1.cliqueFree_five,by simpa only [if_neg hn8] using h.2⟩

end GraphicalZonotopes

end
end
end BundlePart279

section BundlePart280
/- Source: Papers/GraphicalZonotopes/BooleanLinkRows.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace GraphicalZonotopes.BooleanLinkRows

def IsBit (x : ℝ) : Prop := x = 0 ∨ x = 1

theorem bit_square {x : ℝ} (hx : IsBit x) : x ^ 2 = x := by
  rcases hx with rfl | rfl <;> norm_num

/-- A Boolean affine function cannot vary independently in two directions. -/
theorem affine_two_mul_eq_zero (c a b : ℝ)
    (h00 : IsBit c) (h10 : IsBit (c+a)) (h01 : IsBit (c+b))
    (h11 : IsBit (c+a+b)) : a*b=0 := by
  have h0 := bit_square h00
  have h1 := bit_square h10
  have h2 := bit_square h01
  have h3 := bit_square h11
  nlinarith

/-- The difference of two vectors supported on at most one coordinate
cannot have three nonzero coordinates. -/
theorem three_differences_zero (a b c a' b' c' : ℝ)
    (hab : a*b=0) (hac : a*c=0) (hbc : b*c=0)
    (hab' : a'*b'=0) (hac' : a'*c'=0) (hbc' : b'*c'=0) :
    a'-a=0 ∨ b'-b=0 ∨ c'-c=0 := by
  by_cases ha : a=0
  · by_cases ha' : a'=0
    · exact Or.inl (by simp [ha,ha'])
    · have hb' : b'=0 := (mul_eq_zero.mp hab').resolve_left ha'
      have hc' : c'=0 := (mul_eq_zero.mp hac').resolve_left ha'
      rcases mul_eq_zero.mp hbc with hb | hc
      · exact Or.inr (Or.inl (by simp [hb,hb']))
      · exact Or.inr (Or.inr (by simp [hc,hc']))
  · have hb : b=0 := (mul_eq_zero.mp hab).resolve_left ha
    have hc : c=0 := (mul_eq_zero.mp hac).resolve_left ha
    rcases mul_eq_zero.mp hbc' with hb' | hc'
    · exact Or.inr (Or.inl (by simp [hb,hb']))
    · exact Or.inr (Or.inr (by simp [hc,hc']))

def bit (s : Bool) : ℝ := if s then 1 else 0

def quadratic4 (k a b c d ab ac ad bc bd cd : ℝ) (s t u v : Bool) : ℝ :=
  k + a*bit s + b*bit t + c*bit u + d*bit v +
    ab*bit s*bit t + ac*bit s*bit u + ad*bit s*bit v +
    bc*bit t*bit u + bd*bit t*bit v + cd*bit u*bit v

/-- An induced four-vertex path cannot be the interaction graph of a
Boolean quadratic. The middle edge coefficient is arbitrary. -/
theorem path_end_product_zero (k a b c d ab bc cd : ℝ)
    (h : ∀ s t u v : Bool, IsBit (quadratic4 k a b c d ab 0 0 bc 0 cd s t u v)) :
    ab*cd=0 := by
  have hp (s t : Bool) : (a+ab*bit s)*(d+cd*bit t)=0 := by
    apply affine_two_mul_eq_zero (k+b*bit s+c*bit t+bc*bit s*bit t)
      (a+ab*bit s) (d+cd*bit t)
    · convert h false s t false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h true s t false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h false s t true using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h true s t true using 1 <;> simp [quadratic4,bit] <;> ring
  have h00 := hp false false
  have h10 := hp true false
  have h01 := hp false true
  have h11 := hp true true
  simp only [bit, Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, add_zero] at *
  nlinarith

/-- A Boolean quadratic on a three-leaf star has a zero interaction edge. -/
theorem star_three_zero (k a b c d ab ac ad : ℝ)
    (h : ∀ s t u v : Bool, IsBit (quadratic4 k a b c d ab ac ad 0 0 0 s t u v)) :
    ab=0 ∨ ac=0 ∨ ad=0 := by
  have hbc (s : Bool) : (b+ab*bit s)*(c+ac*bit s)=0 := by
    apply affine_two_mul_eq_zero (k+a*bit s) (b+ab*bit s) (c+ac*bit s)
    · convert h s false false false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s true false false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s false true false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s true true false using 1 <;> simp [quadratic4,bit] <;> ring
  have hbd (s : Bool) : (b+ab*bit s)*(d+ad*bit s)=0 := by
    apply affine_two_mul_eq_zero (k+a*bit s) (b+ab*bit s) (d+ad*bit s)
    · convert h s false false false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s true false false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s false false true using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s true false true using 1 <;> simp [quadratic4,bit] <;> ring
  have hcd (s : Bool) : (c+ac*bit s)*(d+ad*bit s)=0 := by
    apply affine_two_mul_eq_zero (k+a*bit s) (c+ac*bit s) (d+ad*bit s)
    · convert h s false false false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s false true false using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s false false true using 1 <;> simp [quadratic4,bit] <;> ring
    · convert h s false true true using 1 <;> simp [quadratic4,bit] <;> ring
  have hbc0 := hbc false
  have hbd0 := hbd false
  have hcd0 := hcd false
  have hbc1 := hbc true
  have hbd1 := hbd true
  have hcd1 := hcd true
  simp only [bit, Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, add_zero] at *
  rcases three_differences_zero b c d (b+ab) (c+ac) (d+ad)
    hbc0 hbd0 hcd0 hbc1 hbd1 hcd1 with hz | hz | hz
  · left; linarith
  · right; left; linarith
  · right; right; linarith

open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def pick (s : Bool) (a : V) (S : Finset V) : Finset V := if s then insert a S else S

def select4 (a b c d : V) (s t u v : Bool) : Finset V :=
  pick s a (pick t b (pick u c (pick v d ∅)))

/-- Restricting a quadratic set function to any four distinct vertices is
exactly the displayed four-variable polynomial, with its actual coefficients. -/
theorem zeta_select4 (g : SetFunction V)
    (hdegree : ∀ C : Finset V, 2< C.card → g C=0)
    {a b c d : V} (hab : a≠ b) (hac : a≠ c) (had : a≠ d)
    (hbc : b≠ c) (hbd : b≠ d) (hcd : c≠ d) (s t u v : Bool) :
    zeta g (select4 a b c d s t u v) =
      quadratic4 (g ∅) (g {a}) (g {b}) (g {c}) (g {d})
        (g {a,b}) (g {a,c}) (g {a,d}) (g {b,c}) (g {b,d}) (g {c,d}) s t u v := by
  have hABC : g {a,b,c}=0 := hdegree _ (by simp [hab,hac,hbc])
  have hABD : g {a,b,d}=0 := hdegree _ (by simp [hab,had,hbd])
  have hACD : g {a,c,d}=0 := hdegree _ (by simp [hac,had,hcd])
  have hBCD : g {b,c,d}=0 := hdegree _ (by simp [hbc,hbd,hcd])
  have hABCD : g {a,b,c,d}=0 := hdegree _ (by simp [hab,hac,had,hbc,hbd,hcd])
  cases s <;> cases t <;> cases u <;> cases v <;>
    simp [select4,pick,quadratic4,bit,zeta_insert,zeta_empty,zeta_singleton,
      hab,hac,had,hbc,hbd,hcd,hABC,hABD,hACD,hBCD,hABCD] <;> ring

theorem no_induced_path (g : SetFunction V)
    (hdegree : ∀ C : Finset V, 2< C.card → g C=0)
    (hbit : ∀ S, IsBit (zeta g S))
    {a b c d : V} (hab : a≠ b) (hac : a≠ c) (had : a≠ d)
    (hbc : b≠ c) (hbd : b≠ d) (hcd : c≠ d)
    (hac0 : g {a,c}=0) (had0 : g {a,d}=0) (hbd0 : g {b,d}=0) :
    g {a,b} * g {c,d}=0 := by
  apply path_end_product_zero (g ∅) (g {a}) (g {b}) (g {c}) (g {d})
    (g {a,b}) (g {b,c}) (g {c,d})
  intro s t u v
  have hb := hbit (select4 a b c d s t u v)
  rw [zeta_select4 g hdegree hab hac had hbc hbd hcd, hac0,had0,hbd0] at hb
  exact hb

theorem no_three_leaf_star (g : SetFunction V)
    (hdegree : ∀ C : Finset V, 2< C.card → g C=0)
    (hbit : ∀ S, IsBit (zeta g S))
    {a b c d : V} (hab : a≠ b) (hac : a≠ c) (had : a≠ d)
    (hbc : b≠ c) (hbd : b≠ d) (hcd : c≠ d)
    (hbc0 : g {b,c}=0) (hbd0 : g {b,d}=0) (hcd0 : g {c,d}=0) :
    g {a,b}=0 ∨ g {a,c}=0 ∨ g {a,d}=0 := by
  apply star_three_zero (g ∅) (g {a}) (g {b}) (g {c}) (g {d})
    (g {a,b}) (g {a,c}) (g {a,d})
  intro s t u v
  have hb := hbit (select4 a b c d s t u v)
  rw [zeta_select4 g hdegree hab hac had hbc hbd hcd, hbc0,hbd0,hcd0] at hb
  exact hb

end GraphicalZonotopes.BooleanLinkRows

end
end
end BundlePart280

section BundlePart281
/- Source: Papers/GraphicalZonotopes/BooleanFourPartStructure.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanFourPartStructure
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {y : SetFunction V}

theorem clique_card_le_four (hG : G.CliqueFree 5) (D : Finset V)
    (hD : G.IsClique D) : D.card≤4 := by
  by_contra hn
  obtain ⟨E,hED,hE⟩ := exists_subset_card_eq (show 5≤ D.card by omega)
  exact hG E ⟨fun u hu v hv huv => hD (hED hu) (hED hv) huv,hE⟩

theorem edge_boolean
    (hb : ∀ u v,u≠ v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    {u v : V} (huv : u≠ v) (S : Finset V) :
    BooleanLinkRows.IsBit (zeta (edgeCoefficients y u v) S) := by
  rw [zeta_erase_of_containing_zero _ u (by intro C hC;simp [edgeCoefficients,hC])]
  rw [zeta_erase_of_containing_zero _ v (by intro C hC;simp [edgeCoefficients,hC])]
  rw [edgeCoefficients_zeta huv (by simp) (by simp)]
  exact hb u v huv _ (by simp) (by simp)

theorem edge_zero_of_nonadj (hy : CliqueSupported G y) (u v : V)
    {a b : V} (hab : a≠ b) (hn : ¬G.Adj a b) :
    edgeCoefficients y u v {a,b}=0 := by
  unfold edgeCoefficients
  split_ifs
  · exact hy.2.2 _ a b (by simp) (by simp) hab hn
  · rfl

/-- Two different extensions of a triangle in a K5-free graph are nonadjacent. -/
theorem nonadjacent_above_triangle (hG : G.CliqueFree 5)
    {T : Finset V} (hT : T.card=3) {a b : V}
    (ha : a∉T) (hb : b∉T) (hab : a≠ b)
    (hA : G.IsClique (insert a T : Finset V))
    (hB : G.IsClique (insert b T : Finset V)) : ¬G.Adj a b := by
  intro hadj
  have hcl : G.IsClique (insert a (insert b T) : Finset V) := by
    rw [coe_insert]
    change G.IsClique (insert a ((insert b T : Finset V) : Set V))
    apply hB.insert
    intro v hv hav
    rcases mem_insert.mp hv with rfl | hvT
    · exact hadj
    · exact hA (by simp) (by simp [hvT]) hav
  have hc := clique_card_le_four hG _ hcl
  rw [card_insert_of_notMem (by simp [hab,ha]),card_insert_of_notMem hb,hT] at hc
  omega

theorem nonadjacent_replacement (hG : G.CliqueFree 5)
    {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    {u x : V} (hu : u∈D) (hx : x∉D)
    (hcx : G.IsClique (insert x (D.erase u) : Finset V)) : ¬G.Adj u x := by
  apply nonadjacent_above_triangle hG (T := D.erase u)
    (by rw [card_erase_of_mem hu,hD]) (by simp)
    (fun h => hx (mem_of_mem_erase h)) (fun he => hx (he ▸ hu))
  · simpa only [insert_erase hu] using hcl
  · exact hcx

/-- Three nonzero tetrahedra cannot share one triangle. This is the literal
thinness obstruction and uses Boolean rows on all contexts. -/
theorem three_extensions_impossible (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠ v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    {T : Finset V} (hT : T.card=3) {x y' z : V}
    (hx : x∉T) (hy' : y'∉T) (hz : z∉T)
    (hxy : x≠ y') (hxz : x≠ z) (hyz : y'≠ z)
    (hX : y (insert x T)≠0) (hY : y (insert y' T)≠0)
    (hZ : y (insert z T)≠0) : False := by
  have hclX := hy.clique_of_nonzero hX
  have hclY := hy.clique_of_nonzero hY
  have hclZ := hy.clique_of_nonzero hZ
  have hnXY := nonadjacent_above_triangle hG hT hx hy' hxy hclX hclY
  have hnXZ := nonadjacent_above_triangle hG hT hx hz hxz hclX hclZ
  have hnYZ := nonadjacent_above_triangle hG hT hy' hz hyz hclY hclZ
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := card_eq_three.mp hT
  have hax : a≠ x := by intro h;exact hx (by simp [← h])
  have hay : a≠ y' := by intro h;exact hy' (by simp [← h])
  have haz : a≠ z := by intro h;exact hz (by simp [← h])
  have hbx : b≠ x := by intro h;exact hx (by simp [← h])
  have hby : b≠ y' := by intro h;exact hy' (by simp [← h])
  have hbz : b≠ z := by intro h;exact hz (by simp [← h])
  have hcx : c≠ x := by intro h;exact hx (by simp [← h])
  have hcy : c≠ y' := by intro h;exact hy' (by simp [← h])
  have hcz : c≠ z := by intro h;exact hz (by simp [← h])
  have hbad := BooleanLinkRows.no_three_leaf_star (edgeCoefficients y a b)
    (edgeCoefficients_degree_two hy (clique_card_le_four hG) hab)
    (edge_boolean hb hab) hcx hcy hcz hxy hxz hyz
    (edge_zero_of_nonadj hy a b hxy hnXY)
    (edge_zero_of_nonadj hy a b hxz hnXZ)
    (edge_zero_of_nonadj hy a b hyz hnYZ)
  have heX : insert a (insert b ({c,x} : Finset V))=insert x {a,b,c} := by
    ext v;simp [or_comm,or_left_comm,or_assoc]
  have heY : insert a (insert b ({c,y'} : Finset V))=insert y' {a,b,c} := by
    ext v;simp [or_comm,or_left_comm,or_assoc]
  have heZ : insert a (insert b ({c,z} : Finset V))=insert z {a,b,c} := by
    ext v;simp [or_comm,or_left_comm,or_assoc]
  simp only [edgeCoefficients,mem_insert,mem_singleton,hac,hax,hay,haz,hbc,hbx,hby,hbz,
    false_or,not_false_eq_true,and_self,if_true,heX,heY,heZ] at hbad
  exact hbad.elim hX (fun h => h.elim hY hZ)

/-- Two replacements in different positions complete to a fourth nonzero
tetrahedron. The two replacement vertices must be distinct. -/
theorem replacement_square (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠ v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    {D : Finset V} (hD : D.card=4) (hbase : y D≠0)
    {u v x y' : V} (hu : u∈D) (hv : v∈D) (huv : u≠ v)
    (hx : x∉D) (hy' : y'∉D)
    (hX : y (insert x (D.erase u))≠0) (hY : y (insert y' (D.erase v))≠0) :
    x≠ y' ∧ y (insert y' (insert x ((D.erase u).erase v)))≠0 := by
  have hcl := hy.clique_of_nonzero hbase
  have hclX := hy.clique_of_nonzero hX
  have hclY := hy.clique_of_nonzero hY
  have hnUX := nonadjacent_replacement hG hD hcl hu hx hclX
  have hnVY := nonadjacent_replacement hG hD hcl hv hy' hclY
  have hux : u≠ x := fun he => hx (he ▸ hu)
  have hvx : v≠ x := fun he => hx (he ▸ hv)
  have huy : u≠ y' := fun he => hy' (he ▸ hu)
  have hvy : v≠ y' := fun he => hy' (he ▸ hv)
  have hxy : x≠ y' := by
    intro he
    apply hnUX
    rw [he]
    exact hclY (mem_insert_of_mem (mem_erase.mpr ⟨huv,hu⟩)) (mem_insert_self _ _) huy
  have hEcard : ((D.erase u).erase v).card=2 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm huv,hv⟩),card_erase_of_mem hu,hD]
  obtain ⟨p,q,hpq,hE⟩ := card_eq_two.mp hEcard
  have hpE : p∈(D.erase u).erase v := by rw [hE];simp
  have hqE : q∈(D.erase u).erase v := by rw [hE];simp
  have hpD : p∈D := mem_of_mem_erase (mem_of_mem_erase hpE)
  have hqD : q∈D := mem_of_mem_erase (mem_of_mem_erase hqE)
  have hpu : p≠ u := ne_of_mem_erase (mem_of_mem_erase hpE)
  have hpv : p≠ v := ne_of_mem_erase hpE
  have hqu : q≠ u := ne_of_mem_erase (mem_of_mem_erase hqE)
  have hqv : q≠ v := ne_of_mem_erase hqE
  have hpx : p≠ x := fun he => hx (he ▸ hpD)
  have hqx : q≠ x := fun he => hx (he ▸ hqD)
  have hpy : p≠ y' := fun he => hy' (he ▸ hpD)
  have hqy : q≠ y' := fun he => hy' (he ▸ hqD)
  have hDrepr : insert u (insert v ({p,q} : Finset V))=D := by
    rw [← hE,insert_erase (mem_erase.mpr ⟨Ne.symm huv,hv⟩),insert_erase hu]
  have hDu : D.erase u=insert v {p,q} := by
    rw [← hDrepr];simp [huv,Ne.symm hpu,Ne.symm hqu]
  have hDv : D.erase v=insert u {p,q} := by
    ext w
    rw [← hDrepr]
    simp only [mem_erase,mem_insert,mem_singleton]
    constructor
    · rintro ⟨hwv,rfl | rfl | hw⟩
      · exact Or.inl rfl
      · exact False.elim (hwv rfl)
      · exact Or.inr hw
    · rintro (rfl | rfl | rfl)
      · exact ⟨huv,Or.inl rfl⟩
      · exact ⟨hpv,Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨hqv,Or.inr (Or.inr (Or.inr rfl))⟩
  have heX : insert p (insert q ({x,v} : Finset V))=insert x (D.erase u) := by
    rw [hDu];ext w;simp [or_comm,or_left_comm,or_assoc]
  have heY : insert p (insert q ({u,y'} : Finset V))=insert y' (D.erase v) := by
    rw [hDv];ext w;simp [or_comm,or_left_comm,or_assoc]
  have hnonX : edgeCoefficients y p q {x,v}≠0 := by
    simpa only [edgeCoefficients,mem_insert,mem_singleton,hpx,hpv,hqx,hqv,
      false_or,not_false_eq_true,and_self,if_true,heX] using hX
  have hnonY : edgeCoefficients y p q {u,y'}≠0 := by
    simpa only [edgeCoefficients,mem_insert,mem_singleton,hpu,hpy,hqu,hqy,
      false_or,not_false_eq_true,and_self,if_true,heY] using hY
  have hnonXY : edgeCoefficients y p q {x,y'}≠0 := by
    intro hzero
    have hm := BooleanLinkRows.no_induced_path (edgeCoefficients y p q)
      (edgeCoefficients_degree_two hy (clique_card_le_four hG) hpq)
      (edge_boolean hb hpq) (Ne.symm hvx) (Ne.symm hux) hxy (Ne.symm huv) hvy huy
      (edge_zero_of_nonadj hy p q (Ne.symm hux) (fun h => hnUX (G.adj_symm h)))
      hzero (edge_zero_of_nonadj hy p q hvy hnVY)
    exact (mul_ne_zero hnonX hnonY) hm
  refine ⟨hxy,?_⟩
  have heNew : insert p (insert q ({x,y'} : Finset V))=
      insert y' (insert x ((D.erase u).erase v)) := by
    rw [hE];ext w;simp [or_comm,or_left_comm,or_assoc]
  simpa only [edgeCoefficients,mem_insert,mem_singleton,hpx,hpy,hqx,hqy,
    false_or,not_false_eq_true,and_self,if_true,heNew] using hnonXY

end GraphicalZonotopes.BooleanFourPartStructure

end
end
end BundlePart281
