module

public import canonical_main.PalomarPart004
import all canonical_main.PalomarPart004
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

section BundlePart282
/- Source: Papers/GraphicalZonotopes/FourPartCompletion.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes.FourPartCompletion
open Finset Function

variable {V : Type*} [Fintype V] [DecidableEq V]

def vertices (v : Fin 4 → V) : Finset V := univ.image v

def Face (C : Finset (Finset V)) (v : Fin 4 → V) : Prop := vertices v ∈ C

def Thin (C : Finset (Finset V)) : Prop :=
  ∀ v, Injective v → Face C v → ∀ i x y,
    x ∉ vertices v → y ∉ vertices v →
    Face C (update v i x) → Face C (update v i y) → x=y

def SquareClosed (C : Finset (Finset V)) : Prop :=
  ∀ v, Injective v → Face C v → ∀ i j, i≠ j → ∀ x y,
    x ∉ vertices v → y ∉ vertices v →
    Face C (update v i x) → Face C (update v j y) →
    x≠ y ∧ Face C (update (update v i x) j y)

@[simp] theorem mem_vertices (v : Fin 4 → V) (x : V) :
    x ∈ vertices v ↔ ∃ i, v i=x := by simp [vertices]

theorem self_mem_vertices (v : Fin 4 → V) (i : Fin 4) : v i∈vertices v :=
  (mem_vertices v _).mpr ⟨i,rfl⟩

theorem vertices_card (v : Fin 4 → V) (hv : Injective v) : (vertices v).card=4 := by
  simp [vertices, card_image_of_injective _ hv]

theorem vertices_update (v : Fin 4 → V) (hv : Injective v) (i : Fin 4) (x : V) :
    vertices (update v i x)=insert x ((vertices v).erase (v i)) := by
  ext a
  simp only [mem_vertices,mem_insert,mem_erase]
  constructor
  · rintro ⟨j,hj⟩
    by_cases hji : j=i
    · subst j; exact Or.inl (by simpa using hj.symm)
    · right
      have hval : v j=a := by simpa [update_of_ne hji] using hj
      exact ⟨fun he => hji (hv (hval.trans he)),⟨j,hval⟩⟩
  · rintro (rfl | ⟨ha,j,hj⟩)
    · exact ⟨i,by simp⟩
    · refine ⟨j,?_⟩
      have hji : j≠ i := fun he => ha (by simpa [he] using hj.symm)
      simpa [update_of_ne hji] using hj

def rootParts (C : Finset (Finset V)) (v : Fin 4 → V) (i : Fin 4) : Finset V :=
  insert (v i) (univ.filter (fun x => x∉vertices v ∧ Face C (update v i x)))

@[simp] theorem mem_rootParts (C : Finset (Finset V)) (v : Fin 4 → V)
    (i : Fin 4) (x : V) :
    x∈rootParts C v i ↔ x=v i ∨ x∉vertices v ∧ Face C (update v i x) := by
  simp [rootParts]

theorem root_mem_part (C : Finset (Finset V)) (v : Fin 4 → V) (i : Fin 4) :
    v i∈rootParts C v i := (mem_rootParts _ _ _ _).mpr (Or.inl rfl)

theorem rootParts_small {C : Finset (Finset V)} (hthin : Thin C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v) (i : Fin 4) :
    (rootParts C v i).card=1 ∨ (rootParts C v i).card=2 := by
  let A := univ.filter (fun x => x∉vertices v ∧ Face C (update v i x))
  have hsub : A.card≤1 := card_le_one.mpr (by
    intro x hx y hy
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    exact hthin v hv hf i x y hx'.1 hy'.1 hx'.2 hy'.2)
  have hnot : v i∉A := by
    intro h
    exact (mem_filter.mp h).2.1 (self_mem_vertices v i)
  have hc : (rootParts C v i).card=A.card+1 := card_insert_of_notMem hnot
  omega

theorem rootParts_disjoint {C : Finset (Finset V)} (hsq : SquareClosed C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v) :
    ∀ i j, i≠ j → Disjoint (rootParts C v i) (rootParts C v j) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases (mem_rootParts _ _ _ _).mp hxi with rfl | ⟨hxi,hfi⟩
  · rcases (mem_rootParts _ _ _ _).mp hxj with he | ⟨hn,_⟩
    · exact hij (hv he)
    · exact hn (self_mem_vertices v i)
  · rcases (mem_rootParts _ _ _ _).mp hxj with rfl | ⟨hxj,hfj⟩
    · exact hxi (self_mem_vertices v j)
    · exact (hsq v hv hf i j hij x x hxi hxj hfi hfj).1 rfl

theorem injective_of_parts {A : Fin 4 → Finset V}
    (hA : ∀ i j, i≠ j → Disjoint (A i) (A j))
    {v : Fin 4 → V} (hv : ∀ i,v i∈A i) : Injective v := by
  intro i j he
  by_contra hij
  exact (disjoint_left.mp (hA i j hij)) (hv i) (by rw [he]; exact hv j)

def patch (v w : Fin 4 → V) (S : Finset (Fin 4)) (i : Fin 4) : V :=
  if i∈S then w i else v i

@[simp] theorem patch_empty (v w : Fin 4 → V) : patch v w ∅=v := by
  funext i; simp [patch]

theorem patch_insert (v w : Fin 4 → V) (S : Finset (Fin 4)) (i : Fin 4) :
    patch v w (insert i S)=update (patch v w S) i (w i) := by
  funext j
  by_cases hji : j=i <;> simp [patch,hji]

theorem patch_mem_parts {A : Fin 4 → Finset V} {v w : Fin 4 → V}
    (hv : ∀ i,v i∈A i) (hw : ∀ i,w i∈A i) (S : Finset (Fin 4)) :
    ∀ i,patch v w S i∈A i := by
  intro i
  by_cases hi : i∈S <;> simp [patch,hi,hv i,hw i]

theorem outside_patch {A : Fin 4 → Finset V}
    (hA : ∀ i j, i≠ j → Disjoint (A i) (A j))
    {v w : Fin 4 → V} (hv : ∀ i,v i∈A i) (hw : ∀ i,w i∈A i)
    (S : Finset (Fin 4)) {i : Fin 4} (hi : i∉S) (hne : w i≠ v i) :
    w i∉vertices (patch v w S) := by
  rintro hx
  obtain ⟨j,hj⟩ := (mem_vertices _ _).mp hx
  have hm := patch_mem_parts hv hw S j
  by_cases hij : i=j
  · subst j
    exact hne (by simpa [patch,hi] using hj.symm)
  · exact (disjoint_left.mp (hA i j hij)) (hw i) (hj ▸ hm)

/-- Every independent combination of the root's elementary replacements is
present. The proof transports each remaining replacement across a square. -/
theorem fill_product {C : Finset (Finset V)} (hsq : SquareClosed C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v)
    {w : Fin 4 → V} (hw : ∀ i,w i∈rootParts C v i) : Face C w := by
  let A := rootParts C v
  have hA : ∀ i j,i≠ j → Disjoint (A i) (A j) := rootParts_disjoint hsq hv hf
  have hvA : ∀ i,v i∈A i := root_mem_part C v
  let D : Finset (Fin 4) := univ.filter (fun i => w i≠ v i)
  have hD (i : Fin 4) : i∈D ↔ w i≠ v i := by simp [D]
  have hfill : ∀ S : Finset (Fin 4),S⊆D →
      Face C (patch v w S) ∧
      ∀ i∈D,i∉S → Face C (update (patch v w S) i (w i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨by simpa using hf,?_⟩
      intro i hi _
      have hn := (hD i).mp hi
      have hm := (mem_rootParts C v i (w i)).mp (hw i)
      simpa using (hm.resolve_left hn).2
    | @insert i S hi ih =>
      intro hSD
      have hS : S⊆D := fun j hj => hSD (mem_insert_of_mem hj)
      have hiD : i∈D := hSD (mem_insert_self _ _)
      obtain ⟨hface,hedge⟩ := ih hS
      have hnext := hedge i hiD hi
      refine ⟨by simpa [patch_insert] using hnext,?_⟩
      intro j hjD hj
      have hji : j≠ i := fun he => hj (by simp [he])
      have hjS : j∉S := fun hm => hj (mem_insert_of_mem hm)
      have hwi := outside_patch hA hvA hw S hi ((hD i).mp hiD)
      have hwj := outside_patch hA hvA hw S hjS ((hD j).mp hjD)
      have hinj := injective_of_parts hA (patch_mem_parts hvA hw S)
      have hsquare := (hsq _ hinj hface i j hji.symm (w i) (w j)
        hwi hwj hnext (hedge j hjD hjS)).2
      simpa [patch_insert] using hsquare
  have he : patch v w D=w := by
    funext i
    by_cases hi : w i=v i <;> simp [patch,D,hi]
  rw [← he]
  exact (hfill D (Subset.refl _)).1

theorem outside_of_parts {A : Fin 4 → Finset V}
    (hA : ∀ i j,i≠ j → Disjoint (A i) (A j))
    {v : Fin 4 → V} (hv : ∀ i,v i∈A i)
    {i : Fin 4} {x : V} (hx : x∈A i) (hne : x≠ v i) :
    x∉vertices v := by
  rintro hm
  obtain ⟨j,hj⟩ := (mem_vertices v x).mp hm
  by_cases hij : i=j
  · subst j; exact hne hj.symm
  · exact (disjoint_left.mp (hA i j hij)) hx (hj ▸ hv j)

def changed (v w : Fin 4 → V) : Finset (Fin 4) := univ.filter (fun i => w i≠ v i)

@[simp] theorem mem_changed (v w : Fin 4 → V) (i : Fin 4) :
    i∈changed v w ↔ w i≠ v i := by simp [changed]

theorem changed_update (v w : Fin 4 → V) (j : Fin 4) :
    changed v (update w j (v j))=(changed v w).erase j := by
  ext i
  by_cases hij : i=j <;> simp [changed,hij]

/-- Any new facet adjacent to the root cube stays within its four parts.
An alleged new vertex is transported back to the root by square closure. -/
theorem replacement_mem_part {C : Finset (Finset V)}
    (hthin : Thin C) (hsq : SquareClosed C)
    {v : Fin 4 → V} (hv : Injective v) (hf : Face C v)
    {w : Fin 4 → V} (hw : ∀ i,w i∈rootParts C v i)
    (i : Fin 4) (x : V) (hx : x∉vertices w)
    (hfx : Face C (update w i x)) : x∈rootParts C v i := by
  let A := rootParts C v
  have hA : ∀ i j,i≠ j → Disjoint (A i) (A j) := rootParts_disjoint hsq hv hf
  have hvA : ∀ i,v i∈A i := root_mem_part C v
  have hmain : ∀ n : ℕ,∀ w : Fin 4 → V,(changed v w).card=n →
      (∀ i,w i∈A i) → ∀ i x,x∉vertices w →
      Face C (update w i x) → x∈A i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hc hw i x hx hfx
      have hwi : Injective w := injective_of_parts hA hw
      have hfw : Face C w := fill_product hsq hv hf hw
      by_cases hival : w i=v i
      · by_cases he : w=v
        · subst w
          exact (mem_rootParts C v i x).mpr (Or.inr ⟨hx,hfx⟩)
        · obtain ⟨j,hj⟩ : ∃ j,w j≠ v j := by
            by_contra h
            push_neg at h
            exact he (funext h)
          have hij : i≠ j := by intro h; subst j; exact hj hival
          let w' := update w j (v j)
          have hw' : ∀ k,w' k∈A k := by
            intro k
            by_cases hkj : k=j
            · subst k; simpa [w'] using hvA j
            · simpa [w',update_of_ne hkj] using hw k
          have hvj : v j∉vertices w := outside_of_parts hA hw (hvA j) (Ne.symm hj)
          have hfw' : Face C w' := fill_product hsq hv hf hw'
          have hs := hsq w hwi hfw i j hij x (v j) hx hvj hfx hfw'
          have hx' : x∉vertices w' := by
            rw [show vertices w'=insert (v j) ((vertices w).erase (w j)) from
              vertices_update w hwi j (v j)]
            intro hm
            rcases mem_insert.mp hm with he | he
            · exact hs.1 he
            · exact hx (mem_of_mem_erase he)
          have hfx' : Face C (update w' i x) := by
            simpa only [w',update_comm hij] using hs.2
          have hlt : (changed v w').card< n := by
            rw [show changed v w'=(changed v w).erase j from changed_update v w j]
            rw [← hc]
            exact card_erase_lt_of_mem ((mem_changed v w j).mpr hj)
          exact ih _ hlt w' rfl hw' i x hx' hfx'
      · have hvi : v i∉vertices w := outside_of_parts hA hw (hvA i) (Ne.symm hival)
        have hback : Face C (update w i (v i)) := by
          apply fill_product hsq hv hf
          change ∀ j,update w i (v i) j∈A j
          intro j
          by_cases hji : j=i
          · subst j; simp only [update_self]; exact hvA i
          · rw [update_of_ne hji]; exact hw j
        have he := hthin w hwi hfw i x (v i) hx hvi hfx hback
        simpa [he] using hvA i
  exact hmain _ w rfl hw i x hx hfx

theorem adjacent_replacement {D E : Finset V}
    (hD : D.card=4) (hE : E.card=4) (hne : D≠ E)
    (hinter : 3≤(D∩E).card) :
    ∃ u∈D,∃ x,x∉D ∧ E=insert x (D.erase u) := by
  have hle : (D∩E).card≤4 := (card_le_card inter_subset_left).trans_eq hD
  have hne4 : (D∩E).card≠4 := by
    intro he
    have hDI : D∩E=D := eq_of_subset_of_card_le inter_subset_left (by omega)
    have hDE : D⊆E := by rw [← hDI]; exact inter_subset_right
    exact hne (eq_of_subset_of_card_le hDE (by omega))
  have hthree : (D∩E).card=3 := by omega
  have hdiffD : (D\E).card=1 := by
    have hh := card_sdiff_add_card_inter D E
    omega
  have hdiffE : (E\D).card=1 := by
    have hh := card_sdiff_add_card_inter E D
    rw [inter_comm E D] at hh
    omega
  obtain ⟨u,hu⟩ := card_eq_one.mp hdiffD
  obtain ⟨x,hx⟩ := card_eq_one.mp hdiffE
  have hum : u∈D\E := by rw [hu]; simp
  have hxm : x∈E\D := by rw [hx]; simp
  refine ⟨u,(mem_sdiff.mp hum).1,x,(mem_sdiff.mp hxm).2,?_⟩
  ext a
  constructor
  · intro ha
    by_cases haD : a∈D
    · apply mem_insert_of_mem
      exact mem_erase.mpr ⟨fun he => (mem_sdiff.mp hum).2 (he ▸ ha),haD⟩
    · have he : a=x := by
        have hm : a∈E\D := mem_sdiff.mpr ⟨ha,haD⟩
        rw [hx] at hm
        exact mem_singleton.mp hm
      exact mem_insert.mpr (Or.inl he)
  · intro ha
    rcases mem_insert.mp ha with rfl | ha
    · exact (mem_sdiff.mp hxm).1
    · by_contra hn
      have hm : a∈D\E := mem_sdiff.mpr ⟨mem_of_mem_erase ha,hn⟩
      rw [hu] at hm
      exact (mem_erase.mp ha).1 (mem_singleton.mp hm)

theorem exists_vertices {D : Finset V} (hD : D.card=4) :
    ∃ v : Fin 4 → V,Injective v ∧ vertices v=D := by
  let e : Fin 4 ≃ D := (Finset.equivFinOfCardEq hD).symm
  let v : Fin 4 → V := fun i => (e i).val
  refine ⟨v,Subtype.val_injective.comp e.injective,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i,rfl⟩ := (mem_vertices v x).mp hx
    exact (e i).property
  · intro hx
    apply (mem_vertices v x).mpr
    exact ⟨e.symm ⟨x,hx⟩,congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩

/-- A connected family of tetrahedra with thin facets and commuting
facet replacements is exactly the Cartesian product of four parts of size
one or two. No bound on the ambient finite vertex type is assumed. -/
theorem cartesian_completion (C : Finset (Finset V))
    (hfour : ∀ D∈C,D.card=4) (hne : C.Nonempty)
    (hconn : (tetrahedronGraph C).Preconnected)
    (hthin : Thin C) (hsq : SquareClosed C) :
    ∃ A : Fin 4 → Finset V,
      (∀ i,(A i).card=1 ∨ (A i).card=2) ∧
      (∀ i j,i≠ j → Disjoint (A i) (A j)) ∧
      ∀ D : Finset V,D∈C ↔ ∃ w : Fin 4 → V,(∀ i,w i∈A i) ∧ D=univ.image w := by
  obtain ⟨D₀,hD₀⟩ := hne
  obtain ⟨v,hv,hev⟩ := exists_vertices (hfour D₀ hD₀)
  have hf : Face C v := by simpa [Face,hev] using hD₀
  let A := rootParts C v
  have hA : ∀ i j,i≠ j → Disjoint (A i) (A j) := rootParts_disjoint hsq hv hf
  let P : {D : Finset V // D∈C} → Prop :=
    fun D => ∃ w : Fin 4 → V,(∀ i,w i∈A i) ∧ D.val=vertices w
  have hroot : P ⟨D₀,hD₀⟩ := ⟨v,root_mem_part C v,hev.symm⟩
  have hstep : ∀ D E : {D : Finset V // D∈C},
      (tetrahedronGraph C).Adj D E → P D → P E := by
    intro D E hadj hPD
    obtain ⟨w,hw,hew⟩ := hPD
    have hwi : Injective w := injective_of_parts hA hw
    have hDE : D.val≠ E.val := fun he => hadj.1 (Subtype.ext he)
    obtain ⟨u,hu,x,hx,he⟩ := adjacent_replacement
      (hfour _ D.property) (hfour _ E.property) hDE hadj.2
    rw [hew] at hu hx he
    obtain ⟨i,hi⟩ := (mem_vertices w u).mp hu
    subst u
    have hrep : E.val=vertices (update w i x) := by
      rw [vertices_update w hwi i x]
      exact he
    have hfx : Face C (update w i x) := by
      rw [Face,← hrep]
      exact E.property
    have hxi := replacement_mem_part hthin hsq hv hf hw i x hx hfx
    refine ⟨update w i x,?_,hrep⟩
    intro j
    change update w i x j∈A j
    by_cases hji : j=i
    · subst j; simp only [update_self]; exact hxi
    · rw [update_of_ne hji]; exact hw j
  refine ⟨A,rootParts_small hthin hv hf,hA,?_⟩
  intro D
  constructor
  · intro hD
    have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (hconn ⟨D₀,hD₀⟩ ⟨D,hD⟩)
    have hclosed : ∀ E : {E : Finset V // E∈C},
        Relation.ReflTransGen (tetrahedronGraph C).Adj ⟨D₀,hD₀⟩ E → P E := by
      intro E hr
      induction hr with
      | refl => exact hroot
      | tail _ ha ih => exact hstep _ _ ha ih
    exact hclosed ⟨D,hD⟩ hr
  · rintro ⟨w,hw,rfl⟩
    exact fill_product hsq hv hf hw

end GraphicalZonotopes.FourPartCompletion

end
end
end BundlePart282

section BundlePart283
/- Source: Papers/GraphicalZonotopes/UnitFamilyStructure.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.UnitFamilyStructure
open Finset Function FourPartCompletion BooleanFourPartStructure
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {y : SetFunction V} {C : Finset (Finset V)}

theorem update_injective (v : Fin 4 → V) (hv : Injective v)
    (i : Fin 4) (x : V) (hx : x∉vertices v) : Injective (update v i x) := by
  intro a b he
  by_cases hai : a=i
  · subst a
    by_cases hbi : b=i
    · exact hbi.symm
    · have hxb : x=v b := by simpa [update_of_ne hbi] using he
      exact False.elim (hx (hxb.symm ▸ self_mem_vertices v b))
  · by_cases hbi : b=i
    · subst b
      have hax : v a=x := by simpa [update_of_ne hai] using he
      exact False.elim (hx (hax ▸ self_mem_vertices v a))
    · apply hv
      simpa [update_of_ne hai,update_of_ne hbi] using he

theorem thin_of_boolean (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠ v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    (hC : ∀ D,D∈C ↔ D.card=4 ∧ y D≠0) : Thin C := by
  intro v hv hf i x z hx hz hX hZ
  by_contra hxz
  have hvi := self_mem_vertices v i
  have hD := vertices_card v hv
  have hT : ((vertices v).erase (v i)).card=3 := by rw [card_erase_of_mem hvi,hD]
  have hbase : y (insert (v i) ((vertices v).erase (v i)))≠0 := by
    rw [insert_erase hvi]
    exact ((hC _).mp hf).2
  have hx' : x∉(vertices v).erase (v i) := fun h => hx (mem_of_mem_erase h)
  have hz' : z∉(vertices v).erase (v i) := fun h => hz (mem_of_mem_erase h)
  have hix : v i≠ x := fun he => hx (he ▸ hvi)
  have hiz : v i≠ z := fun he => hz (he ▸ hvi)
  have hX' : y (insert x ((vertices v).erase (v i)))≠0 := by
    have h := ((hC _).mp hX).2
    rwa [vertices_update v hv i x] at h
  have hZ' : y (insert z ((vertices v).erase (v i)))≠0 := by
    have h := ((hC _).mp hZ).2
    rwa [vertices_update v hv i z] at h
  exact three_extensions_impossible hG hy hb hT (by simp) hx' hz' hix hiz hxz hbase hX' hZ'

theorem squareClosed_of_boolean (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠ v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    (hC : ∀ D,D∈C ↔ D.card=4 ∧ y D≠0) : SquareClosed C := by
  intro v hv hf i j hij x z hx hz hX hZ
  have hvi := self_mem_vertices v i
  have hvj := self_mem_vertices v j
  have hvij : v i≠ v j := fun he => hij (hv he)
  have hX' : y (insert x ((vertices v).erase (v i)))≠0 := by
    have h := ((hC _).mp hX).2
    rwa [vertices_update v hv i x] at h
  have hZ' : y (insert z ((vertices v).erase (v j)))≠0 := by
    have h := ((hC _).mp hZ).2
    rwa [vertices_update v hv j z] at h
  obtain ⟨hxz,hnew⟩ := replacement_square hG hy hb (vertices_card v hv)
    ((hC _).mp hf).2 hvi hvj hvij hx hz hX' hZ'
  refine ⟨hxz,?_⟩
  have hvx : Injective (update v i x) := update_injective v hv i x hx
  have hznew : z∉vertices (update v i x) := by
    rw [vertices_update v hv i x]
    intro h
    rcases mem_insert.mp h with he | he
    · exact hxz he.symm
    · exact hz (mem_of_mem_erase he)
  apply (hC _).mpr
  refine ⟨vertices_card _ (update_injective _ hvx j z hznew),?_⟩
  have hvjx : v j≠ x := fun he => hx (he ▸ hvj)
  have he : vertices (update (update v i x) j z)=
      insert z (insert x (((vertices v).erase (v i)).erase (v j))) := by
    rw [vertices_update _ hvx j z,vertices_update v hv i x]
    simp only [update_of_ne (Ne.symm hij),erase_insert_of_ne (Ne.symm hvjx)]
  rwa [he]

/-- Exactly the two local structural properties required by the global
Cartesian completion theorem, for the actual nonzero coefficient family. -/
theorem structure_of_boolean (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠ v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    (hC : ∀ D,D∈C ↔ D.card=4 ∧ y D≠0) : Thin C ∧ SquareClosed C :=
  ⟨thin_of_boolean hG hy hb hC,squareClosed_of_boolean hG hy hb hC⟩

end GraphicalZonotopes.UnitFamilyStructure

end
end
end BundlePart283

section BundlePart284
/- Source: Papers/GraphicalZonotopes/UnitLatticeGeometry.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace UnitLatticeGeometry
open Finset RefinedTriangleComponents
open scoped BigOperators Pointwise

/-- Integer lower-support values give integer elemental slacks in every context. -/
theorem integer_delta {V : Type*} [Fintype V] [DecidableEq V]
    {z : SetFunction V} (hz : IntegerValued z) (u v : V) (S : Finset V) :
    ∃ k : ℤ, delta z u v S = (k : ℝ) := by
  obtain ⟨a,ha⟩ := hz (insert u (insert v S))
  obtain ⟨b,hb⟩ := hz S
  obtain ⟨c,hc⟩ := hz (insert u S)
  obtain ⟨d,hd⟩ := hz (insert v S)
  refine ⟨a+b-c-d,?_⟩
  simp only [delta,ha,hb,hc,hd,Int.cast_add,Int.cast_sub]
  ring

theorem integer_between_zero_one {x : ℝ} (hx : ∃ k : ℤ,x=(k : ℝ))
    (h0 : 0≤ x) (h1 : x≤1) : x=0 ∨ x=1 := by
  obtain ⟨k,rfl⟩ := hx
  have hk0 : (0 : ℤ)≤ k := by exact_mod_cast h0
  have hk1 : k≤(1 : ℤ) := by exact_mod_cast h1
  have hk : k=0 ∨ k=1 := by omega
  rcases hk with rfl | rfl <;> norm_num

/-- Exact coefficient data extracted from the actual polytope hypotheses of
Theorem 9.5. These are proved conclusions, not assumptions added to that theorem. -/
structure CoefficientModel {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Set (Fin n → ℝ)) where
  function : SetFunction (Fin n)
  extreme : ExtremeSupermodular function
  integer : IntegerValued (mobius function)
  supported : CliqueSupported G (mobius function)
  boolean : ∀ u v : Fin n,u≠ v → ∀ S : Finset (Fin n),u∉S → v∉S →
    delta (zeta (mobius function)) u v S=0 ∨ delta (zeta (mobius function)) u v S=1
  nonempty : (family (mobius function)).Nonempty
  connected : (tetrahedronGraph (family (mobius function))).Preconnected
  covers : (family (mobius function)).biUnion id=univ
  directions : actualDirectionGraph Q=edgeGraph (mobius function)

/-- Unit dilation forces every integral elemental slack to be Boolean. The
proof retains the given ambient graph, all vertices, and the original translation. -/
theorem coefficient_model {n : ℕ} (hn : 4≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := (hQ.lowerSupport_integerValued hi.1).normalize
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : z≠0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan,_root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hconn,hcover,hactual⟩ := full_refined_support hn hG hext hzg hdim
  refine ⟨⟨z,hext,hzi.mobius,(mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩,
    ?_,hF,hconn,hcover,?_⟩⟩
  · intro u v huv S hu hv
    rw [zeta_mobius]
    by_cases hadj : G.Adj u v
    · apply integer_between_zero_one (integer_delta hzi u v S)
        (hzs.elemental u v huv S hu hv)
      rw [delta_normalize f huv hu hv]
      exact hbound u v huv hadj S hu hv
    · exact Or.inl (hzg u v huv hadj S hu hv)
  · rw [actualDirectionGraph_normalize,← hbody] at hactual
    exact hactual

/-- The ordinary polytope definition of indecomposability gives exactly the
same coefficient model; the necessary GP presentation is derived from the sum. -/
theorem coefficient_model_polytopal {n : ℕ} (hn : 4≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hnz,hsz,hbody,_,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hnz,hsz,hbody⟩
  exact coefficient_model hn hG hQ ((minkowskiIndecomposable_iff_polytopal hgp).mpr hi) hd
    ⟨R,hR,hcR,hnR,he⟩

end UnitLatticeGeometry
end GraphicalZonotopes

end
end
end BundlePart284

section BundlePart285
/- Source: Papers/GraphicalZonotopes/LatticeTranslation.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open RefinedTriangleComponents
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lattice polytopes are allowed arbitrary real translations. -/
def TranslatedLatticePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ (P : Set (V → ℝ)) (t : V → ℝ), LatticePolytope P ∧ Q=t+ᵥP

theorem lowerSupport_vadd {Q : Set (V → ℝ)} (hQ : IsCompact Q)
    (hne : Q.Nonempty) (t : V → ℝ) :
    lowerSupport (t+ᵥQ)=modular t+lowerSupport Q := by
  rw [← singleton_add_eq_vadd,lowerSupport_add isCompact_singleton hQ (Set.singleton_nonempty _) hne]
  congr 1
  funext S
  simp [lowerSupport,modular]

theorem TranslatedLatticePolytope.compact {Q : Set (V → ℝ)}
    (hQ : TranslatedLatticePolytope Q) : IsCompact Q := by
  obtain ⟨P,t,hP,rfl⟩ := hQ
  rw [← singleton_add_eq_vadd]
  exact isCompact_singleton.add hP.compact

theorem TranslatedLatticePolytope.convex {Q : Set (V → ℝ)}
    (hQ : TranslatedLatticePolytope Q) : Convex ℝ Q := by
  obtain ⟨P,t,hP,rfl⟩ := hQ
  exact hP.convex.vadd t

theorem TranslatedLatticePolytope.integer_normalize_lowerSupport {Q : Set (V → ℝ)}
    (hQ : TranslatedLatticePolytope Q) (hne : Q.Nonempty) :
    IntegerValued (normalize (lowerSupport Q)) := by
  obtain ⟨P,t,hP,rfl⟩ := hQ
  have hnP : P.Nonempty := by
    obtain ⟨x,y,hy,hxy⟩ := hne
    exact ⟨y,hy⟩
  rw [lowerSupport_vadd hP.compact hnP,normalize_add,normalize_modular,zero_add]
  exact (hP.lowerSupport_integerValued hnP).normalize

theorem threeTree_integral_normalized_four_coefficients {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : IsCompact Q) (hcQ : Convex ℝ Q)
    (hint : IntegerValued (normalize (lowerSupport Q)))
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0< a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    ∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ hcQ hi.1 hR hcR hnR ha.le he
  let f:=lowerSupport Q
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : normalize f≠0 := by
    intro he
    rw [he,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular (normalize f) := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  have hnormgraph : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hall := (threeTree_all_tetrahedra_nonzero hn hG hext hnormgraph hdim).2
  have hint := hint.mobius
  intro C hC
  obtain ⟨k,hk⟩ := hint C
  have hc : C.card=4 := (mem_filter.mp hC).2.1
  rw [mobius_four_normalize hc] at hk
  refine ⟨k,?_,hk⟩
  intro hzero
  have hc : C.card=4 := (mem_filter.mp hC).2.1
  have hnonzero := hall C hC
  rw [mobius_four_normalize hc] at hnonzero
  exact hnonzero (by simpa [hzero] using hk)

theorem threeTree_integral_normalized_lower_bound {n : ℕ} (hn : 6≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : IsCompact Q) (hcQ : Convex ℝ Q)
    (hint : IntegerValued (normalize (lowerSupport Q)))
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0< a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    2≤ a ∧ (∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k) ∧
      ∀ e∈edgeFamily G,
        (Int.ceil ((1/2 : ℝ)*
          ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius (lowerSupport Q) C|) : ℝ)≤ a := by
  classical
  have hcoeff := threeTree_integral_normalized_four_coefficients (by omega : 4≤ n) hG hQ hcQ hint hi hd ha hsum
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ hcQ hi.1 hR hcR hnR ha.le he
  let f:=lowerSupport Q
  let z:=normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := hint
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

/-- Theorem 9.1 in the full translation-invariant range explicitly stated in
its introduction: every real translate of a lattice polytope is permitted.
All tetrahedral coefficients and every edgewise ceiling retain their literal
values on the original translated body. -/
theorem threeTree_translated_lattice_lower_bound {n : ℕ} (hn : 6≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
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
  exact threeTree_integral_normalized_lower_bound hn hG hQ.compact hQ.convex
    (hQ.integer_normalize_lowerSupport hi.1)
    ((minkowskiIndecomposable_iff_polytopal hgp).mpr hi) hd ha ⟨R,hR,hcR,hnR,he⟩

end GraphicalZonotopes

end
end
end BundlePart285

section BundlePart286
/- Source: Papers/GraphicalZonotopes/UnitTranslatedGeometry.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace UnitLatticeGeometry
open Finset RefinedTriangleComponents
open scoped BigOperators Pointwise

/-- The unit-lattice coefficient model extends to arbitrary real translations.
Its Möbius coefficients and Boolean rows come from integral normalized support. -/
theorem coefficient_model_translated {n : ℕ} (hn : 4≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  let f := lowerSupport Q
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := hQ.integer_normalize_lowerSupport hi.1
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : z≠0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan,_root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hconn,hcover,hactual⟩ := full_refined_support hn hG hext hzg hdim
  refine ⟨⟨z,hext,hzi.mobius,(mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩,
    ?_,hF,hconn,hcover,?_⟩⟩
  · intro u v huv S hu hv
    rw [zeta_mobius]
    by_cases hadj : G.Adj u v
    · apply integer_between_zero_one (integer_delta hzi u v S)
        (hzs.elemental u v huv S hu hv)
      rw [delta_normalize f huv hu hv]
      exact hbound u v huv hadj S hu hv
    · exact Or.inl (hzg u v huv hadj S hu hv)
  · rw [actualDirectionGraph_normalize,← hbody] at hactual
    exact hactual

/-- The ordinary polytope definition of indecomposability gives exactly the
same coefficient model; the necessary GP presentation is derived from the sum. -/
theorem coefficient_model_translated_polytopal {n : ℕ} (hn : 4≤ n) {G : SimpleGraph (Fin n)}
    (hG : G.CliqueFree 5) {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    Nonempty (CoefficientModel G Q) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  have he' : Q+R=(1 : ℝ) • graphicalZonotope G := by simpa using he
  obtain ⟨hnz,hsz,hbody,_,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR (by norm_num : (0 : ℝ)≤1) he'
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hnz,hsz,hbody⟩
  exact coefficient_model_translated hn hG hQ ((minkowskiIndecomposable_iff_polytopal hgp).mpr hi) hd
    ⟨R,hR,hcR,hnR,he⟩

end UnitLatticeGeometry
end GraphicalZonotopes

end
end
end BundlePart286

section BundlePart287
/- Source: Papers/GraphicalZonotopes/FourPartGraphRecognition.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace FourPartGraphRecognition
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

structure FourParts (V : Type*) [Fintype V] [DecidableEq V] where
  parts : Fin 4 → Finset V
  nonempty : ∀ i,(parts i).Nonempty
  disjoint : ∀ i j,i≠ j → Disjoint (parts i) (parts j)
  covers : ∀ v : V,∃ i,v∈parts i

namespace FourParts
variable (P : FourParts V)

def color (v : V) : Fin 4 := Classical.choose (P.covers v)

theorem color_mem (v : V) : v∈P.parts (P.color v) := Classical.choose_spec (P.covers v)

theorem color_eq_of_mem {v : V} {i : Fin 4} (hv : v∈P.parts i) : P.color v=i := by
  by_contra hi
  exact Finset.disjoint_left.mp (P.disjoint _ _ hi) (P.color_mem v) hv

def chosen (i : Fin 4) : V := Classical.choose (P.nonempty i)

theorem chosen_mem (i : Fin 4) : P.chosen i∈P.parts i := Classical.choose_spec (P.nonempty i)

theorem different_of_mem {i j : Fin 4} (hij : i≠ j) {u v : V}
    (hu : u∈P.parts i) (hv : v∈P.parts j) : u≠ v := by
  intro he
  exact Finset.disjoint_left.mp (P.disjoint i j hij) hu (he.symm ▸ hv)

def transversal (u v : V) : Fin 4 → V :=
  fun i => if i=P.color u then u else if i=P.color v then v else P.chosen i

theorem transversal_mem (u v : V) (i : Fin 4) : P.transversal u v i∈P.parts i := by
  unfold transversal
  split_ifs with hi hj
  · simpa only [hi] using P.color_mem u
  · simpa only [hj] using P.color_mem v
  · exact P.chosen_mem i

theorem transversal_left (u v : V) : P.transversal u v (P.color u)=u := by
  simp [transversal]

theorem transversal_right {u v : V} (h : P.color u≠ P.color v) :
    P.transversal u v (P.color v)=v := by simp [transversal,Ne.symm h]

theorem choice_injective (w : Fin 4 → V) (hw : ∀ i,w i∈P.parts i) :
    Function.Injective w := by
  intro i j he
  by_contra hij
  exact P.different_of_mem hij (hw i) (hw j) he

def coordinateEquiv : (Σ i : Fin 4,Fin ((P.parts i).card)) ≃ V := by
  let e (i : Fin 4) : Fin ((P.parts i).card) ≃ {v : V // v∈P.parts i} :=
    Fintype.equivOfCardEq (by simp)
  let f : (Σ i : Fin 4,Fin ((P.parts i).card)) → V := fun x => (e x.1 x.2).1
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hi : i=j := by
      have hci := P.color_eq_of_mem (e i a).2
      have hcj := P.color_eq_of_mem (e j b).2
      exact hci.symm.trans ((congrArg P.color he).trans hcj)
    subst j
    have hab : a=b := (e i).injective (Subtype.ext he)
    subst b
    rfl
  · intro v
    refine ⟨⟨P.color v,(e (P.color v)).symm ⟨v,P.color_mem v⟩⟩,?_⟩
    exact congrArg Subtype.val ((e (P.color v)).apply_symm_apply _)

theorem coordinateEquiv_mem (x : Σ i : Fin 4,Fin ((P.parts i).card)) :
    P.coordinateEquiv x∈P.parts x.1 := by
  change (Fintype.equivOfCardEq _ x.2 : {v : V // v∈P.parts x.1}).1∈P.parts x.1
  exact (Fintype.equivOfCardEq _ x.2 : {v : V // v∈P.parts x.1}).2

theorem card_eq : Fintype.card V=∑ i : Fin 4,(P.parts i).card := by
  rw [← Fintype.card_congr P.coordinateEquiv,Fintype.card_sigma]
  simp

theorem card_le_eight (hsize : ∀ i,(P.parts i).card≤2) : Fintype.card V≤8 := by
  rw [P.card_eq]
  calc
    ∑ i : Fin 4,(P.parts i).card ≤ ∑ _i : Fin 4,2 := sum_le_sum (fun i _ => hsize i)
    _ = 8 := by norm_num

end FourParts

def unionGraph (F : Finset (Finset V)) : SimpleGraph V where
  Adj u v := u≠ v ∧ ∃ D∈F,u∈D ∧ v∈D
  symm := ⟨by rintro u v ⟨hne,D,hD,hu,hv⟩;exact ⟨Ne.symm hne,D,hD,hv,hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def ProductFamily (F : Finset (Finset V)) (A : Fin 4 → Finset V) : Prop :=
  ∀ D : Finset V,D∈F ↔ ∃ w : Fin 4 → V,(∀ i,w i∈A i) ∧ D=univ.image w

variable (P : FourParts V) (F : Finset (Finset V))

theorem unionGraph_adj_iff (hprod : ProductFamily F P.parts) (u v : V) :
    (unionGraph F).Adj u v ↔ P.color u≠ P.color v := by
  constructor
  · rintro ⟨hne,D,hD,hu,hv⟩ he
    obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
    obtain ⟨i,_,hi⟩ := mem_image.mp hu
    obtain ⟨j,_,hj⟩ := mem_image.mp hv
    have hci : P.color u=i := P.color_eq_of_mem (hi ▸ hw i)
    have hcj : P.color v=j := P.color_eq_of_mem (hj ▸ hw j)
    have hij : i=j := hci.symm.trans (he.trans hcj)
    rw [← hij] at hj
    exact hne (hi.symm.trans hj)
  · intro hne
    refine ⟨fun he => hne (congrArg P.color he),univ.image (P.transversal u v),?_,?_,?_⟩
    · exact (hprod _).mpr ⟨P.transversal u v,P.transversal_mem u v,rfl⟩
    · exact mem_image.mpr ⟨P.color u,mem_univ _,P.transversal_left u v⟩
    · exact mem_image.mpr ⟨P.color v,mem_univ _,P.transversal_right hne⟩

theorem unionGraph_le {G : SimpleGraph V} (hcl : ∀ D∈F,G.IsClique D) : unionGraph F≤ G := by
  rintro u v ⟨hne,D,hD,hu,hv⟩
  exact hcl D hD hu hv hne

/-- A K5-free supergraph of a full four-part product has no additional edge:
any within-part edge, together with one vertex from each other part, is a K5. -/
theorem ambient_eq {G : SimpleGraph V} (hprod : ProductFamily F P.parts)
    (hcl : ∀ D∈F,G.IsClique D)
    (hfour : ∀ D : Finset V,G.IsClique D → D.card≤4) : unionGraph F=G := by
  apply le_antisymm (unionGraph_le F hcl)
  intro u v huv
  apply (unionGraph_adj_iff P F hprod u v).mpr
  intro hecolor
  let w := P.transversal u u
  have hw : ∀ i,w i∈P.parts i := P.transversal_mem u u
  let D := univ.image w
  have hDF : D∈F := (hprod D).mpr ⟨w,hw,rfl⟩
  have hDc : D.card=4 := by
    dsimp only [D]
    rw [card_image_of_injective _ (P.choice_injective w hw)]
    simp
  have hvD : v∉D := by
    intro hv
    obtain ⟨i,_,hi⟩ := mem_image.mp hv
    have hci : P.color v=i := P.color_eq_of_mem (hi ▸ hw i)
    have hii : i=P.color u := hci.symm.trans hecolor.symm
    have hwi : w i=u := by simpa only [hii] using P.transversal_left u u
    exact G.ne_of_adj huv (hwi.symm.trans hi)
  have hclE : G.IsClique ((insert v D : Finset V) : Set V) := by
    intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl | hxD
    · rcases mem_insert.mp hy with rfl | hyD
      · exact False.elim (hxy rfl)
      · obtain ⟨i,_,hi⟩ := mem_image.mp hyD
        by_cases hii : i=P.color u
        · have hyu : y=u := hi.symm.trans (by simpa only [hii] using P.transversal_left u u)
          simpa only [hyu] using G.adj_symm huv
        · apply unionGraph_le F hcl
          apply (unionGraph_adj_iff P F hprod x y).mpr
          have hcy : P.color y=i := P.color_eq_of_mem (hi ▸ hw i)
          rw [hcy,← hecolor]
          exact Ne.symm hii
    · rcases mem_insert.mp hy with rfl | hyD
      · apply G.adj_symm
        obtain ⟨i,_,hi⟩ := mem_image.mp hxD
        by_cases hii : i=P.color u
        · have hxu : x=u := hi.symm.trans (by simpa only [hii] using P.transversal_left u u)
          simpa only [hxu] using G.adj_symm huv
        · apply unionGraph_le F hcl
          apply (unionGraph_adj_iff P F hprod y x).mpr
          have hcx : P.color x=i := P.color_eq_of_mem (hi ▸ hw i)
          rw [hcx,← hecolor]
          exact Ne.symm hii
      · exact hcl D hDF hxD hyD hxy
  have hb := hfour (insert v D) hclE
  rw [card_insert_of_notMem hvD,hDc] at hb
  omega

theorem graphIso {G : SimpleGraph V} (heq : unionGraph F=G)
    (hprod : ProductFamily F P.parts) :
    Nonempty (G ≃g fourPartite (fun i => (P.parts i).card)) := by
  let e := P.coordinateEquiv
  have iso : fourPartite (fun i => (P.parts i).card) ≃g G :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        rw [← heq,unionGraph_adj_iff P F hprod]
        rw [P.color_eq_of_mem (P.coordinateEquiv_mem x),P.color_eq_of_mem (P.coordinateEquiv_mem y)]
        rfl }
  exact ⟨iso.symm⟩

/-- The global family conclusion produces the precise ambient graph
classification, including its vertex bound and graph isomorphism. -/
theorem recognize {G : SimpleGraph V} (hprod : ProductFamily F P.parts)
    (hsize : ∀ i,(P.parts i).card=1 ∨ (P.parts i).card=2)
    (hcl : ∀ D∈F,G.IsClique D)
    (hfour : ∀ D : Finset V,G.IsClique D → D.card≤4) :
    unionGraph F=G ∧ Fintype.card V≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  have heq := ambient_eq P F hprod hcl hfour
  exact ⟨heq,P.card_le_eight (fun i => by rcases hsize i with h | h <;> omega),
    (fun i => (P.parts i).card),hsize,graphIso P F heq hprod⟩

/-- A Cartesian family covering every vertex gives the needed literal
partition without adding an ambient coverage assumption. -/
theorem parts_of_cover (A : Fin 4 → Finset V)
    (hne : ∀ i,(A i).Nonempty) (hdis : ∀ i j,i≠ j → Disjoint (A i) (A j))
    (hprod : ProductFamily F A) (hcover : F.biUnion id=univ) :
    ∃ P : FourParts V,P.parts=A := by
  refine ⟨⟨A,hne,hdis,?_⟩,rfl⟩
  intro v
  have hv : v∈F.biUnion id := by rw [hcover];exact mem_univ _
  obtain ⟨D,hD,hv⟩ := mem_biUnion.mp hv
  obtain ⟨w,hw,rfl⟩ := (hprod D).mp hD
  obtain ⟨i,_,hi⟩ := mem_image.mp hv
  exact ⟨i,hi ▸ hw i⟩

end FourPartGraphRecognition
end GraphicalZonotopes

end
end
end BundlePart287

section BundlePart288
/- Source: Papers/GraphicalZonotopes/UnitLatticeClassification.lean -/







@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace GraphicalZonotopes
open Finset RefinedTriangleComponents

namespace UnitLatticeGeometry

/-- The actual coefficient model has a Cartesian tetrahedral family. Its
coverage forces the entire ambient graph to be the corresponding four-partite
graph; no extra ambient edges or unused vertices remain. -/
theorem CoefficientModel.classification {n : ℕ} {G : SimpleGraph (Fin n)}
    {Q : Set (Fin n → ℝ)} (M : CoefficientModel G Q) (hG : G.CliqueFree 5) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  let F := family (mobius M.function)
  have hmem : ∀ D,D∈F ↔ D.card=4 ∧ mobius M.function D≠0 := mem_family _
  obtain ⟨hthin,hsquare⟩ := UnitFamilyStructure.structure_of_boolean
    hG M.supported M.boolean hmem
  obtain ⟨A,hsize,hdis,hprod⟩ := FourPartCompletion.cartesian_completion F
    (fun D hD => ((hmem D).mp hD).1) M.nonempty M.connected hthin hsquare
  have hneA : ∀ i,(A i).Nonempty := by
    intro i
    apply card_pos.mp
    rcases hsize i with he | he <;> omega
  obtain ⟨P,hP⟩ := FourPartGraphRecognition.parts_of_cover F A hneA hdis hprod M.covers
  have hproduct : FourPartGraphRecognition.ProductFamily F P.parts := by
    rw [hP]
    exact hprod
  have hsizeP : ∀ i,(P.parts i).card=1 ∨ (P.parts i).card=2 := by
    rw [hP]
    exact hsize
  have hcl : ∀ D∈F,G.IsClique D := by
    intro D hD
    exact M.supported.clique_of_nonzero ((hmem D).mp hD).2
  obtain ⟨he,hcard,hiso⟩ := FourPartGraphRecognition.recognize P F hproduct hsizeP hcl
    (BooleanFourPartStructure.clique_card_le_four hG)
  have hedge : edgeGraph (mobius M.function)=FourPartGraphRecognition.unionGraph F := rfl
  exact ⟨M.directions.trans (hedge.trans he),by simpa using hcard,hiso⟩

end UnitLatticeGeometry

/-- Theorem 9.5, in its complete unit-summand range: all n≥4, the given
K5-free ambient graph, full dimension, and actual lattice polytopes. -/
theorem unit_lattice_classification : Targets.UnitLatticeClassification := by
  intro n hn G hG Q hQ hi hd hsum
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model hn hG hQ hi hd hsum
  exact M.classification hG

/-- The same theorem with the traditional polytope-only definition of
Minkowski indecomposability, whose equivalence is derived from the actual sum. -/
theorem unit_lattice_classification_polytopal {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5)
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model_polytopal hn hG hQ hi hd hsum
  exact M.classification hG

/-- Arbitrary real translations of lattice polytopes obey the same exact
classification, with every conclusion stated on the original translated body. -/
theorem unit_translated_lattice_classification {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5)
    {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model_translated hn hG hQ hi hd hsum
  exact M.classification hG

theorem unit_translated_lattice_classification_polytopal {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5)
    {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (graphicalZonotope G)) :
    actualDirectionGraph Q=G ∧ n≤8 ∧
      ∃ a : Fin 4 → ℕ,(∀ i,a i=1 ∨ a i=2) ∧ Nonempty (G ≃g fourPartite a) := by
  obtain ⟨M⟩ := UnitLatticeGeometry.coefficient_model_translated_polytopal hn hG hQ hi hd hsum
  exact M.classification hG

end GraphicalZonotopes

end
end
end BundlePart288

section BundlePart289
/- Source: Papers/GraphicalZonotopes/UnitLatticeDilation.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace UnitLatticeDilation
open Finset
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A lattice summand at any real dilation strictly below two is already a
summand of the unscaled graphical zonotope. This is a consequence of integral
support values, not an integrality hypothesis on the dilation parameter. -/
theorem unit_summand_of_lt_two {G : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : LatticePolytope Q) (hnQ : Q.Nonempty) {a : ℝ} (ha : 0< a) (ha2 : a<2)
    (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    IsMinkowskiSummand Q (graphicalZonotope G) := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hn,hs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hnQ hR hcR hnR ha.le he
  rw [hbody]
  have hsum1 : IsMinkowskiSummand (basePolytope (lowerSupport Q))
      ((1 : ℝ) • graphicalZonotope G) := by
    apply (isMinkowskiSummand_graphical_iff hn hs (by norm_num : (0 : ℝ)≤1)).mpr
    refine ⟨hgraph,?_⟩
    intro u v huv hadj S hu hv
    obtain ⟨k,hk⟩ := UnitLatticeGeometry.integer_delta (hQ.lowerSupport_integerValued hnQ) u v S
    have hklt : (k : ℝ)<2 := by rw [← hk];exact (hbound u v huv hadj S hu hv).trans_lt ha2
    have hklt' : k<(2 : ℤ) := by exact_mod_cast hklt
    rw [hk]
    exact_mod_cast (show k≤(1 : ℤ) by omega)
  simpa only [one_smul] using hsum1

/-- Every nontrivial full-dimensional lattice summand requires dilation at
least one, even when its complement and dilation parameter are arbitrary real. -/
theorem dilation_at_least_one {n : ℕ} (hn : 2≤ n) {G : SimpleGraph (Fin n)}
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q) (hnQ : Q.Nonempty)
    (hd : FullDimension Q) {a : ℝ} (ha : 0< a)
    (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) : 1≤ a := by
  by_contra hn1
  have ha1 : a<1 := lt_of_not_ge hn1
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hnQ hR hcR hnR ha.le he
  let f := lowerSupport Q
  have hzero : ∀ u v : Fin n,u≠ v → ∀ S : Finset (Fin n),u∉S → v∉S → delta f u v S=0 := by
    intro u v huv S hu hv
    by_cases hadj : G.Adj u v
    · obtain ⟨k,hk⟩ := UnitLatticeGeometry.integer_delta (hQ.lowerSupport_integerValued hnQ) u v S
      have hk0 : (0 : ℝ)≤ k := by rw [← hk];exact hfs.elemental u v huv S hu hv
      have hk1 : (k : ℝ)<1 := by rw [← hk];exact (hbound u v huv hadj S hu hv).trans_lt ha1
      have hk0' : (0 : ℤ)≤ k := by exact_mod_cast hk0
      have hk1' : k<(1 : ℤ) := by exact_mod_cast hk1
      have hkeq : k=0 := by omega
      simpa only [hkeq,Int.cast_zero] using hk
    · exact hgraph u v huv hadj S hu hv
  have hz : normalize f=0 := by
    apply normalized_zero_elemental_eq_zero (normalize_translationNormalized hfn)
    intro u v huv S hu hv
    rw [delta_normalize f huv hu hv]
    exact hzero u v huv S hu hv
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  rw [hz,basePolytope_zero] at hdim
  have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
      (⊥ : Submodule ℝ (Fin n → ℝ)) :=
    _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
  rw [hspan,_root_.finrank_bot] at hdim
  omega

end UnitLatticeDilation
end GraphicalZonotopes

end
end
end BundlePart289

section BundlePart290
/- Source: Papers/GraphicalZonotopes/OptimalK5FreeDilation.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- Corollary 9.12: exact attainment and the universal lower bound for every
K5-free ambient graph, all n≥4, and every positive real dilation. -/
theorem optimal_k5_free_dilation : Targets.OptimalK5FreeDilation := by
  intro n hn
  refine ⟨optimal_k5_free_dilation_attained hn,?_⟩
  intro G hG a ha hsum
  obtain ⟨Q,hQ,hi,hd,hs⟩ := hsum
  by_cases hn8 : n≤8
  · simpa only [if_pos hn8] using
      UnitLatticeDilation.dilation_at_least_one (by omega : 2≤ n) hQ hi.1 hd ha hs
  · rw [if_neg hn8]
    by_contra hn2
    have ha2 : a<2 := lt_of_not_ge hn2
    have hunit := UnitLatticeDilation.unit_summand_of_lt_two hQ hi.1 ha ha2 hs
    exact hn8 (unit_lattice_classification n hn G hG Q hQ hi hd hunit).2.1

/-- The universal bound in the ordinary polytopal convention. The actual
summand equation supplies the generalized-permutahedron presentation needed
for the equivalence of the two indecomposability conventions. -/
theorem optimal_k5_free_dilation_lower_bound_polytopal {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : G.CliqueFree 5) {a : ℝ} (ha : 0< a)
    {Q : Set (Fin n → ℝ)} (hQ : LatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    (if n≤8 then (1 : ℝ) else 2)≤ a := by
  obtain ⟨R,hR,hRc,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,_,_⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hRc hnR ha.le he
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hfn,hfs,hbody⟩
  have hi' : MinkowskiIndecomposable Q :=
    (minkowskiIndecomposable_iff_polytopal hgp).mpr hi
  exact (optimal_k5_free_dilation n hn).2 G hG a ha
    ⟨Q,hQ,hi',hd,⟨R,hR,hRc,hnR,he⟩⟩

end GraphicalZonotopes

end
end
end BundlePart290

section BundlePart291
/- Source: Papers/GraphicalZonotopes/SmallCliqueDimension.lean -/





/-! # The low-dimensional cases of the partial-three-tree spectrum -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise
namespace GraphicalZonotopes
open Finset
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Triangle-free graphical cones have only segment rays. This uses the
complete nonnegative edge-coefficient decomposition, not a dimension premise. -/
theorem triangleFree_extreme_dimension_le_one {G : SimpleGraph V}
    (hG : G.CliqueFree 3) {z : SetFunction V} (hz : ExtremeSupermodular z)
    (hg : Graphical G z) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) ≤ 1 := by
  let y := mobius z
  have hy : CliqueSupported G y := (mobius_cliqueSupported_iff G z).mpr ⟨hz.1,hg⟩
  have hzero : ∀ C : Finset V,C.card ≠ 2 → y C = 0 := by
    intro C hC
    apply coefficient_zero_of_not_clique hy C
    rintro ⟨hc,hcl⟩
    have hc3 : 3 ≤ C.card := by omega
    obtain ⟨T,hTC,hT⟩ := exists_subset_card_eq hc3
    exact hG T ⟨fun u hu v hv huv => hcl (hTC hu) (hTC hv) huv,hT⟩
  have hnonneg : ∀ C : Finset V,0 ≤ y C := by
    intro C
    by_cases hc : C.card = 2
    · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hc
      have hh := hz.2.1.elemental u v huv ∅ (by simp) (by simp)
      rw [← zeta_mobius z,delta_zeta_empty _ huv] at hh
      exact hh
    · rw [hzero C hc]
  let p : Finset V → SetFunction V := fun C => y C • setMonomial C
  have hp : ∀ C,TranslationNormalized (p C) ∧ Supermodular (p C) := by
    intro C
    refine ⟨?_,(setMonomial_supermodular C).smul (hnonneg C)⟩
    by_cases hc : C.card = 2
    · have hn := setMonomial_translationNormalized (C := C) (by omega)
      exact ⟨by change y C*setMonomial C ∅=0; rw [hn.1,mul_zero],
        fun v => by change y C*setMonomial C {v}=0; rw [hn.2 v,mul_zero]⟩
    · simp only [p,hzero C hc,zero_smul]
      exact ⟨rfl,fun _ => rfl⟩
  have hsum : (∑ C,p C) = z := by
    rw [← zeta_mobius z,zeta_eq_sum_monomials]
  have hex : ∃ C,p C ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz.2.2.1 (hsum.symm.trans (sum_eq_zero (fun C _ => h C)))
  obtain ⟨C,hC⟩ := hex
  obtain ⟨a,ha,hscale⟩ := hz.finite_summand p (fun C => (hp C).1)
    (fun C => (hp C).2) hsum hC
  have hc : C.card = 2 := by
    by_contra hc
    exact hC (by simp only [p,hzero C hc,zero_smul])
  have hdep : DependsOn (p C) C := (setMonomial_dependsOn C).smul _
  rw [hscale] at hdep
  have hb := finrank_vectorSpan_le_support hz.1 hz.2.1
    (DependsOn.of_smul (ne_of_gt ha) hdep)
  simpa only [hc] using hb

theorem triangleFree_summand_dimension_le_one {G : SimpleGraph V}
    (hG : G.CliqueFree 3) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ 1 := by
  obtain ⟨z,hzs,hze,hd⟩ := weak_summand_extreme_or_zero hQ hi hw
  rw [hd]
  rcases hze with hz | hz
  · rw [hz,basePolytope_zero,_root_.vectorSpan_singleton,finrank_bot]
    omega
  · exact triangleFree_extreme_dimension_le_one hG hz z.2.2

theorem triangleFree_maximum_dimension {G : SimpleGraph V} (hG : G.CliqueFree 3)
    (hE : ∃ u v : V,G.Adj u v) : maximumIndecomposableDimension G = 1 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact triangleFree_summand_dimension_le_one hG hQ hi hw
  · obtain ⟨u,v,huv⟩ := hE
    have hcl : G.IsClique ({u,v} : Finset V) := by
      intro a ha b hb hab
      change a ∈ ({u,v} : Finset V) at ha
      change b ∈ ({u,v} : Finset V) at hb
      simp only [mem_insert,mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact huv
      · exact huv.symm
      · exact False.elim (hab rfl)
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness
      (by rw [card_pair huv.ne]) hcl
    have hb := dimension_le_maximum hQ.finitePolytope hi hw
    rw [hd,card_pair huv.ne] at hb
    exact hb

theorem edgeless_maximum_dimension {G : SimpleGraph V}
    (hG : ∀ u v : V,¬G.Adj u v) : maximumIndecomposableDimension G = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro d ⟨Q,hQ,hi,hw,hd⟩
  obtain ⟨z,hzs,hze,hqdim⟩ := weak_summand_extreme_or_zero hQ hi hw
  have hz : z.1 = 0 := normalized_zero_elemental_eq_zero z.2.1
    (fun u v huv S hu hv => z.2.2 u v huv (hG u v) S hu hv)
  rw [hz,basePolytope_zero,_root_.vectorSpan_singleton,finrank_bot] at hqdim
  omega

theorem partial_threeTree_no_tetrahedron_dimension_le_two {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : tetrahedra G = ∅)
    {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    Module.finrank ℝ (vectorSpan ℝ Q) ≤ 2 := by
  by_contra hd
  have hd3 : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) := by omega
  obtain ⟨U,hU,ha,ht,hA,hD⟩ := partial_threeTree_polytope_support hG hQ hi hw hd3
  obtain ⟨C,hC⟩ := ht.tetrahedra_nonempty
  have hc := tetrahedra_mono (inducedOn_le G U) hC
  rw [hK] at hc
  exact notMem_empty C hc

theorem partial_threeTree_triangle_maximum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (hK : tetrahedra G = ∅)
    (hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T) :
    maximumIndecomposableDimension G = 2 := by
  apply le_antisymm
  · apply csSup_le'
    rintro d ⟨Q,hQ,hi,hw,hd⟩
    rw [← hd]
    exact partial_threeTree_no_tetrahedron_dimension_le_two hG hK hQ hi hw
  · obtain ⟨T,hT,hcl⟩ := hT
    obtain ⟨Q,hQ,hi,hw,hd⟩ := clique_simplex_witness (by omega) hcl
    have hb := dimension_le_maximum hQ.finitePolytope hi hw
    rw [hd,hT] at hb
    exact hb

/-- The complete piecewise dimension formula of Corollary 6.8. -/
def partialThreeTreeDimension (G : SimpleGraph V) : ℕ :=
  if (tetrahedra G).Nonempty then maximumAdmissibleCliqueCount G+2
  else if ∃ T : Finset V,T.card = 3 ∧ G.IsClique T then 2
  else if ∃ u v : V,G.Adj u v then 1 else 0

theorem partial_threeTree_piecewise_maximum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) :
    maximumIndecomposableDimension G = partialThreeTreeDimension G := by
  unfold partialThreeTreeDimension
  by_cases hK : (tetrahedra G).Nonempty
  · rw [if_pos hK]
    exact partial_threeTree_maximum_dimension hG hK
  · rw [if_neg hK]
    have hKe : tetrahedra G = ∅ := not_nonempty_iff_eq_empty.mp hK
    by_cases hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T
    · rw [if_pos hT]
      exact partial_threeTree_triangle_maximum hG hKe hT
    · rw [if_neg hT]
      have hcf : G.CliqueFree 3 := fun T h => hT ⟨T,h.card_eq,h.isClique⟩
      by_cases hE : ∃ u v : V,G.Adj u v
      · rw [if_pos hE]
        exact triangleFree_maximum_dimension hcf hE
      · rw [if_neg hE]
        exact edgeless_maximum_dimension (fun u v huv => hE ⟨u,v,huv⟩)

/-- The full positive spectrum, including graphs with no tetrahedron. -/
theorem partial_threeTree_full_dimension_spectrum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (d : ℕ) (hd : 1 ≤ d)
    (hmax : d ≤ maximumIndecomposableDimension G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hK : (tetrahedra G).Nonempty
  · apply partial_threeTree_dimension_spectrum hG hK d hd
    rwa [partial_threeTree_maximum_dimension hG hK] at hmax
  · have hKe : tetrahedra G = ∅ := not_nonempty_iff_eq_empty.mp hK
    by_cases hT : ∃ T : Finset V,T.card = 3 ∧ G.IsClique T
    · rw [partial_threeTree_triangle_maximum hG hKe hT] at hmax
      obtain ⟨T,hT,hcl⟩ := hT
      obtain ⟨C,hCT,hC⟩ := exists_subset_card_eq (s := T) (n := d+1) (by omega)
      obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness (by omega : 2 ≤ C.card)
        (fun u hu v hv huv => hcl (hCT hu) (hCT hv) huv)
      exact ⟨Q,hQ,hi,hw,by omega⟩
    · have hcf : G.CliqueFree 3 := fun T h => hT ⟨T,h.card_eq,h.isClique⟩
      by_cases hE : ∃ u v : V,G.Adj u v
      · rw [triangleFree_maximum_dimension hcf hE] at hmax
        have hd1 : d = 1 := by omega
        obtain ⟨u,v,huv⟩ := hE
        have hcl : G.IsClique ({u,v} : Finset V) := by
          intro a ha b hb hab
          change a ∈ ({u,v} : Finset V) at ha
          change b ∈ ({u,v} : Finset V) at hb
          simp only [mem_insert,mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact False.elim (hab rfl)
          · exact huv
          · exact huv.symm
          · exact False.elim (hab rfl)
        obtain ⟨Q,hQ,hi,hw,hqdim⟩ := clique_simplex_witness
          (by rw [card_pair huv.ne]) hcl
        refine ⟨Q,hQ,hi,hw,?_⟩
        simpa only [card_pair huv.ne,hd1] using hqdim
      · have hdim := edgeless_maximum_dimension (fun u v huv => hE ⟨u,v,huv⟩)
        omega

end GraphicalZonotopes

end
end
end BundlePart291

section BundlePart292
/- Source: Papers/GraphicalZonotopes/PartialThreeTreePaperStatements.lean -/





/-! # Finite-graph formulations of Corollaries 6.6--6.8

An ordering of the finite vertex set is chosen inside each statement. It is
used only by the geometric coordinate machinery and is not an extra graph
hypothesis. The support and spectrum statements use ordinary polytopal
Minkowski indecomposability, with its equivalence proved for actual weak
summands before invoking the core results.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Pointwise
namespace GraphicalZonotopes

/-- Corollary 6.6 on every finite vertex type, with the actual direction
graph induced on its active coordinate set and no order assumption. -/
theorem partial_threeTree_support_classification_polytopal_finite
    {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), IsPartialThreeTree G → ∀ H : SimpleGraph V,
      (∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) ∧ actualDirectionGraph Q = H) ↔
      ∃ U : Finset V, H = inducedOn G U ∧ ThreeTreeOn U H ∧ Admissible H := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  intro G hG H
  constructor
  · rintro ⟨Q,hQ,hi,hw,hd,ha⟩
    exact (partial_threeTree_support_classification hG H).mp
      ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi,hw,hd,ha⟩
  · intro h
    obtain ⟨Q,hQ,hi,hw,hd,ha⟩ :=
      (partial_threeTree_support_classification hG H).mpr h
    exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ hw).mp hi,hw,hd,ha⟩

/-- Corollary 6.8's complete piecewise maximum on arbitrary finite graphs:
`M(G)+2`, two, one, or zero according to tetrahedra, triangles, and edges. -/
theorem partial_threeTree_piecewise_maximum_finite {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), IsPartialThreeTree G →
      maximumIndecomposableDimension G = partialThreeTreeDimension G := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  exact fun G hG => partial_threeTree_piecewise_maximum hG

/-- Every positive dimension up to the sharp maximum occurs on every
partial three-tree, with an actual lattice polytope and the ordinary
polytopal indecomposability convention. -/
theorem partial_threeTree_full_dimension_spectrum_polytopal_finite
    {V : Type*} [Fintype V] :
    letI : LinearOrder V := Separator.finiteVertexOrder V;
    ∀ (G : SimpleGraph V), IsPartialThreeTree G → ∀ d : ℕ,
      1 ≤ d → d ≤ maximumIndecomposableDimension G →
      ∃ Q : Set (V → ℝ), LatticePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  letI : LinearOrder V := Separator.finiteVertexOrder V
  intro G hG d hd hmax
  obtain ⟨Q,hQ,hi,hw,hD⟩ := partial_threeTree_full_dimension_spectrum hG d hd hmax
  exact ⟨Q,hQ,(weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,hw,hD⟩

end GraphicalZonotopes

end
end
end BundlePart292

section BundlePart293
/- Source: Papers/GraphicalZonotopes/PathPaperStatement.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace Path
open scoped BigOperators

/-- Equation (3.1) with subtraction in the real numbers, exactly as in the
paper. The lower bound on n justifies the natural-subtraction cast used by
the uniform finite-window definition. -/
theorem polytope_defining_equations_real {n : ℕ} (hn : 4 ≤ n) :
    polytope n = {x : Fin n → ℝ | subsetSum x Finset.univ = (n : ℝ)-2 ∧
      ∀ S, setFunction n S ≤ subsetSum x S} := by
  simpa only [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_ofNat] using
    polytope_defining_equations n

/-- The same literal statement in ordinary finite-sum notation. -/
theorem polytope_defining_equations_sums {n : ℕ} (hn : 4 ≤ n) :
    polytope n = {x : Fin n → ℝ | (∑ i, x i) = (n : ℝ)-2 ∧
      ∀ S : Finset (Fin n), setFunction n S ≤ ∑ i ∈ S, x i} := by
  simpa only [subsetSum] using polytope_defining_equations_real hn

end Path
end GraphicalZonotopes

end
end
end BundlePart293

section BundlePart294
/- Source: Papers/GraphicalZonotopes/PathBooleanStatement.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators

/-- The indicator of a triple is the product of its three membership bits,
even if some of the displayed vertices coincide. -/
theorem setMonomial_three_membershipBits {V : Type*} [DecidableEq V]
    (a b c : V) (S : Finset V) :
    setMonomial {a,b,c} S =
      membershipBit S a * membershipBit S b * membershipBit S c := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S <;>
    simp [setMonomial,membershipBit,Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb,hc]

/-- The analogous exact identity for the four-vertex term. -/
theorem setMonomial_four_membershipBits {V : Type*} [DecidableEq V]
    (a b c d : V) (S : Finset V) :
    setMonomial {a,b,c,d} S =
      membershipBit S a * membershipBit S b * membershipBit S c * membershipBit S d := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
    by_cases hc : c ∈ S <;> by_cases hd : d ∈ S <;>
    simp [setMonomial,membershipBit,Finset.insert_subset_iff,Finset.singleton_subset_iff,ha,hb,hc,hd]

namespace Path

/-- The displayed Boolean-product formula preceding equation (3.1), with
the paper's labels 1,...,n represented by the zero-based labels of Fin n. -/
def booleanFormula (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  (∑ i : Fin (n-2), integerBit S (i.val : ℤ) *
    integerBit S ((i.val : ℤ)+1) * integerBit S ((i.val : ℤ)+2)) +
  (∑ i : Fin (n-3), integerBit S (i.val : ℤ) *
    integerBit S ((i.val : ℤ)+2) * integerBit S ((i.val : ℤ)+3)) -
  (∑ i : Fin (n-3), integerBit S (i.val : ℤ) *
    integerBit S ((i.val : ℤ)+1) * integerBit S ((i.val : ℤ)+2) *
      integerBit S ((i.val : ℤ)+3))

/-- The original coefficient construction and the paper's membership-bit
polynomial agree at every subset and every path length. -/
theorem setFunction_eq_booleanFormula (n : ℕ) : setFunction n = booleanFormula n := by
  funext S
  have h012 (i : Fin (n-2)) :
      setMonomial (window n i.val {0,1,2}) S =
        integerBit S (i.val : ℤ) * integerBit S ((i.val : ℤ)+1) *
          integerBit S ((i.val : ℤ)+2) := by
    rw [window_triple_eq
      (window_index_bound (n := n) (p := 2) i (by decide : 0 ≤ 2))
      (window_index_bound (n := n) (p := 2) i (by decide : 1 ≤ 2))
      (window_index_bound (n := n) (p := 2) i (by decide : 2 ≤ 2)),
      setMonomial_three_membershipBits]
    simp only [membershipBit_vertex,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
  have h023 (i : Fin (n-3)) :
      setMonomial (window n i.val {0,2,3}) S =
        integerBit S (i.val : ℤ) * integerBit S ((i.val : ℤ)+2) *
          integerBit S ((i.val : ℤ)+3) := by
    rw [window_triple_eq
      (window_index_bound (n := n) (p := 3) i (by decide : 0 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 2 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 3 ≤ 3)),
      setMonomial_three_membershipBits]
    simp only [membershipBit_vertex,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
  have h0123 (i : Fin (n-3)) :
      setMonomial (window n i.val {0,1,2,3}) S =
        integerBit S (i.val : ℤ) * integerBit S ((i.val : ℤ)+1) *
          integerBit S ((i.val : ℤ)+2) * integerBit S ((i.val : ℤ)+3) := by
    rw [window_quad_eq
      (window_index_bound (n := n) (p := 3) i (by decide : 0 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 1 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 2 ≤ 3))
      (window_index_bound (n := n) (p := 3) i (by decide : 3 ≤ 3)),
      setMonomial_four_membershipBits]
    simp only [membershipBit_vertex,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
  have he := congrFun (setFunction_expansion n) S
  simpa only [Pi.add_apply,Pi.sub_apply,Finset.sum_apply,h012,h023,h0123,
    booleanFormula] using he

/-- The complete defining equations using ordinary finite sums and the
literal membership-bit polynomial. -/
theorem polytope_boolean_defining_equations {n : ℕ} (hn : 4 ≤ n) :
    polytope n = {x : Fin n → ℝ | (∑ i, x i) = (n : ℝ)-2 ∧
      ∀ S : Finset (Fin n), booleanFormula n S ≤ ∑ i ∈ S, x i} := by
  rw [polytope_defining_equations_sums hn,setFunction_eq_booleanFormula]

end Path
end GraphicalZonotopes

end
end
end BundlePart294

section BundlePart295
/- Source: Papers/GraphicalZonotopes/PathJoinPolynomial.lean -/








/-!
# The endpoint-corrected path-join polynomial

The parameter `n` means that the path has `n+2` vertices. Thus every path
length in Appendix B is included. The ambient vertex set has `n+4`
vertices, with hubs 0,1 and path vertices 2,...,n+3.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

abbrev Vertex (n : ℕ) := Fin (n+4)
def hubA (n : ℕ) : Vertex n := ⟨0,by omega⟩
def hubB (n : ℕ) : Vertex n := ⟨1,by omega⟩
def vertex {n : ℕ} (i : Fin (n+2)) : Vertex n := ⟨i.val+2,by omega⟩

@[simp] theorem hubA_ne_hubB (n : ℕ) : hubA n ≠ hubB n := by
  simp [hubA,hubB,Fin.ext_iff]
@[simp] theorem hubB_ne_hubA (n : ℕ) : hubB n ≠ hubA n := Ne.symm (hubA_ne_hubB n)
@[simp] theorem vertex_ne_hubA {n : ℕ} (i : Fin (n+2)) : vertex i ≠ hubA n := by
  intro h
  have hv := congrArg Fin.val h
  change i.val+2=0 at hv
  omega
@[simp] theorem vertex_ne_hubB {n : ℕ} (i : Fin (n+2)) : vertex i ≠ hubB n := by
  simp [vertex,hubB,Fin.ext_iff]
@[simp] theorem hubA_ne_vertex {n : ℕ} (i : Fin (n+2)) : hubA n ≠ vertex i :=
  Ne.symm (vertex_ne_hubA i)
@[simp] theorem hubB_ne_vertex {n : ℕ} (i : Fin (n+2)) : hubB n ≠ vertex i :=
  Ne.symm (vertex_ne_hubB i)
@[simp] theorem vertex_inj {n : ℕ} {i j : Fin (n+2)} : vertex i=vertex j ↔ i=j := by
  simp [vertex,Fin.ext_iff]
@[simp] theorem vertex_left_ne_right {n : ℕ} (i : Fin (n+1)) :
    vertex i.castSucc ≠ vertex i.succ := by simp [vertex,Fin.ext_iff]
@[simp] theorem vertex_right_ne_left {n : ℕ} (i : Fin (n+1)) :
    vertex i.succ ≠ vertex i.castSucc := Ne.symm (vertex_left_ne_right i)

theorem vertex_cases {n : ℕ} (v : Vertex n) :
    v=hubA n ∨ v=hubB n ∨ ∃ i : Fin (n+2),v=vertex i := by
  by_cases ha : v.val=0
  · exact Or.inl (Fin.ext ha)
  by_cases hb : v.val=1
  · exact Or.inr (Or.inl (Fin.ext hb))
  refine Or.inr (Or.inr ⟨⟨v.val-2,by omega⟩,?_⟩)
  apply Fin.ext
  simp only [vertex]
  omega

/-- The literal graph K₂ * P_(n+2), with its labelled hubs and path. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj u v := u≠ v ∧ (u.val<2 ∨ v.val<2 ∨ u.val+1=v.val ∨ v.val+1=u.val)
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1,by tauto⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance (n : ℕ) : DecidableRel (graph n).Adj := fun u v =>
  inferInstanceAs (Decidable (u≠ v ∧
    (u.val<2 ∨ v.val<2 ∨ u.val+1=v.val ∨ v.val+1=u.val)))

@[simp] theorem graph_hubA {n : ℕ} {v : Vertex n} :
    (graph n).Adj (hubA n) v ↔ hubA n≠ v := by simp [graph,hubA]
@[simp] theorem graph_hubB {n : ℕ} {v : Vertex n} :
    (graph n).Adj (hubB n) v ↔ hubB n≠ v := by simp [graph,hubB]
@[simp] theorem graph_vertices {n : ℕ} (i j : Fin (n+2)) :
    (graph n).Adj (vertex i) (vertex j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
  change (vertex i≠ vertex j ∧
    (i.val+2<2 ∨ j.val+2<2 ∨ i.val+2+1=j.val+2 ∨ j.val+2+1=i.val+2)) ↔ _
  rw [Ne,vertex_inj]
  simp only [Fin.ext_iff]
  omega

/-- Every clique of cardinality at least two has exactly one of these
coordinate shapes: the hub edge, a spoke/hub triangle, or a path edge
with any subset of its two hubs. -/
abbrev Slot (n : ℕ) := Unit ⊕ (Fin 3 × Fin (n+2)) ⊕ (Fin 4 × Fin (n+1))

def clique {n : ℕ} : Slot n → Finset (Vertex n)
  | .inl _ => {hubA n,hubB n}
  | .inr (.inl (r,i)) =>
    if r=0 then {hubA n,vertex i}
    else if r=1 then {hubB n,vertex i}
    else {hubA n,hubB n,vertex i}
  | .inr (.inr (r,i)) =>
    if r=0 then {vertex i.castSucc,vertex i.succ}
    else if r=1 then {hubA n,vertex i.castSucc,vertex i.succ}
    else if r=2 then {hubB n,vertex i.castSucc,vertex i.succ}
    else {hubA n,hubB n,vertex i.castSucc,vertex i.succ}

theorem clique_card_ge_two {n : ℕ} (i : Slot n) : 2≤(clique i).card := by
  rcases i with u | ⟨r,i⟩ | ⟨r,i⟩
  · simp [clique]
  · fin_cases r <;> simp [clique]
  · fin_cases r <;> simp [clique,Finset.card_pair (vertex_left_ne_right i)]

theorem clique_isClique {n : ℕ} (i : Slot n) : (graph n).IsClique (clique i) := by
  have insA {S : Finset (Vertex n)} (h : (graph n).IsClique S) :
      (graph n).IsClique (insert (hubA n) S : Finset (Vertex n)) := by
    simpa only [Finset.coe_insert] using
      h.insert (fun v hv hav => graph_hubA.mpr hav)
  have insB {S : Finset (Vertex n)} (h : (graph n).IsClique S) :
      (graph n).IsClique (insert (hubB n) S : Finset (Vertex n)) := by
    simpa only [Finset.coe_insert] using
      h.insert (fun v hv hbv => graph_hubB.mpr hbv)
  have one (v : Vertex n) : (graph n).IsClique ({v} : Finset (Vertex n)) := by
    simpa only [Finset.coe_singleton] using (graph n).isClique_singleton v
  have pair (j : Fin (n+1)) :
      (graph n).IsClique ({vertex j.castSucc,vertex j.succ} : Finset (Vertex n)) := by
    rw [Finset.coe_pair,SimpleGraph.isClique_pair]
    intro hj
    apply (graph_vertices _ _).mpr
    exact Or.inl rfl
  rcases i with w | ⟨r,i⟩ | ⟨r,i⟩
  · exact insA (one (hubB n))
  · fin_cases r
    · exact insA (one (vertex i))
    · exact insB (one (vertex i))
    · exact insA (insB (one (vertex i)))
  · fin_cases r
    · exact pair i
    · exact insA (pair i)
    · exact insB (pair i)
    · exact insA (insB (pair i))

def coefficient (n : ℕ) : Slot n → ℝ
  | .inl _ => ((n+2)/2 : ℕ)
  | .inr (.inl (r,i)) =>
    if r=0 then 1
    else if r=1 then (if i=0 then 0 else 1)
    else if i=0 then 0 else -1
  | .inr (.inr (r,i)) =>
    if r=0 then 1
    else if r=1 then (if i.val%2=0 then -1 else 0)
    else if r=2 then (if i.val%2=0 then 0 else -1)
    else 1

def setFunction (n : ℕ) : SetFunction (Vertex n) :=
  FiniteMonomial.polynomial clique (coefficient n)

theorem normalized (n : ℕ) : TranslationNormalized (setFunction n) :=
  FiniteMonomial.polynomial_normalized clique clique_card_ge_two _

theorem graphical (n : ℕ) : Graphical (graph n) (setFunction n) :=
  FiniteMonomial.polynomial_graphical clique clique_isClique _

end GraphicalZonotopes.PathJoin

end
end
end BundlePart295

section BundlePart296
/- Source: Papers/GraphicalZonotopes/PathJoinCliques.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset

def privatePart {n : ℕ} (C : Finset (Vertex n)) : Finset (Vertex n) :=
  (C.erase (hubA n)).erase (hubB n)

@[simp] theorem privatePart_hub {n : ℕ} :
    privatePart (clique (.inl () : Slot n))=∅ := by simp [privatePart,clique]

@[simp] theorem privatePart_single {n : ℕ} (r : Fin 3) (i : Fin (n+2)) :
    privatePart (clique (.inr (.inl (r,i)) : Slot n))={vertex i} := by
  fin_cases r <;> simp [privatePart,clique]

@[simp] theorem privatePart_pair {n : ℕ} (r : Fin 4) (i : Fin (n+1)) :
    privatePart (clique (.inr (.inr (r,i)) : Slot n))=
      {vertex i.castSucc,vertex i.succ} := by
  fin_cases r <;> simp [privatePart,clique]

@[simp] theorem vertex_mem_privatePart {n : ℕ} (C : Finset (Vertex n))
    (i : Fin (n+2)) : vertex i∈privatePart C ↔ vertex i∈C := by
  simp [privatePart]

theorem eq_of_privatePart {n : ℕ} {C D : Finset (Vertex n)}
    (hp : privatePart C=privatePart D)
    (ha : hubA n∈C ↔ hubA n∈D) (hb : hubB n∈C ↔ hubB n∈D) : C=D := by
  ext v
  rcases vertex_cases v with rfl | rfl | ⟨i,rfl⟩
  · exact ha
  · exact hb
  · rw [← vertex_mem_privatePart C i,← vertex_mem_privatePart D i,hp]

theorem pathPair_injective {n : ℕ} : Function.Injective
    (fun i : Fin (n+1) => ({vertex i.castSucc,vertex i.succ} : Finset (Vertex n))) := by
  intro i j h
  change ({vertex i.castSucc,vertex i.succ} : Finset (Vertex n))=
    {vertex j.castSucc,vertex j.succ} at h
  have hl : vertex i.castSucc ∈ ({vertex j.castSucc,vertex j.succ} : Finset (Vertex n)) := by
    rw [← h]; simp
  have hr : vertex i.succ ∈ ({vertex j.castSucc,vertex j.succ} : Finset (Vertex n)) := by
    rw [← h]; simp
  simp only [mem_insert,mem_singleton,vertex_inj,Fin.ext_iff,vertex,
    Fin.val_castSucc,Fin.val_succ] at hl hr
  apply Fin.ext
  omega

theorem clique_injective {n : ℕ} : Function.Injective (clique (n := n)) := by
  intro x y h
  have hp := congrArg privatePart h
  have ha : hubA n∈clique x ↔ hubA n∈clique y := by rw [h]
  have hb : hubB n∈clique x ↔ hubB n∈clique y := by rw [h]
  rcases x with u | ⟨r,i⟩ | ⟨r,i⟩ <;>
    rcases y with v | ⟨s,j⟩ | ⟨s,j⟩
  · cases u; cases v; rfl
  · cases u; simp only [privatePart_hub,privatePart_single] at hp
    exact (Finset.empty_ne_singleton _ hp).elim
  · cases u; simp only [privatePart_hub,privatePart_pair] at hp
    have hm : vertex j.castSucc∈(∅ : Finset (Vertex n)) := by rw [hp]; simp
    simp at hm
  · cases v; simp only [privatePart_hub,privatePart_single] at hp
    exact (Finset.empty_ne_singleton _ hp.symm).elim
  · simp only [privatePart_single,Finset.singleton_inj,vertex_inj] at hp
    subst j
    have hrs : r=s := by
      fin_cases r <;> fin_cases s <;> simp [clique] at ha hb ⊢
    subst s
    rfl
  · have hc := congrArg Finset.card hp
    simp only [privatePart_single,privatePart_pair,Finset.card_singleton,
      Finset.card_pair (vertex_left_ne_right j)] at hc
    omega
  · cases v; simp only [privatePart_hub,privatePart_pair] at hp
    have hm : vertex i.castSucc∈(∅ : Finset (Vertex n)) := by rw [← hp]; simp
    simp at hm
  · have hc := congrArg Finset.card hp
    simp only [privatePart_single,privatePart_pair,Finset.card_singleton,
      Finset.card_pair (vertex_left_ne_right i)] at hc
    omega
  · simp only [privatePart_pair] at hp
    have hij := pathPair_injective hp
    subst j
    have hrs : r=s := by
      fin_cases r <;> fin_cases s <;> simp [clique] at ha hb ⊢
    subst s
    rfl

theorem privatePart_vertex {n : ℕ} {C : Finset (Vertex n)} {v : Vertex n}
    (hv : v∈privatePart C) : ∃ i : Fin (n+2),v=vertex i := by
  have hA : v≠ hubA n := (mem_erase.mp (mem_erase.mp hv).2).1
  have hB : v≠ hubB n := (mem_erase.mp hv).1
  rcases vertex_cases v with ha | hb | hi
  · exact (hA ha).elim
  · exact (hB hb).elim
  · exact hi

theorem privatePart_subset {n : ℕ} (C : Finset (Vertex n)) : privatePart C⊆C :=
  (erase_subset _ _).trans (erase_subset _ _)

theorem privatePart_card_le_two {n : ℕ} {C : Finset (Vertex n)}
    (hC : (graph n).IsClique C) : (privatePart C).card≤2 := by
  by_contra hn
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := two_lt_card_iff.mp (Nat.lt_of_not_ge hn)
  obtain ⟨i,rfl⟩ := privatePart_vertex hu
  obtain ⟨j,rfl⟩ := privatePart_vertex hv
  obtain ⟨k,rfl⟩ := privatePart_vertex hw
  have hij := (graph_vertices i j).mp
    (hC (privatePart_subset C hu) (privatePart_subset C hv) huv)
  have hik := (graph_vertices i k).mp
    (hC (privatePart_subset C hu) (privatePart_subset C hw) huw)
  have hjk := (graph_vertices j k).mp
    (hC (privatePart_subset C hv) (privatePart_subset C hw) hvw)
  omega

theorem adjacent_pair_index {n : ℕ} {i j : Fin (n+2)}
    (hij : (graph n).Adj (vertex i) (vertex j)) :
    ∃ k : Fin (n+1),({vertex i,vertex j} : Finset (Vertex n))=
      {vertex k.castSucc,vertex k.succ} := by
  rcases (graph_vertices i j).mp hij with h | h
  · let k : Fin (n+1) := ⟨i.val,by omega⟩
    have hi : k.castSucc=i := Fin.ext rfl
    have hj : k.succ=j := Fin.ext h
    exact ⟨k,by rw [hi,hj]⟩
  · let k : Fin (n+1) := ⟨j.val,by omega⟩
    have hj : k.castSucc=j := Fin.ext rfl
    have hi : k.succ=i := Fin.ext h
    exact ⟨k,by rw [hi,hj]; exact pair_comm _ _⟩

theorem clique_covers {n : ℕ} (C : Finset (Vertex n))
    (hC : IsCliqueCoordinate (graph n) C) : ∃ i : Slot n,clique i=C := by
  have hcard := hC.1
  have hcl := hC.2
  have hp_le := privatePart_card_le_two hcl
  by_cases h0 : (privatePart C).card=0
  · have hp0 : privatePart C=∅ := card_eq_zero.mp h0
    have hsub : C⊆{hubA n,hubB n} := by
      intro v hv
      rcases vertex_cases v with rfl | rfl | ⟨i,rfl⟩
      · simp
      · simp
      · have hm : vertex i∈privatePart C := (vertex_mem_privatePart C i).mpr hv
        rw [hp0] at hm
        exact (notMem_empty _ hm).elim
    have he : C={hubA n,hubB n} := eq_of_subset_of_card_le hsub (by simpa using hcard)
    exact ⟨.inl (),he.symm⟩
  by_cases h1 : (privatePart C).card=1
  · obtain ⟨v,hp⟩ := card_eq_one.mp h1
    have hv : v∈privatePart C := by rw [hp]; simp
    obtain ⟨i,rfl⟩ := privatePart_vertex hv
    by_cases ha : hubA n∈C <;> by_cases hb : hubB n∈C
    · refine ⟨.inr (.inl (2,i)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_single] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inl (0,i)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_single] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inl (1,i)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_single] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · have he : C={vertex i} := eq_of_privatePart (by simpa [privatePart] using hp)
        (by simp [ha]) (by simp [hb])
      rw [he,card_singleton] at hcard
      omega
  · have h2 : (privatePart C).card=2 := by omega
    obtain ⟨u,v,huv,hp⟩ := card_eq_two.mp h2
    have hu : u∈privatePart C := by rw [hp]; simp
    have hv : v∈privatePart C := by rw [hp]; simp
    obtain ⟨i,rfl⟩ := privatePart_vertex hu
    obtain ⟨j,rfl⟩ := privatePart_vertex hv
    have hadj := hcl (privatePart_subset C hu) (privatePart_subset C hv) huv
    obtain ⟨k,hk⟩ := adjacent_pair_index hadj
    rw [hk] at hp
    by_cases ha : hubA n∈C <;> by_cases hb : hubB n∈C
    · refine ⟨.inr (.inr (3,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inr (1,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inr (2,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]
    · refine ⟨.inr (.inr (0,k)),eq_of_privatePart ?_ ?_ ?_⟩
      · simpa only [privatePart_pair] using hp.symm
      · simp [clique,ha]
      · simp [clique,hb]

theorem graphical_coordinates {n : ℕ} {f : SetFunction (Vertex n)}
    (hn : TranslationNormalized f) (hG : Graphical (graph n) f) :
    f=FiniteMonomial.polynomial clique (fun i => mobius f (clique i)) :=
  FiniteMonomial.graphical_eq_polynomial clique clique_injective clique_covers hn hG

end GraphicalZonotopes.PathJoin

end
end
end BundlePart296

section BundlePart297
/- Source: Papers/GraphicalZonotopes/PathJoinSlacks.lean -/




@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped BigOperators

def bit {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) : ℝ := if v∈S then 1 else 0

theorem bit_cases {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) :
    bit v S=0 ∨ bit v S=1 := by
  by_cases h : v∈S <;> simp [bit,h]

theorem bit_nonneg {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) : 0≤ bit v S := by
  rcases bit_cases v S with h | h <;> rw [h] <;> norm_num

theorem bit_le_one {n : ℕ} (v : Vertex n) (S : Finset (Vertex n)) : bit v S≤1 := by
  rcases bit_cases v S with h | h <;> rw [h] <;> norm_num

theorem delta_clique_hub {n : ℕ} (s : Slot n) (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    delta (setMonomial (clique s)) (hubA n) (hubB n) S =
      match s with
      | .inl _ => 1
      | .inr (.inl (r,i)) => if r=2 then bit (vertex i) S else 0
      | .inr (.inr (r,i)) =>
        if r=3 then bit (vertex i.castSucc) S*bit (vertex i.succ) S else 0 := by
  rw [delta_setMonomial (hubA_ne_hubB n) ha hb]
  rcases s with u | ⟨r,i⟩ | ⟨r,i⟩
  · simp [clique]
  · fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
  · fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    by_cases hl : vertex i.castSucc∈S <;> by_cases hr : vertex i.succ∈S <;>
      simp [hl,hr]

theorem delta_polynomial_hub {n : ℕ} (x : Slot n → ℝ) (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    delta (FiniteMonomial.polynomial clique x) (hubA n) (hubB n) S =
      x (.inl ()) +
        ∑ i : Fin (n+2),x (.inr (.inl (2,i)))*bit (vertex i) S +
        ∑ i : Fin (n+1),x (.inr (.inr (3,i)))*
          bit (vertex i.castSucc) S*bit (vertex i.succ) S := by
  rw [FiniteMonomial.polynomial,delta_sum]
  simp only [delta_smul]
  simp_rw [delta_clique_hub _ _ ha hb]
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three,
    Fin.sum_univ_four,mul_assoc,add_assoc]

theorem delta_hub {n : ℕ} (S : Finset (Vertex n))
    (ha : hubA n∉S) (hb : hubB n∉S) :
    delta (setFunction n) (hubA n) (hubB n) S = ((n+2)/2 : ℕ) -
      ∑ i : Fin (n+1),(1-bit (vertex i.castSucc) S)*bit (vertex i.succ) S := by
  rw [setFunction,delta_polynomial_hub _ _ ha hb]
  have hsum : (∑ i : Fin (n+2),
      coefficient n (.inr (.inl (2,i)))*bit (vertex i) S) =
      -∑ i : Fin (n+1),bit (vertex i.succ) S := by
    rw [Fin.sum_univ_succ]
    simp [coefficient,Fin.succ_ne_zero,Finset.sum_neg_distrib]
  rw [hsum]
  simp only [coefficient,Fin.isValue,Fin.reduceEq,ite_false,one_mul]
  simp only [sub_mul,one_mul,Finset.sum_sub_distrib]
  ring

theorem path_vertices_mem_pair_iff {n : ℕ} (r : Fin 4) (j : Fin (n+1))
    (i : Fin (n+2)) :
    vertex i∈clique (.inr (.inr (r,j)) : Slot n) ↔ i=j.castSucc ∨ i=j.succ := by
  fin_cases r <;> simp [clique]

theorem delta_clique_path {n : ℕ} (s : Slot n) (i : Fin (n+1))
    (S : Finset (Vertex n)) (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (setMonomial (clique s)) (vertex i.castSucc) (vertex i.succ) S =
      match s with
      | .inl _ => 0
      | .inr (.inl _) => 0
      | .inr (.inr (r,j)) =>
        if j=i then
          if r=0 then 1 else if r=1 then bit (hubA n) S
          else if r=2 then bit (hubB n) S else bit (hubA n) S*bit (hubB n) S
        else 0 := by
  rw [delta_setMonomial (vertex_left_ne_right i) hl hr]
  rcases s with u | ⟨r,j⟩ | ⟨r,j⟩
  · simp [clique]
  · have hne : i.castSucc≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
    fin_cases r <;> simp [clique,vertex_inj]
    all_goals intro h0 h1; exact (hne (h0.trans h1.symm)).elim
  · by_cases he : j=i
    · subst j
      fin_cases r <;> simp [clique,bit,Finset.insert_subset_iff,Finset.singleton_subset_iff]
      by_cases ha : hubA n∈S <;> by_cases hb : hubB n∈S <;> simp [ha,hb]
    · have hnot : ¬(vertex i.castSucc∈clique (.inr (.inr (r,j)) : Slot n) ∧
          vertex i.succ∈clique (.inr (.inr (r,j)) : Slot n)) := by
        intro h
        have h0 := (path_vertices_mem_pair_iff r j i.castSucc).mp h.1
        have h1 := (path_vertices_mem_pair_iff r j i.succ).mp h.2
        simp only [Fin.ext_iff,Fin.val_castSucc,Fin.val_succ] at h0 h1
        apply he
        apply Fin.ext
        omega
      simp only [he,ite_false]
      apply if_neg
      intro h
      exact hnot ⟨h.1,h.2.1⟩

theorem delta_polynomial_path {n : ℕ} (x : Slot n → ℝ) (i : Fin (n+1))
    (S : Finset (Vertex n)) (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (FiniteMonomial.polynomial clique x) (vertex i.castSucc) (vertex i.succ) S =
      x (.inr (.inr (0,i))) + x (.inr (.inr (1,i)))*bit (hubA n) S +
      x (.inr (.inr (2,i)))*bit (hubB n) S +
      x (.inr (.inr (3,i)))*bit (hubA n) S*bit (hubB n) S := by
  rw [FiniteMonomial.polynomial,delta_sum]
  simp only [delta_smul]
  simp_rw [delta_clique_path _ _ _ hl hr]
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_three,
    Fin.sum_univ_four,mul_ite,mul_assoc,add_assoc]

theorem delta_path {n : ℕ} (i : Fin (n+1)) (S : Finset (Vertex n))
    (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (setFunction n) (vertex i.castSucc) (vertex i.succ) S =
      1 - (if i.val%2=0 then bit (hubA n) S else bit (hubB n) S) +
        bit (hubA n) S*bit (hubB n) S := by
  rw [setFunction,delta_polynomial_path _ _ _ hl hr]
  by_cases he : i.val%2=0 <;> simp [coefficient,he] <;> ring

theorem delta_path_boolean {n : ℕ} (i : Fin (n+1)) (S : Finset (Vertex n))
    (hl : vertex i.castSucc∉S) (hr : vertex i.succ∉S) :
    delta (setFunction n) (vertex i.castSucc) (vertex i.succ) S=0 ∨
      delta (setFunction n) (vertex i.castSucc) (vertex i.succ) S=1 := by
  rw [delta_path i S hl hr]
  rcases bit_cases (hubA n) S with ha | ha <;>
    rcases bit_cases (hubB n) S with hb | hb <;>
      by_cases he : i.val%2=0 <;> simp [ha,hb,he]

end GraphicalZonotopes.PathJoin

end
end
end BundlePart297

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

section BundlePart314
/- Source: Papers/GraphicalZonotopes/SaturatedBookGeometry.lean -/






/-! # The universal geometric lower bound for saturated books

All hypotheses are imposed on the actual polytope.  The normalized graphical
function and its actual direction graph are derived, not supplied as premises.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SaturatedDirections
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable

theorem full_weak_direction_model {V : Type*} [Fintype V] [DecidableEq V]
    (hn : 2 ≤ Fintype.card V) {H : SimpleGraph V} {Q : Set (V → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hd : FullDimension Q) (hw : IsWeakMinkowskiSummand Q (graphicalZonotope H)) :
    ∃ z : graphicalFunctionSpace (actualDirectionGraph Q),ExtremeSupermodular z.1 ∧
      FullDimension (basePolytope z.1) ∧ actualDirectionGraph Q ≤ H := by
  obtain ⟨a,ha,R,hR,hRc,hnR,hQR⟩ := hw
  have hTn : Normalized (a • graphFunction H) := by
    change a*graphFunction H ∅ = 0
    rw [graphFunction_normalized,mul_zero]
  have hTs := (graphFunction_supermodular H).smul ha.le
  have hbase : Q + R = basePolytope (a • graphFunction H) := by
    rw [basePolytope_smul (graphFunction_normalized H) (graphFunction_supermodular H) ha.le,
      baseGraphFunction_eq_graphicalZonotope]
    exact hQR
  let f := lowerSupport Q
  have hfn : Normalized f := lowerSupport_normalized hQ.compact hi.1
  have hfs : Supermodular f := summand_lowerSupport_supermodular hTn hTs
    hQ.compact hR hi.1 hnR hbase
  have hbody : Q = basePolytope f := summand_eq_basePolytope hTn hTs
    hQ.compact hR hQ.convex hi.1 hnR hbase
  let z := normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hdim : FullDimension (basePolytope z) := by
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f))) = _
    rw [vectorSpan_basePolytope_normalize,← hbody]
    exact hd
  have hne : z ≠ 0 := by
    intro hz
    have hh := hdim
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope z)) = Fintype.card V - 1 at hh
    rw [hz,basePolytope_zero,vectorSpan_singleton,finrank_bot] at hh
    omega
  have hext : ExtremeSupermodular z :=
    MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne (hbody ▸ hi)
  have hactual : actualDirectionGraph (basePolytope z) = actualDirectionGraph Q := by
    rw [actualDirectionGraph_normalize,← hbody]
  have hzg : Graphical (actualDirectionGraph Q) z := by
    rw [← hactual]
    intro u v huv hnon S hu hv
    have hnonneg := hzs.elemental u v huv S hu hv
    apply le_antisymm _ hnonneg
    by_contra h
    have hpos : 0 < delta z u v S := lt_of_not_ge h
    exact hnon (exposedSegment_of_positive_delta hzn.1 hzs huv hu hv hpos)
  refine ⟨⟨z,hzn,hzg⟩,hext,hdim,?_⟩
  intro u v huv
  rw [hbody] at huv
  exact basePolytope_summand_actualRootEdge hfn hfs H ha.le R (hbody ▸ hQR) huv

variable {s : ℕ}
local instance geometricVertexOrder (s k : ℕ) : LinearOrder (Vertex s k) :=
  inferInstanceAs (LinearOrder (Fin s ⊕ₗ Fin k))
local instance geometricVertexDecidableEq (s k : ℕ) : DecidableEq (Vertex s k) :=
  (geometricVertexOrder s k).toDecidableEq

/-- Saturation forces every hub pair to occur and supplies the sharp bound
on the number of actual spokes at every hub. -/
theorem actual_hub_spoke_lower (hs : 2 ≤ s)
    {Q : Set (Vertex s (cliqueCapacity s) → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hd : FullDimension Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s)))) :
    actualDirectionGraph Q ≤ cliqueBook s (cliqueCapacity s) ∧
    (∀ i j : Fin s,i ≠ j → ActualRootEdge Q (Sum.inl i) (Sum.inl j)) ∧
    ∀ i : Fin s,saturatedHubNeighbors s ≤
      (univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card := by
  obtain ⟨z,hz,hdz,hsub⟩ := full_weak_direction_model
    (by simp only [Fintype.card_sum,Fintype.card_fin]; omega) hQ hi hd hw
  refine ⟨hsub,?_⟩
  by_cases hs2 : s = 2
  · subst s
    have ht : actualDirectionGraph Q = ⊤ := three_vertex_complete
      (by norm_num [Fintype.card_sum,Fintype.card_fin,cliqueCapacity,Nat.choose]) _ z hz hdz
    constructor
    · intro i j hij
      change (actualDirectionGraph Q).Adj (Sum.inl i) (Sum.inl j)
      rw [ht]
      exact (SimpleGraph.top_adj _ _).mpr (fun he => hij (Sum.inl_injective he))
    · intro i
      have ha : ∀ j : Fin (cliqueCapacity 2),ActualRootEdge Q (Sum.inl i) (Sum.inr j) := by
        intro j
        change (actualDirectionGraph Q).Adj (Sum.inl i) (Sum.inr j)
        rw [ht]
        exact (SimpleGraph.top_adj _ _).mpr Sum.inl_ne_inr
      simp only [ha,filter_true,card_univ,Fintype.card_fin]
      norm_num [saturatedHubNeighbors,cliqueCapacity,Nat.choose]
  · have hs3 : 3 ≤ s := by omega
    have hc := hubs_clique hs3 hsub z hz hdz
    constructor
    · intro i j hij
      exact hc (mem_image.mpr ⟨i,mem_univ _,rfl⟩) (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
        (fun he => hij (Sum.inl_injective he))
    · intro i
      exact outer_neighbors_lower hs3 hsub z hz hdz i

/-- Theorem 7.12, universal actual-direction lower bound. -/
theorem direction_lower (hs : 2 ≤ s)
    {Q : Set (Vertex s (cliqueCapacity s) → ℝ)}
    (hQ : IsFinitePolytope Q) (hi : MinkowskiIndecomposable Q)
    (hd : FullDimension Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s)))) :
    s.choose 2 + s*saturatedHubNeighbors s ≤ directionCount Q := by
  obtain ⟨hsub,hh,hn⟩ := actual_hub_spoke_lower hs hQ hi hd hw
  exact BookEdges.edge_count_lower (actualDirectionGraph Q) hsub hh
    (saturatedHubNeighbors s) hn

end GraphicalZonotopes.SaturatedDirections

end
end
end BundlePart314

section BundlePart315
/- Source: Papers/GraphicalZonotopes/MatchingPureModules.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule
open Finset
variable {H : Type*} [Fintype H] [LinearOrder H]

def pairVertices {C : Finset H} (e : PairIn C) : Finset H := {e.1.1.1,e.1.1.2}

theorem pairVertices_subset {C : Finset H} (e : PairIn C) : pairVertices e⊆C := by
  simp [pairVertices,insert_subset_iff,singleton_subset_iff,e.2.1,e.2.2]

theorem pairVertices_card {C : Finset H} (e : PairIn C) : (pairVertices e).card=2 :=
  card_pair (ne_of_lt e.1.2.1)

def IsPairMatching {C : Finset H} (A : Finset (PairIn C)) : Prop :=
  ∀ e∈A,∀ f∈A,e≠ f → Disjoint (pairVertices e) (pairVertices f)

def matchingBlocks {C : Finset H} (A : Finset (PairIn C)) : Finset (Finset H) :=
  A.image pairVertices ∪ (C.filter (fun a => ∀ e∈A,a∉pairVertices e)).image singleton

theorem mem_matchingBlocks {C : Finset H} (A : Finset (PairIn C)) (B : Finset H) :
    B∈matchingBlocks A ↔
      (∃ e∈A,B=pairVertices e) ∨
      ∃ a∈C,(∀ e∈A,a∉pairVertices e) ∧ B={a} := by
  simp only [matchingBlocks,mem_union,mem_image,mem_filter]
  constructor
  · rintro (⟨e,he,rfl⟩ | ⟨a,⟨ha,hn⟩,rfl⟩)
    · exact Or.inl ⟨e,he,rfl⟩
    · exact Or.inr ⟨a,ha,hn,rfl⟩
  · rintro (⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩)
    · exact Or.inl ⟨e,he,rfl⟩
    · exact Or.inr ⟨a,⟨ha,hn⟩,rfl⟩

theorem matchingBlocks_cover {C : Finset H} (A : Finset (PairIn C)) {a : H}
    (ha : a∈C) : ∃ B∈matchingBlocks A,a∈B := by
  by_cases he : ∃ e∈A,a∈pairVertices e
  · obtain ⟨e,he,hae⟩ := he
    exact ⟨pairVertices e,(mem_matchingBlocks A _).mpr (Or.inl ⟨e,he,rfl⟩),hae⟩
  · have hn : ∀ e∈A,a∉pairVertices e := by simpa only [not_exists,not_and] using he
    exact ⟨{a},(mem_matchingBlocks A _).mpr (Or.inr ⟨a,ha,hn,rfl⟩),mem_singleton_self _⟩

theorem matchingBlocks_subset {C : Finset H} (A : Finset (PairIn C))
    {B : Finset H} (hB : B∈matchingBlocks A) : B⊆C := by
  rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
  · exact pairVertices_subset e
  · exact singleton_subset_iff.mpr ha

theorem matchingBlocks_card_le_two {C : Finset H} (A : Finset (PairIn C))
    {B : Finset H} (hB : B∈matchingBlocks A) : B.card≤2 := by
  rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
  · rw [pairVertices_card]
  · simp

theorem matchingBlocks_family {C : Finset H} (hC : 3≤ C.card)
    (A : Finset (PairIn C)) (hA : IsPairMatching A) :
    ComplementFamily C (matchingBlocks A) := by
  refine ⟨?_,fun B hB => matchingBlocks_subset A hB,?_,?_⟩
  · by_contra hh
    have hcard : (matchingBlocks A).card≤1 := by omega
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0< C.card)
    obtain ⟨B,hB,haB⟩ := matchingBlocks_cover A ha
    have hsub : C⊆B := by
      intro b hb
      obtain ⟨D,hD,hbD⟩ := matchingBlocks_cover A hb
      have he : D=B := (card_le_one.mp hcard) D hD B hB
      exact he ▸ hbD
    have hc := (card_le_card hsub).trans (matchingBlocks_card_le_two A hB)
    omega
  · intro B hB
    rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
    · exact ⟨e.1.1.1,by simp [pairVertices]⟩
    · exact singleton_nonempty _
  · intro B hB D hD hBD
    rcases (mem_matchingBlocks A B).mp hB with ⟨e,he,rfl⟩ | ⟨a,ha,hn,rfl⟩
    · rcases (mem_matchingBlocks A D).mp hD with ⟨f,hf,rfl⟩ | ⟨b,hb,hm,rfl⟩
      · exact hA e he f hf (fun h => hBD (congrArg pairVertices h))
      · exact disjoint_singleton_right.mpr (hm e he)
    · rcases (mem_matchingBlocks A D).mp hD with ⟨f,hf,rfl⟩ | ⟨b,hb,hm,rfl⟩
      · exact disjoint_singleton_left.mpr (hn f hf)
      · exact disjoint_singleton.mpr (fun h => hBD (congrArg singleton h))

theorem pairVertices_membership {C : Finset H} (e f : PairIn C) :
    (e.1.1.1∈pairVertices f ∧ e.1.1.2∈pairVertices f) ↔ e=f := by
  rw [pairVertices,ordered_pair_membership e.1.2.1 f.1.2.1]
  constructor
  · rintro ⟨hu,hv⟩
    exact Subtype.ext (Subtype.ext (Prod.ext hu hv))
  · rintro rfl
    exact ⟨rfl,rfl⟩

theorem crosses_matchingBlocks {C : Finset H} (hC : 3≤ C.card)
    (A : Finset (PairIn C)) (hA : IsPairMatching A) (e : PairIn C) :
    Crosses (matchingBlocks A) e.1.1.1 e.1.1.2 ↔ e∉A := by
  let hf := matchingBlocks_family hC A hA
  constructor
  · rintro ⟨B,hB,D,hD,hBD,hu,hv⟩ he
    have hE := (mem_matchingBlocks A (pairVertices e)).mpr (Or.inl ⟨e,he,rfl⟩)
    have hBE := hf.shared_mem_eq hB hE hu (by simp [pairVertices])
    have hDE := hf.shared_mem_eq hD hE hv (by simp [pairVertices])
    exact hBD (hBE.trans hDE.symm)
  · intro he
    obtain ⟨B,hB,hu⟩ := matchingBlocks_cover A e.2.1
    obtain ⟨D,hD,hv⟩ := matchingBlocks_cover A e.2.2
    refine ⟨B,hB,D,hD,?_,hu,hv⟩
    intro hBD
    have hvB : e.1.1.2∈B := hBD.symm ▸ hv
    rcases (mem_matchingBlocks A B).mp hB with ⟨f,hf,rfl⟩ | ⟨a,ha,hn,rfl⟩
    · have hef := (pairVertices_membership e f).mp ⟨hu,hvB⟩
      exact he (hef.symm ▸ hf)
    · have heq : e.1.1.1=e.1.1.2 := (mem_singleton.mp hu).trans (mem_singleton.mp hvB).symm
      exact (ne_of_lt e.1.2.1) heq

/-- Every matching gives an actual all-essential pure Boolean response equal
to its negative edge indicator, modulo the diagonal clique coefficient. -/
theorem pureRealizable_negative_matching {C : Finset H} (hC : 3≤ C.card)
    (A : Finset (PairIn C)) (hA : IsPairMatching A) :
    PureRealizable C (-pairIndicator A) := by
  classical
  let hf := matchingBlocks_family hC A hA
  refine ⟨complementModule C (matchingBlocks A),hf.module_boolean,
    fun a ha => hf.essential ha,
    fun a ha S => complementModule_ignores_outside C _ ha S,?_⟩
  rw [responseClass_eq_coefficientClass,complementModule_response_coefficients hf]
  have hcoord : (fun r : HubResponseRow H =>
      if rowClique r=C ∧ Crosses (matchingBlocks A) r.1.1.1 r.1.1.2 then (1 : ℝ) else 0)=
      blockCoordinates C (fun e => 1-pairIndicator A e) := by
    funext r
    by_cases hr : rowClique r=C
    · have hc := crosses_matchingBlocks hC A hA (pairAtRow C r hr)
      change (if rowClique r=C ∧ _ then (1 : ℝ) else 0)=
        if h : rowClique r=C then 1-pairIndicator A (pairAtRow C r h) else 0
      rw [dif_pos hr]
      simp only [hr,true_and]
      change (if Crosses (matchingBlocks A) (pairAtRow C r hr).1.1.1
        (pairAtRow C r hr).1.1.2 then (1 : ℝ) else 0)=_
      rw [hc]
      by_cases he : pairAtRow C r hr∈A <;> simp [pairIndicator,he]
    · simp [blockCoordinates,hr]
  rw [hcoord]
  change blockClass C (fun e => 1-pairIndicator A e)=_
  have hfun : (fun e : PairIn C => (1 : ℝ)-pairIndicator A e)=
      (fun _ => (1 : ℝ))+(-pairIndicator A) := by rfl
  have hz : blockClass C (fun _ : PairIn C => (1 : ℝ))=0 := by
    change coefficientClass (blockCoordinates C (fun _ => 1))=0
    have hco : blockCoordinates C (fun _ : PairIn C => (1 : ℝ))=
        fun r : HubResponseRow H => if rowClique r=C then 1 else 0 := by
      funext r
      change (if _h : rowClique r=C then (1 : ℝ) else 0)=_
      split <;> rfl
    rw [hco]
    exact coefficientClass_block_zero C
  rw [hfun,map_add,hz,zero_add]

end GraphicalZonotopes.BooleanModule

end
end
end BundlePart315

section BundlePart316
/- Source: Papers/GraphicalZonotopes/SaturatedBookPartition.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators

abbrev HubPair (s : ℕ) := PairIn (univ : Finset (Fin s))

def natPair {s : ℕ} (i j : ℕ) (hij : i< j) (hj : j< s) : HubPair s :=
  orderedPair univ ⟨i,lt_trans hij hj⟩ ⟨j,hj⟩ hij (mem_univ _) (mem_univ _)

def pairSum {s : ℕ} (e : HubPair s) : ℕ := e.1.1.1.val+e.1.1.2.val

def Retained {s : ℕ} (e : HubPair s) : Prop :=
  ¬(e.1.1.1.val=0 ∧ e.1.1.2.val=1) ∧
  ¬(e.1.1.1.val=1 ∧ e.1.1.2.val< s-1) ∧
  ¬(e.1.1.1.val=2 ∧ e.1.1.2.val=3)

instance {s : ℕ} (e : HubPair s) : Decidable (Retained e) := inferInstanceAs
  (Decidable (¬(e.1.1.1.val=0 ∧ e.1.1.2.val=1) ∧
    ¬(e.1.1.1.val=1 ∧ e.1.1.2.val< s-1) ∧
    ¬(e.1.1.1.val=2 ∧ e.1.1.2.val=3)))

def retainedPairs (s : ℕ) : Finset (HubPair s) := univ.filter Retained

@[simp] theorem mem_retainedPairs {s : ℕ} {e : HubPair s} :
    e∈retainedPairs s ↔ Retained e := by simp [retainedPairs]

def referencePair {s : ℕ} (hs : 2≤ s) : HubPair s := natPair 0 1 (by omega) (by omega)

theorem pair_eq_reference {s : ℕ} (hs : 2≤ s) (e : HubPair s) :
    e=referencePair hs ↔ e.1.1.1.val=0 ∧ e.1.1.2.val=1 := by
  constructor
  · rintro rfl
    exact ⟨rfl,rfl⟩
  · rintro ⟨hu,hv⟩
    exact Subtype.ext (Subtype.ext (Prod.ext (Fin.ext hu) (Fin.ext hv)))

abbrev ActivePair {s : ℕ} (hs : 2≤ s) := {e : HubPair s // e≠ referencePair hs}

def groupPair {s : ℕ} (hs : 5≤ s) (e : ActivePair (show 2≤ s by omega)) : HubPair s :=
  if h : e.1.1.1.1.val=1 ∧ e.1.1.1.2.val< s-1 then
    natPair 0 (1+e.1.1.1.2.val) (by omega) (by omega)
  else if h : e.1.1.1.1.val=2 ∧ e.1.1.1.2.val=3 then
    if hs6 : 6≤ s then natPair 0 5 (by omega) (by omega)
    else natPair 1 4 (by omega) (by omega)
  else e.1

theorem groupPair_retained {s : ℕ} (hs : 5≤ s)
    (e : ActivePair (show 2≤ s by omega)) : Retained (groupPair hs e) := by
  have huv : e.1.1.1.1.val< e.1.1.1.2.val := e.1.1.2.1
  have hne : ¬(e.1.1.1.1.val=0 ∧ e.1.1.1.2.val=1) := by
    intro h
    exact e.2 ((pair_eq_reference (show 2≤ s by omega) e.1).mpr h)
  unfold groupPair
  split_ifs with h1 h2 h6
  · simp only [Retained,natPair,orderedPair]
    omega
  · simp only [Retained,natPair,orderedPair]
    omega
  · simp only [Retained,natPair,orderedPair]
    omega
  · exact ⟨hne,h1,h2⟩

theorem groupPair_sum {s : ℕ} (hs : 5≤ s)
    (e : ActivePair (show 2≤ s by omega)) : pairSum (groupPair hs e)=pairSum e.1 := by
  unfold groupPair
  split_ifs with h1 h2 h6 <;> simp only [pairSum,natPair,orderedPair] <;> omega

theorem retained_not_reference {s : ℕ} (hs : 2≤ s) {e : HubPair s}
    (he : Retained e) : e≠ referencePair hs := by
  intro h
  exact he.1 ((pair_eq_reference hs e).mp h)

theorem groupPair_of_retained {s : ℕ} (hs : 5≤ s) {e : HubPair s} (he : Retained e) :
    groupPair hs ⟨e,retained_not_reference (by omega) he⟩=e := by
  simp only [groupPair,he.2.1,he.2.2,dite_false]

def group {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) : Finset (HubPair s) :=
  univ.filter (fun e => ∃ h : e≠ referencePair (show 2≤ s by omega),groupPair hs ⟨e,h⟩=r.1)

theorem mem_group {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) (e : HubPair s) :
    e∈group hs r ↔ ∃ h : e≠ referencePair (show 2≤ s by omega),groupPair hs ⟨e,h⟩=r.1 := by
  classical
  simp only [group,mem_filter,mem_univ,true_and]

theorem group_nonempty {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) :
    (group hs r).Nonempty := by
  refine ⟨r.1,(mem_group hs r r.1).mpr ?_⟩
  have hr := mem_retainedPairs.mp r.2
  exact ⟨retained_not_reference (by omega) hr,groupPair_of_retained hs hr⟩

theorem group_reference_not_mem {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) :
    referencePair (show 2≤ s by omega)∉group hs r := by
  intro h
  obtain ⟨hn,_⟩ := (mem_group hs r _).mp h
  exact hn rfl

theorem group_pairSum {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s))
    {e : HubPair s} (he : e∈group hs r) : pairSum e=pairSum r.1 := by
  obtain ⟨hn,hg⟩ := (mem_group hs r e).mp he
  rw [←hg,groupPair_sum]

theorem equal_sum_matching {s : ℕ} (A : Finset (HubPair s)) (t : ℕ)
    (hA : ∀ e∈A,pairSum e=t) : IsPairMatching A := by
  intro e he f hf hne
  apply disjoint_left.mpr
  intro a hae haf
  have hsum : e.1.1.1.val+e.1.1.2.val=f.1.1.1.val+f.1.1.2.val :=
    (hA e he).trans (hA f hf).symm
  have heord : e.1.1.1.val< e.1.1.2.val := e.1.2.1
  have hford : f.1.1.1.val< f.1.1.2.val := f.1.2.1
  simp only [pairVertices,mem_insert,mem_singleton] at hae haf
  apply hne
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  all_goals rcases hae with hae | hae <;> rcases haf with haf | haf
  all_goals have haev := congrArg Fin.val hae
  all_goals have hafv := congrArg Fin.val haf
  all_goals omega

theorem group_matching {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) :
    IsPairMatching (group hs r) :=
  equal_sum_matching _ (pairSum r.1) (fun _ he => group_pairSum hs r he)

theorem group_realizable {s : ℕ} (hs : 5≤ s) (r : ↥(retainedPairs s)) :
    PureRealizable (univ : Finset (Fin s)) (-pairIndicator (group hs r)) :=
  pureRealizable_negative_matching (by simpa using (show 3≤ s by omega)) _
    (group_matching hs r)

theorem group_unique {s : ℕ} (hs : 5≤ s) (r t : ↥(retainedPairs s))
    {e : HubPair s} (hr : e∈group hs r) (ht : e∈group hs t) : r=t := by
  obtain ⟨hn,he⟩ := (mem_group hs r e).mp hr
  obtain ⟨hm,hf⟩ := (mem_group hs t e).mp ht
  exact Subtype.ext (he.symm.trans hf)

theorem group_cover {s : ℕ} (hs : 5≤ s) (e : HubPair s)
    (he : e≠ referencePair (show 2≤ s by omega)) : ∃ r : ↥(retainedPairs s),e∈group hs r := by
  let r : ↥(retainedPairs s) := ⟨groupPair hs ⟨e,he⟩,
    mem_retainedPairs.mpr (groupPair_retained hs ⟨e,he⟩)⟩
  exact ⟨r,(mem_group hs r e).mpr ⟨he,rfl⟩⟩

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart316

section BundlePart317
/- Source: Papers/GraphicalZonotopes/SaturatedBookPartitionCount.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators

variable {s : ℕ}

def lastHub (hs : 1≤ s) : Fin s := ⟨s-1,by omega⟩
def oneHub (hs : 2≤ s) : Fin s := ⟨1,by omega⟩

def omittedStar (hs : 5≤ s) : Finset (HubPair s) :=
  starPairs univ (oneHub (by omega))
    (((univ : Finset (Fin s)).erase (oneHub (by omega))).erase (lastHub (by omega)))

theorem mem_omittedStar (hs : 5≤ s) (e : HubPair s) :
    e∈omittedStar hs ↔
      (e.1.1.1.val=0 ∧ e.1.1.2.val=1) ∨
      (e.1.1.1.val=1 ∧ e.1.1.2.val< s-1) := by
  have huv : e.1.1.1.val< e.1.1.2.val := e.1.2.1
  have hub := e.1.1.2.isLt
  have hone : (oneHub (show 2≤ s by omega)).val=1 := rfl
  have hlast : (lastHub (show 1≤ s by omega)).val=s-1 := rfl
  simp only [omittedStar,mem_starPairs,StarPair,mem_erase,mem_univ,and_true,
    Fin.ext_iff,hone,hlast]
  dsimp
  omega

theorem omittedStar_card (hs : 5≤ s) : (omittedStar hs).card=s-2 := by
  rw [omittedStar,starPairs_card _ (mem_univ _) (subset_univ _) (by simp)]
  have hne : lastHub (show 1≤ s by omega)≠ oneHub (show 2≤ s by omega) := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [lastHub,oneHub] at hv
    omega
  rw [card_erase_of_mem (by simp [hne]),card_erase_of_mem (mem_univ _),card_univ]
  simp only [Fintype.card_fin]
  omega

theorem retainedPairs_eq_sdiff (hs : 5≤ s) :
    retainedPairs s=univ\(insert (natPair 2 3 (by omega) (by omega)) (omittedStar hs)) := by
  ext e
  simp only [mem_retainedPairs,mem_sdiff,mem_univ,true_and,mem_insert,mem_omittedStar]
  have heq : e=natPair 2 3 (by omega) (by omega) ↔
      e.1.1.1.val=2 ∧ e.1.1.2.val=3 := by
    constructor
    · rintro rfl
      exact ⟨rfl,rfl⟩
    · rintro ⟨hu,hv⟩
      exact Subtype.ext (Subtype.ext (Prod.ext (Fin.ext hu) (Fin.ext hv)))
  rw [heq]
  unfold Retained
  tauto

theorem retainedPairs_card (hs : 5≤ s) : (retainedPairs s).card=s.choose 2-(s-1) := by
  rw [retainedPairs_eq_sdiff hs,card_sdiff_of_subset (subset_univ _),
    card_insert_of_notMem]
  · rw [omittedStar_card hs,card_univ,pairIn_card,card_univ]
    simp only [Fintype.card_fin]
    congr 1
    omega
  · rw [mem_omittedStar]
    simp only [natPair,orderedPair]
    omega

theorem retained_count_add_anchors (hs : 5≤ s) :
    (s-1)+(retainedPairs s).card=s.choose 2 := by
  rw [retainedPairs_card hs]
  have hchoose : s-1≤ s.choose 2 := by
    rw [Nat.choose_two_right]
    apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
    calc
      (s-1)*2≤(s-1)*s := Nat.mul_le_mul_left _ (by omega)
      _ = s*(s-1) := Nat.mul_comm _ _
  omega

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart317

section BundlePart318
/- Source: Papers/GraphicalZonotopes/SaturatedBookRigidity.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

def activeNatPair (hs : 5≤ s) (i j : ℕ) (hij : i< j) (hj : j< s)
    (hne : ¬(i=0 ∧ j=1)) : ActivePair (show 2≤ s by omega) :=
  ⟨natPair i j hij hj,by
    intro h
    exact hne ((pair_eq_reference (show 2≤ s by omega) _).mp h)⟩

theorem groupPair_03_12 (hs : 5≤ s) :
    groupPair hs (activeNatPair hs 0 3 (by omega) (by omega) (by omega))=
    groupPair hs (activeNatPair hs 1 2 (by omega) (by omega) (by omega)) := by
  simp [groupPair,activeNatPair,natPair,orderedPair,(show 2< s-1 by omega)]

theorem groupPair_04_13 (hs : 5≤ s) :
    groupPair hs (activeNatPair hs 0 4 (by omega) (by omega) (by omega))=
    groupPair hs (activeNatPair hs 1 3 (by omega) (by omega) (by omega)) := by
  simp [groupPair,activeNatPair,natPair,orderedPair,(show 3< s-1 by omega)]

theorem groupPair_14_23 (hs : 5≤ s) :
    groupPair hs (activeNatPair hs 1 4 (by omega) (by omega) (by omega))=
    groupPair hs (activeNatPair hs 2 3 (by omega) (by omega) (by omega)) := by
  by_cases hs6 : 6≤ s
  · simp [groupPair,activeNatPair,natPair,orderedPair,hs6,(show 4< s-1 by omega)]
  · have hs5 : s=5 := by omega
    subst s
    simp [groupPair,activeNatPair,natPair,orderedPair]

theorem groupPair_step (hs : 5≤ s) (j : ℕ) (hj : 5≤ j) (hjs : j< s) :
    groupPair hs (activeNatPair hs 0 j (by omega) hjs (by omega))=
    groupPair hs (activeNatPair hs 1 (j-1) (by omega) (by omega) (by omega)) := by
  have he : 1+(j-1)=j := by omega
  simp [groupPair,activeNatPair,natPair,orderedPair,he,(show j≠1 by omega),
    (show j-1< s-1 by omega)]

/-- The matching partition retains exactly the endpoint comparisons needed
for full arithmetic-progression rigidity; all other pair pieces may be split. -/
theorem grouped_endpoint_rigidity (hs : 5≤ s) (d : Fin s → ℝ)
    (h0 : d ⟨0,by omega⟩=0)
    (hgroup : ∀ e f : ActivePair (show 2≤ s by omega),groupPair hs e=groupPair hs f →
      d e.1.1.1.1+d e.1.1.1.2=d f.1.1.1.1+d f.1.1.1.2) :
    ∀ a : Fin s,d a=(a.val : ℝ)*d ⟨1,by omega⟩ := by
  let D : ℕ → ℝ := fun j => if h : j< s then d ⟨j,h⟩ else 0
  have hD : ∀ j : Fin s,D j.val=d j := by
    intro j
    simp only [D,dite_eq_left j.isLt]
  have h03 : D 0+D 3=D 1+D 2 := by
    have h := hgroup _ _ (groupPair_03_12 hs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 0< s by omega),(show 1< s by omega),
      (show 2< s by omega),(show 3< s by omega)] using h
  have h04 : D 0+D 4=D 1+D 3 := by
    have h := hgroup _ _ (groupPair_04_13 hs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 0< s by omega),(show 1< s by omega),
      (show 3< s by omega),(show 4< s by omega)] using h
  have h14 : D 1+D 4=D 2+D 3 := by
    have h := hgroup _ _ (groupPair_14_23 hs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 1< s by omega),(show 2< s by omega),
      (show 3< s by omega),(show 4< s by omega)] using h
  have hstep : ∀ j,5≤ j → j< s → D 0+D j=D 1+D (j-1) := by
    intro j hj hjs
    have h := hgroup _ _ (groupPair_step hs j hj hjs)
    simpa [D,activeNatPair,natPair,orderedPair,(show 0< s by omega),(show 1< s by omega),
      hjs,(show j-1< s by omega)] using h
  have h := quadrilateral_endpoint_rigidity s hs D
    (by simpa [D,(show 0< s by omega)] using h0) h03 h04 h14 hstep
  intro a
  have ha := h a.val a.isLt
  rw [hD a] at ha
  simpa [D,(show 1< s by omega)] using ha

def groupIndex (hs : 5≤ s) (e : ActivePair (show 2≤ s by omega)) : ↥(retainedPairs s) :=
  ⟨groupPair hs e,mem_retainedPairs.mpr (groupPair_retained hs e)⟩

theorem mem_group_iff (hs : 5≤ s) (e : ActivePair (show 2≤ s by omega))
    (r : ↥(retainedPairs s)) : e.1∈group hs r ↔ r=groupIndex hs e := by
  rw [mem_group]
  constructor
  · rintro ⟨hn,hg⟩
    exact Subtype.ext hg.symm
  · rintro rfl
    exact ⟨e.2,rfl⟩

theorem sum_group_indicator (hs : 5≤ s) (w : ↥(retainedPairs s) → ℝ)
    (e : ActivePair (show 2≤ s by omega)) :
    (∑ r : ↥(retainedPairs s),w r*pairIndicator (group hs r) e.1)=w (groupIndex hs e) := by
  simp only [pairIndicator,mem_group_iff,mul_ite,mul_one,mul_zero,
    sum_ite_eq',mem_univ,ite_true]

theorem sum_group_indicator_reference (hs : 5≤ s) (w : ↥(retainedPairs s) → ℝ) :
    (∑ r : ↥(retainedPairs s),w r*pairIndicator (group hs r) (referencePair (show 2≤ s by omega)))=0 := by
  simp only [pairIndicator,group_reference_not_mem,ite_false,mul_zero,sum_const_zero]

/-- Every zero full-block relation has the prescribed positive scales. -/
theorem full_block_unique (hs : 5≤ s) (d : Fin s → ℝ)
    (h0 : d ⟨0,by omega⟩=0) (w : ↥(retainedPairs s) → ℝ)
    (hz : blockClass (univ : Finset (Fin s))
      (endpointCoefficients univ d-∑ r : ↥(retainedPairs s),w r • pairIndicator (group hs r))=0) :
    (∀ a : Fin s,d a=(a.val : ℝ)*d ⟨1,by omega⟩) ∧
    (∀ r : ↥(retainedPairs s),w r=((pairSum r.1 : ℝ)-1)*d ⟨1,by omega⟩) := by
  obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff univ (referencePair (show 2≤ s by omega)) _).mp hz
  have hrow : ∀ e : HubPair s,d e.1.1.1+d e.1.1.2-
      ∑ r : ↥(retainedPairs s),w r*pairIndicator (group hs r) e=c := by
    intro e
    simpa only [Pi.sub_apply,endpointCoefficients,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hc e
  have hc1 : c=d ⟨1,by omega⟩ := by
    have h := hrow (referencePair (show 2≤ s by omega))
    rw [sum_group_indicator_reference] at h
    change d ⟨0,by omega⟩+d ⟨1,by omega⟩-0=c at h
    simpa only [h0,zero_add,sub_zero] using h.symm
  have hactive : ∀ e : ActivePair (show 2≤ s by omega),
      d e.1.1.1.1+d e.1.1.1.2-w (groupIndex hs e)=c := by
    intro e
    simpa only [sum_group_indicator] using hrow e.1
  have hd := grouped_endpoint_rigidity hs d h0 (by
    intro e f hef
    have hidx : groupIndex hs e=groupIndex hs f := Subtype.ext hef
    have he := hactive e
    have hf := hactive f
    rw [hidx] at he
    linarith)
  refine ⟨hd,?_⟩
  intro r
  have hr := mem_retainedPairs.mp r.2
  let e : ActivePair (show 2≤ s by omega) := ⟨r.1,retained_not_reference (by omega) hr⟩
  have hidx : groupIndex hs e=r := Subtype.ext (groupPair_of_retained hs hr)
  have h := hactive e
  rw [hidx,hc1] at h
  change d r.1.1.1.1+d r.1.1.1.2-w r=d ⟨1,by omega⟩ at h
  simp only [pairSum,Nat.cast_add]
  nlinarith [hd r.1.1.1.1,hd r.1.1.1.2]

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart318

section BundlePart319
/- Source: Papers/GraphicalZonotopes/SaturatedPairBases.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule
open Finset
open scoped BigOperators

/-- Distinct numerical hub labels have a unique largest endpoint sum: the
pair of the two largest vertices of the clique. -/
theorem exists_unique_maximum_label_pair {s : ℕ} (C : Finset (Fin s)) (hC : 3≤ C.card) :
    ∃ e₀ : PairIn C,∀ e : PairIn C,e≠ e₀ → endpointLabels C e< endpointLabels C e₀ := by
  have hne : C.Nonempty := card_pos.mp (by omega)
  let m := C.max' hne
  have hm : m∈C := max'_mem C hne
  have hecard : 2≤(C.erase m).card := by rw [card_erase_of_mem hm]; omega
  have hene : (C.erase m).Nonempty := card_pos.mp (by omega)
  let n := (C.erase m).max' hene
  have hn : n∈C.erase m := max'_mem _ hene
  have hnC := (mem_erase.mp hn).2
  have hnm : n< m := lt_of_le_of_ne (le_max' C n hnC) (mem_erase.mp hn).1
  let e₀ := orderedPair C n m hnm hnC hm
  refine ⟨e₀,?_⟩
  intro e he
  have hv : e.1.1.2≤ m := le_max' C _ e.2.2
  have hu : e.1.1.1< m := lt_of_lt_of_le e.1.2.1 hv
  have huErase : e.1.1.1∈C.erase m := mem_erase.mpr ⟨ne_of_lt hu,e.2.1⟩
  have hun : e.1.1.1≤ n := le_max' _ _ huErase
  have heq : ¬(e.1.1.1=n ∧ e.1.1.2=m) := by
    rintro ⟨hu,hv⟩
    exact he (Subtype.ext (Subtype.ext (Prod.ext hu hv)))
  have hun' : e.1.1.1.val≤ n.val := hun
  have hvm' : e.1.1.2.val≤ m.val := hv
  have heq' : ¬(e.1.1.1.val=n.val ∧ e.1.1.2.val=m.val) := by
    rintro ⟨hu,hv⟩
    exact heq ⟨Fin.ext hu,Fin.ext hv⟩
  have hh : e.1.1.1.val+e.1.1.2.val< n.val+m.val := by omega
  change (e.1.1.1.val : ℝ)+(e.1.1.2.val : ℝ)<(n.val : ℝ)+(m.val : ℝ)
  exact_mod_cast hh

/-- Every clique block admits a full independent signed pair basis cancelling
any signed endpoint-label vector, with positive integral scales. -/
theorem saturated_pair_basis {s : ℕ} (C : Finset (Fin s)) (hC : 3≤ C.card)
    (ε : ℝ) (hε : ε=1 ∨ ε= -1) :
    Nonempty (WeightedPureBlock C (2*s : ℕ) (ε • blockClass C (endpointLabels C))
      (C.card.choose 2-1)) := by
  obtain ⟨e₀,he₀⟩ := exists_unique_maximum_label_pair C hC
  let w : PairIn C → ℤ := fun e =>
    ((e₀.1.1.1.val : ℤ)+(e₀.1.1.2.val : ℤ))-((e.1.1.1.val : ℤ)+(e.1.1.2.val : ℤ))
  have hw0 : w e₀=0 := by simp [w]
  have hwp : ∀ e,e≠ e₀ → 0< w e := by
    intro e he
    dsimp only [w]
    apply sub_pos.mpr
    have hh := he₀ e he
    unfold endpointLabels at hh
    exact_mod_cast hh
  have hwb : ∀ e,w e≤(2*s : ℕ) := by
    intro e
    have h1 := e₀.1.1.1.isLt
    have h2 := e₀.1.1.2.isLt
    dsimp [w,endpointLabels]
    push_cast
    omega
  have hε' : -ε=1 ∨ -ε= -1 := by rcases hε with rfl | rfl <;> norm_num
  let P := signed_pair_basis C hC e₀ (-ε) hε' w hw0 hwp (2*s : ℕ) (fun e _ => hwb e)
  have hfun : (fun e : PairIn C => (w e : ℝ))=
      (fun _ : PairIn C => (endpointLabels C e₀ : ℝ))-
      (fun e : PairIn C => (endpointLabels C e : ℝ)) := by
    funext e
    simp [w,endpointLabels]
  have hz : blockClass C (fun _ : PairIn C => (endpointLabels C e₀ : ℝ))=0 :=
    (blockClass_eq_zero_iff C e₀ _).mpr ⟨_,fun _ => rfl⟩
  have ht : blockClass C ((-ε) • fun e : PairIn C => (w e : ℝ))=
      ε • blockClass C (fun e => (endpointLabels C e : ℝ)) := by
    rw [hfun,map_smul,map_sub,hz,zero_sub]
    simp
  exact ⟨ht ▸ P⟩

end GraphicalZonotopes.BooleanModule

end
end
end BundlePart319

section BundlePart320
/- Source: Papers/GraphicalZonotopes/SaturatedFullBlock.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

def matchingEquiv (s : ℕ) : Fin (retainedPairs s).card ≃ ↥(retainedPairs s) :=
  (finCongr (Fintype.card_coe (retainedPairs s)).symm).trans (Fintype.equivFin _).symm

def matchingWeight (r : ↥(retainedPairs s)) : ℤ := (pairSum r.1 : ℤ)-1

theorem matchingWeight_positive (r : ↥(retainedPairs s)) : 0< matchingWeight r := by
  have hr := mem_retainedPairs.mp r.2
  have huv : r.1.1.1.1.val< r.1.1.1.2.val := r.1.1.2.1
  have hn := hr.1
  dsimp [matchingWeight,pairSum]
  push_cast
  omega

theorem matchingWeight_bound (r : ↥(retainedPairs s)) : matchingWeight r≤(2*s : ℕ) := by
  have hu := r.1.1.1.1.isLt
  have hv := r.1.1.1.2.isLt
  dsimp [matchingWeight,pairSum]
  push_cast
  omega

theorem matching_vectors_independent (hs : 5≤ s) :
    LinearIndependent ℝ (fun r : ↥(retainedPairs s) => -pairIndicator (group hs r)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc r
  have hr := mem_retainedPairs.mp r.2
  have hmem : ∀ t : ↥(retainedPairs s),r.1∈group hs t ↔ t=r := by
    intro t
    let e : ActivePair (show 2≤ s by omega) := ⟨r.1,retained_not_reference (by omega) hr⟩
    have hidx : groupIndex hs e=r := Subtype.ext (groupPair_of_retained hs hr)
    exact (mem_group_iff hs e t).trans (by rw [hidx])
  have h := congrFun hc r.1
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.neg_apply,Pi.zero_apply,smul_eq_mul,
    pairIndicator,hmem,neg_ite,neg_zero,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true] at h
  linarith

theorem matching_classes_independent (hs : 5≤ s) :
    LinearIndependent ℝ (fun r : ↥(retainedPairs s) =>
      blockClass univ (-pairIndicator (group hs r))) := by
  apply blockClass_linearIndependent_of_reference univ (referencePair (show 2≤ s by omega))
    _ (matching_vectors_independent hs)
  intro r
  simp [pairIndicator,group_reference_not_mem]

theorem matching_weighted_vector (hs : 5≤ s) :
    (∑ r : ↥(retainedPairs s),(matchingWeight r : ℝ) • (-pairIndicator (group hs r)))=
      (fun _ : HubPair s => (1 : ℝ))-endpointLabels univ := by
  funext e
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.neg_apply,Pi.sub_apply,smul_eq_mul,mul_neg,sum_neg_distrib]
  by_cases he : e=referencePair (show 2≤ s by omega)
  · subst e
    rw [sum_group_indicator_reference]
    norm_num [endpointLabels,referencePair,natPair,orderedPair]
  · let a : ActivePair (show 2≤ s by omega) := ⟨e,he⟩
    rw [show (∑ r : ↥(retainedPairs s),(matchingWeight r : ℝ)*pairIndicator (group hs r) e)=
      (matchingWeight (groupIndex hs a) : ℝ) from sum_group_indicator hs _ a]
    have hsum := groupPair_sum hs a
    change pairSum (groupIndex hs a).1=pairSum e at hsum
    simp only [matchingWeight,Int.cast_sub,Int.cast_natCast,Int.cast_one]
    rw [hsum]
    simp only [pairSum,Nat.cast_add,endpointLabels]
    ring

theorem matching_weighted_class (hs : 5≤ s) :
    (∑ r : ↥(retainedPairs s),(matchingWeight r : ℝ) • blockClass univ (-pairIndicator (group hs r)))=
      -blockClass univ (endpointLabels univ) := by
  simp only [←map_smul,←map_sum]
  rw [matching_weighted_vector,map_sub]
  have hz : blockClass univ (fun _ : HubPair s => (1 : ℝ))=0 :=
    (blockClass_eq_zero_iff univ (referencePair (show 2≤ s by omega)) _).mpr ⟨1,fun _ => rfl⟩
  rw [hz,zero_sub]

def matchingPureBlock (hs : 5≤ s) :
    WeightedPureBlock (univ : Finset (Fin s)) (2*s : ℕ)
      (-blockClass univ (endpointLabels univ)) (retainedPairs s).card where
  column j := -pairIndicator (group hs (matchingEquiv s j))
  realizable j := group_realizable hs (matchingEquiv s j)
  weight j := matchingWeight (matchingEquiv s j)
  positive j := matchingWeight_positive _
  bounded j := matchingWeight_bound _
  independent := (matching_classes_independent hs).comp (matchingEquiv s) (matchingEquiv s).injective
  weighted_sum := ((matchingEquiv s).sum_comp _).trans (matching_weighted_class hs)

theorem matchingPureBlock_rigidity (hs : 5≤ s) (d : Fin s → ℝ)
    (h0 : d ⟨0,by omega⟩=0) (t : Fin (retainedPairs s).card → ℝ)
    (hz : blockClass (univ : Finset (Fin s))
      (endpointCoefficients univ d+∑ j,t j • (matchingPureBlock hs).column j)=0) :
    ∀ a : Fin s,d a=(a.val : ℝ)*d ⟨1,by omega⟩ := by
  let w : ↥(retainedPairs s) → ℝ := fun r => t ((matchingEquiv s).symm r)
  have he : (∑ j,t j • (matchingPureBlock hs).column j)=
      -(∑ r : ↥(retainedPairs s),w r • pairIndicator (group hs r)) := by
    change (∑ j,t j • (-pairIndicator (group hs (matchingEquiv s j))))=_
    simp only [smul_neg,sum_neg_distrib]
    congr 1
    have hh := (matchingEquiv s).sum_comp (fun r => w r • pairIndicator (group hs r))
    simpa only [w,Equiv.symm_apply_apply] using hh
  rw [he,←sub_eq_add_neg] at hz
  exact (full_block_unique hs d h0 w hz).1

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart320

section BundlePart321
/- Source: Papers/GraphicalZonotopes/ScopedBookGeometry.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanModule
open Finset
open scoped BigOperators

variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [LinearOrder J]

local instance sumOrder : LinearOrder (H⊕J) := inferInstanceAs (LinearOrder (H⊕ₗJ))
local instance sumDecidableEq : DecidableEq (H⊕J) := (sumOrder (H:=H) (J:=J)).toDecidableEq

theorem assembled_actual_spoke_iff {z : SetFunction H} (hz : TranslationNormalized z)
    {F : J → SetFunction H} (hF : ∀ j,IsMonotoneBoolean (F j))
    {w : J → ℝ} (hw : ∀ j,0< w j) (hc : Compatible z F w)
    (scope : J → Finset H) (hessential : ∀ j a,a∈scope j → Essential (F j) a)
    (hignore : ∀ j a,a∉scope j → ∀ X,F j (insert a X)=F j X) (a : H) (j : J) :
    ActualRootEdge (basePolytope (assembled z F w)) (Sum.inl a) (Sum.inr j) ↔ a∈scope j := by
  have hn := assembled_normalized hz F hF w
  have hs := assembled_supermodular z F hF w (fun j => (hw j).le) hc
  rw [actualRootEdge_iff_nonzero_elemental hn.1 hs]
  constructor
  · rintro ⟨hne,X,ha,hj,hd⟩
    by_contra hn
    rw [delta_assembled_spoke _ _ _ _ _ _ hj,hignore j a hn,sub_self,mul_zero] at hd
    exact hd rfl
  · intro ha
    obtain ⟨X,hu,hj,hd⟩ := essential_spoke_slack (z:=z) (F:=F)
      (a:=Sum.inl a) (b:=Sum.inr j) hw (hessential j a ha)
    exact ⟨Sum.inl_ne_inr,X,hu,hj,hd⟩

/-- A finite integral circuit with explicit essential-variable sets gives a
literal clique-book polytope with exactly the specified active spokes. -/
theorem scoped_book_of_finite_circuit
    {J : Type*} [Fintype J] [DecidableEq J] {s k : ℕ} (hs : 0< s)
    (F : J → SetFunction (Fin s)) (hF : ∀ j,IsMonotoneBoolean (F j))
    (scope : J → Finset (Fin s))
    (hessential : ∀ j a,a∈scope j → Essential (F j) a)
    (hignore : ∀ j a,a∉scope j → ∀ X,F j (insert a X)=F j X)
    (j₀ : J) (hanchor : scope j₀=univ) (hbranch : ∀ j,(scope j).Nonempty)
    (w : J → ℤ) (hw : ∀ j,0< w j)
    (hrel : (fun j => (w j : ℝ))∈LinearMap.ker (quotientRelation F))
    (huniq : UniqueIntegrableRelation F (fun j => (w j : ℝ)))
    (hcard : Fintype.card J=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin k =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card=
        (univ.filter (fun j : J => a∈scope j)).card := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  letI : Nonempty J := ⟨j₀⟩
  have hk : 0< k := by rw [←hcard]; exact Fintype.card_pos
  let e : Fin k ≃ J := (finCongr hcard.symm).trans (Fintype.equivFin J).symm
  let F' : Fin k → SetFunction (Fin s) := fun i => F (e i)
  let w' : Fin k → ℤ := fun i => w (e i)
  let C' : Fin k → Finset (Fin s) := fun i => scope (e i)
  have hc : (essentialSpokeGraph F').Connected := by
    apply essentialSpokeGraph_connected_of_anchor F' (e.symm j₀)
    · intro a
      apply hessential
      simp only [e.apply_symm_apply,hanchor,mem_univ]
    · intro i
      obtain ⟨a,ha⟩ := hbranch (e i)
      exact ⟨a,hessential (e i) a ha⟩
  obtain ⟨z,hzn,hzc⟩ := (mem_quotientRelation_ker_iff F _).mp hrel
  have hrel' : (fun i => (w' i : ℝ))∈LinearMap.ker (quotientRelation F') := by
    apply (mem_quotientRelation_ker_iff F' _).mpr
    have hh : Compatible z F (fun j => (w' (e.symm j) : ℝ)) := by
      simpa only [w',e.apply_symm_apply] using hzc
    exact ⟨z,hzn,(compatible_reindex e z F (fun i => (w' i : ℝ))).mpr hh⟩
  have huniq' : UniqueIntegrableRelation F' (fun i => (w' i : ℝ)) := by
    intro t ht
    obtain ⟨u,hun,huc⟩ := ht
    have hold : Compatible u F (fun j => t (e.symm j)) :=
      (compatible_reindex e u F t).mp huc
    obtain ⟨c,hc'⟩ := huniq (fun j => t (e.symm j)) ⟨u,hun,hold⟩
    refine ⟨c,?_⟩
    funext i
    simpa only [e.symm_apply_apply,Pi.smul_apply,w'] using congrFun hc' (e i)
  obtain ⟨u,hun,hui,huc⟩ := integral_compatible_lift F' (fun i => hF (e i)) w' hrel'
  have hw' : ∀ i,0<(w' i : ℝ) := fun i => by exact_mod_cast hw (e i)
  let f := assembled u F' (fun i => (w' i : ℝ))
  have hfn := assembled_normalized hun F' (fun i => hF (e i)) (fun i => (w' i : ℝ))
  have hfi := assembled_integerValued hui F' (fun i => hF (e i)) w'
  have hfe := positive_circuit_extreme hun (fun i => hF (e i))
    (fun i => (hw' i).le) ⟨⟨0,hk⟩,ne_of_gt (hw' ⟨0,hk⟩)⟩ huc huniq'
  refine ⟨f,hfn,hfi,hfe,assembled_graphical u F' _,
    assembled_fullDimension hun (fun i => hF (e i)) hw' huc hc,
    hfi.basePolytope hfn.1 hfe.2.1,?_⟩
  intro a
  have hedge : ∀ i : Fin k,ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr i) ↔ a∈scope (e i) := by
    intro i
    exact assembled_actual_spoke_iff hun (fun i => hF (e i)) hw' huc C'
      (fun j a ha => hessential (e j) a ha) (fun j a ha => hignore (e j) a ha) a i
  apply card_bij (fun i _ => e i)
  · intro i hi
    simp only [mem_filter,mem_univ,true_and] at hi ⊢
    exact (hedge i).mp hi
  · intro i hi j hj he
    exact e.injective he
  · intro j hj
    refine ⟨e.symm j,?_,e.apply_symm_apply j⟩
    simp only [mem_filter,mem_univ,true_and] at hj ⊢
    apply (hedge _).mpr
    simpa only [e.apply_symm_apply] using hj

end GraphicalZonotopes.BooleanModule

end
end
end BundlePart321

section BundlePart322
/- Source: Papers/GraphicalZonotopes/ScopedAnchorCircuits.lean -/





@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanModule
open Finset
open scoped BigOperators

variable {s : ℕ}

def coefficientExtension (A : Finset (Fin s)) (t : A → ℝ) : Fin s → ℝ :=
  fun a => if h : a∈A then t ⟨a,h⟩ else 0

@[simp] theorem coefficientExtension_subtype (A : Finset (Fin s)) (t : A → ℝ) (a : A) :
    coefficientExtension A t a.1=t a := by simp [coefficientExtension,a.2]

theorem coefficientExtension_not_mem (A : Finset (Fin s)) (t : A → ℝ) {a : Fin s}
    (ha : a∉A) : coefficientExtension A t a=0 := by simp [coefficientExtension,ha]

theorem sum_coefficientExtension {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (A : Finset (Fin s)) (t : A → ℝ) (v : Fin s → W) :
    (∑ a : A,t a • v a.1)=∑ a,coefficientExtension A t a • v a := by
  have hfirst : (∑ a : A,t a • v a.1)=∑ a∈A,coefficientExtension A t a • v a := by
    rw [←sum_coe_sort A (fun a => coefficientExtension A t a • v a)]
    exact sum_congr rfl (fun a _ => by rw [coefficientExtension_subtype])
  rw [hfirst]
  apply sum_subset (subset_univ _)
  intro a ha hn
  rw [coefficientExtension_not_mem A t hn,zero_smul]

abbrev ScopedAnchorIndex (A : Finset (Fin s)) (r : BookBlock (Fin s) → ℕ) :=
  A ⊕ (Σ C : BookBlock (Fin s),Fin (r C))

def scopedAnchorScope (A : Finset (Fin s)) (r : BookBlock (Fin s) → ℕ) :
    ScopedAnchorIndex A r → Finset (Fin s)
  | .inl _ => univ
  | .inr j => j.1.1

section Circuit
variable (A : Finset (Fin s)) (η : ℝ) (FA : A → SetFunction (Fin s))
    (hFA : ∀ a,responseClass (FA a)=η • responseClass (thresholdStar a.1))
    (wA : A → ℤ) (M : ℤ) (r : BookBlock (Fin s) → ℕ)
    (P : ∀ C : BookBlock (Fin s),WeightedPureBlock C.1 M
      (-((η*((-1 : ℝ)^(C.1.card-3))) • blockClass C.1
        (endpointCoefficients C.1 (coefficientExtension A (fun a => (wA a : ℝ)))))) (r C))

def scopedAnchorVector : ScopedAnchorIndex A r → ResponseQuotient (Fin s)
  | .inl a => responseClass (FA a)
  | .inr j => blockClass j.1.1 ((P j.1).column j.2)

def scopedAnchorWeight : ScopedAnchorIndex A r → ℤ
  | .inl a => wA a
  | .inr j => (P j.1).weight j.2

def scopedAnchorCombination (t : ScopedAnchorIndex A r → ℝ) (C : BookBlock (Fin s)) : PairIn C.1 → ℝ :=
  (η*((-1 : ℝ)^(C.1.card-3))) • endpointCoefficients C.1
    (coefficientExtension A (fun a => t (.inl a)))+
    ∑ j : Fin (r C),t (.inr ⟨C,j⟩) • (P C).column j

include hFA in
theorem scopedAnchor_sum_blocks (t : ScopedAnchorIndex A r → ℝ) :
    (∑ j,t j • scopedAnchorVector A η FA wA M r P j)=
      ∑ C : BookBlock (Fin s),blockClass C.1 (scopedAnchorCombination A η wA M r P t C) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  change (∑ a : A,t (.inl a) • responseClass (FA a))+
    (∑ C,∑ j : Fin (r C),t (.inr ⟨C,j⟩) • blockClass C.1 ((P C).column j))=_
  simp_rw [hFA]
  have ha : (∑ a : A,t (.inl a) • η • responseClass (thresholdStar a.1))=
      η • (∑ a : A,t (.inl a) • responseClass (thresholdStar a.1)) := by
    rw [smul_sum]
    exact sum_congr rfl (fun a _ => smul_comm _ _ _)
  rw [ha,sum_coefficientExtension A (fun a => t (.inl a))
    (fun a => responseClass (thresholdStar a)),weighted_threshold_response,smul_sum]
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro C hC
  simp only [scopedAnchorCombination,map_add,map_smul,map_sum,mul_smul]

include hFA in
theorem scopedAnchor_weighted_sum :
    (∑ j,(scopedAnchorWeight A η wA M r P j : ℝ) • scopedAnchorVector A η FA wA M r P j)=0 := by
  rw [scopedAnchor_sum_blocks A η FA hFA wA M r P]
  apply sum_eq_zero
  intro C hC
  simp only [scopedAnchorCombination,map_add,map_smul,map_sum,scopedAnchorWeight]
  rw [(P C).weighted_sum]
  exact add_neg_cancel _

theorem scopedAnchor_pure_independent :
    LinearIndependent ℝ (fun j : Σ C : BookBlock (Fin s),Fin (r C) =>
      blockClass j.1.1 ((P j.1).column j.2)) := by
  have hpair : ∀ C : BookBlock (Fin s),∃ p : PairIn C.1,True := by
    intro C
    obtain ⟨p,hp⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨p,trivial⟩
  exact block_families_independent Subtype.val Subtype.val_injective
    (fun C => (hpair C).choose) (fun C => (P C).column) (fun C => (P C).independent)

def ScopedAnchorRigidity : Prop :=
  ∀ t : ScopedAnchorIndex A r → ℝ,
    (∀ C : BookBlock (Fin s),blockClass C.1 (scopedAnchorCombination A η wA M r P t C)=0) →
      ∃ c : ℝ,∀ a : A,t (.inl a)=c*(wA a : ℝ)

include hFA in
theorem scopedAnchor_unique (hrigid : ScopedAnchorRigidity A η wA M r P)
    (t : ScopedAnchorIndex A r → ℝ)
    (ht : (∑ j,t j • scopedAnchorVector A η FA wA M r P j)=0) :
    ∃ c : ℝ,t=c • (fun j => (scopedAnchorWeight A η wA M r P j : ℝ)) := by
  rw [scopedAnchor_sum_blocks A η FA hFA wA M r P] at ht
  have hpair : ∀ C : BookBlock (Fin s),∃ p : PairIn C.1,True := by
    intro C
    obtain ⟨p,hp⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨p,trivial⟩
  have hb := block_sum_zero_component Subtype.val Subtype.val_injective
    (fun C => (hpair C).choose) (scopedAnchorCombination A η wA M r P t) ht
  obtain ⟨c,hc⟩ := hrigid t hb
  have hz : (∑ j : ScopedAnchorIndex A r,
      (t j-c*(scopedAnchorWeight A η wA M r P j : ℝ)) •
        scopedAnchorVector A η FA wA M r P j)=0 := by
    simp only [sub_smul,mul_smul,sum_sub_distrib,←smul_sum]
    rw [scopedAnchor_sum_blocks A η FA hFA wA M r P,ht,
      scopedAnchor_weighted_sum A η FA hFA wA M r P,smul_zero,sub_self]
  rw [Fintype.sum_sum_type] at hz
  have ha : (∑ a : A,(t (.inl a)-c*(scopedAnchorWeight A η wA M r P (.inl a) : ℝ)) •
      scopedAnchorVector A η FA wA M r P (.inl a))=0 := by
    apply sum_eq_zero
    intro a ha
    rw [scopedAnchorWeight,hc,sub_self,zero_smul]
  rw [ha,zero_add] at hz
  have hp := Fintype.linearIndependent_iff.mp (scopedAnchor_pure_independent A η wA M r P)
    (fun j => t (.inr j)-c*(scopedAnchorWeight A η wA M r P (.inr j) : ℝ)) hz
  refine ⟨c,?_⟩
  funext j
  cases j with
  | inl a => exact hc a
  | inr j => exact sub_eq_zero.mp (hp j)

include hFA in
/-- The complete circuit theorem retaining its exact essential-variable
scopes; the final principal constructions supply every algebraic premise. -/
theorem scoped_book_of_anchor_circuit (hs : 3≤ s)
    (hAb : ∀ a,IsMonotoneBoolean (FA a)) (hAe : ∀ a i,Essential (FA a) i)
    (a₀ : A) (hwA : ∀ a,0< wA a)
    (hrigid : ScopedAnchorRigidity A η wA M r P)
    {k : ℕ} (hcard : Fintype.card (ScopedAnchorIndex A r)=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin k =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card=
        (univ.filter (fun j : ScopedAnchorIndex A r => a∈scopedAnchorScope A r j)).card := by
  have hF : ∀ C j,∃ F : SetFunction (Fin s),IsMonotoneBoolean F ∧
      (∀ a,a∈C.1 → Essential F a) ∧
      (∀ a,a∉C.1 → ∀ X,F (insert a X)=F X) ∧
      responseClass F=blockClass C.1 ((P C).column j) := fun C j => (P C).realizable j
  choose F hFb hFe hFi hFc using hF
  let G : ScopedAnchorIndex A r → SetFunction (Fin s)
    | .inl a => FA a
    | .inr j => F j.1 j.2
  have hGb : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | inl a => exact hAb a
    | inr j => exact hFb j.1 j.2
  have hGe : ∀ j a,a∈scopedAnchorScope A r j → Essential (G j) a := by
    intro j a ha
    cases j with
    | inl b => exact hAe b a
    | inr j => exact hFe j.1 j.2 a ha
  have hGi : ∀ j a,a∉scopedAnchorScope A r j → ∀ X,G j (insert a X)=G j X := by
    intro j a ha X
    cases j with
    | inl b => exact False.elim (ha (mem_univ _))
    | inr j => exact hFi j.1 j.2 a ha X
  have hGc : ∀ j,responseClass (G j)=scopedAnchorVector A η FA wA M r P j := by
    intro j
    cases j with
    | inl a => rfl
    | inr j => exact hFc j.1 j.2
  have hnon : ∀ j,(scopedAnchorScope A r j).Nonempty := by
    intro j
    cases j with
    | inl a => exact ⟨⟨0,by omega⟩,mem_univ _⟩
    | inr j =>
      change j.1.1.Nonempty
      exact card_pos.mp (by have h := (mem_largeBlocks.mp j.1.2).2; omega)
  have hw : ∀ j,0< scopedAnchorWeight A η wA M r P j := by
    intro j
    cases j with
    | inl a => exact hwA a
    | inr j => exact (P j.1).positive j.2
  have hrel : (fun j => (scopedAnchorWeight A η wA M r P j : ℝ))∈LinearMap.ker (quotientRelation G) := by
    change quotientRelation G _=0
    rw [quotientRelation_apply_eq_sum]
    simp_rw [hGc]
    exact scopedAnchor_weighted_sum A η FA hFA wA M r P
  have huniq : UniqueIntegrableRelation G (fun j => (scopedAnchorWeight A η wA M r P j : ℝ)) := by
    intro t ht
    have ht0 : quotientRelation G t=0 := (mem_quotientRelation_ker_iff G t).mpr ht
    rw [quotientRelation_apply_eq_sum] at ht0
    simp_rw [hGc] at ht0
    exact scopedAnchor_unique A η FA hFA wA M r P hrigid t ht0
  exact scoped_book_of_finite_circuit (by omega) G hGb (scopedAnchorScope A r)
    hGe hGi (.inl a₀) rfl hnon (scopedAnchorWeight A η wA M r P) hw hrel huniq hcard

end Circuit
end GraphicalZonotopes.BooleanModule

end
end
end BundlePart322

section BundlePart323
/- Source: Papers/GraphicalZonotopes/JunctionStar.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule
open Finset PowersetTransform
variable {H : Type*} [Fintype H] [LinearOrder H]

/-- The second all-essential anchor, `x_a` conjoined with the disjunction of
all other variables. -/
def junctionStar (a : H) : SetFunction H :=
  fun S => if a∈S ∧ 2≤ S.card then 1 else 0

theorem junctionStar_boolean (hs : 2≤ Fintype.card H) (a : H) :
    IsMonotoneBoolean (junctionStar a) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro S T hST
    by_cases hS : a∈S ∧ 2≤ S.card
    · have hT : a∈T ∧ 2≤ T.card := ⟨hST hS.1,hS.2.trans (card_le_card hST)⟩
      simp only [junctionStar,if_pos hS,if_pos hT,le_refl]
    · unfold junctionStar
      rw [if_neg hS]
      split_ifs <;> norm_num
  · intro S
    unfold junctionStar
    split_ifs <;> simp
  · simp [junctionStar]
  · simp [junctionStar,hs]

theorem junctionStar_zero_iff (a : H) (S : Finset H) :
    junctionStar a S=0 ↔ a∉S ∨ S.card<2 := by
  by_cases ha : a∈S <;> simp [junctionStar,ha] <;> omega

theorem junctionStar_one_iff (a : H) (S : Finset H) :
    junctionStar a S=1 ↔ a∈S ∧ 2≤ S.card := by
  by_cases ha : a∈S <;> simp [junctionStar,ha] <;> omega

theorem junctionStar_essential (hs : 2≤ Fintype.card H) (a i : H) :
    Essential (junctionStar a) i := by
  by_cases hi : i=a
  · subst i
    have he : ∃ b : H,b≠ a := by
      by_contra hn
      have hsub : (univ : Finset H)⊆{a} := by
        intro b hb
        simp only [mem_singleton]
        by_contra hba
        exact hn ⟨b,hba⟩
      have hc := card_le_card hsub
      simp only [card_univ,card_singleton] at hc
      omega
    obtain ⟨b,hba⟩ := he
    refine ⟨{b},by simpa only [mem_singleton] using hba.symm,?_⟩
    simp [junctionStar,hba,Ne.symm hba]
  · refine ⟨{a},by simpa only [mem_singleton] using hi,?_⟩
    simp [junctionStar,hi,Ne.symm hi]

theorem junctionStar_negativeResponse (hs : 2≤ Fintype.card H) (a : H)
    {u v : H} (huv : u≠ v) (S : Finset H) (hu : u∉S) (hv : v∉S) :
    negativeResponse (junctionStar a) u v S=
      if a∈S then exactlyOne S else 0 := by
  have hone : negativeResponse (junctionStar a) u v S=1 ↔ a∈S ∧ S.card=1 := by
    rw [negativeResponse_eq_one_iff (junctionStar_boolean hs a),
      junctionStar_zero_iff,junctionStar_one_iff,junctionStar_one_iff]
    simp only [mem_insert,card_insert_of_notMem hu,card_insert_of_notMem hv]
    constructor
    · rintro ⟨hzero,⟨hua,huc⟩,⟨hva,hvc⟩⟩
      have ha : a∈S := by
        by_contra hn
        have hau : a=u := hua.resolve_right hn
        have hav : a=v := hva.resolve_right hn
        exact huv (hau.symm.trans hav)
      have hc : S.card<2 := hzero.resolve_left (not_not.mpr ha)
      exact ⟨ha,by omega⟩
    · rintro ⟨ha,hc⟩
      exact ⟨Or.inr (by omega),⟨Or.inr ha,by omega⟩,⟨Or.inr ha,by omega⟩⟩
  rcases negativeResponse_values (junctionStar_boolean hs a) u v S with hz | ho
  · have hn : ¬(a∈S ∧ S.card=1) := by
      intro h
      have hh := hone.mpr h
      rw [hz] at hh
      norm_num at hh
    by_cases ha : a∈S
    · have hc : S.card≠1 := fun h => hn ⟨ha,h⟩
      simp [hz,ha,exactlyOne,hc]
    · simp [hz,ha]
  · obtain ⟨ha,hc⟩ := hone.mp ho
    simp [ho,ha,exactlyOne,hc]

/-- Both anchor responses are opposite in the actual quotient, in every
clique block simultaneously. -/
theorem junctionStar_response_class (hs : 2≤ Fintype.card H) (a : H) :
    responseClass (junctionStar a)= -responseClass (thresholdStar a) := by
  let x : HubResponseRow H → ℝ := fun r => exactlyOneCoefficient r.2.1.card
  have hvec : responseVector (junctionStar a)+responseVector (thresholdStar a)=
      rowLowerEquiv x := by
    funext r
    have hu : r.1.1.1∉r.2.1 := by
      intro h
      exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
    have hv : r.1.1.2∉r.2.1 := by
      intro h
      exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
    change negativeResponse (junctionStar a) r.1.1.1 r.1.1.2 r.2.1+
      negativeResponse (thresholdStar a) r.1.1.1 r.1.1.2 r.2.1=
      lowerSum (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
        (fun T => exactlyOneCoefficient T.1.card) r.2
    rw [junctionStar_negativeResponse hs a (ne_of_lt r.1.2.1) _ hu hv,
      thresholdStar_negativeResponse a (ne_of_lt r.1.2.1) _ hu hv,
      lowerSum_restriction _ (fun T : Finset H => exactlyOneCoefficient T.card) r.2]
    change _=zeta (fun T : Finset H => exactlyOneCoefficient T.card) r.2.1
    rw [zeta_exactlyOneCoefficient]
    by_cases ha : a∈r.2.1 <;> simp [ha]
  have hz : coefficientClass x=0 := by
    apply (coefficientClass_eq_zero_iff x).mpr
    intro r t hrt
    have hc := congrArg (fun C : CliqueIndex (⊤ : SimpleGraph H) => C.1.card) hrt
    have hr := rowClique_card_eq_context_add_two r
    have ht := rowClique_card_eq_context_add_two t
    have he : r.2.1.card=t.2.1.card := by
      change (rowClique r).card=(rowClique t).card at hc
      omega
    change exactlyOneCoefficient r.2.1.card=exactlyOneCoefficient t.2.1.card
    rw [he]
  have hsum : responseClass (junctionStar a)+responseClass (thresholdStar a)=0 := by
    change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ _+
      (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ _=0
    rw [← map_add,hvec]
    exact hz
  exact eq_neg_of_add_eq_zero_left hsum

end GraphicalZonotopes.BooleanModule

end
end
end BundlePart323

section BundlePart324
/- Source: Papers/GraphicalZonotopes/SaturatedGeneralBlocks.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

abbrev fullBlock (hs : 3≤ s) : BookBlock (Fin s) :=
  ⟨univ,mem_largeBlocks.mpr ⟨subset_univ _,by simpa using hs⟩⟩

def eta (s : ℕ) : ℝ := (-1 : ℝ)^(s-3)

theorem eta_sign (s : ℕ) : eta s=1 ∨ eta s= -1 := neg_one_pow_eq_or ℝ _

theorem eta_full_factor (hs : 3≤ s) : eta s*((-1 : ℝ)^((fullBlock hs).1.card-3))=1 := by
  change eta s*((-1 : ℝ)^((univ : Finset (Fin s)).card-3))=1
  rw [card_univ,Fintype.card_fin]
  change eta s*eta s=1
  rcases eta_sign s with h | h <;> rw [h] <;> norm_num

def anchorFamily (hs : 3≤ s) (a : BookAnchor hs) : SetFunction (Fin s) :=
  if eta s=1 then thresholdStar a.1 else junctionStar a.1

theorem anchorFamily_boolean (hs : 3≤ s) (a : BookAnchor hs) :
    IsMonotoneBoolean (anchorFamily hs a) := by
  unfold anchorFamily
  split_ifs
  · exact thresholdStar_boolean _
  · exact junctionStar_boolean (by simpa using (show 2≤ s by omega)) _

theorem anchorFamily_essential (hs : 3≤ s) (a : BookAnchor hs) (i : Fin s) :
    Essential (anchorFamily hs a) i := by
  unfold anchorFamily
  split_ifs
  · exact thresholdStar_essential (by simpa using hs) _ _
  · exact junctionStar_essential (by simpa using (show 2≤ s by omega)) _ _

theorem anchorFamily_response (hs : 3≤ s) (a : BookAnchor hs) :
    responseClass (anchorFamily hs a)=eta s • responseClass (thresholdStar a.1) := by
  unfold anchorFamily
  by_cases h : eta s=1
  · simp only [h,ite_true,one_smul]
  · have he : eta s= -1 := (eta_sign s).resolve_left h
    rw [if_neg h,junctionStar_response_class (by simpa using (show 2≤ s by omega)),he,neg_one_smul]

def anchorWeights (hs : 3≤ s) (a : BookAnchor hs) : ℤ := (a.1.val : ℤ)

theorem anchorWeights_positive (hs : 3≤ s) (a : BookAnchor hs) : 0< anchorWeights hs a := by
  have h := (mem_erase.mp a.2).1
  have hv : a.1.val≠0 := fun he => h (Fin.ext he)
  change 0<(a.1.val : ℤ)
  omega

theorem coefficientExtension_anchor_labels (hs : 3≤ s) :
    coefficientExtension ((univ : Finset (Fin s)).erase (bookZero hs))
      (fun a => (anchorWeights hs a : ℝ))=(fun a : Fin s => (a.val : ℝ)) := by
  funext a
  by_cases ha : a=bookZero hs
  · subst a
    simp [coefficientExtension,bookZero]
  · have ham : a∈(univ : Finset (Fin s)).erase (bookZero hs) := mem_erase.mpr ⟨ha,mem_univ _⟩
    simp only [coefficientExtension,dif_pos ham,anchorWeights,Int.cast_natCast]

def pureRank (s : ℕ) (C : BookBlock (Fin s)) : ℕ :=
  if C.1=univ then (retainedPairs s).card else C.1.card.choose 2-1

abbrev anchorSet (hs : 3≤ s) : Finset (Fin s) := (univ : Finset (Fin s)).erase (bookZero hs)

theorem pureRank_full (hs : 3≤ s) : pureRank s (fullBlock hs)=(retainedPairs s).card := by
  simp [pureRank,fullBlock]

def pureBlock (hs : 5≤ s) (C : BookBlock (Fin s)) :
    WeightedPureBlock C.1 (2*s : ℕ)
      (-((eta s*((-1 : ℝ)^(C.1.card-3))) • blockClass C.1
        (endpointCoefficients C.1 (coefficientExtension (anchorSet (show 3≤ s by omega))
          (fun a => (anchorWeights (show 3≤ s by omega) a : ℝ)))))) (pureRank s C) := by
  classical
  have hd := coefficientExtension_anchor_labels (show 3≤ s by omega)
  by_cases hC : C=fullBlock (show 3≤ s by omega)
  · subst C
    let e : Fin (pureRank s (fullBlock (show 3≤ s by omega))) ≃
        Fin (retainedPairs s).card := finCongr (pureRank_full (show 3≤ s by omega))
    refine {
      column := fun j => (matchingPureBlock hs).column (e j)
      realizable := fun j => (matchingPureBlock hs).realizable (e j)
      weight := fun j => (matchingPureBlock hs).weight (e j)
      positive := fun j => (matchingPureBlock hs).positive (e j)
      bounded := fun j => (matchingPureBlock hs).bounded (e j)
      independent := (matchingPureBlock hs).independent.comp e e.injective
      weighted_sum := ?_ }
    rw [e.sum_comp (fun j => ((matchingPureBlock hs).weight j : ℝ) •
      blockClass univ ((matchingPureBlock hs).column j)),
      (matchingPureBlock hs).weighted_sum,eta_full_factor,one_smul,hd]
    rfl
  · have hCu : C.1≠ univ := fun h => hC (Subtype.ext h)
    rw [pureRank,if_neg hCu]
    have hε : -(eta s*((-1 : ℝ)^(C.1.card-3)))=1 ∨
        -(eta s*((-1 : ℝ)^(C.1.card-3)))= -1 := by
      rcases eta_sign s with h1 | h1 <;>
        rcases neg_one_pow_eq_or ℝ (C.1.card-3) with h2 | h2 <;> simp [h1,h2]
    let Q := Classical.choice (saturated_pair_basis C.1 (mem_largeBlocks.mp C.2).2 _ hε)
    refine {
      column := Q.column
      realizable := Q.realizable
      weight := Q.weight
      positive := Q.positive
      bounded := Q.bounded
      independent := Q.independent
      weighted_sum := ?_ }
    rw [Q.weighted_sum,hd,neg_smul]
    rfl

theorem pureBlock_full_column (hs : 5≤ s)
    (j : Fin (pureRank s (fullBlock (show 3≤ s by omega)))) :
    (pureBlock hs (fullBlock (show 3≤ s by omega))).column j =
      (matchingPureBlock hs).column (finCongr (pureRank_full (show 3≤ s by omega)) j) := by
  unfold pureBlock
  simp only [dite_true] <;> rfl

theorem pureRank_proper (hs : 3≤ s) (C : BookBlock (Fin s)) (hC : C≠ fullBlock hs) :
    pureRank s C=C.1.card.choose 2-1 := by
  have h : C.1≠ univ := fun he => hC (Subtype.ext he)
  simp only [pureRank,h,ite_false]

-- The checked column identity above supplies the data needed below;
-- elaboration need not expand the Boolean realizations of those columns.
attribute [local irreducible] pureBlock matchingPureBlock

/-- The full-clique matching rows force every all-hub anchor scale before any
proper-clique basis is used. -/
theorem general_scale_rigidity (hs : 5≤ s) :
    ScopedAnchorRigidity (anchorSet (show 3≤ s by omega)) (eta s)
      (anchorWeights (show 3≤ s by omega)) (2*s : ℕ) (pureRank s) (pureBlock hs) := by
  intro t ht
  let d := coefficientExtension (anchorSet (show 3≤ s by omega)) (fun a => t (.inl a))
  have h0 : d ⟨0,by omega⟩=0 := by
    simp [d,coefficientExtension,anchorSet,bookZero]
  have hfull := ht (fullBlock (show 3≤ s by omega))
  dsimp only [scopedAnchorCombination] at hfull
  -- Rewrite the displayed coefficient only. The same coefficient also
  -- occurs in the type of the fixed circuit data, which must stay intact.
  rw (occs := .pos [1]) [eta_full_factor (show 3≤ s by omega)] at hfull
  rw [one_smul] at hfull
  let e : Fin (pureRank s (fullBlock (show 3≤ s by omega))) ≃
      Fin (retainedPairs s).card := finCongr (pureRank_full (show 3≤ s by omega))
  let t' : Fin (retainedPairs s).card → ℝ :=
    fun j => t (.inr ⟨fullBlock (show 3≤ s by omega),e.symm j⟩)
  have hsum : (∑ j,t (.inr ⟨fullBlock (show 3≤ s by omega),j⟩) •
      (pureBlock hs (fullBlock (show 3≤ s by omega))).column j) =
      ∑ j,t' j • (matchingPureBlock hs).column j := by
    calc
      _ = ∑ j,t (.inr ⟨fullBlock (show 3≤ s by omega),j⟩) •
          (matchingPureBlock hs).column (e j) := by
        apply sum_congr rfl
        intro j hj
        exact congrArg (fun v => t (.inr ⟨fullBlock (show 3≤ s by omega),j⟩) • v)
          (pureBlock_full_column hs j)
      _ = _ := by
        have he := e.sum_comp (fun j => t' j • (matchingPureBlock hs).column j)
        simpa only [t',Equiv.symm_apply_apply] using he
  rw [hsum] at hfull
  have hd := matchingPureBlock_rigidity hs d h0 t' hfull
  refine ⟨d ⟨1,by omega⟩,?_⟩
  intro a
  have ha := hd a.1
  change coefficientExtension (anchorSet (show 3≤ s by omega)) (fun a => t (.inl a)) a.1=_ at ha
  rw [coefficientExtension_subtype] at ha
  simpa only [anchorWeights,Int.cast_natCast,mul_comm] using ha

theorem sum_bookBlock_split {W : Type*} [AddCommMonoid W] (hs : 3≤ s)
    (f : BookBlock (Fin s) → W) :
    (∑ C : BookBlock (Fin s),f C)=f (fullBlock hs)+
      ∑ C : {C : BookBlock (Fin s) // C≠ fullBlock hs},f C.1 := by
  have h := (Equiv.optionSubtypeNe (fullBlock hs)).sum_comp f
  rw [Fintype.sum_option] at h
  exact h.symm

theorem general_circuit_card (hs : 5≤ s) :
    Fintype.card (ScopedAnchorIndex (anchorSet (show 3≤ s by omega)) (pureRank s))=cliqueCapacity s := by
  rw [Fintype.card_sum,Fintype.card_sigma]
  simp only [Fintype.card_fin,Fintype.card_coe,anchorSet,card_erase_of_mem (mem_univ _),card_univ]
  rw [sum_bookBlock_split (show 3≤ s by omega),pureRank_full]
  have hproper : ∀ C : {C : BookBlock (Fin s) // C≠ fullBlock (show 3≤ s by omega)},
      pureRank s C.1=C.1.1.card.choose 2-1 := fun C =>
    pureRank_proper (show 3≤ s by omega) C.1 C.2
  simp_rw [hproper]
  have h := BookBlock_dimension_sum (H:=Fin s)
  rw [sum_bookBlock_split (show 3≤ s by omega)] at h
  have hfullcard : (fullBlock (show 3≤ s by omega)).1.card=s := by simp [fullBlock]
  rw [hfullcard,Fintype.card_fin] at h
  have hc := retained_count_add_anchors hs
  have hchoose : 1≤ s.choose 2 := Nat.choose_pos (by omega)
  omega

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart324

section BundlePart325
/- Source: Papers/GraphicalZonotopes/SaturatedGeneralAttainment.lean -/





/-! # Exact spoke counts in the saturated matching construction

The proper blocks avoiding a selected hub are exactly the response blocks on
the other hubs.  This identifies the missing spokes with their total dimension.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanModule.Saturated
open Finset
open scoped BigOperators
variable {s : ℕ}

theorem nonneighbor_count (hs : 5 ≤ s) (a : Fin s) :
    (univ.filter (fun j : ScopedAnchorIndex (anchorSet (show 3 ≤ s by omega)) (pureRank s) =>
      a ∉ scopedAnchorScope (anchorSet (show 3 ≤ s by omega)) (pureRank s) j)).card + 1 =
      cliqueCapacity (s - 1) := by
  classical
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_sum_type]
  simp only [scopedAnchorScope,mem_univ,not_true_eq_false,ite_false,sum_const_zero,zero_add]
  rw [Fintype.sum_sigma]
  have hc : ∀ C : BookBlock (Fin s),
      (∑ j : Fin (pureRank s C),if a ∉ C.1 then (1 : ℕ) else 0) =
        if a ∉ C.1 then C.1.card.choose 2 - 1 else 0 := by
    intro C
    by_cases ha : a ∈ C.1
    · simp only [ha,not_true_eq_false,ite_false,sum_const_zero]
    · have hCu : C.1 ≠ univ := by
        intro he
        apply ha
        rw [he]
        exact mem_univ a
      simp only [ha,not_false_eq_true,ite_true,sum_const,card_univ,Fintype.card_fin,
        smul_eq_mul,mul_one,pureRank,if_neg hCu]
  simp_rw [hc]
  rw [sum_coe_sort (largeBlocks (univ : Finset (Fin s)))
    (fun C => if a ∉ C then C.card.choose 2 - 1 else 0)]
  rw [← sum_filter]
  have hfilter : (largeBlocks (univ : Finset (Fin s))).filter (fun C => a ∉ C) =
      largeBlocks (univ.erase a) := by
    ext C
    simp only [mem_filter,mem_largeBlocks,subset_erase]
    tauto
  rw [hfilter,largeBlocks_dimension_sum,← cliqueCapacity_eq_dimension_sum,
    card_erase_of_mem (mem_univ a),card_univ,Fintype.card_fin]

theorem neighbor_count (hs : 5 ≤ s) (a : Fin s) :
    (univ.filter (fun j : ScopedAnchorIndex (anchorSet (show 3 ≤ s by omega)) (pureRank s) =>
      a ∈ scopedAnchorScope (anchorSet (show 3 ≤ s by omega)) (pureRank s) j)).card =
        saturatedHubNeighbors s := by
  classical
  have hc := card_filter_add_card_filter_not
    (s := (univ : Finset (ScopedAnchorIndex (anchorSet (show 3 ≤ s by omega)) (pureRank s))))
    (p := fun j => a ∈ scopedAnchorScope (anchorSet (show 3 ≤ s by omega)) (pureRank s) j)
  rw [card_univ,general_circuit_card hs] at hc
  have hn := nonneighbor_count hs a
  have hmono := cliqueCapacity_pred_le (show 1 ≤ s by omega)
  unfold saturatedHubNeighbors
  rw [if_neg (by omega : s ≠ 2)]
  omega

/-- For every number of hubs at least five, the matching circuit gives an
actual full-dimensional lattice polytope with exactly the optimal number of
active spokes at each hub. -/
theorem spoke_attainment (s : ℕ) (hs : 5 ≤ s) :
    ∃ f : SetFunction (Fin s ⊕ Fin (cliqueCapacity s)),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s (cliqueCapacity s)) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card =
          saturatedHubNeighbors s := by
  let hs3 : 3 ≤ s := by omega
  let a₀ : anchorSet hs3 := ⟨⟨1,by omega⟩,by
    simp only [anchorSet,mem_erase,mem_univ,and_true,bookZero]
    intro he
    have hv := congrArg Fin.val he
    norm_num at hv⟩
  obtain ⟨f,hn,hi,he,hG,hd,hl,hcount⟩ := scoped_book_of_anchor_circuit
    (anchorSet hs3) (eta s) (anchorFamily hs3) (anchorFamily_response hs3)
    (anchorWeights hs3) (2*s : ℕ) (pureRank s) (pureBlock hs) hs3
    (anchorFamily_boolean hs3) (anchorFamily_essential hs3) a₀
    (anchorWeights_positive hs3) (general_scale_rigidity hs) (general_circuit_card hs)
  exact ⟨f,hn,hi,he,hG,hd,hl,fun a => (hcount a).trans (neighbor_count hs a)⟩

end GraphicalZonotopes.BooleanModule.Saturated

end
end
end BundlePart325

section BundlePart326
/- Source: Papers/GraphicalZonotopes/SaturatedFourBlocks.lean -/






@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.BooleanModule.SaturatedFour
open Finset
open scoped BigOperators
open Saturated

abbrev H := Fin 4
abbrev Cfull : Finset H := univ

def anchors : Finset H := {2,3}

def label (a : H) : ℤ := if a=2 ∨ a=3 then 1 else 0

def column : Fin 4 → PairIn Cfull → ℝ
  | 0 => pairIndicator (starPairs Cfull 2 {0,3})
  | 1 => pairIndicator (starPairs Cfull 2 {1,3})
  | 2 => pairIndicator {natPair 0 3 (by decide) (by decide)}
  | 3 => pairIndicator {natPair 1 3 (by decide) (by decide)}

theorem column_realizable (i : Fin 4) : PureRealizable Cfull (column i) := by
  fin_cases i
  · exact pureRealizable_star Cfull (mem_univ _) (subset_univ _) (by simp) (by decide)
  · exact pureRealizable_star Cfull (mem_univ _) (subset_univ _) (by simp) (by decide)
  · exact pureRealizable_pair Cfull _
  · exact pureRealizable_pair Cfull _

theorem column_reference (i : Fin 4) : column i (natPair 0 1 (by decide) (by decide))=0 := by
  fin_cases i <;> norm_num [column,pairIndicator,mem_starPairs,StarPair,natPair,orderedPair]

theorem column_independent : LinearIndependent ℝ column := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrFun hc (natPair 0 2 (by decide) (by decide))
  have h1 := congrFun hc (natPair 1 2 (by decide) (by decide))
  have h2 := congrFun hc (natPair 0 3 (by decide) (by decide))
  have h3 := congrFun hc (natPair 1 3 (by decide) (by decide))
  norm_num [Fin.sum_univ_succ,column,pairIndicator,mem_starPairs,StarPair,natPair,orderedPair] at h0 h1 h2 h3
  fin_cases i <;> assumption

theorem column_sum : (∑ i,column i)=endpointCoefficients Cfull (fun a => (label a : ℝ)) := by
  funext e
  obtain ⟨⟨⟨u,v⟩,huv,hG⟩,hu,hv⟩ := e
  fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals norm_num [Fin.sum_univ_succ,column,pairIndicator,mem_starPairs,StarPair,
    natPair,orderedPair,endpointCoefficients,label]

theorem full_rigidity (d : H → ℝ) (h0 : d 0=0) (h1 : d 1=0) (t : Fin 4 → ℝ)
    (hz : blockClass Cfull ((-1 : ℝ) • endpointCoefficients Cfull d+∑ i,t i • column i)=0) :
    d 2=d 3 := by
  obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff Cfull (natPair 0 1 (by decide) (by decide)) _).mp hz
  have h01 := hc (natPair 0 1 (by decide) (by decide))
  have h02 := hc (natPair 0 2 (by decide) (by decide))
  have h12 := hc (natPair 1 2 (by decide) (by decide))
  have h23 := hc (natPair 2 3 (by decide) (by decide))
  norm_num [Fin.sum_univ_succ,column,pairIndicator,mem_starPairs,StarPair,natPair,orderedPair,
    endpointCoefficients,h0,h1] at h01 h02 h12 h23
  linarith

def fullPureBlock : WeightedPureBlock Cfull 1
    (blockClass Cfull (endpointCoefficients Cfull (fun a => (label a : ℝ)))) 4 where
  column := column
  realizable := column_realizable
  weight := fun _ => 1
  positive := fun _ => by norm_num
  bounded := fun _ => le_rfl
  independent := blockClass_linearIndependent_of_reference Cfull
    (natPair 0 1 (by decide) (by decide)) column column_independent column_reference
  weighted_sum := by
    simp only [Int.cast_one,one_smul]
    rw [←map_sum,column_sum]

theorem proper_card {C : BookBlock H} (hC : C.1≠ univ) : C.1.card=3 := by
  have h3 := (mem_largeBlocks.mp C.2).2
  have h4 : C.1.card≤4 := by simpa using card_le_card (subset_univ C.1)
  have hlt : C.1.card≠4 := by
    intro he
    apply hC
    exact eq_of_subset_of_card_le (subset_univ _) (by simpa using he.ge)
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem proper_reference_exists :
    ∀ C : BookBlock H,C.1≠ univ → ∃ e₀ : PairIn C.1,
      (label e₀.1.1.1+label e₀.1.1.2=0 ∨ label e₀.1.1.1+label e₀.1.1.2=2) ∧
      ∀ e : PairIn C.1,e≠ e₀ → label e.1.1.1+label e.1.1.2=1 := by
  have hfinite : ∀ C : Finset H,C.card=3 → ∃ u v : H,
      u< v ∧ u∈C ∧ v∈C ∧ (label u+label v=0 ∨ label u+label v=2) ∧
      ∀ a b : H,a< b → a∈C → b∈C → (a≠ u ∨ b≠ v) → label a+label b=1 := by
    decide
  intro C hC
  obtain ⟨u,v,huv,hu,hv,hl,he⟩ := hfinite C.1 (proper_card hC)
  let e₀ : PairIn C.1 := ⟨⟨(u,v),huv,ne_of_lt huv⟩,hu,hv⟩
  refine ⟨e₀,hl,?_⟩
  intro e hne
  apply he e.1.1.1 e.1.1.2 e.1.2.1 e.2.1 e.2.2
  by_contra hn
  push_neg at hn
  apply hne
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hn.1 hn.2

def properPureBlock (C : BookBlock H) (hC : C.1≠ univ) :
    WeightedPureBlock C.1 1 (-blockClass C.1 (endpointCoefficients C.1 (fun a => (label a : ℝ)))) 2 := by
  let e₀ : PairIn C.1 := (proper_reference_exists C hC).choose
  have hv : label e₀.1.1.1+label e₀.1.1.2=0 ∨ label e₀.1.1.1+label e₀.1.1.2=2 :=
    (proper_reference_exists C hC).choose_spec.1
  have he : ∀ e : PairIn C.1,e≠ e₀ → label e.1.1.1+label e.1.1.2=1 :=
    (proper_reference_exists C hC).choose_spec.2
  let ε : ℝ := if label e₀.1.1.1+label e₀.1.1.2=0 then -1 else 1
  let w : PairIn C.1 → ℤ := fun e => if e=e₀ then 0 else 1
  have hε : ε=1 ∨ ε= -1 := by unfold ε; split_ifs <;> simp
  let P := signed_pair_basis C.1 (mem_largeBlocks.mp C.2).2 e₀ ε hε w
    (by simp [w]) (fun e he => by simp [w,he]) 1 (fun e he => by simp [w,he])
  have htarget : blockClass C.1 (ε • (fun e => (w e : ℝ)))=
      -blockClass C.1 (endpointCoefficients C.1 (fun a => (label a : ℝ))) := by
    have hc : blockClass C.1 ((ε • (fun e => (w e : ℝ)))+
        endpointCoefficients C.1 (fun a => (label a : ℝ)))=0 := by
      apply (blockClass_eq_zero_iff C.1 e₀ _).mpr
      refine ⟨((label e₀.1.1.1+label e₀.1.1.2 : ℤ) : ℝ),?_⟩
      intro e
      by_cases heq : e=e₀
      · subst e
        simp [w,endpointCoefficients]
      · have hh := he e heq
        rcases hv with hv | hv
        · have hh' : (label e.1.1.1 : ℝ)+(label e.1.1.2 : ℝ)=1 := by exact_mod_cast hh
          simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,w,if_neg heq,Int.cast_one,
            mul_one,endpointCoefficients,ε,if_pos hv,Int.cast_add]
          rw [hh']
          exact_mod_cast hv.symm
        · have hn : label e₀.1.1.1+label e₀.1.1.2≠0 := by omega
          have hh' : (label e.1.1.1 : ℝ)+(label e.1.1.2 : ℝ)=1 := by exact_mod_cast hh
          simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,w,if_neg heq,Int.cast_one,
            mul_one,endpointCoefficients,ε,if_neg hn,Int.cast_add]
          rw [hh']
          exact_mod_cast hv.symm
    rw [map_add] at hc
    exact eq_neg_of_add_eq_zero_left hc
  have hr : C.1.card.choose 2-1=2 := by rw [proper_card hC]; decide
  exact hr ▸ htarget ▸ P

abbrev fullBlock : BookBlock H := ⟨univ,by simp [mem_largeBlocks]⟩

def rank (C : BookBlock H) : ℕ := if C=fullBlock then 4 else 2

theorem anchor_extension : coefficientExtension anchors (fun _ => (1 : ℝ))=
    fun a => (label a : ℝ) := by
  funext a
  fin_cases a <;> norm_num [coefficientExtension,anchors,label]

def block (C : BookBlock H) :
    WeightedPureBlock C.1 1 (-((1*((-1 : ℝ)^(C.1.card-3))) • blockClass C.1
      (endpointCoefficients C.1 (coefficientExtension anchors (fun _ => ((1 : ℤ) : ℝ)))))) (rank C) := by
  classical
  by_cases hC : C=fullBlock
  · subst C
    rw [rank,if_pos rfl]
    refine {
      column := fullPureBlock.column
      realizable := fullPureBlock.realizable
      weight := fullPureBlock.weight
      positive := fullPureBlock.positive
      bounded := fullPureBlock.bounded
      independent := fullPureBlock.independent
      weighted_sum := ?_ }
    simp only [Int.cast_one]
    rw [fullPureBlock.weighted_sum,anchor_extension]
    simp [fullBlock]
  · have hCu : C.1≠ univ := fun h => hC (Subtype.ext h)
    rw [rank,if_neg hC]
    let P := properPureBlock C hCu
    refine {
      column := P.column
      realizable := P.realizable
      weight := P.weight
      positive := P.positive
      bounded := P.bounded
      independent := P.independent
      weighted_sum := ?_ }
    simp only [Int.cast_one]
    rw [P.weighted_sum,anchor_extension,proper_card hCu]
    norm_num

theorem block_full_column : (block fullBlock).column=column := by
  unfold block
  simp only [dite_true] <;> rfl

theorem scale_rigidity : ScopedAnchorRigidity anchors 1 (fun _ => 1) 1 rank block := by
  intro t ht
  let d := coefficientExtension anchors (fun a => t (.inl a))
  have h0 : d 0=0 := by simp [d,coefficientExtension,anchors]
  have h1 : d 1=0 := by simp [d,coefficientExtension,anchors]
  have hfull := ht fullBlock
  change blockClass Cfull ((1*((-1 : ℝ)^((fullBlock.1).card-3))) • endpointCoefficients Cfull d+
    ∑ j,t (.inr ⟨fullBlock,j⟩) • (block fullBlock).column j)=0 at hfull
  have hfactor : (1 : ℝ)*(-1)^((fullBlock.1).card-3)= -1 := by norm_num [fullBlock]
  rw [block_full_column,hfactor] at hfull
  have h23 := full_rigidity d h0 h1 (fun j => t (.inr ⟨fullBlock,j⟩)) hfull
  refine ⟨d 2,?_⟩
  intro a
  have ha : a.1=2 ∨ a.1=3 := by simpa only [anchors,mem_insert,mem_singleton] using a.2
  have hd : t (.inl a)=d a.1 :=
    (coefficientExtension_subtype anchors (fun b => t (.inl b)) a).symm
  simp only [Int.cast_one,mul_one]
  rw [hd]
  rcases ha with ha | ha
  · rw [ha]
  · rw [ha,h23]

end GraphicalZonotopes.BooleanModule.SaturatedFour

end
end
end BundlePart326

section BundlePart327
/- Source: Papers/GraphicalZonotopes/SaturatedFourAttainment.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes.BooleanModule.SaturatedFour
open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem circuit_card : Fintype.card (ScopedAnchorIndex anchors rank)=14 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem neighbor_count : ∀ a : Fin 4,
    (univ.filter (fun j : ScopedAnchorIndex anchors rank => a∈scopedAnchorScope anchors rank j)).card=12 := by
  decide

open scoped Classical

/-- The exceptional saturated four-hub circuit has six all-hub modules,
eight triple modules, and exactly twelve active spokes at each hub. -/
theorem spoke_attainment :
    ∃ f : SetFunction (Fin 4⊕Fin 14),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 4 14) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin 4,(univ.filter (fun j : Fin 14 =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card=12 := by
  let a₀ : anchors := ⟨2,by simp [anchors]⟩
  obtain ⟨f,hn,hi,he,hG,hd,hl,hcount⟩ := scoped_book_of_anchor_circuit
    anchors 1 (fun a => thresholdStar a.1) (fun a => by simp)
    (fun _ => 1) 1 rank block (by decide)
    (fun a => thresholdStar_boolean a.1)
    (fun a i => thresholdStar_essential (by decide) a.1 i) a₀
    (fun _ => by norm_num) scale_rigidity circuit_card
  exact ⟨f,hn,hi,he,hG,hd,hl,fun a => (hcount a).trans (neighbor_count a)⟩

end GraphicalZonotopes.BooleanModule.SaturatedFour

end
end
end BundlePart327

section BundlePart328
/- Source: Papers/GraphicalZonotopes/SaturatedBookArithmetic.lean -/




/-! # The closed formula for the optimal saturated-book hub degree

The integer-power exponent retains the paper's value (2^{-1}) when there
are three hubs.  The natural-number capacity difference is justified by
the proved monotonicity of clique capacity.
-/

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open BooleanModule

private theorem twice_choose_two_int (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ) * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  have h := Nat.add_one_mul_choose_eq (n - 1) 1
  have he : n - 1 + 1 = n := by omega
  have hnat : n * (n - 1) = n.choose 2 * 2 := by
    simpa only [he,Nat.choose_one_right] using h
  have hi : (n : ℤ) * ((n - 1 : ℕ) : ℤ) = (n.choose 2 : ℤ) * 2 := by
    exact_mod_cast hnat
  rw [Nat.cast_sub hn,Nat.cast_one] at hi
  nlinarith

theorem saturatedHubNeighbors_twice_formula {s : ℕ} (hs : 3 ≤ s) :
    (2 : ℤ) * (saturatedHubNeighbors s : ℤ) =
      ((s : ℤ)^2 + (s : ℤ) - 10) * (2 : ℤ)^(s - 3) + 4 := by
  have hmono := cliqueCapacity_pred_le (show 1 ≤ s by omega)
  have hu : (saturatedHubNeighbors s : ℤ) =
      (cliqueCapacity s : ℤ) - (cliqueCapacity (s - 1) : ℤ) + 1 := by
    rw [saturatedHubNeighbors,if_neg (by omega : s ≠ 2),Nat.cast_add,
      Nat.cast_sub hmono,Nat.cast_one]
  have hc := twice_choose_two_int s (by omega)
  have hp := twice_choose_two_int (s - 1) (by omega)
  rw [Nat.cast_sub (show 1 ≤ s by omega),Nat.cast_one] at hp
  have hcoef : 4 * (s.choose 2 : ℤ) - 2 * ((s - 1).choose 2 : ℤ) - 8 =
      (s : ℤ)^2 + (s : ℤ) - 10 := by nlinarith
  have hpow2 : (2 : ℤ)^(s - 2) = 2 * (2 : ℤ)^(s - 3) := by
    rw [show s - 2 = (s - 3) + 1 by omega,pow_add]
    norm_num <;> ring
  have hpow1 : (2 : ℤ)^(s - 1) = 4 * (2 : ℤ)^(s - 3) := by
    rw [show s - 1 = (s - 3) + 2 by omega,pow_add]
    norm_num <;> ring
  have hpow : (2 : ℤ)^s = 8 * (2 : ℤ)^(s - 3) := by
    calc
      (2 : ℤ)^s = (2 : ℤ)^((s - 3) + 3) := congrArg (fun n => (2 : ℤ)^n) (by omega)
      _ = _ := by rw [pow_add]; norm_num; ring
  calc
    (2 : ℤ) * (saturatedHubNeighbors s : ℤ) =
        (4 * (s.choose 2 : ℤ) - 2 * ((s - 1).choose 2 : ℤ) - 8) *
          (2 : ℤ)^(s - 3) + 4 := by
      rw [hu,cliqueCapacity_int_formula,cliqueCapacity_int_formula,
        show s - 1 - 2 = s - 3 by omega,hpow2,hpow1,hpow,
        Nat.cast_sub (show 1 ≤ s by omega),Nat.cast_one]
      ring
    _ = _ := by rw [hcoef]

/-- The numerical identity displayed in Theorem 7.12, including its
three-hub case with exponent (-1). -/
theorem saturatedHubNeighbors_closed_formula {s : ℕ} (hs : 3 ≤ s) :
    (saturatedHubNeighbors s : ℝ) =
      ((s : ℝ)^2 + (s : ℝ) - 10) * (2 : ℝ)^((s : ℤ) - 4) + 2 := by
  by_cases hs3 : s = 3
  · subst s
    norm_num [saturatedHubNeighbors,cliqueCapacity,Nat.choose]
  have hs4 : 4 ≤ s := by omega
  have hi := saturatedHubNeighbors_twice_formula hs
  have hr : (2 : ℝ) * (saturatedHubNeighbors s : ℝ) =
      ((s : ℝ)^2 + (s : ℝ) - 10) * (2 : ℝ)^(s - 3) + 4 := by
    exact_mod_cast hi
  have he : (s : ℤ) - 4 = ((s - 4 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hs4]
    norm_num
  rw [he,zpow_natCast]
  have hp : (2 : ℝ)^(s - 3) = 2 * (2 : ℝ)^(s - 4) := by
    rw [show s - 3 = (s - 4) + 1 by omega,pow_add]
    norm_num <;> ring
  rw [hp] at hr
  nlinarith

end GraphicalZonotopes

end
end
end BundlePart328

