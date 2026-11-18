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

public import verified.parts.part011
import all verified.parts.part011

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart160
/- Source: Papers/GraphicalZonotopes/BookQuadrilateralModules.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

structure BalancedQuad (s : ℕ) where
  point : Fin 4 → Fin s
  ordered : StrictMono point
  balanced : (point 0).val+(point 3).val=(point 1).val+(point 2).val

namespace BalancedQuad
variable {s : ℕ} (Q : BalancedQuad s)

def clique : Finset (Fin s) := univ.image Q.point

@[simp] theorem point_mem (i : Fin 4) : Q.point i∈Q.clique :=
  mem_image.mpr ⟨i,mem_univ _,rfl⟩

@[simp] theorem card_clique : Q.clique.card=4 := by
  rw [clique,card_image_of_injective _ Q.ordered.injective]
  rfl

def pair (i j : Fin 4) (hij : i< j) : PairIn Q.clique :=
  orderedPair Q.clique (Q.point i) (Q.point j) (Q.ordered hij) (Q.point_mem i) (Q.point_mem j)

@[simp] theorem pair_eq_iff (i j k l : Fin 4) (hij : i< j) (hkl : k< l) :
    Q.pair i j hij=Q.pair k l hkl ↔ i=k ∧ j=l := by
  constructor
  · intro h
    exact ⟨Q.ordered.injective (congrArg (fun e : PairIn Q.clique => e.1.1.1) h),
      Q.ordered.injective (congrArg (fun e : PairIn Q.clique => e.1.1.2) h)⟩
  · rintro ⟨rfl,rfl⟩
    rfl

def reference : PairIn Q.clique := Q.pair 0 3 (by decide)
def opposite : PairIn Q.clique := Q.pair 1 2 (by decide)

def retainedIndices : Fin 4 → Fin 4×Fin 4 := ![(0,1),(0,2),(1,3),(2,3)]
theorem retainedIndices_order (i : Fin 4) : (retainedIndices i).1<(retainedIndices i).2 := by
  fin_cases i <;> decide
theorem retainedIndices_injective : Function.Injective retainedIndices := by decide

def retainedPair (i : Fin 4) : PairIn Q.clique :=
  Q.pair (retainedIndices i).1 (retainedIndices i).2 (retainedIndices_order i)

theorem retainedPair_injective : Function.Injective Q.retainedPair := by
  intro i j h
  apply retainedIndices_injective
  apply Prod.ext
  · exact ((Q.pair_eq_iff _ _ _ _ _ _).mp h).1
  · exact ((Q.pair_eq_iff _ _ _ _ _ _).mp h).2

@[simp] theorem reference_ne_retained (i : Fin 4) : Q.reference≠ Q.retainedPair i := by
  change Q.pair 0 3 _≠ Q.pair _ _ _
  rw [ne_eq,pair_eq_iff]
  fin_cases i <;> decide

@[simp] theorem opposite_ne_retained (i : Fin 4) : Q.opposite≠ Q.retainedPair i := by
  change Q.pair 1 2 _≠ Q.pair _ _ _
  rw [ne_eq,pair_eq_iff]
  fin_cases i <;> decide

def columnSign (i : Fin 4) : ℝ := if i.val<2 then -1 else 1

def column (i : Fin 4) : PairIn Q.clique → ℝ :=
  columnSign i • pairIndicator {Q.retainedPair i}

def label (i : Fin 4) : ℤ := ((Q.point i).val : ℤ)

def weight : Fin 4 → ℤ :=
  ![Q.label 3-Q.label 1,Q.label 3-Q.label 2,Q.label 1-Q.label 0,Q.label 2-Q.label 0]

@[simp] theorem columnSign_ne_zero (i : Fin 4) : columnSign i≠0 := by
  unfold columnSign
  split <;> norm_num

theorem column_realizable (i : Fin 4) : PureRealizable Q.clique (Q.column i) := by
  by_cases h : i.val<2
  · have he : Q.column i= -pairIndicator {Q.retainedPair i} := by
      simp only [column,columnSign,ite_eq_left h,neg_one_smul]
    rw [he]
    exact pureRealizable_negative_pair Q.clique (by rw [Q.card_clique]; omega) (Q.retainedPair i)
  · have he : Q.column i=pairIndicator {Q.retainedPair i} := by
      simp only [column,columnSign,ite_eq_right h,one_smul]
    rw [he]
    exact pureRealizable_pair Q.clique (Q.retainedPair i)

theorem weight_positive (i : Fin 4) : 0< Q.weight i := by
  have h01 : Q.label 0< Q.label 1 := by
    change ((Q.point 0).val : ℤ)<((Q.point 1).val : ℤ)
    exact_mod_cast (show (Q.point 0).val<(Q.point 1).val from Q.ordered (by decide : (0 : Fin 4)<1))
  have h02 : Q.label 0< Q.label 2 := by
    change ((Q.point 0).val : ℤ)<((Q.point 2).val : ℤ)
    exact_mod_cast (show (Q.point 0).val<(Q.point 2).val from Q.ordered (by decide : (0 : Fin 4)<2))
  have h13 : Q.label 1< Q.label 3 := by
    change ((Q.point 1).val : ℤ)<((Q.point 3).val : ℤ)
    exact_mod_cast (show (Q.point 1).val<(Q.point 3).val from Q.ordered (by decide : (1 : Fin 4)<3))
  have h23 : Q.label 2< Q.label 3 := by
    change ((Q.point 2).val : ℤ)<((Q.point 3).val : ℤ)
    exact_mod_cast (show (Q.point 2).val<(Q.point 3).val from Q.ordered (by decide : (2 : Fin 4)<3))
  fin_cases i <;> change 0 < _ - _ <;> omega

theorem weight_bounded (i : Fin 4) : Q.weight i≤((s-1 : ℕ) : ℤ) := by
  have hlo : ∀ j,0≤ Q.label j := fun j => Int.natCast_nonneg _
  have hhi : ∀ j,Q.label j<(s : ℤ) := fun j => by
    change ((Q.point j).val : ℤ)<(s : ℤ)
    exact_mod_cast (Q.point j).isLt
  have h0 := hlo 0
  have h1 := hlo 1
  have h2 := hlo 2
  have h3 := hhi 3
  have h1' := hhi 1
  have h2' := hhi 2
  fin_cases i <;> change _ - _ ≤ ((s-1 : ℕ) : ℤ) <;> omega

theorem columns_independent : LinearIndependent ℝ (fun i => blockClass Q.clique (Q.column i)) := by
  let p : Fin 4 → ↥((univ : Finset (PairIn Q.clique)).erase Q.reference) :=
    fun i => ⟨Q.retainedPair i,mem_erase.mpr ⟨Ne.symm (Q.reference_ne_retained i),mem_univ _⟩⟩
  have hp : Function.Injective p := fun i j h => Q.retainedPair_injective (congrArg Subtype.val h)
  have hi : LinearIndependent ℝ (fun i => blockClass Q.clique (pairIndicator {Q.retainedPair i})) :=
    (reference_pair_columns_independent Q.clique Q.reference).comp p hp
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hz : (∑ j,(c j*columnSign j) • blockClass Q.clique (pairIndicator {Q.retainedPair j}))=0 := by
    simpa only [column,map_smul,mul_smul] using hc
  exact (mul_eq_zero.mp ((Fintype.linearIndependent_iff.mp hi) _ hz i)).resolve_right (columnSign_ne_zero i)

@[simp] theorem column_reference (i : Fin 4) : Q.column i Q.reference=0 := by
  simp [column,pairIndicator]

@[simp] theorem column_opposite (i : Fin 4) : Q.column i Q.opposite=0 := by
  simp [column,pairIndicator]

/-- All six pair coordinates are checked: four retained signed pairs have
positive scales, and the two omitted pairs have the same endpoint sum. -/
theorem weighted_columns_vector :
    (∑ i : Fin 4,(Q.weight i : ℝ) • Q.column i)=
      endpointLabels Q.clique-(fun _ => ((Q.label 0+Q.label 3 : ℤ) : ℝ)) := by
  funext e
  obtain ⟨i,hi,hui⟩ := mem_image.mp e.2.1
  obtain ⟨j,hj,hvj⟩ := mem_image.mp e.2.2
  have hij : i< j := by
    by_contra hn
    have hle := Q.ordered.monotone (le_of_not_gt hn)
    have hlt : Q.point i< Q.point j := by simpa only [hui,hvj] using e.1.2.1
    exact (not_le_of_gt hlt) hle
  have he : e=Q.pair i j hij := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hui.symm hvj.symm
  rw [he]
  have hb : ((Q.point 0).val : ℝ)+(Q.point 3).val=
      ((Q.point 1).val : ℝ)+(Q.point 2).val := by exact_mod_cast Q.balanced
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    simp [Fin.sum_univ_four,Pi.smul_apply,smul_eq_mul,column,columnSign,pairIndicator,
      retainedPair,retainedIndices,pair_eq_iff,weight,
      Int.cast_sub,Int.cast_add,Int.cast_natCast]
    simp only [endpointLabels,pair,orderedPair,label,Pi.sub_apply]
    push_cast
    linarith

theorem weighted_columns_response :
    (∑ i : Fin 4,(Q.weight i : ℝ) • blockClass Q.clique (Q.column i))=
      ordinaryBookTarget Q.clique := by
  have hz : blockClass Q.clique (fun _ : PairIn Q.clique => ((Q.label 0+Q.label 3 : ℤ) : ℝ))=0 :=
    (blockClass_eq_zero_iff Q.clique Q.reference _).mpr ⟨_,fun _ => rfl⟩
  calc
    _ = blockClass Q.clique (∑ i : Fin 4,(Q.weight i : ℝ) • Q.column i) := by simp only [map_sum,map_smul]
    _ = blockClass Q.clique (endpointLabels Q.clique) := by
      rw [Q.weighted_columns_vector,map_sub,hz,sub_zero]
    _ = ordinaryBookTarget Q.clique := by simp [ordinaryBookTarget,Q.card_clique]

end BalancedQuad
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart160

section BundlePart161
/- Source: Papers/GraphicalZonotopes/WeightedPureBlocks.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {H : Type*} [Fintype H] [LinearOrder H]

/-- Positive integral pure module data, with the actual quotient classes and
actual monotone Boolean realizations as part of the construction. -/
structure WeightedPureBlock (C : Finset H) (M : ℤ)
    (v : ResponseQuotient H) (r : ℕ) where
  column : Fin r → PairIn C → ℝ
  realizable : ∀ j,PureRealizable C (column j)
  weight : Fin r → ℤ
  positive : ∀ j,0< weight j
  bounded : ∀ j,weight j≤ M
  independent : LinearIndependent ℝ (fun j => blockClass C (column j))
  weighted_sum : (∑ j,(weight j : ℝ) • blockClass C (column j))=v

namespace WeightedStarFamily

def toPureBlock {C : Finset H} {M : ℤ} {v : ResponseQuotient H} {r : ℕ}
    (P : WeightedStarFamily C M v r) : WeightedPureBlock C M v r where
  column := fun j => (P.piece j).vector
  realizable := fun j => (P.piece j).realizable
  weight := P.weight
  positive := P.positive
  bounded := P.bounded
  independent := P.independent
  weighted_sum := P.weighted_sum

end WeightedStarFamily

namespace BalancedQuad
variable {s : ℕ}

def pureBlock (Q : BalancedQuad s) :
    WeightedPureBlock Q.clique ((s-1 : ℕ) : ℤ) (ordinaryBookTarget Q.clique) 4 where
  column := Q.column
  realizable := Q.column_realizable
  weight := Q.weight
  positive := Q.weight_positive
  bounded := Q.weight_bounded
  independent := Q.columns_independent
  weighted_sum := Q.weighted_columns_response

end BalancedQuad

theorem ordinary_book_pure_block {s : ℕ} (C : Finset (Fin s)) (hC : 3≤ C.card)
    {k : ℕ} (hklo : C.card-1≤ k) (hkhi : k≤ C.card.choose 2-1) :
    Nonempty (WeightedPureBlock C ((s-1 : ℕ) : ℤ) (ordinaryBookTarget C) k) := by
  exact ⟨(Classical.choice (ordinary_book_block_interpolation C hC hklo hkhi)).toPureBlock⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart161

section BundlePart162
/- Source: Papers/GraphicalZonotopes/ExactlyOneExpansion.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [DecidableEq H]

def exactlyOne (S : Finset H) : ℝ:=if S.card=1 then 1 else 0

def exactlyOneCoefficient (n : ℕ) : ℝ:=
  if n=0 then 0 else (n : ℝ)*(-1 : ℝ)^(n-1)

theorem exactlyOneCoefficient_step (n : ℕ) :
    exactlyOneCoefficient n+exactlyOneCoefficient (n+1)=(-1 : ℝ)^n := by
  cases n with
  | zero => norm_num [exactlyOneCoefficient]
  | succ n =>
    simp only [exactlyOneCoefficient,Nat.add_one_ne_zero,Nat.succ_ne_zero,
      ite_false,Nat.add_sub_cancel,Nat.succ_sub_one,Nat.cast_add,Nat.cast_one,
      Nat.cast_succ,pow_succ]
    ring

theorem real_alternating_powerset (S : Finset H) :
    (∑ T∈S.powerset,(-1 : ℝ)^T.card)=if S=∅ then 1 else 0 := by
  have hi:=sum_powerset_neg_one_pow_card (x:=S)
  exact_mod_cast hi

/-- The full finite multilinear expansion of the exactly-one indicator.
It includes the empty coefficient and every subset of the ambient type. -/
theorem zeta_exactlyOneCoefficient :
    zeta (fun S : Finset H => exactlyOneCoefficient S.card)=exactlyOne := by
  funext S
  by_cases hS : S=∅
  · subst S
    simp [zeta,exactlyOneCoefficient,exactlyOne]
  · obtain ⟨a,ha⟩:=nonempty_iff_ne_empty.mpr hS
    let T:=S.erase a
    have haT : a∉T:=notMem_erase a S
    have he : insert a T=S:=insert_erase ha
    rw [← he]
    change (∑ U∈(insert a T).powerset,exactlyOneCoefficient U.card)=_
    rw [sum_powerset_insert haT,← sum_add_distrib]
    have hs : (∑ U∈T.powerset,
        (exactlyOneCoefficient U.card+exactlyOneCoefficient (insert a U).card))=
        ∑ U∈T.powerset,(-1 : ℝ)^U.card := by
      apply sum_congr rfl
      intro U hU
      have haU : a∉U:=fun h => haT ((mem_powerset.mp hU) h)
      rw [card_insert_of_notMem haU,exactlyOneCoefficient_step]
    rw [hs,real_alternating_powerset]
    simp only [exactlyOne,card_insert_of_notMem haT]
    have hn : T.card+1=1 ↔ T=∅:=by rw [← card_eq_zero]; omega
    simp only [hn]

def absentCoefficient (a : H) (y : SetFunction H) : SetFunction H:=
  fun T => if a∈T then -y (T.erase a) else y T

/-- Multiplication by the Boolean factor `(1-x_a)` in actual subset
coordinates, derived by cancelling the two halves of the powerset sum. -/
theorem zeta_absentCoefficient (a : H) (y : SetFunction H) (S : Finset H) :
    zeta (absentCoefficient a y) S=if a∈S then 0 else zeta y S := by
  by_cases ha : a∈S
  · let T:=S.erase a
    have haT : a∉T:=notMem_erase a S
    have he : insert a T=S:=insert_erase ha
    rw [if_pos ha,← he]
    unfold zeta
    rw [sum_powerset_insert haT]
    have hfirst : (∑ U∈T.powerset,absentCoefficient a y U)=∑ U∈T.powerset,y U := by
      apply sum_congr rfl
      intro U hU
      have haU : a∉U:=fun h => haT ((mem_powerset.mp hU) h)
      exact if_neg haU
    have hsecond : (∑ U∈T.powerset,absentCoefficient a y (insert a U))=
        -(∑ U∈T.powerset,y U) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro U hU
      have haU : a∉U:=fun h => haT ((mem_powerset.mp hU) h)
      simp only [absentCoefficient,mem_insert_self,ite_true,erase_insert haU]
    rw [hfirst,hsecond,add_neg_cancel]
  · rw [if_neg ha]
    apply sum_congr rfl
    intro U hU
    have haU : a∉U:=fun h => ha ((mem_powerset.mp hU) h)
    exact if_neg haU

theorem zeta_absent_exactlyOne (a : H) (S : Finset H) :
    zeta (absentCoefficient a (fun T => exactlyOneCoefficient T.card)) S=
      if a∈S then 0 else exactlyOne S := by
  rw [zeta_absentCoefficient,zeta_exactlyOneCoefficient]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart162

section BundlePart163
/- Source: Papers/GraphicalZonotopes/ThresholdBoolean.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The threshold module of Lemma 7.6. Counting the whole set in the second
disjunct is equivalent to counting the hubs other than `a`: the first
disjunct already makes the value one whenever `a` is present. -/
def thresholdStar (a : H) : SetFunction H :=
  fun S => if a∈S ∨ 2≤ S.card then 1 else 0

theorem thresholdStar_literal (a : H) (S : Finset H) :
    thresholdStar a S=if a∈S ∨ 2≤(S.erase a).card then 1 else 0 := by
  by_cases ha : a∈S
  · simp only [thresholdStar,ha,true_or,ite_true]
  · simp only [thresholdStar,ha,false_or,erase_eq_of_notMem ha]

theorem thresholdStar_boolean (a : H) : IsMonotoneBoolean (thresholdStar a) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro S T hST
    by_cases hS : a∈S ∨ 2≤ S.card
    · have hT : a∈T ∨ 2≤ T.card := by
        rcases hS with ha | hc
        · exact Or.inl (hST ha)
        · exact Or.inr (hc.trans (card_le_card hST))
      simp only [thresholdStar,if_pos hS,if_pos hT,le_refl]
    · by_cases hT : a∈T ∨ 2≤ T.card <;>
        simp only [thresholdStar,if_neg hS,hT,ite_true,ite_false] <;> norm_num
  · intro S
    by_cases hS : a∈S ∨ 2≤ S.card <;> simp only [thresholdStar,hS,ite_true,ite_false] <;> simp
  · simp [thresholdStar]
  · simp [thresholdStar]

theorem thresholdStar_eq_zero_iff (a : H) (S : Finset H) :
    thresholdStar a S=0 ↔ a∉S ∧ S.card<2 := by
  by_cases ha : a∈S
  · simp [thresholdStar,ha]
  · by_cases hc : 2≤ S.card
    · simp [thresholdStar,ha,hc,Nat.not_lt.mpr hc]
    · have hlt : S.card<2:=Nat.lt_of_not_ge hc
      simp [thresholdStar,ha,hc,hlt]

theorem thresholdStar_eq_one_iff (a : H) (S : Finset H) :
    thresholdStar a S=1 ↔ a∈S ∨ 2≤ S.card := by
  by_cases h : a∈S ∨ 2≤ S.card <;> simp only [thresholdStar,h,ite_true,ite_false] <;> norm_num

/-- Essentiality is witnessed by literal Boolean covers, including all
ambient hubs rather than only the distinguished one. -/
theorem thresholdStar_essential (hs : 3≤ Fintype.card H) (a i : H) :
    Essential (thresholdStar a) i := by
  by_cases hi : i=a
  · subst i
    refine ⟨∅,notMem_empty _,?_⟩
    simp [thresholdStar]
  · have hb : ∃ b : H,b≠ a ∧ b≠ i := by
      by_contra hn
      have hsub : (univ : Finset H)⊆{a,i} := by
        intro b hb
        by_cases hba : b=a
        · simp only [hba,mem_insert_self]
        · by_cases hbi : b=i
          · simp only [hbi,mem_insert,mem_singleton,or_true]
          · exact False.elim (hn ⟨b,hba,hbi⟩)
      have hc:=card_le_card hsub
      rw [card_univ,card_pair (Ne.symm hi)] at hc
      omega
    obtain ⟨b,hba,hbi⟩:=hb
    refine ⟨{b},by simpa only [mem_singleton] using Ne.symm hbi,?_⟩
    have hai : a≠ i:=Ne.symm hi
    have hab : a≠ b:=Ne.symm hba
    simp only [thresholdStar,mem_insert,mem_singleton,hai,hab,false_or,
      card_pair (Ne.symm hbi),card_singleton]
    norm_num

/-- Every actual pair response is the exactly-one indicator on its context,
with the distinguished hub excluded. The formula also covers pairs incident
with `a`, since their legitimate contexts already omit `a`. -/
theorem thresholdStar_negativeResponse (a : H) {u v : H} (huv : u≠ v)
    (S : Finset H) (hu : u∉S) (hv : v∉S) :
    negativeResponse (thresholdStar a) u v S=
      if a∈S then 0 else exactlyOne S := by
  have hone : negativeResponse (thresholdStar a) u v S=1 ↔ a∉S ∧ S.card=1 := by
    rw [negativeResponse_eq_one_iff (thresholdStar_boolean a),
      thresholdStar_eq_zero_iff,thresholdStar_eq_one_iff,thresholdStar_eq_one_iff]
    simp only [mem_insert,card_insert_of_notMem hu,card_insert_of_notMem hv]
    constructor
    · rintro ⟨⟨ha,hc⟩,hu',hv'⟩
      refine ⟨ha,?_⟩
      by_cases hpos : 1≤ S.card
      · omega
      · have hau : a=u := by
          rcases hu' with (hau | haS) | hcard
          · exact hau
          · exact False.elim (ha haS)
          · omega
        have hav : a=v := by
          rcases hv' with (hav | haS) | hcard
          · exact hav
          · exact False.elim (ha haS)
          · omega
        exact False.elim (huv (hau.symm.trans hav))
    · rintro ⟨ha,hc⟩
      exact ⟨⟨ha,by omega⟩,Or.inr (by omega),Or.inr (by omega)⟩
  rcases negativeResponse_values (thresholdStar_boolean a) u v S with hz | ho
  · have hn : ¬(a∉S ∧ S.card=1) := by
      intro h
      have hh:=hone.mpr h
      rw [hz] at hh
      norm_num at hh
    by_cases ha : a∈S
    · simp only [hz,if_pos ha]
    · have hc : S.card≠1:=fun h => hn ⟨ha,h⟩
      simp only [hz,if_neg ha,exactlyOne,if_neg hc]
  · obtain ⟨ha,hc⟩:=hone.mp ho
    simp only [ho,if_neg ha,exactlyOne,if_pos hc]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart163

section BundlePart164
/- Source: Papers/GraphicalZonotopes/ThresholdResponse.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
variable {H : Type*} [Fintype H] [LinearOrder H]

def thresholdCoefficients (a : H) : HubResponseRow H → ℝ :=
  fun r => absentCoefficient a (fun T => exactlyOneCoefficient T.card) r.2.1

/-- The actual inverse of the pairwise response zeta transform, with every
context retained. This is computed from the Boolean function, not stipulated
as a response vector. -/
theorem thresholdStar_coefficients (a : H) :
    rowLowerEquiv.symm (responseVector (thresholdStar a))=thresholdCoefficients a := by
  apply rowLowerEquiv.injective
  rw [rowLowerEquiv.apply_symm_apply]
  funext r
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  change negativeResponse (thresholdStar a) r.1.1.1 r.1.1.2 r.2.1=
    lowerSum (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
      (fun T => absentCoefficient a (fun U => exactlyOneCoefficient U.card) T.1) r.2
  rw [lowerSum_restriction]
  change negativeResponse (thresholdStar a) r.1.1.1 r.1.1.2 r.2.1=
    zeta (absentCoefficient a (fun U => exactlyOneCoefficient U.card)) r.2.1
  rw [zeta_absent_exactlyOne,
    thresholdStar_negativeResponse a (ne_of_lt r.1.2.1) r.2.1 hu hv]

def thresholdSign (n : ℕ) : ℝ :=
  if n=0 then 0 else (-1 : ℝ)^(n-1)

theorem exactlyOneCoefficient_sub_sign (n : ℕ) (hn : 0< n) :
    exactlyOneCoefficient n-thresholdSign n= -exactlyOneCoefficient (n-1) := by
  have hs:=exactlyOneCoefficient_step (n-1)
  have he : n-1+1=n:=by omega
  rw [he] at hs
  rw [thresholdSign,if_neg (Nat.ne_of_gt hn)]
  linarith

theorem rowClique_card_eq_context_add_two (r : HubResponseRow H) :
    (rowClique r).card=r.2.1.card+2 := by
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hu' : r.1.1.1∉insert r.1.1.2 r.2.1 := by
    simpa only [mem_insert,not_or] using And.intro (ne_of_lt r.1.2.1) hu
  simp only [rowClique,card_insert_of_notMem hu',card_insert_of_notMem hv]

def thresholdCommon (a : H) (C : Finset H) : ℝ :=
  exactlyOneCoefficient (C.card-2)-if a∈C then thresholdSign (C.card-2) else 0

/-- The literal signed-star representative appearing in equation (7.2),
including its zero value on blocks not containing the distinguished hub. -/
def thresholdSignedStar (a : H) : HubResponseRow H → ℝ :=
  fun r => if 3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2)
    then (-1 : ℝ)^((rowClique r).card-3) else 0

theorem thresholdSignedStar_eq (a : H) (r : HubResponseRow H) :
    thresholdSignedStar a r=
      if a=r.1.1.1 ∨ a=r.1.1.2 then thresholdSign r.2.1.card else 0 := by
  have hc:=rowClique_card_eq_context_add_two r
  by_cases ha : a=r.1.1.1 ∨ a=r.1.1.2
  · by_cases hn : r.2.1.card=0
    · have hC : ¬3≤(rowClique r).card:=by omega
      simp [thresholdSignedStar,ha,hC,thresholdSign,hn]
    · have hC : 3≤(rowClique r).card:=by omega
      have he : (rowClique r).card-3=r.2.1.card-1:=by omega
      simp [thresholdSignedStar,ha,hC,thresholdSign,hn,he]
  · simp only [thresholdSignedStar,ha,and_false,ite_false]

/-- Before passing to the quotient, the response differs from the signed
star by exactly one common coefficient on each full clique block. -/
theorem thresholdCoefficients_decomposition (a : H) :
    thresholdCoefficients a=
      (fun r : HubResponseRow H => thresholdCommon a (rowClique r))+
        thresholdSignedStar a := by
  funext r
  have hc:=rowClique_card_eq_context_add_two r
  have hsub : (rowClique r).card-2=r.2.1.card:=by omega
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  simp only [Pi.add_apply,thresholdCoefficients,thresholdCommon,hsub,
    thresholdSignedStar_eq,absentCoefficient]
  by_cases hp : a=r.1.1.1 ∨ a=r.1.1.2
  · have ha : a∈rowClique r := by
      rcases hp with ha | ha
      · simp only [rowClique,ha,mem_insert_self]
      · simp [rowClique,ha]
    have haS : a∉r.2.1 := by
      rcases hp with ha | ha
      · simpa only [ha] using hu
      · simpa only [ha] using hv
    rw [if_neg haS,if_pos ha,if_pos hp]
    ring
  · by_cases haS : a∈r.2.1
    · have ha : a∈rowClique r:=mem_insert_of_mem (mem_insert_of_mem haS)
      have hn : 0< r.2.1.card:=card_pos.mpr ⟨a,haS⟩
      rw [if_pos haS,if_pos ha,if_neg hp,add_zero,card_erase_of_mem haS,
        exactlyOneCoefficient_sub_sign _ hn]
    · have ha : a∉rowClique r := by
        simp only [rowClique,mem_insert]
        intro h
        rcases h with h | h | h
        · exact hp (Or.inl h)
        · exact hp (Or.inr h)
        · exact haS h
      rw [if_neg haS,if_neg ha,if_neg hp,sub_zero,add_zero]

/-- Lemma 7.6 in the actual quotient by all central elemental responses.
There are no omitted contexts or unproved block-identification assumptions. -/
theorem thresholdStar_response_class (a : H) :
    responseClass (thresholdStar a)=coefficientClass (thresholdSignedStar a) := by
  rw [responseClass_eq_coefficientClass,thresholdStar_coefficients,
    thresholdCoefficients_decomposition,map_add]
  have hz : coefficientClass
      (fun r : HubResponseRow H => thresholdCommon a (rowClique r))=0 := by
    apply (coefficientClass_eq_zero_iff _).mpr
    intro r t hrt
    exact congrArg (thresholdCommon a) (congrArg Subtype.val hrt)
  rw [hz,zero_add]

theorem thresholdStar_response_lemma (hs : 3≤ Fintype.card H) (a : H) :
    IsMonotoneBoolean (thresholdStar a) ∧
    (∀ i,Essential (thresholdStar a) i) ∧
    responseClass (thresholdStar a)=coefficientClass (thresholdSignedStar a) :=
  ⟨thresholdStar_boolean a,thresholdStar_essential hs a,thresholdStar_response_class a⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart164

section BundlePart165
/- Source: Papers/GraphicalZonotopes/BookCombinatorialCounts.lean -/







@[expose] public section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

/-- Bounded integral sums attain every value between zero and their total
capacity. This supplies every intermediate branch count, uniformly. -/
theorem bounded_sum_composition {E : Type*} [DecidableEq E] (S : Finset E)
    (d : E → ℕ) {n : ℕ} (hn : n≤∑ i∈S,d i) :
    ∃ f : E → ℕ,(∀ i∈S,f i≤ d i) ∧ (∑ i∈S,f i)=n := by
  classical
  induction S using Finset.induction_on generalizing n with
  | empty =>
    have hn0 : n=0 := by simpa using hn
    exact ⟨fun _ => 0,by simp,by simp [hn0]⟩
  | @insert a S ha ih =>
    rw [sum_insert ha] at hn
    have hr : n-min (d a) n≤∑ i∈S,d i := by
      by_cases h : d a≤ n
      · rw [min_eq_left h]
        omega
      · rw [min_eq_right (by omega)]
        omega
    obtain ⟨f,hf,hfs⟩ := ih hr
    let g := fun i => if i=a then min (d a) n else f i
    refine ⟨g,?_,?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · simp only [g,ite_true]
        exact min_le_left _ _
      · have hia : i≠ a := fun h => ha (h ▸ hi)
        simpa only [g,ite_eq_right hia] using hf i hi
    · rw [sum_insert ha]
      have hg : (∑ i∈S,g i)=∑ i∈S,f i := by
        apply sum_congr rfl
        intro i hi
        change (if i=a then min (d a) n else f i)=f i
        exact ite_eq_right (fun (h : i=a) => ha (h ▸ hi))
      rw [hg,hfs]
      simp only [g,ite_true]
      omega

theorem positive_sum_composition {B : Type*} [Fintype B] [DecidableEq B]
    (d : B → ℕ) (hd : ∀ b,1≤ d b) {n : ℕ}
    (hnlo : Fintype.card B≤ n) (hnhi : n≤∑ b,d b) :
    ∃ k : B → ℕ,(∀ b,1≤ k b ∧ k b≤ d b) ∧ (∑ b,k b)=n := by
  classical
  have hsum : (∑ b,(d b-1))+Fintype.card B=∑ b,d b := by
    calc
      _ = ∑ b,((d b-1)+1) := by simp [sum_add_distrib]
      _ = _ := sum_congr rfl (fun b _ => Nat.sub_add_cancel (hd b))
  obtain ⟨f,hf,hfs⟩ := bounded_sum_composition (univ : Finset B) (fun b => d b-1)
    (n:=n-Fintype.card B) (by omega)
  refine ⟨fun b => f b+1,?_,?_⟩
  · intro b
    have h := hf b (mem_univ b)
    have hdb := hd b
    change 1≤ f b+1 ∧ f b+1≤ d b
    constructor <;> omega
  · rw [sum_add_distrib,hfs]
    simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.cast_id]
    omega

section Powersets
variable {H : Type*} [DecidableEq H]

def blockDimensionSum (S : Finset H) : ℕ :=
  ∑ C∈S.powerset,(C.card.choose 2-1)

def nontrivialSubsets (S : Finset H) : Finset (Finset H) :=
  S.powerset.filter (fun C => 2≤ C.card)

theorem small_subsets_card (S : Finset H) :
    (S.powerset.filter (fun C => ¬2≤ C.card)).card=S.card+1 := by
  have he : S.powerset.filter (fun C => ¬2≤ C.card)=insert ∅ (S.image singleton) := by
    ext C
    simp only [mem_filter,mem_powerset,mem_insert,mem_image]
    constructor
    · rintro ⟨hCS,hC⟩
      have hc : C.card=0 ∨ C.card=1 := by omega
      rcases hc with hc | hc
      · exact Or.inl (card_eq_zero.mp hc)
      · obtain ⟨a,rfl⟩ := card_eq_one.mp hc
        exact Or.inr ⟨a,hCS (mem_singleton_self a),rfl⟩
    · rintro (rfl | ⟨a,ha,rfl⟩)
      · simp
      · simp [singleton_subset_iff,ha]
  rw [he,card_insert_of_notMem]
  · rw [card_image_of_injective _ singleton_injective]
  · simp

theorem nontrivialSubsets_card (S : Finset H) :
    (nontrivialSubsets S).card=2^S.card-S.card-1 := by
  have h := card_filter_add_card_filter_not (s:=S.powerset) (p:=fun C => 2≤ C.card)
  rw [small_subsets_card,card_powerset] at h
  change (S.powerset.filter (fun C => 2≤ C.card)).card=_
  omega

theorem sum_powerset_card (S : Finset H) :
    (∑ C∈S.powerset,C.card)=S.card*2^(S.card-1) := by
  rw [sum_powerset_apply_card (fun n : ℕ => n)]
  simpa only [nsmul_eq_mul,Nat.mul_comm,Nat.cast_id] using Nat.sum_range_mul_choose S.card

theorem sum_powerset_choose_two (S : Finset H) :
    (∑ C∈S.powerset,C.card.choose 2)=S.card.choose 2*2^(S.card-2) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [sum_powerset_insert ha]
    have ht : ∀ T∈S.powerset,(insert a T).card.choose 2=T.card+T.card.choose 2 := by
      intro T hT
      have haT : a∉T := fun h => ha ((mem_powerset.mp hT) h)
      rw [card_insert_of_notMem haT]
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ T.card 1
    have ht' : (∑ T∈S.powerset,(insert a T).card.choose 2)=
        ∑ T∈S.powerset,(T.card+T.card.choose 2) := sum_congr rfl ht
    rw [ht']
    rw [sum_add_distrib,ih,sum_powerset_card,card_insert_of_notMem ha]
    by_cases h0 : S.card=0
    · norm_num [h0]
    by_cases h1 : S.card=1
    · norm_num [h1]
    have hn : 2≤ S.card := by omega
    have he : S.card+1-2=S.card-1 := by omega
    have he' : S.card-2+1=S.card-1 := by omega
    have hp : 2^(S.card-1)=2^(S.card-2)*2 := by rw [← he',pow_succ]
    have hc : (S.card+1).choose 2=S.card+S.card.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ S.card 1
    rw [hc,he,hp]
    ring

theorem blockDimensionSum_add_cliques (S : Finset H) :
    blockDimensionSum S+(nontrivialSubsets S).card=∑ C∈S.powerset,C.card.choose 2 := by
  have hd : blockDimensionSum S=∑ C∈nontrivialSubsets S,(C.card.choose 2-1) := by
    symm
    unfold blockDimensionSum nontrivialSubsets
    apply sum_subset (filter_subset _ _)
    intro C hC hn
    have hc : ¬2≤ C.card := fun h => hn (mem_filter.mpr ⟨hC,h⟩)
    have hchoose : C.card.choose 2=0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [hchoose,Nat.zero_sub]
  have hc : (∑ C∈nontrivialSubsets S,C.card.choose 2)=∑ C∈S.powerset,C.card.choose 2 := by
    apply sum_subset (filter_subset _ _)
    intro C hC hn
    exact Nat.choose_eq_zero_of_lt (by
      have h : ¬2≤ C.card := fun h => hn (mem_filter.mpr ⟨hC,h⟩)
      omega)
  rw [hd,← hc]
  calc
    _ = ∑ C∈nontrivialSubsets S,((C.card.choose 2-1)+1) := by simp [sum_add_distrib]
    _ = _ := by
      apply sum_congr rfl
      intro C hC
      exact Nat.sub_add_cancel (Nat.choose_pos (mem_filter.mp hC).2)

theorem blockDimensionSum_eq (S : Finset H) :
    blockDimensionSum S=S.card.choose 2*2^(S.card-2)-(2^S.card-S.card-1) := by
  have h := blockDimensionSum_add_cliques S
  rw [nontrivialSubsets_card,sum_powerset_choose_two] at h
  omega

theorem cliqueCapacity_eq_dimension_sum (S : Finset H) :
    cliqueCapacity S.card=blockDimensionSum S+1 := by
  rw [blockDimensionSum_eq]
  rfl

end Powersets
end BooleanModule
end GraphicalZonotopes

end
end BundlePart165

section BundlePart166
/- Source: Papers/GraphicalZonotopes/BlockFamilies.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

/-- Independent clique blocks remain independent in the actual quotient by
all central coefficients. This proves the direct-sum assertion, rather than
assuming an identification with a synthetic coordinate space. -/
theorem block_sum_zero_component {B : Type*} [Fintype B] [DecidableEq B]
    (C : B → Finset H) (hC : Function.Injective C)
    (e₀ : ∀ b,PairIn (C b)) (x : ∀ b,PairIn (C b) → ℝ)
    (hz : (∑ b,blockClass (C b) (x b))=0) (b : B) :
    blockClass (C b) (x b)=0 := by
  have hraw : coefficientClass (∑ c,blockCoordinates (C c) (x c))=0 := by
    simpa only [map_sum,blockClass,LinearMap.comp_apply] using hz
  have heval : ∀ e : PairIn (C b),
      (∑ c,blockCoordinates (C c) (x c)) (pairRow (C b) e)=x b e := by
    intro e
    rw [Finset.sum_apply]
    rw [sum_eq_single b]
    · exact blockCoordinates_pairRow (C b) (x b) e
    · intro c hc hcb
      have hne : rowClique (pairRow (C b) e)≠ C c := by
        rw [rowClique_pairRow]
        exact fun h => hcb (hC h.symm)
      change (if h : rowClique (pairRow (C b) e)=C c then
        x c (pairAtRow (C c) (pairRow (C b) e) h) else 0)=0
      exact dite_eq_right hne
    · simp
  apply (blockClass_eq_zero_iff (C b) (e₀ b) (x b)).mpr
  refine ⟨x b (e₀ b),?_⟩
  intro e
  have hrows : rowCliqueIndex (pairRow (C b) e)=rowCliqueIndex (pairRow (C b) (e₀ b)) := by
    apply Subtype.ext
    exact (rowClique_pairRow (C b) e).trans (rowClique_pairRow (C b) (e₀ b)).symm
  have hh := (coefficientClass_eq_zero_iff _).mp hraw _ _ hrows
  simpa only [heval] using hh

theorem block_families_independent {B : Type*} [Fintype B] [DecidableEq B]
    (C : B → Finset H) (hC : Function.Injective C) (e₀ : ∀ b,PairIn (C b))
    {J : B → Type*} [∀ b,Fintype (J b)]
    (x : ∀ b,J b → PairIn (C b) → ℝ)
    (hx : ∀ b,LinearIndependent ℝ (fun j => blockClass (C b) (x b j))) :
    LinearIndependent ℝ (fun j : Sigma J => blockClass (C j.1) (x j.1 j.2)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let y := fun b => ∑ i : J b,c ⟨b,i⟩ • x b i
  have hy : (∑ b,blockClass (C b) (y b))=0 := by
    rw [Fintype.sum_sigma] at hc
    simpa only [y,map_sum,map_smul] using hc
  have hj := block_sum_zero_component C hC e₀ y hy j.1
  have hji : (∑ i : J j.1,c ⟨j.1,i⟩ • blockClass (C j.1) (x j.1 i))=0 := by
    simpa only [y,map_sum,map_smul] using hj
  exact (Fintype.linearIndependent_iff.mp (hx j.1)) _ hji j.2

theorem pureDecompositions_independent {B : Type*} [Fintype B] [DecidableEq B]
    (C : B → Finset H) (hC : Function.Injective C) (hsize : ∀ b,2≤(C b).card)
    (v : B → ResponseQuotient H) (k : B → ℕ)
    (P : ∀ b,PureDecomposition (C b) (v b) (k b)) :
    LinearIndependent ℝ (fun j : Σ b,Fin (k b) => responseClass ((P j.1).functions j.2)) := by
  classical
  choose x hx using fun b j => (P b).block_supported j
  have hex : ∀ b,∃ e : PairIn (C b),True := by
    intro b
    obtain ⟨e,he⟩ := cliquePairs_nonempty (C b) (C b) (Subset.refl _) (hsize b)
    exact ⟨e,trivial⟩
  choose e₀ he₀ using hex
  have hi : ∀ b,LinearIndependent ℝ (fun j => blockClass (C b) (x b j)) := by
    intro b
    simpa only [← hx] using (P b).independent
  simpa only [hx] using block_families_independent C hC e₀ x hi

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart166

section BundlePart167
/- Source: Papers/GraphicalZonotopes/BookBlockCoordinates.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {H : Type*} [Fintype H] [LinearOrder H]

def largeBlocks (S : Finset H) : Finset (Finset H) :=
  S.powerset.filter (fun C => 3≤ C.card)

@[simp] theorem mem_largeBlocks {S C : Finset H} :
    C∈largeBlocks S ↔ C⊆S ∧ 3≤ C.card := by
  simp only [largeBlocks,mem_filter,mem_powerset]

abbrev BookBlock (H : Type*) [Fintype H] [LinearOrder H] :=
  ↥(largeBlocks (univ : Finset H))

def endpointCoefficients (C : Finset H) (d : H → ℝ) : PairIn C → ℝ :=
  fun e => d e.1.1.1+d e.1.1.2

theorem sum_full_stars (C : Finset H) (d : H → ℝ) :
    (∑ a,d a • starVector C a)=endpointCoefficients C d := by
  funext e
  have huv : e.1.1.1≠ e.1.1.2 := ne_of_lt e.1.2.1
  have he : ∀ a,starVector C a e=
      (if a=e.1.1.1 then (1 : ℝ) else 0)+(if a=e.1.1.2 then 1 else 0) := by
    intro a
    rw [starVector_eq]
    by_cases hu : a=e.1.1.1
    · have hv : a≠ e.1.1.2 := fun h => huv (hu.symm.trans h)
      simp [hu,hv,huv,Ne.symm huv]
    · by_cases hv : a=e.1.1.2 <;> simp [hu,hv,huv,Ne.symm huv]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,he,mul_add,sum_add_distrib,
    mul_ite,mul_one,mul_zero]
  simp only [sum_ite_eq',mem_univ,ite_true,endpointCoefficients]

/-- A threshold module's full coefficient response over all actual clique
blocks. Blocks that do not contain its distinguished vertex contribute zero. -/
theorem threshold_response_largeBlocks (a : H) :
    responseClass (thresholdStar a)=∑ C : BookBlock H,
      (-1 : ℝ)^(C.1.card-3) • blockClass C.1 (starVector C.1 a) := by
  have hcoord : thresholdSignedStar a=∑ C : BookBlock H,
      (-1 : ℝ)^(C.1.card-3) • blockCoordinates C.1 (starVector C.1 a) := by
    funext r
    rw [Finset.sum_apply]
    by_cases hr : 3≤(rowClique r).card
    · let C₀ : BookBlock H := ⟨rowClique r,mem_largeBlocks.mpr ⟨subset_univ _,hr⟩⟩
      rw [sum_eq_single C₀]
      · change thresholdSignedStar a r=
          (-1 : ℝ)^((rowClique r).card-3)*
            blockCoordinates (rowClique r) (starVector (rowClique r) a) r
        have he : blockCoordinates (rowClique r) (starVector (rowClique r) a) r=
            starVector (rowClique r) a (pairAtRow (rowClique r) r rfl) := by
          change (if h : rowClique r=rowClique r then
            starVector (rowClique r) a (pairAtRow (rowClique r) r h) else 0)=_
          rw [dite_eq_left rfl]
        rw [he,starVector_eq]
        change (if 3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2) then
          (-1 : ℝ)^((rowClique r).card-3) else 0)=
          (-1 : ℝ)^((rowClique r).card-3)*(if a=r.1.1.1 ∨ a=r.1.1.2 then 1 else 0)
        by_cases h : a=r.1.1.1 ∨ a=r.1.1.2 <;> simp [hr,h]
      · intro C hC hne
        have hrow : rowClique r≠ C.1 := fun h => hne (Subtype.ext h.symm)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
      · simp
    · rw [sum_eq_zero]
      · simp only [thresholdSignedStar,hr,false_and,ite_false]
      · intro C hC
        have hrow : rowClique r≠ C.1 := fun h => hr (h ▸ (mem_largeBlocks.mp C.2).2)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
  rw [thresholdStar_response_class,hcoord,map_sum]
  apply sum_congr rfl
  intro C hC
  rw [map_smul]
  rfl

/-- The coefficients of an arbitrary linear combination of threshold modules
are endpoint sums on every clique block, with the exact alternating sign. -/
theorem weighted_threshold_response (d : H → ℝ) :
    (∑ a,d a • responseClass (thresholdStar a))=
      ∑ C : BookBlock H,(-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (endpointCoefficients C.1 d) := by
  simp_rw [threshold_response_largeBlocks,smul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro C hC
  calc
    _ = (-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (∑ a,d a • starVector C.1 a) := by
      simp only [map_sum,map_smul,smul_sum]
      apply sum_congr rfl
      intro a ha
      exact smul_comm _ _ _
    _ = _ := by rw [sum_full_stars]

/-- Every actual block in the decomposition has its full constant kernel,
independently of all other blocks. -/
theorem book_block_sum_zero_component
    (x : (C : BookBlock H) → PairIn C.1 → ℝ)
    (hz : (∑ C : BookBlock H,blockClass C.1 (x C))=0) :
    ∀ C,∃ c : ℝ,∀ e,x C e=c := by
  classical
  have hp : ∀ C : BookBlock H,∃ e : PairIn C.1,True := by
    intro C
    obtain ⟨e,he⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨e,trivial⟩
  let e₀ := fun C => (hp C).choose
  have he := block_sum_zero_component Subtype.val Subtype.val_injective e₀ x hz
  intro C
  exact (blockClass_eq_zero_iff C.1 (e₀ C) (x C)).mp (he C)

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart167

section BundlePart168
/- Source: Papers/GraphicalZonotopes/IntegralBooleanResponse.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

def integerSubring : Subring ℝ:=(Int.castRingHom ℝ).range

theorem mem_integerSubring_iff (x : ℝ) :
    x∈integerSubring ↔ ∃ a : ℤ,x=(a : ℝ) := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,ha.symm⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,ha.symm⟩

theorem rowLower_symm_mem_subring (K : Subring ℝ) (x : HubResponseRow H → ℝ)
    (hx : ∀ r,x r∈K) : ∀ r,rowLowerEquiv.symm x r∈K := by
  intro r
  exact lowerEquiv_symm_mem_subring
    (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2) K
    (fun T => x ⟨r.1,T⟩) (fun T => hx ⟨r.1,T⟩) r.2

theorem weightedResponse_integer (F : J → SetFunction H)
    (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℤ) :
    ∀ r,weightedResponse F (fun j => (w j : ℝ)) r∈integerSubring := by
  intro r
  apply integerSubring.sum_mem
  intro j hj
  apply integerSubring.mul_mem
  · exact (mem_integerSubring_iff _).mpr ⟨w j,rfl⟩
  · rcases negativeResponse_values (hF j) r.1.1.1 r.1.1.2 r.2.1 with h | h
    · change negativeResponse (F j) _ _ _∈integerSubring
      rw [h]
      exact integerSubring.zero_mem
    · change negativeResponse (F j) _ _ _∈integerSubring
      rw [h]
      exact integerSubring.one_mem

/-- Whenever integral pair-response coefficients are integrable over the
reals, their central lift already has integral Möbius coefficients. No
unproved rationality or saturation assertion is used. -/
theorem central_integral_lift (x : HubResponseRow H → ℝ)
    (hx : ∀ r,x r∈integerSubring)
    (hblock : BlockConstant (rowLowerEquiv.symm x)) :
    ∃ c : CliqueIndex (⊤ : SimpleGraph H) → ℝ,
      (∀ C,c C∈integerSubring) ∧ centralCoefficientSlack c=x := by
  obtain ⟨c,hc⟩:=(blockConstant_iff_range_repeatCoefficients _).mp hblock
  have hi:=rowLower_symm_mem_subring integerSubring x hx
  refine ⟨c,?_,?_⟩
  · intro C
    obtain ⟨r,hr⟩:=rowCliqueIndex_surjective C
    have he:=congrFun hc r
    change c (rowCliqueIndex r)=rowLowerEquiv.symm x r at he
    rw [hr] at he
    rw [he]
    exact hi r
  · rw [← rowLower_repeatCoefficients,hc,rowLowerEquiv.apply_symm_apply]

/-- The integral central lift used by every Boolean-module construction in
Section7, stated for arbitrary finite hub and branch sets. -/
theorem integral_compatible_lift (F : J → SetFunction H)
    (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℤ)
    (hrel : (fun j => (w j : ℝ))∈LinearMap.ker (quotientRelation F)) :
    ∃ z : SetFunction H,TranslationNormalized z ∧ IntegerValued z ∧
      Compatible z F (fun j => (w j : ℝ)) := by
  have hi:=weightedResponse_integer F hF w
  have hb : BlockConstant (rowLowerEquiv.symm (weightedResponse F (fun j => (w j : ℝ)))) :=
    (integrable_iff_blockConstant F _).mp ((mem_quotientRelation_ker_iff F _).mp hrel)
  obtain ⟨c,hci,hc⟩:=central_integral_lift _ hi hb
  let y:=coefficientsFromCoordinates (⊤ : SimpleGraph H) c
  let z:=zeta y
  have hn : TranslationNormalized z:=(graphicalCoordinatesEquiv ⊤ c).2.1
  have hyi : IntegerValued y := by
    intro C
    by_cases hC : IsCliqueCoordinate (⊤ : SimpleGraph H) C
    · change (∃ a : ℤ,coefficientsFromCoordinates ⊤ c C=(a : ℝ))
      rw [coefficientsFromCoordinates,dif_pos hC]
      exact (mem_integerSubring_iff _).mp (hci ⟨C,hC⟩)
    · exact ⟨0,by simp only [y,coefficientsFromCoordinates,dif_neg hC,Int.cast_zero]⟩
  refine ⟨z,hn,zeta_integerValued hyi,?_⟩
  apply (compatible_iff_rows hn F _).mpr
  exact hc

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart168

section BundlePart169
/- Source: Papers/GraphicalZonotopes/WeightedBookGeometry.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- One branch depending on every hub joins all remaining nonconstant
branches. Other branches may ignore arbitrarily many of the hubs. -/
theorem essentialSpokeGraph_connected_of_anchor
    {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
    [Nonempty H] (F : J → SetFunction H) (j₀ : J)
    (hanchor : ∀ a, Essential (F j₀) a)
    (hbranch : ∀ j, ∃ a, Essential (F j) a) :
    (essentialSpokeGraph F).Connected := by
  letI : Nonempty J := ⟨j₀⟩
  have hhub : ∀ a, (essentialSpokeGraph F).Reachable (Sum.inl a) (Sum.inr j₀) :=
    fun a => (show (essentialSpokeGraph F).Adj (Sum.inl a) (Sum.inr j₀)
      from hanchor a).reachable
  have hreach : ∀ x, (essentialSpokeGraph F).Reachable x (Sum.inr j₀) := by
    intro x
    cases x with
    | inl a => exact hhub a
    | inr j =>
      obtain ⟨a,ha⟩ := hbranch j
      exact (show (essentialSpokeGraph F).Adj (Sum.inl a) (Sum.inr j)
        from ha).reachable.symm.trans (hhub a)
  exact ⟨fun x y => (hreach x).trans (hreach y).symm⟩

/-- Integral complementary polytope for any integral dilation at least the
sum of the positive branch scales. The complement is constructed from its
supermodular set function, not merely inferred from numerical containment. -/
theorem assembled_lattice_complement_of_weight_sum_le {s k : ℕ}
    {z : SetFunction (Fin s)} (hz : TranslationNormalized z) (hzi : IntegerValued z)
    {F : Fin k → SetFunction (Fin s)} (hF : ∀ j, IsMonotoneBoolean (F j))
    (w : Fin k → ℤ) (hw : ∀ j, 0 ≤ w j)
    (hc : Compatible z F (fun j => (w j : ℝ)))
    (M : ℤ) (hM : ∑ j, w j ≤ M) :
    LatticePolytope (basePolytope (assembled z F (fun j => (w j : ℝ)))) ∧
    ∃ R : Set ((Fin s ⊕ Fin k) → ℝ), LatticePolytope R ∧ R.Nonempty ∧
      basePolytope (assembled z F (fun j => (w j : ℝ))) + R =
        (M : ℝ) • graphicalZonotope (cliqueBook s k) := by
  let f := assembled z F (fun j => (w j : ℝ))
  have hw' : ∀ j, 0 ≤ (w j : ℝ) := fun j => by exact_mod_cast hw j
  have hn := assembled_normalized hz F hF (fun j => (w j : ℝ))
  have hs := assembled_supermodular z F hF (fun j => (w j : ℝ)) hw' hc
  have hi := assembled_integerValued hzi F hF w
  have hG := assembled_graphical z F (fun j => (w j : ℝ))
  have hsum : (∑ j, (w j : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hM
  have ha : 0 ≤ (M : ℝ) := (sum_nonneg (fun j _ => hw' j)).trans hsum
  have hbound : ∀ u v, u ≠ v → (cliqueBook s k).Adj u v → ∀ A,
      u ∉ A → v ∉ A → delta f u v A ≤ (M : ℝ) := by
    intro u v huv hedge A hu hv
    exact (assembled_delta_le_weight_sum hF hw' hc u v huv A hu hv).trans hsum
  let g : SetFunction (Fin s ⊕ Fin k) := (M : ℝ) • graphFunction (cliqueBook s k) - f
  have hgn : Normalized g := by
    change (M : ℝ) * graphFunction (cliqueBook s k) ∅ - f ∅ = 0
    have hf0 : f ∅ = 0 := hn.1
    rw [graphFunction_normalized, hf0, mul_zero, sub_self]
  have hgs : Supermodular g := graphical_complement_supermodular hG ha hbound
  have hgi : IntegerValued g :=
    ((graphFunction_integerValued (cliqueBook s k)).int_smul M).sub hi
  exact ⟨hi.basePolytope hn.1 hs, basePolytope g, hgi.basePolytope hgn hgs,
    basePolytope_nonempty hgn hgs,
    basePolytope_add_graphical_complement hn.1 hs hG ha hbound⟩

/-- A positive integral circuit in the actual response quotient yields a
full dimensional indecomposable lattice polytope and an integral complement.
Every ambient hub and every branch remains present in the dimension claim. -/
theorem lattice_book_of_weighted_modules {s k : ℕ} (hk : 0 < k)
    (F : Fin k → SetFunction (Fin s)) (hF : ∀ j, IsMonotoneBoolean (F j))
    (w : Fin k → ℤ) (hw : ∀ j, 0 < w j)
    (hconn : (essentialSpokeGraph F).Connected)
    (hrel : (fun j => (w j : ℝ)) ∈ LinearMap.ker (quotientRelation F))
    (huniq : UniqueIntegrableRelation F (fun j => (w j : ℝ)))
    (M : ℤ) (hM : ∑ j, w j ≤ M) :
    ∃ f : SetFunction (Fin s ⊕ Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s ⊕ Fin k) → ℝ), LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f + R = (M : ℝ) • graphicalZonotope (cliqueBook s k) := by
  obtain ⟨z,hzn,hzi,hc⟩ := integral_compatible_lift F hF w hrel
  have hw' : ∀ j, 0 < (w j : ℝ) := fun j => by exact_mod_cast hw j
  let f := assembled z F (fun j => (w j : ℝ))
  have hn : TranslationNormalized f := assembled_normalized hzn F hF _
  have hi : IntegerValued f := assembled_integerValued hzi F hF w
  have he : ExtremeSupermodular f := positive_circuit_extreme hzn hF
    (fun j => (hw' j).le) ⟨⟨0,hk⟩,ne_of_gt (hw' ⟨0,hk⟩)⟩ hc huniq
  have hd : FullDimension (basePolytope f) :=
    assembled_fullDimension hzn hF hw' hc hconn
  obtain ⟨hl,R,hR,hnR,hQR⟩ := assembled_lattice_complement_of_weight_sum_le
    hzn hzi hF w (fun j => (hw j).le) hc M hM
  exact ⟨f,hn,hi,he,assembled_graphical z F _,hd,
    he.minkowskiIndecomposable,hl,R,hR,hnR,hQR⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart169

section BundlePart170
/- Source: Papers/GraphicalZonotopes/ResponseBlockHelpers.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J]

/-- The genuine row belonging to a hub pair with every other hub present. -/
def fullRow (e : OrientedEdge (⊤ : SimpleGraph H)) : HubResponseRow H :=
  ⟨e,⟨commonNeighbors ⊤ e.1.1 e.1.2,mem_powerset.mpr (subset_refl _)⟩⟩

@[simp] theorem fullRow_edge (e : OrientedEdge (⊤ : SimpleGraph H)) :
    (fullRow e).1=e := rfl

@[simp] theorem rowClique_fullRow (e : OrientedEdge (⊤ : SimpleGraph H)) :
    rowClique (fullRow e)=univ := by
  ext a
  simp only [rowClique,fullRow,mem_insert,mem_commonNeighbors,SimpleGraph.top_adj,mem_univ,iff_true]
  by_cases ha : a=e.1.1
  · exact Or.inl ha
  · by_cases hb : a=e.1.2
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr ⟨Ne.symm ha,Ne.symm hb⟩)

def fullBlock (x : OrientedEdge (⊤ : SimpleGraph H) → ℝ) : HubResponseRow H → ℝ :=
  fun r => if rowClique r=univ then x r.1 else 0

/-- For an array supported on the full hub block, the actual integrability
condition is precisely equality of all pair coordinates of that block. -/
theorem fullBlock_constant_iff (x : OrientedEdge (⊤ : SimpleGraph H) → ℝ)
    [Nonempty (OrientedEdge (⊤ : SimpleGraph H))] :
    BlockConstant (fullBlock x) ↔ ∃ c : ℝ,∀ e,x e=c := by
  constructor
  · intro hx
    obtain ⟨e₀⟩:=‹Nonempty (OrientedEdge (⊤ : SimpleGraph H))›
    refine ⟨x e₀,?_⟩
    intro e
    have he : rowCliqueIndex (fullRow e)=rowCliqueIndex (fullRow e₀) := by
      apply Subtype.ext
      simp only [rowCliqueIndex,rowClique_fullRow]
    simpa only [fullBlock,rowClique_fullRow,ite_true,fullRow_edge] using hx _ _ he
  · rintro ⟨c,hc⟩ r t he
    have hrt : rowClique r=rowClique t:=congrArg Subtype.val he
    simp only [fullBlock,hrt,hc]

theorem rowLower_symm_weightedResponse (F : J → SetFunction H) (w : J → ℝ) :
    rowLowerEquiv.symm (weightedResponse F w)=
      ∑ j : J,w j • rowLowerEquiv.symm (responseVector (F j)) := by
  have he : weightedResponse F w=∑ j : J,w j • responseVector (F j) := by
    funext r
    simp only [weightedResponse,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he,map_sum]
  apply sum_congr rfl
  intro j hj
  exact map_smul rowLowerEquiv.symm (w j) (responseVector (F j))

theorem weightedResponse_reindex {K : Type*} [Fintype K]
    (e : K≃J) (F : J → SetFunction H) (w : K → ℝ) :
    weightedResponse (fun k => F (e k)) w=
      weightedResponse F (fun j => w (e.symm j)) := by
  funext r
  change (∑ k : K,w k*responseVector (F (e k)) r)=
    ∑ j : J,w (e.symm j)*responseVector (F j) r
  simpa only [e.symm_apply_apply] using
    e.sum_comp (fun j => w (e.symm j)*responseVector (F j) r)

theorem compatible_reindex {K : Type*} [Fintype K]
    (e : K≃J) (z : SetFunction H) (F : J → SetFunction H) (w : K → ℝ) :
    Compatible z (fun k => F (e k)) w ↔
      Compatible z F (fun j => w (e.symm j)) := by
  have hs : ∀ u v S,(∑ k : K,w k*negativeResponse (F (e k)) u v S)=
      ∑ j : J,w (e.symm j)*negativeResponse (F j) u v S := by
    intro u v S
    simpa only [e.symm_apply_apply] using
      e.sum_comp (fun j => w (e.symm j)*negativeResponse (F j) u v S)
  unfold Compatible
  simp only [hs]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart170

section BundlePart171
/- Source: Papers/GraphicalZonotopes/AnchoredBooleanCircuits.lean -/








@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

theorem quotientRelation_apply_eq_sum (F : J → SetFunction H) (w : J → ℝ) :
    quotientRelation F w=∑ j,w j • responseClass (F j) := by
  have he : weightedResponse F w=∑ j,w j • responseVector (F j) := by
    funext r
    simp only [weightedResponse,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change (LinearMap.range centralCoefficientSlack).mkQ (weightedResponse F w)=_
  rw [he,map_sum]
  simp only [map_smul,responseClass]

def anchoredFamily (F₀ : SetFunction H) (F : J → SetFunction H) : Option J → SetFunction H
  | none => F₀
  | some j => F j

/-- One distinguished column plus an independent family with vanishing
unit sum has precisely the unit relation line in the full quotient. -/
theorem anchored_unit_relation (F₀ : SetFunction H) (F : J → SetFunction H)
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,responseClass (F j)=0) :
    (fun _ : Option J => (1 : ℝ))∈LinearMap.ker (quotientRelation (anchoredFamily F₀ F)) ∧
      UniqueIntegrableRelation (anchoredFamily F₀ F) (fun _ => 1) := by
  constructor
  · change quotientRelation (anchoredFamily F₀ F) (fun _ => 1)=0
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option]
    simpa only [one_smul,anchoredFamily] using hsum
  · intro t ht
    have ht0 : quotientRelation (anchoredFamily F₀ F) t=0 :=
      (mem_quotientRelation_ker_iff _ _).mpr ht
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option] at ht0
    change t none • responseClass F₀+∑ j,t (some j) • responseClass (F j)=0 at ht0
    have hsub : (∑ j,(t (some j)-t none) • responseClass (F j))=0 := by
      calc
        _ = (t none • responseClass F₀+∑ j,t (some j) • responseClass (F j))-
            t none • (responseClass F₀+∑ j,responseClass (F j)) := by
          simp only [sub_smul,sum_sub_distrib,smul_add,smul_sum]
          abel
        _ = 0 := by rw [ht0,hsum,smul_zero,sub_self]
    have hcoeff := (Fintype.linearIndependent_iff.mp hind) _ hsub
    refine ⟨t none,?_⟩
    funext i
    cases i with
    | none => simp
    | some j =>
      have hj : t (some j)=t none := sub_eq_zero.mp (hcoeff j)
      simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using hj

/-- Relabeling a positive unit circuit with one all-hub anchor produces an
actual full lattice summand in exactly `k` times the graphical zonotope.
The other modules may have any nonempty proper essential hub sets. -/
theorem lattice_book_of_anchored_circuit {s k : ℕ} (hs : 0< s)
    (F₀ : SetFunction (Fin s)) (F : J → SetFunction (Fin s))
    (hF₀ : IsMonotoneBoolean F₀) (hF : ∀ j,IsMonotoneBoolean (F j))
    (hess₀ : ∀ a,Essential F₀ a) (hess : ∀ j,∃ a,Essential (F j) a)
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,responseClass (F j)=0)
    (hcard : Fintype.card J+1=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  have hk : 0< k := by omega
  have hJ : Fintype.card (Option J)=k := by simpa only [Fintype.card_option] using hcard
  let e : Fin k ≃ Option J := (finCongr hJ.symm).trans (Fintype.equivFin (Option J)).symm
  let G := anchoredFamily F₀ F
  let F' : Fin k → SetFunction (Fin s) := fun i => G (e i)
  have hG : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | none => exact hF₀
    | some j => exact hF j
  have hF' : ∀ i,IsMonotoneBoolean (F' i) := fun i => hG (e i)
  have hconn : (essentialSpokeGraph F').Connected := by
    apply essentialSpokeGraph_connected_of_anchor F' (e.symm none)
    · intro a
      simpa only [F',e.apply_symm_apply,G,anchoredFamily] using hess₀ a
    · intro i
      cases he : e i with
      | none => exact ⟨⟨0,hs⟩,by simpa only [F',he,G,anchoredFamily] using hess₀ ⟨0,hs⟩⟩
      | some j => simpa only [F',he,G,anchoredFamily] using hess j
  obtain ⟨hrel,huniq⟩ := anchored_unit_relation F₀ F hind hsum
  obtain ⟨z,hzn,hzc⟩ := (mem_quotientRelation_ker_iff G _).mp hrel
  have hc : Compatible z F' (fun _ => 1) :=
    (compatible_reindex e z G (fun _ => 1)).mpr hzc
  have huniq' : UniqueIntegrableRelation F' (fun _ => 1) := by
    intro t ht
    obtain ⟨u,hun,huc⟩ := ht
    have hold : Compatible u G (fun j => t (e.symm j)) :=
      (compatible_reindex e u G t).mp huc
    obtain ⟨c,hc⟩ := huniq (fun j => t (e.symm j)) ⟨u,hun,hold⟩
    refine ⟨c,?_⟩
    funext i
    simpa only [e.symm_apply_apply,Pi.smul_apply,smul_eq_mul,mul_one] using congrFun hc (e i)
  have hkrel : (fun _ : Fin k => (1 : ℝ))∈LinearMap.ker (quotientRelation F') :=
    (mem_quotientRelation_ker_iff F' _).mpr ⟨z,hzn,hc⟩
  obtain ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,hR⟩ :=
    lattice_book_of_weighted_modules hk F' hF' (fun _ => (1 : ℤ)) (fun _ => by norm_num)
      hconn (by simpa only [Int.cast_one] using hkrel)
      (by simpa only [Int.cast_one] using huniq') (k : ℤ) (by simp)
  exact ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,by simpa only [Int.cast_natCast] using hR⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart171

section BundlePart172
/- Source: Papers/GraphicalZonotopes/WeightedBooleanCircuits.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- Transport of a finite positive integral response circuit to the literal
book vertex type, retaining its integral dilation bound. -/
theorem lattice_book_of_finite_weighted_circuit
    {J : Type*} [Fintype J] [DecidableEq J] {s k : ℕ} (hs : 0< s)
    (F : J → SetFunction (Fin s)) (hF : ∀ j,IsMonotoneBoolean (F j))
    (j₀ : J) (hanchor : ∀ a,Essential (F j₀) a)
    (hbranch : ∀ j,∃ a,Essential (F j) a)
    (w : J → ℤ) (hw : ∀ j,0< w j)
    (hrel : (fun j => (w j : ℝ))∈LinearMap.ker (quotientRelation F))
    (huniq : UniqueIntegrableRelation F (fun j => (w j : ℝ)))
    (hcard : Fintype.card J=k) (M : ℤ) (hM : ∑ j,w j≤ M) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(M : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  letI : Nonempty J := ⟨j₀⟩
  have hk : 0< k := by rw [← hcard]; exact Fintype.card_pos
  let e : Fin k ≃ J := (finCongr hcard.symm).trans (Fintype.equivFin J).symm
  let F' : Fin k → SetFunction (Fin s) := fun i => F (e i)
  let w' : Fin k → ℤ := fun i => w (e i)
  have hc : (essentialSpokeGraph F').Connected := by
    apply essentialSpokeGraph_connected_of_anchor F' (e.symm j₀)
    · intro a
      simpa only [F',e.apply_symm_apply] using hanchor a
    · intro i
      exact hbranch (e i)
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
  apply lattice_book_of_weighted_modules hk F' (fun i => hF (e i)) w'
    (fun i => hw (e i)) hc hrel' huniq' M
  change (∑ i : Fin k,w (e i))≤ M
  rw [e.sum_comp]
  exact hM

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart172

section BundlePart173
/- Source: Papers/GraphicalZonotopes/BookCircuitAssembly.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

variable {s : ℕ} (hs : 3≤ s)

def bookZero : Fin s := ⟨0,by omega⟩
abbrev BookAnchor := ↥((univ : Finset (Fin s)).erase (bookZero hs))

def anchorExtension (t : BookAnchor hs → ℝ) : Fin s → ℝ :=
  erasedHubWeight univ (bookZero hs) t

@[simp] theorem anchorExtension_zero (t : BookAnchor hs → ℝ) :
    anchorExtension hs t (bookZero hs)=0 := erasedHubWeight_self _ _ _

@[simp] theorem anchorExtension_subtype (t : BookAnchor hs → ℝ) (a : BookAnchor hs) :
    anchorExtension hs t a.1=t a := erasedHubWeight_subtype _ _ _ _

theorem anchorExtension_labels :
    anchorExtension hs (fun a => (a.1.val : ℝ))=(fun a : Fin s => (a.val : ℝ)) := by
  funext a
  by_cases h : a=bookZero hs
  · subst a
    rw [anchorExtension_zero]
    norm_num [bookZero]
  · have ha : a∈(univ : Finset (Fin s)).erase (bookZero hs) := mem_erase.mpr ⟨h,mem_univ _⟩
    exact anchorExtension_subtype hs _ ⟨a,ha⟩

theorem sum_anchor_extension {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (t : BookAnchor hs → ℝ) (v : Fin s → W) :
    (∑ a : BookAnchor hs,t a • v a.1)=∑ a,anchorExtension hs t a • v a := by
  have he : (∑ a : BookAnchor hs,t a • v a.1)=
      ∑ a∈(univ : Finset (Fin s)).erase (bookZero hs),anchorExtension hs t a • v a := by
    rw [← sum_coe_sort ((univ : Finset (Fin s)).erase (bookZero hs))
      (fun a : Fin s => anchorExtension hs t a • v a)]
    exact sum_congr rfl (fun a _ => by rw [anchorExtension_subtype])
  rw [he]
  have hz : anchorExtension hs t (bookZero hs) • v (bookZero hs)=0 := by simp
  have hsum := sum_erase_add (s:=(univ : Finset (Fin s)))
    (f:=fun a => anchorExtension hs t a • v a) (mem_univ (bookZero hs))
  simpa only [hz,add_zero] using hsum

theorem weighted_anchor_response (t : BookAnchor hs → ℝ) :
    (∑ a : BookAnchor hs,t a • responseClass (thresholdStar a.1))=
      ∑ C : BookBlock (Fin s),(-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (endpointCoefficients C.1 (anchorExtension hs t)) := by
  rw [sum_anchor_extension hs t (fun a => responseClass (thresholdStar a)),weighted_threshold_response]

section Family
variable {B : Type*} [Fintype B] [DecidableEq B]
    (e : B ≃ BookBlock (Fin s)) (r : B → ℕ)
    (P : ∀ b,WeightedPureBlock (e b).1 ((s-1 : ℕ) : ℤ)
      (ordinaryBookTarget (e b).1) (r b))

abbrev BookCircuitIndex := BookAnchor hs ⊕ (Σ b,Fin (r b))

def bookCircuitVector : BookCircuitIndex hs r → ResponseQuotient (Fin s)
  | .inl a => responseClass (thresholdStar a.1)
  | .inr j => blockClass (e j.1).1 ((P j.1).column j.2)

def bookCircuitWeight : BookCircuitIndex hs r → ℤ
  | .inl a => (a.1.val : ℤ)
  | .inr j => (P j.1).weight j.2

def bookBlockCombination (t : BookCircuitIndex hs r → ℝ) (b : B) : PairIn (e b).1 → ℝ :=
  (-1 : ℝ)^((e b).1.card-3) • endpointCoefficients (e b).1
    (anchorExtension hs (fun a => t (.inl a)))+
    ∑ j : Fin (r b),t (.inr ⟨b,j⟩) • (P b).column j

theorem bookCircuit_sum_blocks (t : BookCircuitIndex hs r → ℝ) :
    (∑ j,t j • bookCircuitVector hs e r P j)=
      ∑ b,blockClass (e b).1 (bookBlockCombination hs e r P t b) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  change (∑ a : BookAnchor hs,t (.inl a) • responseClass (thresholdStar a.1))+
    (∑ b,∑ j : Fin (r b),t (.inr ⟨b,j⟩) • blockClass (e b).1 ((P b).column j))=_
  rw [weighted_anchor_response]
  have heq : (∑ C : BookBlock (Fin s),(-1 : ℝ)^(C.1.card-3) •
      blockClass C.1 (endpointCoefficients C.1 (anchorExtension hs (fun a => t (.inl a)))))=
      ∑ b,(-1 : ℝ)^((e b).1.card-3) • blockClass (e b).1
        (endpointCoefficients (e b).1 (anchorExtension hs (fun a => t (.inl a)))) := by
    exact (e.sum_comp _).symm
  rw [heq,← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  simp only [bookBlockCombination,map_add,map_smul,map_sum]

theorem bookCircuit_weighted_sum :
    (∑ j,(bookCircuitWeight hs e r P j : ℝ) • bookCircuitVector hs e r P j)=0 := by
  rw [bookCircuit_sum_blocks]
  apply sum_eq_zero
  intro b hb
  have hd : anchorExtension hs (fun a => (bookCircuitWeight hs e r P (.inl a) : ℝ))=
      (fun a : Fin s => (a.val : ℝ)) := by
    simpa only [bookCircuitWeight,Int.cast_natCast] using anchorExtension_labels hs
  simp only [bookBlockCombination,map_add,map_smul,map_sum,bookCircuitWeight,Int.cast_natCast]
  rw [anchorExtension_labels,(P b).weighted_sum]
  change (-1 : ℝ)^((e b).1.card-3) • blockClass (e b).1 (endpointLabels (e b).1)+
    -((-1 : ℝ)^((e b).1.card-3) • blockClass (e b).1 (endpointLabels (e b).1))=0
  exact add_neg_cancel _

theorem bookCircuit_pure_independent :
    LinearIndependent ℝ (fun j : Σ b,Fin (r b) =>
      blockClass (e j.1).1 ((P j.1).column j.2)) := by
  classical
  have hpair : ∀ b,∃ p : PairIn (e b).1,True := by
    intro b
    obtain ⟨p,hp⟩ := cliquePairs_nonempty (e b).1 (e b).1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp (e b).2).2; omega)
    exact ⟨p,trivial⟩
  apply block_families_independent (fun b => (e b).1)
    (Subtype.val_injective.comp e.injective) (fun b => (hpair b).choose)
    (fun b => (P b).column) (fun b => (P b).independent)

/-- The only nonlocal condition needed from the connectors: their block
constant equations force the prescribed arithmetic progression of hub scales. -/
def BookScaleRigidity : Prop :=
  ∀ (d : Fin s → ℝ) (t : (b : B) → Fin (r b) → ℝ),d (bookZero hs)=0 →
    (∀ b,blockClass (e b).1
      ((-1 : ℝ)^((e b).1.card-3) • endpointCoefficients (e b).1 d+
        ∑ j : Fin (r b),t b j • (P b).column j)=0) →
    ∃ c : ℝ,∀ a,d a=c*(a.val : ℝ)

theorem bookCircuit_unique_relation
    (hscale : BookScaleRigidity hs e r P)
    (t : BookCircuitIndex hs r → ℝ)
    (ht : (∑ j,t j • bookCircuitVector hs e r P j)=0) :
    ∃ c : ℝ,t=c • (fun j => (bookCircuitWeight hs e r P j : ℝ)) := by
  classical
  have hpair : ∀ b,∃ p : PairIn (e b).1,True := by
    intro b
    obtain ⟨p,hp⟩ := cliquePairs_nonempty (e b).1 (e b).1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp (e b).2).2; omega)
    exact ⟨p,trivial⟩
  rw [bookCircuit_sum_blocks] at ht
  have hblock := block_sum_zero_component (fun b => (e b).1)
    (Subtype.val_injective.comp e.injective) (fun b => (hpair b).choose)
    (bookBlockCombination hs e r P t) ht
  obtain ⟨c,hc⟩ := hscale (anchorExtension hs (fun a => t (.inl a)))
    (fun b j => t (.inr ⟨b,j⟩)) (anchorExtension_zero hs _) hblock
  have hanchor : ∀ a : BookAnchor hs,t (.inl a)=c*(a.1.val : ℝ) := by
    intro a
    simpa only [anchorExtension_subtype] using hc a.1
  have hzero : (∑ j : BookCircuitIndex hs r,
      (t j-c*(bookCircuitWeight hs e r P j : ℝ)) • bookCircuitVector hs e r P j)=0 := by
    simp only [sub_smul,mul_smul,sum_sub_distrib,← smul_sum]
    rw [bookCircuit_sum_blocks,ht,bookCircuit_weighted_sum,smul_zero,sub_self]
  rw [Fintype.sum_sum_type] at hzero
  have haz : (∑ a : BookAnchor hs,
      (t (.inl a)-c*(bookCircuitWeight hs e r P (.inl a) : ℝ)) •
        bookCircuitVector hs e r P (.inl a))=0 := by
    apply sum_eq_zero
    intro a ha
    simp only [bookCircuitWeight,Int.cast_natCast,hanchor,sub_self,zero_smul]
  rw [haz,zero_add] at hzero
  have hpure := Fintype.linearIndependent_iff.mp (bookCircuit_pure_independent e r P)
    (fun j => t (.inr j)-c*(bookCircuitWeight hs e r P (.inr j) : ℝ)) hzero
  refine ⟨c,?_⟩
  funext j
  cases j with
  | inl a => simpa only [Pi.smul_apply,smul_eq_mul,bookCircuitWeight,Int.cast_natCast] using hanchor a
  | inr j => simpa only [Pi.smul_apply,smul_eq_mul] using sub_eq_zero.mp (hpure j)

/-- A complete family of pure blocks and actual connector rigidity yields
an indecomposable full lattice book summand at the paper's stated scale. -/
theorem lattice_book_of_block_circuit (hscale : BookScaleRigidity hs e r P)
    {k : ℕ} (hcard : Fintype.card (BookCircuitIndex hs r)=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((s-1)*k : ℕ) : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  have hF : ∀ b j,∃ F : SetFunction (Fin s),IsMonotoneBoolean F ∧
      (∀ a,a∈(e b).1 → Essential F a) ∧
      (∀ a,a∉(e b).1 → ∀ X,F (insert a X)=F X) ∧
      responseClass F=blockClass (e b).1 ((P b).column j) := fun b j => (P b).realizable j
  choose F hFb hFe hFi hFc using hF
  let G : BookCircuitIndex hs r → SetFunction (Fin s)
    | .inl a => thresholdStar a.1
    | .inr j => F j.1 j.2
  have hG : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | inl a => exact thresholdStar_boolean a.1
    | inr j => exact hFb j.1 j.2
  have hGc : ∀ j,responseClass (G j)=bookCircuitVector hs e r P j := by
    intro j
    cases j with
    | inl a => rfl
    | inr j => exact hFc j.1 j.2
  let a₁ : BookAnchor hs := ⟨⟨1,by omega⟩,mem_erase.mpr ⟨by
    intro h
    have h' := congrArg Fin.val h
    simp [bookZero] at h',mem_univ _⟩⟩
  have ha₁ : ∀ a,Essential (G (.inl a₁)) a :=
    thresholdStar_essential (by simpa using hs) a₁.1
  have hbranch : ∀ j,∃ a,Essential (G j) a := by
    intro j
    cases j with
    | inl a => exact ⟨a.1,thresholdStar_essential (by simpa using hs) a.1 a.1⟩
    | inr j =>
      have hne : (e j.1).1.Nonempty := card_pos.mp (by
        have h := (mem_largeBlocks.mp (e j.1).2).2
        omega)
      obtain ⟨a,ha⟩ := hne
      exact ⟨a,hFe j.1 j.2 a ha⟩
  have hw : ∀ j,0< bookCircuitWeight hs e r P j := by
    intro j
    cases j with
    | inl a =>
      change 0<(a.1.val : ℤ)
      have hne : a.1≠ bookZero hs := (mem_erase.mp a.2).1
      have hv : a.1.val≠0 := fun h => hne (Fin.ext h)
      omega
    | inr j => exact (P j.1).positive j.2
  have hb : ∀ j,bookCircuitWeight hs e r P j≤((s-1 : ℕ) : ℤ) := by
    intro j
    cases j with
    | inl a =>
      change (a.1.val : ℤ)≤((s-1 : ℕ) : ℤ)
      have h := a.1.isLt
      omega
    | inr j => exact (P j.1).bounded j.2
  have hrel : (fun j => (bookCircuitWeight hs e r P j : ℝ))∈LinearMap.ker (quotientRelation G) := by
    change quotientRelation G _=0
    rw [quotientRelation_apply_eq_sum]
    simp_rw [hGc]
    exact bookCircuit_weighted_sum hs e r P
  have huniq : UniqueIntegrableRelation G (fun j => (bookCircuitWeight hs e r P j : ℝ)) := by
    intro t ht
    have ht0 : quotientRelation G t=0 := (mem_quotientRelation_ker_iff G t).mpr ht
    rw [quotientRelation_apply_eq_sum] at ht0
    simp_rw [hGc] at ht0
    exact bookCircuit_unique_relation hs e r P hscale t ht0
  have hM : (∑ j,bookCircuitWeight hs e r P j)≤(((s-1)*k : ℕ) : ℤ) := by
    calc
      _ ≤ ∑ _ : BookCircuitIndex hs r,((s-1 : ℕ) : ℤ) := sum_le_sum (fun j _ => hb j)
      _ = _ := by simp [hcard,Nat.cast_mul,mul_comm]
  obtain ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,hR⟩ :=
    lattice_book_of_finite_weighted_circuit (by omega) G hG (.inl a₁) ha₁ hbranch
      (bookCircuitWeight hs e r P) hw hrel huniq hcard (((s-1)*k : ℕ) : ℤ) hM
  exact ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,by simpa only [Int.cast_natCast] using hR⟩

end Family
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart173

section BundlePart174
/- Source: Papers/GraphicalZonotopes/BookQuadrilateralPattern.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

/-- The `s-2` quadrilaterals in the paper's upper-interval construction. -/
def connectorLabels {s : ℕ} (i : Fin (s-2)) : Fin 4 → ℕ :=
  if i.val=0 then ![0,1,2,3]
  else if i.val=1 then ![0,1,3,4]
  else if i.val=2 then ![1,2,3,4]
  else ![0,1,i.val+1,i.val+2]

theorem connectorLabels_lt {s : ℕ} (hs : 5≤ s) (i : Fin (s-2)) (j : Fin 4) :
    connectorLabels i j< s := by
  have hi := i.isLt
  by_cases h0 : i.val=0 <;> by_cases h1 : i.val=1 <;> by_cases h2 : i.val=2 <;>
    fin_cases j <;> simp [connectorLabels,h0,h1,h2] <;> omega

theorem connectorLabels_strictMono {s : ℕ} (i : Fin (s-2)) :
    StrictMono (connectorLabels i) := by
  intro u v huv
  by_cases h0 : i.val=0 <;> by_cases h1 : i.val=1 <;> by_cases h2 : i.val=2 <;>
    fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals simp [connectorLabels,h0,h1,h2] <;> omega

theorem connectorLabels_balanced {s : ℕ} (i : Fin (s-2)) :
    connectorLabels i 0+connectorLabels i 3=connectorLabels i 1+connectorLabels i 2 := by
  by_cases h0 : i.val=0 <;> by_cases h1 : i.val=1 <;> by_cases h2 : i.val=2 <;>
    simp [connectorLabels,h0,h1,h2] <;> omega

def bookConnector {s : ℕ} (hs : 5≤ s) (i : Fin (s-2)) : BalancedQuad s where
  point j := ⟨connectorLabels i j,connectorLabels_lt hs i j⟩
  ordered := connectorLabels_strictMono i
  balanced := connectorLabels_balanced i

theorem BalancedQuad.point_le_last {s : ℕ} (Q : BalancedQuad s) {a : Fin s}
    (ha : a∈Q.clique) : a≤ Q.point 3 := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
  exact Q.ordered.monotone (by omega)

theorem connector_zero_mem {s : ℕ} (hs : 5≤ s) (i : Fin (s-2)) :
    (⟨0,by omega⟩ : Fin s)∈(bookConnector hs i).clique ↔ i.val≠2 := by
  have hmem : (⟨0,by omega⟩ : Fin s)∈(bookConnector hs i).clique ↔
      ∃ j : Fin 4,connectorLabels i j=0 := by
    simp only [BalancedQuad.clique,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨j,congrArg Fin.val hj⟩
    · rintro ⟨j,hj⟩
      exact ⟨j,Fin.ext hj⟩
  rw [hmem]
  by_cases h0 : i.val=0
  · constructor
    · intro h
      omega
    · intro h
      exact ⟨0,by simp [connectorLabels,h0]⟩
  by_cases h1 : i.val=1
  · constructor
    · intro h
      omega
    · intro h
      exact ⟨0,by simp [connectorLabels,h0,h1]⟩
  by_cases h2 : i.val=2
  · simp only [h2,ne_eq,not_true_eq_false,iff_false]
    rintro ⟨j,hj⟩
    fin_cases j <;> norm_num [connectorLabels,h0,h1,h2] at hj
  · refine ⟨fun _ => h2,fun _ => ⟨0,?_⟩⟩
    simp [connectorLabels,h0,h1,h2]

theorem bookConnector_clique_injective {s : ℕ} (hs : 5≤ s) :
    Function.Injective (fun i : Fin (s-2) => (bookConnector hs i).clique) := by
  intro i j h
  change (bookConnector hs i).clique=(bookConnector hs j).clique at h
  have hle : (bookConnector hs i).point 3≤(bookConnector hs j).point 3 := by
    apply BalancedQuad.point_le_last
    rw [← h]
    exact BalancedQuad.point_mem _ _
  have hge : (bookConnector hs j).point 3≤(bookConnector hs i).point 3 := by
    apply BalancedQuad.point_le_last
    rw [h]
    exact BalancedQuad.point_mem _ _
  have hmax : connectorLabels i 3=connectorLabels j 3 := congrArg Fin.val (le_antisymm hle hge)
  have hz : i.val≠2 ↔ j.val≠2 := by
    rw [← connector_zero_mem hs i,← connector_zero_mem hs j,h]
  apply Fin.ext
  by_cases hi0 : i.val=0 <;> by_cases hi1 : i.val=1 <;> by_cases hi2 : i.val=2 <;>
    by_cases hj0 : j.val=0 <;> by_cases hj1 : j.val=1 <;> by_cases hj2 : j.val=2 <;>
    simp [connectorLabels,hi0,hi1,hi2,hj0,hj1,hj2] at hmax <;> omega

/-- The three initial equal-endpoint-sum relations and the subsequent chain
force the complete prescribed hub scale vector for every `s≥5`. -/
theorem quadrilateral_endpoint_rigidity (s : ℕ) (hs : 5≤ s) (d : ℕ → ℝ)
    (h0 : d 0=0) (h03 : d 0+d 3=d 1+d 2)
    (h04 : d 0+d 4=d 1+d 3) (h14 : d 1+d 4=d 2+d 3)
    (hstep : ∀ j,5≤ j → j< s → d 0+d j=d 1+d (j-1)) :
    ∀ j,j< s → d j=(j : ℝ)*d 1 := by
  have h2 : d 2=2*d 1 := by linarith
  have h3 : d 3=3*d 1 := by linarith
  have h4 : d 4=4*d 1 := by linarith
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hsmall : j≤4
    · interval_cases j <;> norm_num [h0,h2,h3,h4]
    · have h5 : 5≤ j := by omega
      have hr := hstep j h5 hj
      have hp := ih (j-1) (by omega) (by omega)
      have hc : ((j-1 : ℕ) : ℝ)=(j : ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
      rw [hc] at hp
      linarith

theorem bookConnector_scale_rigidity {s : ℕ} (hs : 5≤ s)
    (d : Fin s → ℝ) (h0 : d ⟨0,by omega⟩=0)
    (hconn : ∀ i : Fin (s-2),
      d ((bookConnector hs i).point 0)+d ((bookConnector hs i).point 3)=
      d ((bookConnector hs i).point 1)+d ((bookConnector hs i).point 2)) :
    ∀ j : Fin s,d j=(j.val : ℝ)*d ⟨1,by omega⟩ := by
  let D : ℕ → ℝ := fun j => if h : j< s then d ⟨j,h⟩ else 0
  have hD : ∀ j : Fin s,D j.val=d j := by
    intro j
    simp only [D,dite_eq_left j.isLt]
  have hb0 := hconn ⟨0,by omega⟩
  have hb1 := hconn ⟨1,by omega⟩
  have hb2 := hconn ⟨2,by omega⟩
  have h03 : D 0+D 3=D 1+D 2 := by simpa [D,bookConnector,connectorLabels,(show 0< s by omega),
    (show 1< s by omega),(show 2< s by omega),(show 3< s by omega)] using hb0
  have h04 : D 0+D 4=D 1+D 3 := by simpa [D,bookConnector,connectorLabels,(show 0< s by omega),
    (show 1< s by omega),(show 3< s by omega),(show 4< s by omega)] using hb1
  have h14 : D 1+D 4=D 2+D 3 := by simpa [D,bookConnector,connectorLabels,(show 1< s by omega),
    (show 2< s by omega),(show 3< s by omega),(show 4< s by omega)] using hb2
  have hstep : ∀ j,5≤ j → j< s → D 0+D j=D 1+D (j-1) := by
    intro j hj hjs
    let i : Fin (s-2) := ⟨j-2,by omega⟩
    have hh := hconn i
    have hia : i.val+1=j-1 := by dsimp [i]; omega
    have hib : i.val+2=j := by dsimp [i]; omega
    have hi0 : i.val≠0 := by dsimp [i]; omega
    have hi1 : i.val≠1 := by dsimp [i]; omega
    have hi2 : i.val≠2 := by dsimp [i]; omega
    simpa [D,bookConnector,connectorLabels,hi0,hi1,hi2,hia,hib,(show 0< s by omega),
      (show 1< s by omega),hjs,(show j-1< s by omega)] using hh
  have h := quadrilateral_endpoint_rigidity s hs D
    (by simpa [D,(show 0< s by omega)] using h0) h03 h04 h14 hstep
  intro j
  have hj := h j.val j.isLt
  rw [hD j] at hj
  simpa [D,(show 1< s by omega)] using hj

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart174

section BundlePart175
/- Source: Papers/GraphicalZonotopes/BookBlockCounts.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

/-- Every integral vector interval realizes every intermediate total. -/
theorem interval_sum_composition {B : Type*} [Fintype B] [DecidableEq B]
    (l u : B → ℕ) (hlu : ∀ b,l b≤ u b) {n : ℕ}
    (hnlo : (∑ b,l b)≤ n) (hnhi : n≤∑ b,u b) :
    ∃ k : B → ℕ,(∀ b,l b≤ k b ∧ k b≤ u b) ∧ (∑ b,k b)=n := by
  have hsum : (∑ b,(u b-l b))+(∑ b,l b)=∑ b,u b := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun b _ => Nat.sub_add_cancel (hlu b))
  obtain ⟨f,hf,hfs⟩ := bounded_sum_composition (univ : Finset B) (fun b => u b-l b)
    (n:=n-∑ b,l b) (by omega)
  refine ⟨fun b => f b+l b,?_,?_⟩
  · intro b
    have hfb := hf b (mem_univ b)
    have hb := hlu b
    constructor <;> dsimp only <;> omega
  · rw [sum_add_distrib,hfs]
    omega

variable {H : Type*} [Fintype H] [LinearOrder H]

theorem largeBlocks_dimension_sum (S : Finset H) :
    (∑ C∈largeBlocks S,(C.card.choose 2-1))=blockDimensionSum S := by
  unfold blockDimensionSum
  apply sum_subset (filter_subset _ _)
  intro C hC hn
  have hc : C.card<3 := by
    have h : ¬3≤ C.card := fun h => hn (mem_largeBlocks.mpr ⟨mem_powerset.mp hC,h⟩)
    omega
  interval_cases hcard : C.card <;> norm_num [hcard,Nat.choose]

theorem BookBlock_dimension_sum :
    (∑ C : BookBlock H,(C.1.card.choose 2-1))+1=cliqueCapacity (Fintype.card H) := by
  rw [sum_coe_sort (largeBlocks (univ : Finset H)) (fun C : Finset H => C.card.choose 2-1)]
  rw [largeBlocks_dimension_sum,← cliqueCapacity_eq_dimension_sum,card_univ]

theorem largeBlocks_lower_count (S : Finset H) :
    (∑ C∈largeBlocks S,(C.card-1))+S.card.choose 2+2^S.card=
      S.card*2^(S.card-1)+1 := by
  let E := S.powerset.filter (fun C => C.Nonempty)
  have hEcard : E.card+1=2^S.card := by
    have hpartition := card_filter_add_card_filter_not (s:=S.powerset) (p:=fun C => C.Nonempty)
    have hempty : S.powerset.filter (fun C => ¬C.Nonempty)={∅} := by
      ext C
      simp only [mem_filter,mem_powerset,not_nonempty_iff_eq_empty,mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨empty_subset _,rfl⟩
    rw [hempty,card_singleton,card_powerset] at hpartition
    exact hpartition
  have hsumE : (∑ C∈E,(C.card-1))+E.card=∑ C∈S.powerset,C.card := by
    calc
      _ = ∑ C∈E,((C.card-1)+1) := by simp [sum_add_distrib]
      _ = ∑ C∈E,C.card := sum_congr rfl (fun C hC =>
        Nat.sub_add_cancel (show 1≤ C.card from (card_pos.mpr (mem_filter.mp hC).2)))
      _ = _ := by
        apply sum_subset (filter_subset _ _)
        intro C hC hn
        have hz : ¬C.Nonempty := fun h => hn (mem_filter.mpr ⟨hC,h⟩)
        exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hz)
  have hsplit : (∑ C∈E,(C.card-1))=
      (∑ C∈largeBlocks S,(C.card-1))+S.card.choose 2 := by
    have hfilter : E.filter (fun C => 3≤ C.card)=largeBlocks S := by
      ext C
      simp only [E,mem_filter,mem_powerset,mem_largeBlocks]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · exact fun h => ⟨⟨h.1,card_pos.mp (by omega)⟩,h.2⟩
    have hsmall : (∑ C∈E.filter (fun C => ¬3≤ C.card),(C.card-1))=
        (S.powersetCard 2).card := by
      have hp : S.powersetCard 2⊆E.filter (fun C => ¬3≤ C.card) := by
        intro C hC
        obtain ⟨hCS,hcard⟩ := mem_powersetCard.mp hC
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr hCS,
          card_pos.mp (by omega)⟩,by omega⟩
      calc
        _ = ∑ C∈S.powersetCard 2,(C.card-1) := by
          symm
          apply sum_subset hp
          intro C hC hn
          have hsize := (mem_filter.mp hC).2
          have hCS := mem_powerset.mp (mem_filter.mp (mem_filter.mp hC).1).1
          have hne2 : C.card≠2 := fun h => hn (mem_powersetCard.mpr ⟨hCS,h⟩)
          omega
        _ = _ := by
          have he : ∀ C∈S.powersetCard 2,C.card-1=1 := fun C hC => by
            rw [(mem_powersetCard.mp hC).2]
          simp only [sum_congr rfl he,sum_const,nsmul_eq_mul,mul_one,Nat.cast_id]
    have hpartition := sum_filter_add_sum_filter_not (s:=E) (p:=fun C => 3≤ C.card)
      (f:=fun C => C.card-1)
    rw [hfilter,hsmall,card_powersetCard] at hpartition
    exact hpartition.symm
  rw [hsplit,sum_powerset_card] at hsumE
  omega

theorem BookBlock_lower_sum {s : ℕ} (hs : 2≤ s) :
    (∑ C : BookBlock (Fin s),(C.1.card-1))+s.choose 2=
      (s-2)*2^(s-1)+1 := by
  have h := largeBlocks_lower_count (univ : Finset (Fin s))
  simp only [card_univ,Fintype.card_fin] at h
  rw [← sum_coe_sort (largeBlocks (univ : Finset (Fin s)))
    (fun C : Finset (Fin s) => C.card-1)] at h
  have hspos : 0< s := by omega
  have hp : 2^s=2*2^(s-1) := by
    have he : s-1+1=s := by omega
    calc
      2^s=2^(s-1+1) := congrArg (fun n => 2^n) he.symm
      _ = 2*2^(s-1) := by rw [pow_succ]; ring
  have hm : s*2^(s-1)=(s-2)*2^(s-1)+2*2^(s-1) := by
    calc
      s*2^(s-1)=((s-2)+2)*2^(s-1) := congrArg (fun n => n*2^(s-1)) (Nat.sub_add_cancel hs).symm
      _ = _ := by rw [Nat.add_mul]
  rw [hp,hm] at h
  exact Nat.add_right_cancel (h.trans (by ac_rfl))

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart175

section BundlePart176
/- Source: Papers/GraphicalZonotopes/BookUpperBlocks.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {s : ℕ} (hs : 5≤ s)

def connectorBlock (i : Fin (s-2)) : BookBlock (Fin s) :=
  ⟨(bookConnector hs i).clique,mem_largeBlocks.mpr
    ⟨subset_univ _,by rw [BalancedQuad.card_clique]; omega⟩⟩

theorem connectorBlock_injective : Function.Injective (connectorBlock hs) := by
  intro i j h
  exact bookConnector_clique_injective hs (congrArg Subtype.val h)

def connectorBlockSet : Finset (BookBlock (Fin s)) := univ.image (connectorBlock hs)

@[simp] theorem connectorBlock_mem (i : Fin (s-2)) :
    connectorBlock hs i∈connectorBlockSet hs := mem_image.mpr ⟨i,mem_univ _,rfl⟩

@[simp] theorem connectorBlockSet_card : (connectorBlockSet hs).card=s-2 := by
  rw [connectorBlockSet,card_image_of_injective _ (connectorBlock_injective hs),card_univ,Fintype.card_fin]

abbrev OrdinaryBookBlock := {C : BookBlock (Fin s) // C∉connectorBlockSet hs}
abbrev UpperBookBlock := Fin (s-2) ⊕ OrdinaryBookBlock hs

def upperBlockMap : UpperBookBlock hs → BookBlock (Fin s)
  | .inl i => connectorBlock hs i
  | .inr C => C.1

theorem upperBlockMap_bijective : Function.Bijective (upperBlockMap hs) := by
  constructor
  · intro b c h
    cases b with
    | inl i =>
      cases c with
      | inl j => exact congrArg Sum.inl (connectorBlock_injective hs h)
      | inr C =>
        change connectorBlock hs i=C.1 at h
        exact False.elim (C.2 (h ▸ connectorBlock_mem hs i))
    | inr C =>
      cases c with
      | inl i =>
        change C.1=connectorBlock hs i at h
        exact False.elim (C.2 (h.symm ▸ connectorBlock_mem hs i))
      | inr D => exact congrArg Sum.inr (Subtype.ext h)
  · intro C
    by_cases h : C∈connectorBlockSet hs
    · obtain ⟨i,hi,he⟩ := mem_image.mp h
      exact ⟨.inl i,he⟩
    · exact ⟨.inr ⟨C,h⟩,rfl⟩

def upperBlockEquiv : UpperBookBlock hs ≃ BookBlock (Fin s) :=
  Equiv.ofBijective (upperBlockMap hs) (upperBlockMap_bijective hs)

@[simp] theorem upperBlockEquiv_inl (i : Fin (s-2)) :
    upperBlockEquiv hs (.inl i)=connectorBlock hs i := rfl

@[simp] theorem upperBlockEquiv_inr (C : OrdinaryBookBlock hs) :
    upperBlockEquiv hs (.inr C)=C.1 := rfl

theorem sum_upperBlock_partition {W : Type*} [AddCommMonoid W]
    (v : BookBlock (Fin s) → W) :
    (∑ C : BookBlock (Fin s),v C)=
      (∑ i : Fin (s-2),v (connectorBlock hs i))+
        ∑ C : OrdinaryBookBlock hs,v C.1 := by
  have h := (upperBlockEquiv hs).sum_comp v
  rw [Fintype.sum_sum_type] at h
  exact h.symm

def upperPureRank (r : OrdinaryBookBlock hs → ℕ) : UpperBookBlock hs → ℕ
  | .inl _ => 4
  | .inr C => r C

def upperPureBlock (r : OrdinaryBookBlock hs → ℕ)
    (P : ∀ C,WeightedPureBlock C.1.1 ((s-1 : ℕ) : ℤ)
      (ordinaryBookTarget C.1.1) (r C)) :
    ∀ b : UpperBookBlock hs,WeightedPureBlock (upperBlockEquiv hs b).1
      ((s-1 : ℕ) : ℤ) (ordinaryBookTarget (upperBlockEquiv hs b).1) (upperPureRank hs r b)
  | .inl i => (bookConnector hs i).pureBlock
  | .inr C => P C

/-- The literal omitted coordinates of the selected quadrilaterals supply
all connector equations, hence force a one-dimensional hub scale space. -/
theorem upper_book_scale_rigidity (r : OrdinaryBookBlock hs → ℕ)
    (P : ∀ C,WeightedPureBlock C.1.1 ((s-1 : ℕ) : ℤ)
      (ordinaryBookTarget C.1.1) (r C)) :
    BookScaleRigidity (show 3≤ s by omega) (upperBlockEquiv hs)
      (upperPureRank hs r) (upperPureBlock hs r P) := by
  intro d t hd hblock
  have hconn : ∀ i : Fin (s-2),
      d ((bookConnector hs i).point 0)+d ((bookConnector hs i).point 3)=
        d ((bookConnector hs i).point 1)+d ((bookConnector hs i).point 2) := by
    intro i
    let Q := bookConnector hs i
    have hi := hblock (.inl i)
    change blockClass Q.clique
      ((-1 : ℝ)^(Q.clique.card-3) • endpointCoefficients Q.clique d+
        ∑ j : Fin 4,t (.inl i) j • Q.column j)=0 at hi
    obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff Q.clique Q.reference _).mp hi
    have hr := hc Q.reference
    have ho := hc Q.opposite
    simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,
      BalancedQuad.column_reference,BalancedQuad.column_opposite,mul_zero,
      sum_const_zero,add_zero] at hr ho
    have he := hr.trans ho.symm
    simp only [Q.card_clique] at he
    have he' : -(d (Q.point 0)+d (Q.point 3))= -(d (Q.point 1)+d (Q.point 2)) := by
      simpa [endpointCoefficients,BalancedQuad.reference,BalancedQuad.opposite,
        BalancedQuad.pair,orderedPair] using he
    exact neg_injective he'
  have h := bookConnector_scale_rigidity hs d hd hconn
  exact ⟨d ⟨1,by omega⟩,fun a => by simpa only [mul_comm] using h a⟩

/-- Exact ordinary-block lower count after removing the `s-2` connectors. -/
theorem ordinary_lower_count :
    3*(s-2)+(∑ C : OrdinaryBookBlock hs,(C.1.1.card-1))+s.choose 2=
      (s-2)*2^(s-1)+1 := by
  have h := BookBlock_lower_sum (show 2≤ s by omega)
  rw [sum_upperBlock_partition hs] at h
  have he : (∑ i : Fin (s-2),((connectorBlock hs i).1.card-1))=3*(s-2) := by
    simp only [connectorBlock,BalancedQuad.card_clique]
    norm_num [Nat.choose]
    ring
  rw [he] at h
  exact h

theorem ordinary_upper_count :
    5*(s-2)+(∑ C : OrdinaryBookBlock hs,(C.1.1.card.choose 2-1))+1=cliqueCapacity s := by
  have h := BookBlock_dimension_sum (H:=Fin s)
  simp only [Fintype.card_fin] at h
  rw [sum_upperBlock_partition hs] at h
  have he : (∑ i : Fin (s-2),((connectorBlock hs i).1.card.choose 2-1))=5*(s-2) := by
    simp only [connectorBlock,BalancedQuad.card_clique]
    norm_num [Nat.choose]
    ring
  rw [he] at h
  exact h

def bookUpperIntervalStart (s : ℕ) : ℕ :=
  (s-2)*2^(s-1)+2*s-2-s.choose 2

theorem bookUpperIntervalStart_eq :
    bookUpperIntervalStart s=(s-1)+4*(s-2)+∑ C : OrdinaryBookBlock hs,(C.1.1.card-1) := by
  have h := ordinary_lower_count hs
  unfold bookUpperIntervalStart
  omega

theorem cliqueCapacity_upper_ordinary :
    cliqueCapacity s=(s-1)+4*(s-2)+∑ C : OrdinaryBookBlock hs,(C.1.1.card.choose 2-1) := by
  have h := ordinary_upper_count hs
  omega

private theorem card_le_choose_two {n : ℕ} (hn : 3≤ n) : n≤ n.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left n (show 2≤ n-1 by omega)

/-- The full uniform upper interval of Theorem 7.10, with the paper's exact
integral dilation and an explicit integral Minkowski complement. -/
theorem book_upper_interval (hs : 5≤ s) {k : ℕ} (hklo : bookUpperIntervalStart s≤ k)
    (hkhi : k≤ cliqueCapacity s) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((s-1)*k : ℕ) : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  let N := (s-1)+4*(s-2)
  let l : OrdinaryBookBlock hs → ℕ := fun C => C.1.1.card-1
  let u : OrdinaryBookBlock hs → ℕ := fun C => C.1.1.card.choose 2-1
  have hlu : ∀ C,l C≤ u C := by
    intro C
    have hsize := (mem_largeBlocks.mp C.1.2).2
    have hchoose := card_le_choose_two hsize
    dsimp only [l,u]
    omega
  have hlo : N+(∑ C,l C)≤ k := by
    rw [bookUpperIntervalStart_eq hs] at hklo
    exact hklo
  have hhi : k≤ N+∑ C,u C := by
    rw [cliqueCapacity_upper_ordinary hs] at hkhi
    exact hkhi
  obtain ⟨r,hr,hrsum⟩ := interval_sum_composition l u hlu (n:=k-N) (by omega) (by omega)
  have hP : ∀ C : OrdinaryBookBlock hs,Nonempty
      (WeightedPureBlock C.1.1 ((s-1 : ℕ) : ℤ) (ordinaryBookTarget C.1.1) (r C)) := by
    intro C
    exact ordinary_book_pure_block C.1.1 (mem_largeBlocks.mp C.1.2).2 (hr C).1 (hr C).2
  let P := fun C => Classical.choice (hP C)
  apply lattice_book_of_block_circuit (show 3≤ s by omega) (upperBlockEquiv hs)
    (upperPureRank hs r) (upperPureBlock hs r P) (upper_book_scale_rigidity hs r P)
  have ha : Fintype.card (BookAnchor (show 3≤ s by omega))=s-1 := by
    simp only [BookAnchor,Fintype.card_coe,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
  change Fintype.card (BookAnchor (show 3≤ s by omega) ⊕
    (Σ b : UpperBookBlock hs,Fin (upperPureRank hs r b)))=k
  rw [Fintype.card_sum,Fintype.card_sigma]
  simp only [Fintype.card_fin,ha,Fintype.sum_sum_type]
  simp only [upperPureRank,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,hrsum]
  dsimp only [N] at hlo ⊢
  omega

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart176

section BundlePart177
/- Source: Papers/GraphicalZonotopes/AnchorBlockCounts.lean -/




@[expose] public section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [DecidableEq H]

def anchorBlocks (S : Finset H) (a : H) : Finset (Finset H) :=
  S.powerset.filter (fun C => a∈C ∧ 3≤ C.card)

@[simp] theorem mem_anchorBlocks {S C : Finset H} {a : H} :
    C∈anchorBlocks S a ↔ C⊆S ∧ a∈C ∧ 3≤ C.card := by
  simp only [anchorBlocks,mem_filter,mem_powerset]

private theorem nontrivial_erase_notMem (S : Finset H) (a : H)
    {T : Finset H} (hT : T∈nontrivialSubsets (S.erase a)) : a∉T := by
  intro h
  exact (notMem_erase a S) ((mem_powerset.mp (mem_filter.mp hT).1) h)

private theorem insert_anchor_injOn (S : Finset H) (a : H) :
    Set.InjOn (fun T : Finset H => insert a T) (↑(nontrivialSubsets (S.erase a)) : Set (Finset H)) := by
  intro T hT U hU he
  have haT := nontrivial_erase_notMem S a hT
  have haU := nontrivial_erase_notMem S a hU
  have h := congrArg (fun X : Finset H => X.erase a) he
  simpa only [erase_insert haT,erase_insert haU] using h

theorem anchorBlocks_eq_image (S : Finset H) (a : H) (ha : a∈S) :
    anchorBlocks S a=(nontrivialSubsets (S.erase a)).image (insert a) := by
  ext C
  rw [mem_anchorBlocks,mem_image]
  constructor
  · rintro ⟨hCS,haC,hC⟩
    refine ⟨C.erase a,mem_filter.mpr ⟨mem_powerset.mpr ?_,?_⟩,insert_erase haC⟩
    · intro x hx
      exact mem_erase.mpr ⟨(mem_erase.mp hx).1,hCS (mem_of_mem_erase hx)⟩
    · rw [card_erase_of_mem haC]
      omega
  · rintro ⟨T,hT,rfl⟩
    have hTS := mem_powerset.mp (mem_filter.mp hT).1
    have haT := nontrivial_erase_notMem S a hT
    refine ⟨insert_subset_iff.mpr ⟨ha,hTS.trans (erase_subset _ _)⟩,mem_insert_self _ _,?_⟩
    rw [card_insert_of_notMem haT]
    have hc := (mem_filter.mp hT).2
    omega

theorem anchorBlocks_card (S : Finset H) (a : H) (ha : a∈S) :
    (anchorBlocks S a).card=2^(S.card-1)-S.card := by
  rw [anchorBlocks_eq_image S a ha,card_image_of_injOn (insert_anchor_injOn S a),
    nontrivialSubsets_card,card_erase_of_mem ha]
  have hs : 1≤ S.card := card_pos.mpr ⟨a,ha⟩
  omega

theorem blockDimensionSum_erase_add_anchor (S : Finset H) (a : H) (ha : a∈S) :
    blockDimensionSum (S.erase a)+
      (∑ C∈anchorBlocks S a,(C.card.choose 2-1))=blockDimensionSum S := by
  have hsum : (∑ C∈anchorBlocks S a,(C.card.choose 2-1))=
      ∑ T∈(S.erase a).powerset,((insert a T).card.choose 2-1) := by
    rw [anchorBlocks_eq_image S a ha,sum_image (insert_anchor_injOn S a)]
    apply sum_subset (filter_subset _ _)
    intro T hT hn
    have haT : a∉T := fun h => (notMem_erase a S) ((mem_powerset.mp hT) h)
    have hsmall : ¬2≤ T.card := fun h => hn (mem_filter.mpr ⟨hT,h⟩)
    have hcases : T.card=0 ∨ T.card=1 := by omega
    rw [card_insert_of_notMem haT]
    rcases hcases with h | h <;> norm_num [h,Nat.choose]
  rw [hsum]
  conv_rhs => rw [← insert_erase ha]
  unfold blockDimensionSum
  rw [sum_powerset_insert (notMem_erase a S)]

theorem anchorBlocks_dimension_sum (S : Finset H) (a : H) (ha : a∈S) :
    (∑ C∈anchorBlocks S a,(C.card.choose 2-1))=
      cliqueCapacity S.card-cliqueCapacity (S.card-1) := by
  have h := blockDimensionSum_erase_add_anchor S a ha
  have hc := cliqueCapacity_eq_dimension_sum S
  have hd := cliqueCapacity_eq_dimension_sum (S.erase a)
  rw [card_erase_of_mem ha] at hd
  omega

end BooleanModule
end GraphicalZonotopes

end
end BundlePart177
