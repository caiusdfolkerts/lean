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

public import verified.parts.part012
import all verified.parts.part012

@[expose] public section

set_option debug.skipKernelTC false
set_option linter.all false
set_option Elab.async false
set_option internal.cmdlineSnapshots true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

section BundlePart178
/- Source: Papers/GraphicalZonotopes/BookIntervalArithmetic.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

theorem cliqueCapacity_int_formula (s : ℕ) :
    (cliqueCapacity s : ℤ)=(s.choose 2 : ℤ)*(2 : ℤ)^(s-2)-(2 : ℤ)^s+(s : ℤ)+2 := by
  let S := (univ : Finset (Fin s))
  have hsum := blockDimensionSum_add_cliques S
  rw [sum_powerset_choose_two] at hsum
  have hcount := card_filter_add_card_filter_not (s:=S.powerset) (p:=fun C => 2≤ C.card)
  rw [small_subsets_card,card_powerset] at hcount
  change (nontrivialSubsets S).card+(S.card+1)=2^S.card at hcount
  have hcap := cliqueCapacity_eq_dimension_sum S
  have hScard : S.card=s := by simp [S]
  rw [hScard] at hsum hcount hcap
  have hsum' : (blockDimensionSum S : ℤ)+((nontrivialSubsets S).card : ℤ)=
      (s.choose 2 : ℤ)*(2 : ℤ)^(s-2) := by exact_mod_cast hsum
  have hcount' : ((nontrivialSubsets S).card : ℤ)+(s : ℤ)+1=(2 : ℤ)^s := by exact_mod_cast hcount
  have hcap' : (cliqueCapacity s : ℤ)=(blockDimensionSum S : ℤ)+1 := by exact_mod_cast hcap
  linarith

theorem cliqueCapacity_pred_le {s : ℕ} (hs : 1≤ s) :
    cliqueCapacity (s-1)≤ cliqueCapacity s := by
  let S := (univ : Finset (Fin s))
  let a : Fin s := ⟨0,by omega⟩
  have ha : a∈S := mem_univ _
  have h := blockDimensionSum_erase_add_anchor S a ha
  have hcap := cliqueCapacity_eq_dimension_sum S
  have hprev := cliqueCapacity_eq_dimension_sum (S.erase a)
  rw [card_erase_of_mem ha] at hprev
  have hScard : S.card=s := by simp [S]
  rw [hScard] at hcap hprev
  omega

theorem two_mul_le_choose_two {n : ℕ} (hn : 5≤ n) : 2*n≤ n.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  calc
    (2*n)*2=n*4 := by ring
    _ ≤ n*(n-1) := Nat.mul_le_mul_left n (by omega)

private theorem pow_pred_four {s : ℕ} (hs : 3≤ s) :
    (2 : ℤ)^(s-1)=4*(2 : ℤ)^(s-3) := by
  have he : s-1=(s-3)+2 := by omega
  calc
    (2 : ℤ)^(s-1)=(2 : ℤ)^((s-3)+2) := congrArg (fun n => (2 : ℤ)^n) he
    _ = _ := by rw [pow_add]; norm_num; ring

private theorem pow_pred_two {s : ℕ} (hs : 3≤ s) :
    (2 : ℤ)^(s-2)=2*(2 : ℤ)^(s-3) := by
  have he : s-2=(s-3)+1 := by omega
  calc
    (2 : ℤ)^(s-2)=(2 : ℤ)^((s-3)+1) := congrArg (fun n => (2 : ℤ)^n) he
    _ = _ := by rw [pow_succ]; ring

private theorem pow_eight {s : ℕ} (hs : 3≤ s) :
    (2 : ℤ)^s=8*(2 : ℤ)^(s-3) := by
  have he : s=(s-3)+3 := by omega
  calc
    (2 : ℤ)^s=(2 : ℤ)^((s-3)+3) := congrArg (fun n => (2 : ℤ)^n) he
    _ = _ := by rw [pow_add]; norm_num; ring

theorem threshold_start_le_previous_capacity {s : ℕ} (hs : 6≤ s) :
    2^(s-1)-s+1≤ cliqueCapacity (s-1) := by
  have hpowge : s≤2^(s-1) := by
    have h := Nat.lt_two_pow_self (n := s-1)
    omega
  have hcast : ((2^(s-1)-s+1 : ℕ) : ℤ)=(2 : ℤ)^(s-1)-(s : ℤ)+1 := by
    rw [Nat.cast_add,Nat.cast_sub hpowge,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hchoose : (8 : ℤ)≤((s-1).choose 2 : ℤ) := by
    have h := two_mul_le_choose_two (show 5≤ s-1 by omega)
    have h' : (8 : ℕ)≤(s-1).choose 2 := by omega
    exact_mod_cast h'
  have hnonneg : 0≤(((s-1).choose 2 : ℤ)-8)*(2 : ℤ)^(s-3) :=
    mul_nonneg (by omega) (by positivity)
  have hformula := cliqueCapacity_int_formula (s-1)
  have hexp : s-1-2=s-3 := by omega
  rw [hexp,pow_pred_four (by omega),Nat.cast_sub (show 1≤ s by omega),Nat.cast_one] at hformula
  have hbound : ((2^(s-1)-s+1 : ℕ) : ℤ)≤(cliqueCapacity (s-1) : ℤ) := by
    rw [hcast,pow_pred_four (by omega)]
    nlinarith
  exact_mod_cast hbound

theorem bookUpperIntervalStart_int_formula {s : ℕ} (hs : 5≤ s) :
    (bookUpperIntervalStart s : ℤ)=((s : ℤ)-2)*(2 : ℤ)^(s-1)+2*(s : ℤ)-2-(s.choose 2 : ℤ) := by
  have h := BookBlock_lower_sum (show 2≤ s by omega)
  have h2 : 2≤(s-2)*2^(s-1)+2*s := by omega
  have hc : s.choose 2≤(s-2)*2^(s-1)+2*s-2 := by omega
  unfold bookUpperIntervalStart
  rw [Nat.cast_sub hc,Nat.cast_sub h2,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,
    Nat.cast_sub (show 2≤ s by omega),Nat.cast_pow]
  norm_num

theorem upper_start_le_threshold_end {s : ℕ} (hs : 6≤ s) :
    bookUpperIntervalStart s≤ cliqueCapacity s-cliqueCapacity (s-1)+1 := by
  have hmono := cliqueCapacity_pred_le (show 1≤ s by omega)
  have hchoose : (s.choose 2 : ℤ)=((s-1).choose 2 : ℤ)+(s : ℤ)-1 := by
    have h := Nat.choose_succ_succ (s-1) 1
    change (s-1+1).choose 2=(s-1).choose 1+(s-1).choose 2 at h
    have he : s-1+1=s := by omega
    have hc : s.choose 2=(s-1)+(s-1).choose 2 := by
      simpa only [he,Nat.choose_one_right] using h
    rw [hc,Nat.cast_add,Nat.cast_sub (show 1≤ s by omega),Nat.cast_one]
    ring
  have hcpNat := two_mul_le_choose_two (show 5≤ s-1 by omega)
  have hcsNat := two_mul_le_choose_two (show 5≤ s by omega)
  have hcp : 2*((s : ℤ)-1)≤((s-1).choose 2 : ℤ) := by
    have h' : ((2*(s-1) : ℕ) : ℤ)≤((s-1).choose 2 : ℤ) := by exact_mod_cast hcpNat
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (show 1≤ s by omega),Nat.cast_one] using h'
  have hcs : 2*(s : ℤ)≤(s.choose 2 : ℤ) := by exact_mod_cast hcsNat
  have hp : 0≤(((s-1).choose 2 : ℤ)-2*(s : ℤ)+2)*(2 : ℤ)^(s-3) :=
    mul_nonneg (by omega) (by positivity)
  have hgap : ((cliqueCapacity s-cliqueCapacity (s-1)+1 : ℕ) : ℤ)-
      (bookUpperIntervalStart s : ℤ)=
      (((s-1).choose 2 : ℤ)-2*(s : ℤ)+2)*(2 : ℤ)^(s-3)+
        (s.choose 2 : ℤ)-2*(s : ℤ)+4 := by
    rw [Nat.cast_add,Nat.cast_sub hmono,Nat.cast_one,
      bookUpperIntervalStart_int_formula (by omega),cliqueCapacity_int_formula,
      cliqueCapacity_int_formula]
    have hexp : s-1-2=s-3 := by omega
    rw [hexp,pow_pred_two (s:=s) (by omega),pow_eight (s:=s) (by omega),pow_pred_four (s:=s) (by omega),
      Nat.cast_sub (show 1≤ s by omega),Nat.cast_one,hchoose]
    ring
  have hbound : (bookUpperIntervalStart s : ℤ)≤
      ((cliqueCapacity s-cliqueCapacity (s-1)+1 : ℕ) : ℤ) := by linarith
  exact_mod_cast hbound

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart178

section BundlePart179
/- Source: Papers/GraphicalZonotopes/SignedPairBases.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

/-- Finite reindexing of pure module data preserves the exact weighted
relation and all positive integral scale bounds. -/
def weightedPureBlock_of_data (C : Finset H) (M : ℤ) (v : ResponseQuotient H)
    (x : J → PairIn C → ℝ) (hx : ∀ j,PureRealizable C (x j))
    (w : J → ℤ) (hw : ∀ j,0< w j) (hM : ∀ j,w j≤ M)
    (hind : LinearIndependent ℝ (fun j => blockClass C (x j)))
    (hsum : (∑ j,(w j : ℝ) • blockClass C (x j))=v)
    {r : ℕ} (hr : Fintype.card J=r) : WeightedPureBlock C M v r := by
  classical
  let e : Fin r ≃ J := (finCongr hr.symm).trans (Fintype.equivFin J).symm
  exact {
    column := fun j => x (e j)
    realizable := fun j => hx (e j)
    weight := fun j => w (e j)
    positive := fun j => hw (e j)
    bounded := fun j => hM (e j)
    independent := hind.comp e e.injective
    weighted_sum := (e.sum_comp (fun j => (w j : ℝ) • blockClass C (x j))).trans hsum
  }

theorem reference_pair_expansion (C : Finset H) (e₀ : PairIn C)
    (x : PairIn C → ℝ) (hx : x e₀=0) :
    (∑ p : ↥((univ : Finset (PairIn C)).erase e₀),x p.1 • pairIndicator {p.1})=x := by
  classical
  funext e
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,pairIndicator,mem_singleton,mul_ite,mul_one,mul_zero]
  by_cases he : e=e₀
  · subst e
    have hn : ∀ p : ↥((univ : Finset (PairIn C)).erase e₀),e₀≠ p.1 :=
      fun p => Ne.symm (mem_erase.mp p.2).1
    simp only [hn,ite_false,sum_const_zero,hx]
  · let p₀ : ↥((univ : Finset (PairIn C)).erase e₀) := ⟨e,mem_erase.mpr ⟨he,mem_univ _⟩⟩
    have hp : ∀ p : ↥((univ : Finset (PairIn C)).erase e₀),e=p.1 ↔ p=p₀ := by
      intro p
      exact ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩
    simp only [hp,sum_ite_eq',mem_univ,ite_true]
    rfl

/-- The complete signed pair basis excluding one reference coordinate,
realized by genuine positive or negative pure Boolean pair modules. -/
def signed_pair_basis (C : Finset H) (hC : 3≤ C.card) (e₀ : PairIn C)
    (ε : ℝ) (hε : ε=1 ∨ ε= -1) (w : PairIn C → ℤ)
    (hw₀ : w e₀=0) (hw : ∀ e,e≠ e₀ → 0< w e) (M : ℤ)
    (hM : ∀ e,e≠ e₀ → w e≤ M) :
    WeightedPureBlock C M (blockClass C (ε • (fun e => (w e : ℝ)))) (C.card.choose 2-1) := by
  classical
  let J := ↥((univ : Finset (PairIn C)).erase e₀)
  let x : J → PairIn C → ℝ := fun p => ε • pairIndicator {p.1}
  have hx : ∀ p,PureRealizable C (x p) := by
    intro p
    rcases hε with h | h
    · simpa only [x,h,one_smul] using pureRealizable_pair C p.1
    · simpa only [x,h,neg_one_smul] using pureRealizable_negative_pair C hC p.1
  have hε₀ : ε≠0 := by rcases hε with rfl | rfl <;> norm_num
  have hind : LinearIndependent ℝ (fun p : J => blockClass C (x p)) := by
    have hi := reference_pair_columns_independent C e₀
    rw [Fintype.linearIndependent_iff]
    intro t ht p
    have hz : (∑ q : J,(t q*ε) • blockClass C (pairIndicator {q.1}))=0 := by
      simpa only [x,map_smul,mul_smul] using ht
    exact (mul_eq_zero.mp ((Fintype.linearIndependent_iff.mp hi) _ hz p)).resolve_right hε₀
  have hsum : (∑ p : J,(w p.1 : ℝ) • blockClass C (x p))=
      blockClass C (ε • (fun e => (w e : ℝ))) := by
    have he : (∑ p : J,(w p.1 : ℝ) • x p)=ε • (fun e => (w e : ℝ)) := by
      calc
        _ = ε • (∑ p : J,(w p.1 : ℝ) • pairIndicator {p.1}) := by
          simp only [x,smul_sum]
          exact sum_congr rfl (fun p _ => smul_comm _ _ _)
        _ = _ := congrArg (fun y : PairIn C → ℝ => ε • y)
          (reference_pair_expansion C e₀ (fun e => (w e : ℝ)) (by simp [hw₀]))
    simpa only [map_sum,map_smul] using congrArg (blockClass C) he
  apply weightedPureBlock_of_data C M _ x hx (fun p : J => w p.1)
    (fun p => hw p.1 (mem_erase.mp p.2).1)
    (fun p => hM p.1 (mem_erase.mp p.2).1) hind hsum
  simp only [J,Fintype.card_coe,card_erase_of_mem (mem_univ _),card_univ,pairIn_card]

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart179

section BundlePart180
/- Source: Papers/GraphicalZonotopes/PositiveStarInterpolation.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

private def starSeed (C : Finset H) (a : H) (ha : a∈C) (i : C.erase a) : PairIn C :=
  pairOfNe C a i.1 (Ne.symm (mem_erase.mp i.2).1) ha (mem_of_mem_erase i.2)

private theorem starSeed_eq_iff (C : Finset H) (a : H) (ha : a∈C)
    (i : C.erase a) (e : PairIn C) :
    e=starSeed C a ha i ↔
      (e.1.1.1=a ∧ e.1.1.2=i.1) ∨ (e.1.1.2=a ∧ e.1.1.1=i.1) := by
  have h := congrArg (fun A : Finset (PairIn C) => e∈A)
    (starPairs_singleton C (Ne.symm (mem_erase.mp i.2).1) ha (mem_of_mem_erase i.2))
  simpa only [mem_starPairs,StarPair,mem_singleton,starSeed] using Iff.of_eq h.symm

private theorem starSeed_injective (C : Finset H) (a : H) (ha : a∈C) :
    Function.Injective (starSeed C a ha) := by
  intro i j hij
  have hi := (starSeed_eq_iff C a ha i (starSeed C a ha i)).mp rfl
  have hj := (starSeed_eq_iff C a ha j (starSeed C a ha i)).mp hij
  apply Subtype.ext
  rcases hi with ⟨hia,hi⟩ | ⟨hia,hi⟩ <;> rcases hj with ⟨hja,hj⟩ | ⟨hja,hj⟩
  · exact hi.symm.trans hj
  · exact False.elim ((mem_erase.mp j.2).1 (hj.symm.trans hia))
  · exact False.elim ((mem_erase.mp j.2).1 (hj.symm.trans hia))
  · exact hi.symm.trans hj

private theorem starSeed_range (C : Finset H) (a : H) (ha : a∈C) (e : PairIn C) :
    e∈starPairs C a (C.erase a) ↔ ∃ i : C.erase a,e=starSeed C a ha i := by
  rw [mem_starPairs]
  constructor
  · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
    · exact ⟨⟨e.1.1.2,hv⟩,(starSeed_eq_iff C a ha _ e).mpr (Or.inl ⟨hu,rfl⟩)⟩
    · exact ⟨⟨e.1.1.1,hu⟩,(starSeed_eq_iff C a ha _ e).mpr (Or.inr ⟨hv,rfl⟩)⟩
  · rintro ⟨i,hi⟩
    rcases (starSeed_eq_iff C a ha i e).mp hi with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact Or.inl ⟨hu,hv.symm ▸ i.2⟩
    · exact Or.inr ⟨hv,hu.symm ▸ i.2⟩

private theorem starSeed_not_extra (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆cliquePairs C (C.erase a)) :
    ∀ i,starSeed C a ha i∉D := by
  intro i h
  obtain ⟨hu,hv⟩ := mem_cliquePairs.mp (hD h)
  rcases (starSeed_eq_iff C a ha i (starSeed C a ha i)).mp rfl with hh | hh
  · exact (mem_erase.mp hu).1 hh.1
  · exact (mem_erase.mp hv).1 hh.1

private def starOwner (C : Finset H) (a : H) (D : Finset (PairIn C))
    (hD : D⊆cliquePairs C (C.erase a)) (d : D) : C.erase a :=
  ⟨d.1.1.1.1,(mem_cliquePairs.mp (hD d.2)).1⟩

private def starOutNeighbors (C : Finset H) (a : H) (D : Finset (PairIn C))
    (i : C.erase a) : Finset H :=
  insert a ((D.filter (fun e => e.1.1.1=i.1)).image (fun e => e.1.1.2))

private theorem starOutNeighbors_subset (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (i : C.erase a) : starOutNeighbors C a D i⊆C := by
  intro b hb
  rcases mem_insert.mp hb with rfl | hb
  · exact ha
  · obtain ⟨e,he,rfl⟩ := mem_image.mp hb
    exact e.2.2

private theorem starOutNeighbors_ne (C : Finset H) (a : H)
    (D : Finset (PairIn C)) (i : C.erase a) : i.1∉starOutNeighbors C a D i := by
  intro h
  rcases mem_insert.mp h with h | h
  · exact (mem_erase.mp i.2).1 h
  · obtain ⟨e,he,hi⟩ := mem_image.mp h
    have he' := (mem_filter.mp he).2
    exact (ne_of_lt e.1.2.1) (he'.trans hi.symm)

private theorem starOutNeighbors_characterization (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆cliquePairs C (C.erase a))
    (i : C.erase a) (e : PairIn C) :
    StarPair i.1 (starOutNeighbors C a D i) e.1.1.1 e.1.1.2 ↔
      e=starSeed C a ha i ∨ ∃ h : e∈D,starOwner C a D hD ⟨e,h⟩=i := by
  constructor
  · rintro (⟨hu,hv⟩ | ⟨hv,hu⟩)
    · rcases mem_insert.mp hv with hv | hv
      · exact Or.inl ((starSeed_eq_iff C a ha i e).mpr (Or.inr ⟨hv,hu⟩))
      · obtain ⟨d,hd,hv⟩ := mem_image.mp hv
        have hdu := (mem_filter.mp hd).2
        have he : e=d := by
          apply Subtype.ext
          apply Subtype.ext
          exact Prod.ext (hu.trans hdu.symm) hv.symm
        have heD : e∈D := he.symm ▸ (mem_filter.mp hd).1
        exact Or.inr ⟨heD,Subtype.ext hu⟩
    · rcases mem_insert.mp hu with hu | hu
      · exact Or.inl ((starSeed_eq_iff C a ha i e).mpr (Or.inl ⟨hu,hv⟩))
      · obtain ⟨d,hd,hu⟩ := mem_image.mp hu
        have hdu := (mem_filter.mp hd).2
        have hlt : e.1.1.2< e.1.1.1 := by
          simpa only [hdu,hu,hv] using d.1.2.1
        exact False.elim ((not_lt_of_ge e.1.2.1.le) hlt)
  · rintro (h | ⟨heD,howner⟩)
    · rcases (starSeed_eq_iff C a ha i e).mp h with ⟨hu,hv⟩ | ⟨hv,hu⟩
      · exact Or.inr ⟨hv,hu.symm ▸ mem_insert_self _ _⟩
      · exact Or.inl ⟨hu,hv.symm ▸ mem_insert_self _ _⟩
    · have hu : e.1.1.1=i.1 := congrArg Subtype.val howner
      exact Or.inl ⟨hu,mem_insert_of_mem (mem_image.mpr
        ⟨e,mem_filter.mpr ⟨heD,hu⟩,rfl⟩)⟩

private theorem starPivot_realizable (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) (D : Finset (PairIn C))
    (hD : D⊆cliquePairs C (C.erase a)) :
    ∀ j : C.erase a ⊕ D, PureRealizable C
      (pivotColumns (starSeed C a ha) D (starOwner C a D hD) j) := by
  intro j
  cases j with
  | inl i =>
    have he : pivotColumns (starSeed C a ha) D (starOwner C a D hD) (Sum.inl i)=
        pairIndicator (starPairs C i.1 (starOutNeighbors C a D i)) := by
      funext e
      change pivotPositive _ _ _ i e=_
      simp only [pairIndicator,mem_starPairs,starOutNeighbors_characterization C a ha D hD i e]
      unfold pivotPositive
      by_cases hs : e=starSeed C a ha i
      · have hn : e∉D := hs.symm ▸ starSeed_not_extra C a ha D hD i
        have hn' := starSeed_not_extra C a ha D hD i
        simp [hs,hn']
      · by_cases heD : e∈D
        · simp only [hs,ite_false,dite_eq_left heD,zero_add,false_or]
          congr 1
          apply propext
          constructor
          · exact fun h => ⟨heD,h⟩
          · exact fun ⟨_,h⟩ => h
        · simp [hs,heD]
    rw [he]
    exact pureRealizable_star C (mem_of_mem_erase i.2)
      (starOutNeighbors_subset C a ha D i) ⟨a,mem_insert_self _ _⟩
      (starOutNeighbors_ne C a D i)
  | inr d =>
    have he : pivotColumns (starSeed C a ha) D (starOwner C a D hD) (Sum.inr d)=
        -pairIndicator {d.1} := by
      funext e
      by_cases h : e=d.1 <;> simp [pivotColumns,pairIndicator,h]
    rw [he]
    exact pureRealizable_negative_pair C hC d.1

private theorem starPivot_sum (C : Finset H) (a : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆cliquePairs C (C.erase a)) :
    (∑ j : C.erase a ⊕ D,pivotColumns (starSeed C a ha) D (starOwner C a D hD) j)=
      starVector C a := by
  rw [pivotColumns_sum]
  funext e
  change (∑ i : C.erase a,if e=starSeed C a ha i then (1 : ℝ) else 0)=
    if e∈starPairs C a (C.erase a) then 1 else 0
  by_cases he : e∈starPairs C a (C.erase a)
  · obtain ⟨i,rfl⟩ := (starSeed_range C a ha e).mp he
    have hinj := starSeed_injective C a ha
    simp only [hinj.eq_iff,ite_eq_left he]
    simp
  · have hn : ∀ i : C.erase a,e≠ starSeed C a ha i :=
      fun i h => he ((starSeed_range C a ha e).mpr ⟨i,h⟩)
    simp [he,hn]

/-- The second range in the positive-star interpolation. New pairs are
inserted into an actual partial-star column and canceled by a negative pure
pair. Unique seed pairs and the omitted reference pair prove independence. -/
theorem positive_star_large_interpolation (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : C.card-1≤ k) (hkC : k≤ C.card.choose 2-1) :
    Nonempty (PureDecomposition C (blockClass C (starVector C a)) k) := by
  classical
  have hecard : (C.erase a).card=C.card-1 := card_erase_of_mem ha
  have hsub : C.erase a⊆C := erase_subset _ _
  have hchoose : C.card.choose 2=(C.card-1).choose 2+(C.card-1) := by
    have h := Nat.choose_succ_succ (C.card-1) 1
    have hs : C.card-1+1=C.card := by omega
    simpa only [Nat.succ_eq_add_one,hs,Nat.choose_one_right,Nat.add_comm] using h
  obtain ⟨e₀,he₀⟩ := cliquePairs_nonempty C (C.erase a) hsub (by omega)
  have hcapacity : k-(C.card-1)≤((cliquePairs C (C.erase a)).erase e₀).card := by
    rw [card_erase_of_mem he₀,cliquePairs_card C (C.erase a) hsub,hecard]
    omega
  obtain ⟨D,hD,hDc⟩ := exists_subset_card_eq hcapacity
  have hD' : D⊆cliquePairs C (C.erase a) := hD.trans (erase_subset _ _)
  let seed := starSeed C a ha
  let owner := starOwner C a D hD'
  let x := pivotColumns seed D owner
  have hreal : ∀ j,PureRealizable C (x j) := starPivot_realizable C hC a ha D hD'
  have hind : LinearIndependent ℝ x := pivotColumns_linearIndependent seed
    (starSeed_injective C a ha) D owner (starSeed_not_extra C a ha D hD')
  have hzero : ∀ j,x j e₀=0 := by
    apply pivotColumns_zero_at seed D owner e₀
    · exact fun h => (mem_erase.mp (hD h)).1 rfl
    · intro i he
      have hm := he.symm ▸ he₀
      exact starSeed_not_extra C a ha (cliquePairs C (C.erase a)) (Subset.refl _) i hm
  apply pureDecomposition_of_vectors x hreal
    (blockClass_linearIndependent_of_reference C e₀ x hind hzero) _ _
  · rw [← map_sum]
    exact congrArg (blockClass C) (starPivot_sum C a ha D hD')
  · simp only [Fintype.card_sum,Fintype.card_coe,hecard,hDc]
    omega

/-- The positive half of Lemma 7.7, with every intermediate count and the
actual response quotient. -/
theorem positive_star_interpolation (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : 1≤ k) (hkC : k≤ C.card.choose 2-1) :
    Nonempty (PureDecomposition C (blockClass C (starVector C a)) k) := by
  by_cases h : k≤ C.card-1
  · exact positive_star_small_interpolation C hC a ha hk h
  · exact positive_star_large_interpolation C hC a ha (by omega) hkC

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart180

section BundlePart181
/- Source: Papers/GraphicalZonotopes/NegativeStarInterpolation.lean -/




@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

private theorem pairIndicator_singleton_eq (C : Finset H) (e : PairIn C) :
    pairIndicator {e}=(fun f => if f=e then (1 : ℝ) else 0) := by
  funext f
  simp only [pairIndicator,mem_singleton]

private theorem pairOfNe_char (C : Finset H) (a b : H) (hab : a≠ b)
    (ha : a∈C) (hb : b∈C) (e : PairIn C) :
    e=pairOfNe C a b hab ha hb ↔
      (e.1.1.1=a ∧ e.1.1.2=b) ∨ (e.1.1.2=a ∧ e.1.1.1=b) := by
  have h := congrArg (fun A : Finset (PairIn C) => e∈A)
    (starPairs_singleton C hab ha hb)
  simpa only [mem_starPairs,StarPair,mem_singleton] using Iff.of_eq h.symm

private theorem pairOfNe_symm (C : Finset H) (a b : H) (hab : a≠ b)
    (ha : a∈C) (hb : b∈C) :
    pairOfNe C a b hab ha hb=pairOfNe C b a (Ne.symm hab) hb ha := by
  apply (pairOfNe_char C b a (Ne.symm hab) hb ha _).mpr
  rcases pairOfNe_endpoints C a b hab ha hb with h | h
  · exact Or.inr ⟨h.2,h.1⟩
  · exact Or.inl h

private theorem pairOfNe_other_eq (C : Finset H) (a b c : H) (hab : a≠ b)
    (hac : a≠ c) (ha : a∈C) (hb : b∈C) (hc : c∈C)
    (h : pairOfNe C a b hab ha hb=pairOfNe C a c hac ha hc) : b=c := by
  have hi := (pairOfNe_char C a b hab ha hb _).mp rfl
  have hj := (pairOfNe_char C a c hac ha hc _).mp h
  rcases hi with ⟨hia,hi⟩ | ⟨hia,hi⟩ <;> rcases hj with ⟨hja,hj⟩ | ⟨hja,hj⟩
  · exact hi.symm.trans hj
  · exact False.elim (hac (hia.symm.trans hj))
  · exact False.elim (hac (hia.symm.trans hj))
  · exact hi.symm.trans hj

private theorem pureRealizable_pair_sum (C : Finset H) (b u v : H)
    (hbu : b≠ u) (hbv : b≠ v) (huv : u≠ v)
    (hb : b∈C) (hu : u∈C) (hv : v∈C) :
    PureRealizable C (pairIndicator {pairOfNe C b u hbu hb hu}+
      pairIndicator {pairOfNe C b v hbv hb hv}) := by
  have he : pairIndicator {pairOfNe C b u hbu hb hu}+
      pairIndicator {pairOfNe C b v hbv hb hv}=
      pairIndicator (starPairs C b {u,v}) := by
    rw [← starPairs_singleton C hbu hb hu,← starPairs_singleton C hbv hb hv]
    have hs : ({u,v} : Finset H)={u}∪{v} := by simp
    rw [hs,starPairs_union]
    have hd := starPairs_disjoint C b (B:={u}) (D:={v}) (disjoint_singleton_left.mpr
      (by simpa only [mem_singleton] using huv))
      (by simpa only [mem_singleton] using hbu)
      (by simpa only [mem_singleton] using hbv)
    funext e
    by_cases he1 : e∈starPairs C b {u} <;> by_cases he2 : e∈starPairs C b {v}
    · exact False.elim (disjoint_left.mp hd he1 he2)
    all_goals simp [pairIndicator,he1,he2]
  rw [he]
  apply pureRealizable_star C (a:=b) (B:={u,v}) hb
  · exact insert_subset_iff.mpr ⟨hu,singleton_subset_iff.mpr hv⟩
  · exact insert_nonempty _ _
  · intro h
    rcases mem_insert.mp h with h | h
    · exact hbu h
    · exact hbv (mem_singleton.mp h)

private theorem pivotPositive_unique_owner {E I : Type*} [DecidableEq E]
    [Fintype I] [DecidableEq I] (seed : I → E) (D : Finset E)
    (owner : D → I) (hinj : Function.Injective owner) (d : D) :
    pivotPositive seed D owner (owner d)=
      (fun e => if e=seed (owner d) then (1 : ℝ) else 0)+
      (fun e => if e=d.1 then (1 : ℝ) else 0) := by
  funext e
  simp only [pivotPositive,Pi.add_apply]
  congr 1
  by_cases he : e∈D
  · rw [dite_eq_left he]
    have hh : owner ⟨e,he⟩=owner d ↔ e=d.1 := by
      rw [hinj.eq_iff]
      exact Subtype.ext_iff
    simp only [hh]
  · have hn : e≠ d.1 := fun h => he (h.symm ▸ d.2)
    simp [he,hn]

private theorem pivotPositive_no_owner {E I : Type*} [DecidableEq E]
    [Fintype I] [DecidableEq I] (seed : I → E) (D : Finset E)
    (owner : D → I) (i : I) (h : ¬∃ d,owner d=i) :
    pivotPositive seed D owner i=fun e => if e=seed i then (1 : ℝ) else 0 := by
  funext e
  unfold pivotPositive
  by_cases he : e∈D
  · have hn : owner ⟨e,he⟩≠ i := fun hh => h ⟨⟨e,he⟩,hh⟩
    simp [he,hn]
  · simp [he]

private theorem extraTip_exists (C : Finset H) (a q : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) (d : D) :
    ∃ b : (C.erase a).erase q,
      d.1=pairOfNe C a b.1 (Ne.symm (mem_erase.mp (mem_of_mem_erase b.2)).1)
        ha (mem_of_mem_erase (mem_of_mem_erase b.2)) := by
  rcases mem_starPairs.mp (hD d.2) with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · refine ⟨⟨d.1.1.1.2,hv⟩,?_⟩
    exact (pairOfNe_char C _ _ _ _ _ _).mpr (Or.inl ⟨hu,rfl⟩)
  · refine ⟨⟨d.1.1.1.1,hu⟩,?_⟩
    exact (pairOfNe_char C _ _ _ _ _ _).mpr (Or.inr ⟨hv,rfl⟩)

private def extraTip (C : Finset H) (a q : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) (d : D) :=
  Classical.choose (extraTip_exists C a q ha D hD d)

private theorem extraTip_spec (C : Finset H) (a q : H) (ha : a∈C)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) (d : D) :
    d.1=pairOfNe C a (extraTip C a q ha D hD d).1
      (Ne.symm (mem_erase.mp (mem_of_mem_erase (extraTip C a q ha D hD d).2)).1)
      ha (mem_of_mem_erase (mem_of_mem_erase (extraTip C a q ha D hD d).2)) :=
  Classical.choose_spec (extraTip_exists C a q ha D hD d)

private def cliqueOwner (C : Finset H) (a q : H) (ha : a∈C) (hq : q∈C.erase a)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q))
    (d : D) : cliquePairs C (C.erase a) :=
  let b := extraTip C a q ha D hD d
  ⟨pairOfNe C q b.1 (Ne.symm (mem_erase.mp b.2).1)
    (mem_of_mem_erase hq) (mem_of_mem_erase (mem_of_mem_erase b.2)),by
    rw [mem_cliquePairs]
    rcases pairOfNe_endpoints C q b.1 (Ne.symm (mem_erase.mp b.2).1)
      (mem_of_mem_erase hq) (mem_of_mem_erase (mem_of_mem_erase b.2)) with h | h
    · exact ⟨h.1.symm ▸ hq,h.2.symm ▸ mem_of_mem_erase b.2⟩
    · exact ⟨h.1.symm ▸ mem_of_mem_erase b.2,h.2.symm ▸ hq⟩⟩

private theorem cliqueOwner_injective (C : Finset H) (a q : H)
    (ha : a∈C) (hq : q∈C.erase a) (D : Finset (PairIn C))
    (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    Function.Injective (cliqueOwner C a q ha hq D hD) := by
  intro d e h
  let b := extraTip C a q ha D hD d
  let c := extraTip C a q ha D hD e
  have hh := pairOfNe_other_eq C q b.1 c.1
    (Ne.symm (mem_erase.mp b.2).1) (Ne.symm (mem_erase.mp c.2).1)
    (mem_of_mem_erase hq) (mem_of_mem_erase (mem_of_mem_erase b.2))
    (mem_of_mem_erase (mem_of_mem_erase c.2)) (congrArg Subtype.val h)
  have ht : extraTip C a q ha D hD d=extraTip C a q ha D hD e := Subtype.ext hh
  apply Subtype.ext
  rw [extraTip_spec C a q ha D hD d,extraTip_spec C a q ha D hD e,ht]

private theorem cliqueSeed_not_extra (C : Finset H) (a q : H)
    (D : Finset (PairIn C)) (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    ∀ i : cliquePairs C (C.erase a),i.1∉D := by
  intro i hi
  obtain ⟨hu,hv⟩ := mem_cliquePairs.mp i.2
  rcases mem_starPairs.mp (hD hi) with ⟨hh,_⟩ | ⟨hh,_⟩
  · exact (mem_erase.mp hu).1 hh
  · exact (mem_erase.mp hv).1 hh

private theorem cliquePivot_realizable (C : Finset H) (hC : 3≤ C.card)
    (a q : H) (ha : a∈C) (hq : q∈C.erase a) (D : Finset (PairIn C))
    (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    ∀ j : cliquePairs C (C.erase a) ⊕ D,
      PureRealizable C (pivotColumns Subtype.val D (cliqueOwner C a q ha hq D hD) j) := by
  intro j
  cases j with
  | inl i =>
    by_cases hi : ∃ d,cliqueOwner C a q ha hq D hD d=i
    · obtain ⟨d,rfl⟩ := hi
      change PureRealizable C (pivotPositive _ _ _ _)
      rw [pivotPositive_unique_owner Subtype.val D _
        (cliqueOwner_injective C a q ha hq D hD) d]
      let b := extraTip C a q ha D hD d
      have hbq : b.1≠ q := (mem_erase.mp b.2).1
      have hba : b.1≠ a := (mem_erase.mp (mem_of_mem_erase b.2)).1
      have hbC : b.1∈C := mem_of_mem_erase (mem_of_mem_erase b.2)
      have hqC : q∈C := mem_of_mem_erase hq
      have hqa : q≠ a := (mem_erase.mp hq).1
      have he1 : (cliqueOwner C a q ha hq D hD d).1=
          pairOfNe C b.1 q hbq hbC hqC := pairOfNe_symm C q b.1 (Ne.symm hbq) hqC hbC
      have he2 : d.1=pairOfNe C b.1 a hba hbC ha :=
        (extraTip_spec C a q ha D hD d).trans (pairOfNe_symm C a b.1 (Ne.symm hba) ha hbC)
      simp only [he1,he2]
      have hp := pureRealizable_pair_sum C b.1 q a hbq hba hqa hbC hqC ha
      rw [pairIndicator_singleton_eq,pairIndicator_singleton_eq] at hp
      exact hp
    · change PureRealizable C (pivotPositive _ _ _ _)
      rw [pivotPositive_no_owner Subtype.val D _ i hi]
      have hp := pureRealizable_pair C i.1
      rw [pairIndicator_singleton_eq] at hp
      exact hp
  | inr d =>
    have he : pivotColumns (fun i : cliquePairs C (C.erase a) => i.1) D
        (cliqueOwner C a q ha hq D hD) (Sum.inr d)=-pairIndicator {d.1} := by
      funext e
      by_cases h : e=d.1 <;> simp [pivotColumns,pairIndicator,h]
    rw [he]
    exact pureRealizable_negative_pair C hC d.1

private theorem cliquePivot_sum (C : Finset H) (a q : H)
    (ha : a∈C) (hq : q∈C.erase a) (D : Finset (PairIn C))
    (hD : D⊆starPairs C a ((C.erase a).erase q)) :
    (∑ j : cliquePairs C (C.erase a) ⊕ D,
      pivotColumns Subtype.val D (cliqueOwner C a q ha hq D hD) j)=
      pairIndicator (cliquePairs C (C.erase a)) := by
  rw [pivotColumns_sum]
  funext e
  by_cases he : e∈cliquePairs C (C.erase a)
  · have heq : ∀ i : cliquePairs C (C.erase a),e=i.1 ↔ i=⟨e,he⟩ :=
      fun i => ⟨fun h => Subtype.ext h.symm,fun h => congrArg Subtype.val h.symm⟩
    simp [heq,pairIndicator,he]
  · have hn : ∀ i : cliquePairs C (C.erase a),e≠ i.1 := fun i h => he (h.symm ▸ i.2)
    simp [hn,pairIndicator,he]

/-- The upper range of the negative-star interpolation. The initial clique
on the other hubs is extended using distinct seed pairs incident with `q`;
the reference pair `aq` is never activated. -/
theorem negative_star_large_interpolation (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : (C.card-1).choose 2≤ k)
    (hkC : k≤ C.card.choose 2-1) :
    Nonempty (PureDecomposition C (-blockClass C (starVector C a)) k) := by
  classical
  have hecard : (C.erase a).card=C.card-1 := card_erase_of_mem ha
  have hsub : C.erase a⊆C := erase_subset _ _
  have hchoose : C.card.choose 2=(C.card-1).choose 2+(C.card-1) := by
    have h := Nat.choose_succ_succ (C.card-1) 1
    have hs : C.card-1+1=C.card := by omega
    simpa only [Nat.succ_eq_add_one,hs,Nat.choose_one_right,Nat.add_comm] using h
  obtain ⟨q,hq⟩ := card_pos.mp (show 0<(C.erase a).card by omega)
  have hecard2 : ((C.erase a).erase q).card=C.card-2 := by
    rw [card_erase_of_mem hq,hecard]
    omega
  have hsub2 : (C.erase a).erase q⊆C := (erase_subset _ _).trans hsub
  have hn : a∉(C.erase a).erase q := fun h => (notMem_erase a C) (mem_of_mem_erase h)
  have hcapacity : k-(C.card-1).choose 2≤(starPairs C a ((C.erase a).erase q)).card := by
    rw [starPairs_card C ha hsub2 hn,hecard2]
    omega
  obtain ⟨D,hD,hDc⟩ := exists_subset_card_eq hcapacity
  let owner := cliqueOwner C a q ha hq D hD
  let seed := fun i : cliquePairs C (C.erase a) => i.1
  let x := pivotColumns seed D owner
  let e₀ := pairOfNe C a q (Ne.symm (mem_erase.mp hq).1) ha (mem_of_mem_erase hq)
  have hnotseed : ∀ i : cliquePairs C (C.erase a),e₀≠ seed i := by
    intro i hi
    obtain ⟨hu,hv⟩ := mem_cliquePairs.mp i.2
    have hends := pairOfNe_endpoints C a q (Ne.symm (mem_erase.mp hq).1) ha (mem_of_mem_erase hq)
    rcases hends with hh | hh
    · exact (mem_erase.mp hu).1 ((congrArg (fun e : PairIn C => e.1.1.1) hi).symm.trans hh.1)
    · exact (mem_erase.mp hv).1 ((congrArg (fun e : PairIn C => e.1.1.2) hi).symm.trans hh.2)
  have heD : e₀∉D := by
    intro h
    have hs := mem_starPairs.mp (hD h)
    have hends := (pairOfNe_char C a q (Ne.symm (mem_erase.mp hq).1) ha (mem_of_mem_erase hq) e₀).mp rfl
    rcases hs with ⟨hu,hv⟩ | ⟨hv,hu⟩ <;> rcases hends with hh | hh
    · exact (mem_erase.mp hv).1 hh.2
    · exact (mem_erase.mp hq).1 (hh.2.symm.trans hu)
    · exact (mem_erase.mp hq).1 (hh.2.symm.trans hv)
    · exact (mem_erase.mp hu).1 hh.2
  apply pureDecomposition_of_vectors x (cliquePivot_realizable C hC a q ha hq D hD)
    (blockClass_linearIndependent_of_reference C e₀ x
      (pivotColumns_linearIndependent seed Subtype.val_injective D owner
        (cliqueSeed_not_extra C a q D hD))
      (pivotColumns_zero_at seed D owner e₀ heD hnotseed)) _ _
  · rw [← map_sum,cliquePivot_sum C a q ha hq D hD]
    exact clique_without_vertex_class C a
  · simp only [Fintype.card_sum,Fintype.card_coe,cliquePairs_card C (C.erase a) hsub,
      hecard,hDc]
    omega

/-- The negative half of Lemma 7.7, with every count through the entire
block dimension and actual Boolean realizations. -/
theorem negative_star_interpolation (C : Finset H) (hC : 3≤ C.card)
    (a : H) (ha : a∈C) {k : ℕ} (hk : 1≤ k) (hkC : k≤ C.card.choose 2-1) :
    Nonempty (PureDecomposition C (-blockClass C (starVector C a)) k) := by
  by_cases h : k≤(C.card-1).choose 2
  · exact negative_star_small_interpolation C hC a ha hk h
  · exact negative_star_large_interpolation C hC a ha (by omega) hkC

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart181

section BundlePart182
/- Source: Papers/GraphicalZonotopes/TwoAnchorPureBlocks.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

theorem starVector_eq_zero_of_notMem (C : Finset H) {a : H} (ha : a∉C) :
    starVector C a=0 := by
  funext e
  have hu : a≠ e.1.1.1 := fun h => ha (h.symm ▸ e.2.1)
  have hv : a≠ e.1.1.2 := fun h => ha (h.symm ▸ e.2.2)
  simp only [starVector_eq,hu,hv,false_or,ite_false,Pi.zero_apply]

def PureDecomposition.toWeightedBlock {C : Finset H} {v : ResponseQuotient H} {r : ℕ}
    (P : PureDecomposition C v r) (M : ℤ) (hM : 1≤ M) : WeightedPureBlock C M v r := by
  classical
  choose x hx using P.block_supported
  exact {
    column := x
    realizable := fun j => ⟨P.functions j,P.monotone_boolean j,P.essential j,P.ignored j,hx j⟩
    weight := fun _ => 1
    positive := fun _ => by norm_num
    bounded := fun _ => hM
    independent := by simpa only [← hx] using P.independent
    weighted_sum := by simpa only [Int.cast_one,one_smul,← hx] using P.sum_eq
  }

def twoAnchorTarget (C : Finset H) (a b : H) : ResponseQuotient H :=
  -((-1 : ℝ)^(C.card-3) • blockClass C (starVector C a+starVector C b))

theorem twoAnchorTarget_symm (C : Finset H) (a b : H) :
    twoAnchorTarget C a b=twoAnchorTarget C b a := by rw [twoAnchorTarget,twoAnchorTarget,add_comm]

theorem one_anchor_pure_block (C : Finset H) (hC : 3≤ C.card)
    {a b : H} (ha : a∈C) (hb : b∉C) {k : ℕ} (hk : 1≤ k)
    (hkC : k≤ C.card.choose 2-1) :
    Nonempty (WeightedPureBlock C 2 (twoAnchorTarget C a b) k) := by
  have hb0 := starVector_eq_zero_of_notMem C hb
  rcases neg_one_pow_eq_or ℝ (C.card-3) with h | h
  · obtain ⟨P⟩ := negative_star_interpolation C hC a ha hk hkC
    refine ⟨?_⟩
    have hp := P.toWeightedBlock 2 (by norm_num)
    simpa only [twoAnchorTarget,hb0,add_zero,h,one_smul] using hp
  · obtain ⟨P⟩ := positive_star_interpolation C hC a ha hk hkC
    refine ⟨?_⟩
    have hp := P.toWeightedBlock 2 (by norm_num)
    simpa only [twoAnchorTarget,hb0,add_zero,h,neg_one_smul,neg_neg] using hp

theorem pair_contains_two_iff (C : Finset H) {a b : H} (hab : a< b)
    (ha : a∈C) (hb : b∈C) (e : PairIn C) :
    ((a=e.1.1.1 ∨ a=e.1.1.2) ∧ (b=e.1.1.1 ∨ b=e.1.1.2)) ↔
      e=orderedPair C a b hab ha hb := by
  constructor
  · rintro ⟨(hae | hae),(hbe | hbe)⟩
    · exact False.elim ((ne_of_lt hab) (hae.trans hbe.symm))
    · apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hae.symm hbe.symm
    · have hbad : b< a := by simpa only [← hae,← hbe] using e.1.2.1
      exact False.elim ((not_lt_of_ge hab.le) hbad)
    · exact False.elim ((ne_of_lt hab) (hae.trans hbe.symm))
  · rintro rfl
    exact ⟨Or.inl rfl,Or.inr rfl⟩

def twoAnchorPairWeight (C : Finset H) (a b : H) (e : PairIn C) : ℤ :=
  2-((if a=e.1.1.1 ∨ a=e.1.1.2 then 1 else 0)+
    (if b=e.1.1.1 ∨ b=e.1.1.2 then 1 else 0))

theorem twoAnchorPairWeight_zero (C : Finset H) {a b : H} (hab : a< b)
    (ha : a∈C) (hb : b∈C) :
    twoAnchorPairWeight C a b (orderedPair C a b hab ha hb)=0 := by
  simp [twoAnchorPairWeight,orderedPair]

theorem twoAnchorPairWeight_positive (C : Finset H) {a b : H} (hab : a< b)
    (ha : a∈C) (hb : b∈C) (e : PairIn C)
    (he : e≠ orderedPair C a b hab ha hb) : 0< twoAnchorPairWeight C a b e := by
  have hn := mt (pair_contains_two_iff C hab ha hb e).mp he
  by_cases hA : a=e.1.1.1 ∨ a=e.1.1.2 <;>
    by_cases hB : b=e.1.1.1 ∨ b=e.1.1.2 <;> simp_all [twoAnchorPairWeight]

theorem twoAnchorPairWeight_bounded (C : Finset H) (a b : H) (e : PairIn C) :
    twoAnchorPairWeight C a b e≤2 := by
  unfold twoAnchorPairWeight
  split <;> split <;> norm_num

theorem twoAnchorPairWeight_vector (C : Finset H) (a b : H) :
    (fun e => (twoAnchorPairWeight C a b e : ℝ))=
      (fun _ : PairIn C => (2 : ℝ))-(starVector C a+starVector C b) := by
  funext e
  simp only [twoAnchorPairWeight,Int.cast_sub,Int.cast_ofNat,Int.cast_add,
    Pi.sub_apply,Pi.add_apply,starVector_eq]
  by_cases hA : a=e.1.1.1 ∨ a=e.1.1.2 <;>
    by_cases hB : b=e.1.1.1 ∨ b=e.1.1.2 <;> simp [hA,hB]

/-- Every double-anchor block other than the single connector is filled to
its full quotient dimension with positive integral weights one or two. -/
theorem two_anchor_full_pure_block (C : Finset H) (hC : 3≤ C.card)
    {a b : H} (hab : a< b) (ha : a∈C) (hb : b∈C) :
    Nonempty (WeightedPureBlock C 2 (twoAnchorTarget C a b) (C.card.choose 2-1)) := by
  let e₀ := orderedPair C a b hab ha hb
  let ε : ℝ := (-1)^(C.card-3)
  let P := signed_pair_basis C hC e₀ ε (neg_one_pow_eq_or ℝ (C.card-3))
    (twoAnchorPairWeight C a b) (twoAnchorPairWeight_zero C hab ha hb)
    (fun e he => twoAnchorPairWeight_positive C hab ha hb e he) 2
    (fun e _ => twoAnchorPairWeight_bounded C a b e)
  have hz : blockClass C (fun _ : PairIn C => (2 : ℝ))=0 :=
    (blockClass_eq_zero_iff C e₀ _).mpr ⟨2,fun _ => rfl⟩
  have hv : blockClass C (ε • (fun e => (twoAnchorPairWeight C a b e : ℝ)))=
      twoAnchorTarget C a b := by
    rw [twoAnchorPairWeight_vector,map_smul,map_sub,hz,zero_sub,smul_neg]
    rfl
  exact ⟨hv ▸ P⟩

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart182

section BundlePart183
/- Source: Papers/GraphicalZonotopes/TwoAnchorConnector.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {H : Type*} [Fintype H] [LinearOrder H]

structure OrderedTriple (H : Type*) [LinearOrder H] where
  a : H
  b : H
  c : H
  ab : a< b
  bc : b< c

namespace OrderedTriple
variable (T : OrderedTriple H)

def clique : Finset H := {T.a,T.b,T.c}

theorem ac : T.a< T.c := T.ab.trans T.bc

@[simp] theorem card_clique : T.clique.card=3 := by
  simp [clique,T.ab.ne,T.ac.ne,T.bc.ne]

@[simp] theorem a_mem : T.a∈T.clique := by simp [clique]
@[simp] theorem b_mem : T.b∈T.clique := by simp [clique]
@[simp] theorem c_mem : T.c∈T.clique := by simp [clique]

def abPair : PairIn T.clique := orderedPair T.clique T.a T.b T.ab T.a_mem T.b_mem
def acPair : PairIn T.clique := orderedPair T.clique T.a T.c T.ac T.a_mem T.c_mem
def bcPair : PairIn T.clique := orderedPair T.clique T.b T.c T.bc T.b_mem T.c_mem

@[simp] theorem ac_ne_ab : T.acPair≠ T.abPair := by
  intro h
  exact T.bc.ne (congrArg (fun e : PairIn T.clique => e.1.1.2) h).symm

@[simp] theorem bc_ne_ab : T.bcPair≠ T.abPair := by
  intro h
  exact T.ab.ne (congrArg (fun e : PairIn T.clique => e.1.1.1) h).symm

/-- On a triple, the sum of the two distinguished stars is the distinguished
pair plus the constant pair vector. -/
theorem two_stars_vector :
    starVector T.clique T.a+starVector T.clique T.b=
      pairIndicator {T.abPair}+(fun _ : PairIn T.clique => (1 : ℝ)) := by
  funext e
  have hu : e.1.1.1=T.a ∨ e.1.1.1=T.b ∨ e.1.1.1=T.c := by
    simpa only [clique,mem_insert,mem_singleton] using e.2.1
  have hv : e.1.1.2=T.a ∨ e.1.1.2=T.b ∨ e.1.1.2=T.c := by
    simpa only [clique,mem_insert,mem_singleton] using e.2.2
  have hne : e.1.1.1≠ e.1.1.2 := ne_of_lt e.1.2.1
  have he : e=T.abPair ↔
      (T.a=e.1.1.1 ∨ T.a=e.1.1.2) ∧ (T.b=e.1.1.1 ∨ T.b=e.1.1.2) :=
    (pair_contains_two_iff T.clique T.ab T.a_mem T.b_mem e).symm
  simp only [Pi.add_apply,starVector_eq,pairIndicator,mem_singleton,he]
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;>
    simp [hu,hv,T.ab.ne,T.ac.ne,T.bc.ne,Ne.symm T.ab.ne,Ne.symm T.ac.ne,Ne.symm T.bc.ne] at hne ⊢

theorem connector_response :
    blockClass T.clique (-pairIndicator {T.abPair})=twoAnchorTarget T.clique T.a T.b := by
  have hz : blockClass T.clique (fun _ : PairIn T.clique => (1 : ℝ))=0 :=
    (blockClass_eq_zero_iff T.clique T.abPair _).mpr ⟨1,fun _ => rfl⟩
  rw [twoAnchorTarget,T.two_stars_vector,map_add,hz,add_zero,map_neg,T.card_clique]
  norm_num

/-- The unique connector column is a genuine negative pure pair module. -/
def pureBlock : WeightedPureBlock T.clique 2 (twoAnchorTarget T.clique T.a T.b) 1 := by
  have hne : blockClass T.clique (-pairIndicator {T.abPair})≠0 := by
    intro hz
    obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff T.clique T.abPair _).mp hz
    have hab := hc T.abPair
    have hac := hc T.acPair
    simp [pairIndicator] at hab hac
    linarith
  exact {
    column := fun _ => -pairIndicator {T.abPair}
    realizable := fun _ => pureRealizable_negative_pair T.clique (by rw [T.card_clique]) T.abPair
    weight := fun _ => 1
    positive := fun _ => by norm_num
    bounded := fun _ => by norm_num
    independent := (linearIndependent_unique_iff).mpr hne
    weighted_sum := by simpa using T.connector_response
  }

def firstRow : HubResponseRow H := pairRow T.clique T.acPair
def secondRow : HubResponseRow H := pairRow T.clique T.bcPair

@[simp] theorem firstRow_clique : rowClique T.firstRow=T.clique := rowClique_pairRow _ _
@[simp] theorem secondRow_clique : rowClique T.secondRow=T.clique := rowClique_pairRow _ _

theorem row_index_eq : rowCliqueIndex T.firstRow=rowCliqueIndex T.secondRow := by
  apply Subtype.ext
  exact T.firstRow_clique.trans T.secondRow_clique.symm

@[simp] theorem threshold_a_first : thresholdSignedStar T.a T.firstRow=1 := by
  rw [thresholdSignedStar,T.firstRow_clique,T.card_clique]
  norm_num [firstRow,acPair,pairRow,orderedPair]

@[simp] theorem threshold_a_second : thresholdSignedStar T.a T.secondRow=0 := by
  simp [thresholdSignedStar,T.secondRow_clique,T.card_clique,secondRow,bcPair,pairRow,orderedPair,
    T.ab.ne,T.ac.ne]

@[simp] theorem threshold_b_first : thresholdSignedStar T.b T.firstRow=0 := by
  simp [thresholdSignedStar,T.firstRow_clique,T.card_clique,firstRow,acPair,pairRow,orderedPair,
    Ne.symm T.ab.ne,T.bc.ne]

@[simp] theorem threshold_b_second : thresholdSignedStar T.b T.secondRow=1 := by
  rw [thresholdSignedStar,T.secondRow_clique,T.card_clique]
  norm_num [secondRow,bcPair,pairRow,orderedPair]

@[simp] theorem pureBlock_first (j : Fin 1) :
    blockCoordinates T.clique (T.pureBlock.column j) T.firstRow=0 := by
  change blockCoordinates T.clique (-pairIndicator {T.abPair}) (pairRow T.clique T.acPair)=0
  rw [blockCoordinates_pairRow]
  simp [pairIndicator]

@[simp] theorem pureBlock_second (j : Fin 1) :
    blockCoordinates T.clique (T.pureBlock.column j) T.secondRow=0 := by
  change blockCoordinates T.clique (-pairIndicator {T.abPair}) (pairRow T.clique T.bcPair)=0
  rw [blockCoordinates_pairRow]
  simp [pairIndicator]

end OrderedTriple
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart183

section BundlePart184
/- Source: Papers/GraphicalZonotopes/TwoAnchorBlockData.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators
variable {H : Type*} [Fintype H] [LinearOrder H]

namespace OrderedTriple
variable (T : OrderedTriple H)

def block : BookBlock H := ⟨T.clique,mem_largeBlocks.mpr ⟨subset_univ _,by rw [T.card_clique]⟩⟩

structure OmittedBlock (C : BookBlock H) (r : ℕ)
    extends WeightedPureBlock C.1 2 (twoAnchorTarget C.1 T.a T.b) r where
  first_zero : ∀ j,blockCoordinates C.1 (column j) T.firstRow=0
  second_zero : ∀ j,blockCoordinates C.1 (column j) T.secondRow=0

def ordinaryOmittedBlock (C : BookBlock H) (hne : C.1≠ T.clique) {r : ℕ}
    (P : WeightedPureBlock C.1 2 (twoAnchorTarget C.1 T.a T.b) r) : T.OmittedBlock C r := by
  refine { P with first_zero := ?_,second_zero := ?_ }
  · intro j
    have hr : rowClique T.firstRow≠ C.1 := by rw [T.firstRow_clique]; exact Ne.symm hne
    change (if h : rowClique T.firstRow=C.1 then P.column j (pairAtRow C.1 T.firstRow h) else 0)=0
    exact dite_eq_right hr
  · intro j
    have hr : rowClique T.secondRow≠ C.1 := by rw [T.secondRow_clique]; exact Ne.symm hne
    change (if h : rowClique T.secondRow=C.1 then P.column j (pairAtRow C.1 T.secondRow h) else 0)=0
    exact dite_eq_right hr

def connectorOmittedBlock : T.OmittedBlock T.block 1 where
  toWeightedPureBlock := T.pureBlock
  first_zero := T.pureBlock_first
  second_zero := T.pureBlock_second

def lowerRank (C : BookBlock H) : ℕ :=
  if C.1=T.clique then 1 else
  if T.a∈C.1 ∧ T.b∈C.1 then C.1.card.choose 2-1 else
  if T.a∈C.1 ∨ T.b∈C.1 then 1 else 0

def upperRank (C : BookBlock H) : ℕ :=
  if C.1=T.clique then 1 else
  if T.a∈C.1 ∨ T.b∈C.1 then C.1.card.choose 2-1 else 0

theorem lowerRank_le_upperRank (C : BookBlock H) : T.lowerRank C≤ T.upperRank C := by
  have hsize := (mem_largeBlocks.mp C.2).2
  have hc : 1≤ C.1.card.choose 2-1 := by
    have h := Nat.choose_le_choose 2 hsize
    norm_num [Nat.choose] at h
    omega
  unfold lowerRank upperRank
  by_cases hC : C.1=T.clique <;> by_cases ha : T.a∈C.1 <;> by_cases hb : T.b∈C.1 <;>
    simp [hC,ha,hb,hc]

/-- Each local branch count in the exact interval is realized, with both
connector test coordinates zero for every pure column. -/
theorem omittedBlock_exists (C : BookBlock H) {r : ℕ}
    (hrlo : T.lowerRank C≤ r) (hrhi : r≤ T.upperRank C) :
    Nonempty (T.OmittedBlock C r) := by
  classical
  by_cases hC : C.1=T.clique
  · have hCe : C=T.block := Subtype.ext hC
    subst C
    have hr : r=1 := by
      simp only [lowerRank,upperRank,block,ite_true] at hrlo hrhi
      omega
    subst r
    exact ⟨T.connectorOmittedBlock⟩
  · apply Nonempty.map (T.ordinaryOmittedBlock C hC)
    have hsize := (mem_largeBlocks.mp C.2).2
    by_cases ha : T.a∈C.1
    · by_cases hb : T.b∈C.1
      · have hr : r=C.1.card.choose 2-1 := by
          simp only [lowerRank,upperRank,ite_eq_right hC,ha,hb,true_and,true_or,ite_true] at hrlo hrhi
          omega
        subst r
        exact two_anchor_full_pure_block C.1 hsize T.ab ha hb
      · have hlo : 1≤ r := by simpa only [lowerRank,ite_eq_right hC,ha,hb,
          true_and,false_or,true_or,ite_false,ite_true] using hrlo
        have hhi : r≤ C.1.card.choose 2-1 := by
          simpa only [upperRank,ite_eq_right hC,ha,true_or,ite_true] using hrhi
        exact one_anchor_pure_block C.1 hsize ha hb hlo hhi
    · by_cases hb : T.b∈C.1
      · have hlo : 1≤ r := by simpa only [lowerRank,ite_eq_right hC,ha,hb,
          false_and,false_or,ite_false,ite_true] using hrlo
        have hhi : r≤ C.1.card.choose 2-1 := by
          simpa only [upperRank,ite_eq_right hC,hb,or_true,ite_true] using hrhi
        rw [twoAnchorTarget_symm]
        exact one_anchor_pure_block C.1 hsize hb ha hlo hhi
      · have hr : r=0 := by
          simpa only [upperRank,ite_eq_right hC,ha,hb,false_or,ite_false,Nat.le_zero] using hrhi
        subst r
        have hz : twoAnchorTarget C.1 T.a T.b=0 := by
          simp only [twoAnchorTarget,starVector_eq_zero_of_notMem C.1 ha,
            starVector_eq_zero_of_notMem C.1 hb,add_zero,map_zero,smul_zero,neg_zero]
        exact ⟨{
          column := fun j => Fin.elim0 j
          realizable := fun j => Fin.elim0 j
          weight := fun j => Fin.elim0 j
          positive := fun j => Fin.elim0 j
          bounded := fun j => Fin.elim0 j
          independent := linearIndependent_empty_type
          weighted_sum := by simpa only [Fin.sum_univ_zero] using hz.symm
        }⟩

end OrderedTriple
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart184

section BundlePart185
/- Source: Papers/GraphicalZonotopes/AnchoredWeightedCircuits.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

def anchoredWeights (w : J → ℤ) : Option J → ℤ
  | none => 1
  | some j => w j

theorem anchored_weighted_relation (F₀ : SetFunction H) (F : J → SetFunction H)
    (w : J → ℤ) (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,(w j : ℝ) • responseClass (F j)=0) :
    (fun j => (anchoredWeights w j : ℝ))∈LinearMap.ker (quotientRelation (anchoredFamily F₀ F)) ∧
      UniqueIntegrableRelation (anchoredFamily F₀ F) (fun j => (anchoredWeights w j : ℝ)) := by
  constructor
  · change quotientRelation (anchoredFamily F₀ F) _=0
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option]
    simpa only [anchoredWeights,Int.cast_one,one_smul,anchoredFamily] using hsum
  · intro t ht
    have ht0 : quotientRelation (anchoredFamily F₀ F) t=0 :=
      (mem_quotientRelation_ker_iff _ _).mpr ht
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option] at ht0
    change t none • responseClass F₀+∑ j,t (some j) • responseClass (F j)=0 at ht0
    have hsub : (∑ j,(t (some j)-t none*(w j : ℝ)) • responseClass (F j))=0 := by
      calc
        _ = (t none • responseClass F₀+∑ j,t (some j) • responseClass (F j))-
            t none • (responseClass F₀+∑ j,(w j : ℝ) • responseClass (F j)) := by
          simp only [sub_smul,sum_sub_distrib,smul_add,smul_sum,mul_smul]
          abel
        _ = 0 := by rw [ht0,hsum,smul_zero,sub_self]
    have hcoeff := (Fintype.linearIndependent_iff.mp hind) _ hsub
    refine ⟨t none,?_⟩
    funext i
    cases i with
    | none => simp [anchoredWeights]
    | some j =>
      simpa only [Pi.smul_apply,smul_eq_mul,anchoredWeights] using sub_eq_zero.mp (hcoeff j)

theorem lattice_book_of_anchored_weighted_circuit {s k : ℕ} (hs : 0< s)
    (F₀ : SetFunction (Fin s)) (F : J → SetFunction (Fin s))
    (hF₀ : IsMonotoneBoolean F₀) (hF : ∀ j,IsMonotoneBoolean (F j))
    (hess₀ : ∀ a,Essential F₀ a) (hess : ∀ j,∃ a,Essential (F j) a)
    (w : J → ℤ) (hw : ∀ j,0< w j) (M : ℤ) (hM₀ : 1≤ M) (hM : ∀ j,w j≤ M)
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,(w j : ℝ) • responseClass (F j)=0)
    (hcard : Fintype.card J+1=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=((M*k : ℤ) : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  obtain ⟨hrel,huniq⟩ := anchored_weighted_relation F₀ F w hind hsum
  let G := anchoredFamily F₀ F
  have hG : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | none => exact hF₀
    | some j => exact hF j
  have hbranch : ∀ j,∃ a,Essential (G j) a := by
    intro j
    cases j with
    | none => exact ⟨⟨0,hs⟩,hess₀ ⟨0,hs⟩⟩
    | some j => exact hess j
  have hw' : ∀ j,0< anchoredWeights w j := by
    intro j
    cases j with
    | none => norm_num [anchoredWeights]
    | some j => exact hw j
  have hb : ∀ j,anchoredWeights w j≤ M := by
    intro j
    cases j with
    | none => exact hM₀
    | some j => exact hM j
  have hcard' : Fintype.card (Option J)=k := by simpa only [Fintype.card_option] using hcard
  apply lattice_book_of_finite_weighted_circuit hs G hG none hess₀ hbranch
    (anchoredWeights w) hw' hrel huniq hcard' (M*k)
  calc
    _ ≤ ∑ _ : Option J,M := sum_le_sum (fun j _ => hb j)
    _ = _ := by simp [hcard',mul_comm]

/-- Two genuine response coordinates detect the relative scales of two
threshold modules. The statement concerns their full integrability quotient;
no private row equations are omitted. -/
theorem two_threshold_coefficients_equal (a b : H)
    (r t : HubResponseRow H) (hrt : rowCliqueIndex r=rowCliqueIndex t)
    (har : thresholdSignedStar a r=1) (hat : thresholdSignedStar a t=0)
    (hbr : thresholdSignedStar b r=0) (hbt : thresholdSignedStar b t=1)
    (C : J → Finset H) (x : (j : J) → PairIn (C j) → ℝ)
    (hxt : ∀ j,blockCoordinates (C j) (x j) r=blockCoordinates (C j) (x j) t)
    (α β : ℝ) (w : J → ℝ)
    (hz : α • responseClass (thresholdStar a)+β • responseClass (thresholdStar b)+
      ∑ j,w j • blockClass (C j) (x j)=0) : α=β := by
  have hclass : coefficientClass (α • thresholdSignedStar a+β • thresholdSignedStar b+
      ∑ j,w j • blockCoordinates (C j) (x j))=0 := by
    simpa only [map_add,map_smul,map_sum,← thresholdStar_response_class,blockClass,
      LinearMap.comp_apply] using hz
  have he := (coefficientClass_eq_zero_iff _).mp hclass r t hrt
  simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,har,hat,hbr,hbt,
    mul_one,mul_zero,add_zero,zero_add] at he
  have hsum : (∑ j,w j*blockCoordinates (C j) (x j) r)=
      ∑ j,w j*blockCoordinates (C j) (x j) t := sum_congr rfl (fun j _ => by rw [hxt j])
  rw [hsum] at he
  exact add_right_cancel he

theorem second_threshold_and_pure_independent (a b : H)
    (C : J → Finset H) (x : (j : J) → PairIn (C j) → ℝ)
    (F : J → SetFunction H) (hF : ∀ j,responseClass (F j)=blockClass (C j) (x j))
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (r t : HubResponseRow H) (hrt : rowCliqueIndex r=rowCliqueIndex t)
    (har : thresholdSignedStar a r=1) (hat : thresholdSignedStar a t=0)
    (hbr : thresholdSignedStar b r=0) (hbt : thresholdSignedStar b t=1)
    (hxt : ∀ j,blockCoordinates (C j) (x j) r=blockCoordinates (C j) (x j) t) :
    LinearIndependent ℝ (fun j => responseClass (anchoredFamily (thresholdStar b) F j)) := by
  rw [Fintype.linearIndependent_iff]
  intro w hw j
  rw [Fintype.sum_option] at hw
  change w none • responseClass (thresholdStar b)+∑ i,w (some i) • responseClass (F i)=0 at hw
  have hz : (0 : ℝ) • responseClass (thresholdStar a)+
      w none • responseClass (thresholdStar b)+
      ∑ i,w (some i) • blockClass (C i) (x i)=0 := by
    simpa only [zero_smul,zero_add,← hF] using hw
  have hnone : w none=0 := (two_threshold_coefficients_equal a b r t hrt har hat hbr hbt
    C x hxt 0 (w none) (fun i => w (some i)) hz).symm
  cases j with
  | none => exact hnone
  | some j =>
    rw [hnone,zero_smul,zero_add] at hw
    exact (Fintype.linearIndependent_iff.mp hind) _ hw j

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart185

section BundlePart186
/- Source: Papers/GraphicalZonotopes/TwoAnchorBookCircuits.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- The complete two-threshold construction, uniformly in the ambient hub
set and every admissible intermediate sum of local block ranks. -/
theorem two_threshold_book_interval {s k : ℕ} (hs : 3≤ s)
    (T : OrderedTriple (Fin s))
    (hklo : (∑ C : BookBlock (Fin s),T.lowerRank C)+2≤ k)
    (hkhi : k≤(∑ C : BookBlock (Fin s),T.upperRank C)+2) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook s k) := by
  classical
  obtain ⟨r,hr,hrsum⟩ := interval_sum_composition T.lowerRank T.upperRank T.lowerRank_le_upperRank
    (n:=k-2) (by omega) (by omega)
  let P := fun C => Classical.choice (T.omittedBlock_exists C (hr C).1 (hr C).2)
  have hF : ∀ C j,∃ F : SetFunction (Fin s),IsMonotoneBoolean F ∧
      (∀ a,a∈C.1 → Essential F a) ∧
      (∀ a,a∉C.1 → ∀ X,F (insert a X)=F X) ∧
      responseClass F=blockClass C.1 ((P C).column j) := fun C j => (P C).realizable j
  choose F hFb hFe hFi hFc using hF
  let J := Σ C : BookBlock (Fin s),Fin (r C)
  let G : J → SetFunction (Fin s) := fun j => F j.1 j.2
  let w : J → ℤ := fun j => (P j.1).weight j.2
  have hG : ∀ j,IsMonotoneBoolean (G j) := fun j => hFb j.1 j.2
  have hGc : ∀ j : J,responseClass (G j)=blockClass j.1.1 ((P j.1).column j.2) :=
    fun j => hFc j.1 j.2
  have hess : ∀ j,∃ a,Essential (G j) a := by
    intro j
    obtain ⟨a,ha⟩ := card_pos.mp (show 0< j.1.1.card by
      have h := (mem_largeBlocks.mp j.1.2).2
      omega)
    exact ⟨a,hFe j.1 j.2 a ha⟩
  have hpair : ∀ C : BookBlock (Fin s),∃ p : PairIn C.1,True := by
    intro C
    obtain ⟨p,hp⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨p,trivial⟩
  have hind : LinearIndependent ℝ (fun j => responseClass (G j)) := by
    simp_rw [hGc]
    exact block_families_independent Subtype.val Subtype.val_injective
      (fun C => (hpair C).choose) (fun C => (P C).column) (fun C => (P C).independent)
  have hRest : LinearIndependent ℝ
      (fun j => responseClass (anchoredFamily (thresholdStar T.b) G j)) :=
    second_threshold_and_pure_independent T.a T.b (fun j : J => j.1.1)
      (fun j => (P j.1).column j.2) G hGc hind T.firstRow T.secondRow T.row_index_eq
      T.threshold_a_first T.threshold_a_second T.threshold_b_first T.threshold_b_second
      (fun j => ((P j.1).first_zero j.2).trans ((P j.1).second_zero j.2).symm)
  have hanchors : responseClass (thresholdStar T.a)+responseClass (thresholdStar T.b)=
      ∑ C : BookBlock (Fin s),(-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (starVector C.1 T.a+starVector C.1 T.b) := by
    rw [threshold_response_largeBlocks,threshold_response_largeBlocks,← sum_add_distrib]
    apply sum_congr rfl
    intro C hC
    simp only [map_add,smul_add]
  have hpures : (∑ j : J,(w j : ℝ) • responseClass (G j))=
      ∑ C : BookBlock (Fin s),twoAnchorTarget C.1 T.a T.b := by
    rw [Fintype.sum_sigma]
    apply sum_congr rfl
    intro C hC
    simpa only [w,hGc] using (P C).weighted_sum
  have hsum : responseClass (thresholdStar T.a)+
      ∑ j : Option J,(anchoredWeights w j : ℝ) •
        responseClass (anchoredFamily (thresholdStar T.b) G j)=0 := by
    rw [Fintype.sum_option]
    simp only [anchoredWeights,Int.cast_one,anchoredFamily,one_smul]
    rw [← add_assoc,hpures,hanchors]
    simp only [twoAnchorTarget,sum_neg_distrib,add_neg_cancel]
  have hRestB : ∀ j,IsMonotoneBoolean (anchoredFamily (thresholdStar T.b) G j) := by
    intro j
    cases j with
    | none => exact thresholdStar_boolean T.b
    | some j => exact hG j
  have hRestE : ∀ j,∃ a,Essential (anchoredFamily (thresholdStar T.b) G j) a := by
    intro j
    cases j with
    | none => exact ⟨T.b,thresholdStar_essential (by simpa using hs) T.b T.b⟩
    | some j => exact hess j
  have hw : ∀ j,0< anchoredWeights w j := by
    intro j
    cases j with
    | none => norm_num [anchoredWeights]
    | some j => exact (P j.1).positive j.2
  have hb : ∀ j,anchoredWeights w j≤2 := by
    intro j
    cases j with
    | none => norm_num [anchoredWeights]
    | some j => exact (P j.1).bounded j.2
  have hcard : Fintype.card (Option J)+1=k := by
    rw [Fintype.card_option,Fintype.card_sigma]
    simp only [Fintype.card_fin,hrsum]
    omega
  obtain ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,hR⟩ :=
    lattice_book_of_anchored_weighted_circuit (by omega) (thresholdStar T.a)
      (anchoredFamily (thresholdStar T.b) G) (thresholdStar_boolean T.a) hRestB
      (thresholdStar_essential (by simpa using hs) T.a) hRestE
      (anchoredWeights w) hw 2 (by norm_num) hb hRest hsum hcard
  exact ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,by simpa only [Int.cast_mul,
    Int.cast_ofNat,Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat] using hR⟩

def initialTriple {s : ℕ} (hs : 3≤ s) : OrderedTriple (Fin s) where
  a := ⟨0,by omega⟩
  b := ⟨1,by omega⟩
  c := ⟨2,by omega⟩
  ab := by change (0 : ℕ)<1; omega
  bc := by change (1 : ℕ)<2; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem two_threshold_four_counts :
    (∑ C : BookBlock (Fin 4),(initialTriple (by decide : 3≤4)).lowerRank C)=10 ∧
    (∑ C : BookBlock (Fin 4),(initialTriple (by decide : 3≤4)).upperRank C)=12 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem two_threshold_five_counts :
    (∑ C : BookBlock (Fin 5),(initialTriple (by decide : 3≤5)).lowerRank C)=37 ∧
    (∑ C : BookBlock (Fin 5),(initialTriple (by decide : 3≤5)).upperRank C)=51 := by
  decide

/-- The four-hub overlap bridge of Lemma 7.9, including both endpoint sizes. -/
theorem two_threshold_four_bridge {k : ℕ} (hklo : 12≤ k) (hkhi : k≤14) :
    ∃ f : SetFunction (Fin 4⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 4 k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin 4⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook 4 k) := by
  apply two_threshold_book_interval (by decide) (initialTriple (by decide))
  · rw [two_threshold_four_counts.1]
    exact hklo
  · rw [two_threshold_four_counts.2]
    exact hkhi

/-- The five-hub overlap bridge of Lemma 7.9, with every count 39 through 53. -/
theorem two_threshold_five_bridge {k : ℕ} (hklo : 39≤ k) (hkhi : k≤53) :
    ∃ f : SetFunction (Fin 5⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 5 k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin 5⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook 5 k) := by
  apply two_threshold_book_interval (by decide) (initialTriple (by decide))
  · rw [two_threshold_five_counts.1]
    exact hklo
  · rw [two_threshold_five_counts.2]
    exact hkhi

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart186

section BundlePart187
/- Source: Papers/GraphicalZonotopes/ThresholdBookCircuits.lean -/








@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H : Type*} [Fintype H] [LinearOrder H]

abbrev AnchorBlock (a : H) := ↥(anchorBlocks (univ : Finset H) a)

def anchorSignedClass (a : H) (C : AnchorBlock a) : ResponseQuotient H :=
  (-1 : ℝ)^(C.1.card-3) • blockClass C.1 (starVector C.1 a)

/-- The threshold response is the sum of its signed stars over every clique
block containing the anchor, with all other actual rows zero. -/
theorem threshold_response_block_sum (a : H) :
    responseClass (thresholdStar a)=∑ C : AnchorBlock a,anchorSignedClass a C := by
  have hcoord : thresholdSignedStar a=
      ∑ C : AnchorBlock a,(-1 : ℝ)^(C.1.card-3) •
        blockCoordinates C.1 (starVector C.1 a) := by
    funext r
    rw [Finset.sum_apply]
    by_cases hr : rowClique r∈anchorBlocks (univ : Finset H) a
    · let C₀ : AnchorBlock a := ⟨rowClique r,hr⟩
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
        have hsize := (mem_anchorBlocks.mp hr).2.2
        change (if 3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2) then
          (-1 : ℝ)^((rowClique r).card-3) else 0)=
          (-1 : ℝ)^((rowClique r).card-3)*(if a=r.1.1.1 ∨ a=r.1.1.2 then 1 else 0)
        by_cases h : a=r.1.1.1 ∨ a=r.1.1.2 <;> simp [hsize,h]
      · intro C hC hne
        have hrow : rowClique r≠ C.1 := fun h => hne (Subtype.ext h.symm)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
      · simp
    · have hterms : ∀ C : AnchorBlock a,
          ((-1 : ℝ)^(C.1.card-3) • blockCoordinates C.1 (starVector C.1 a)) r=0 := by
        intro C
        have hrow : rowClique r≠ C.1 := fun h => hr (h.symm ▸ C.2)
        change (-1 : ℝ)^(C.1.card-3)*
          (if h : rowClique r=C.1 then starVector C.1 a (pairAtRow C.1 r h) else 0)=0
        rw [dite_eq_right hrow,mul_zero]
      rw [sum_eq_zero (fun C _ => hterms C)]
      have hn : ¬(3≤(rowClique r).card ∧ (a=r.1.1.1 ∨ a=r.1.1.2)) := by
        rintro ⟨hc,ha⟩
        apply hr
        apply mem_anchorBlocks.mpr
        refine ⟨subset_univ _,?_,hc⟩
        rcases ha with h | h <;> simp [rowClique,h]
      exact ite_eq_right hn
  rw [thresholdStar_response_class,hcoord,map_sum]
  apply sum_congr rfl
  intro C hC
  rw [map_smul]
  rfl

theorem anchor_cancellation_decomposition (a : H) (C : AnchorBlock a)
    {k : ℕ} (hk : 1≤ k) (hkC : k≤ C.1.card.choose 2-1) :
    Nonempty (PureDecomposition C.1 (-anchorSignedClass a C) k) := by
  have hsize := (mem_anchorBlocks.mp C.2).2.2
  have ha := (mem_anchorBlocks.mp C.2).2.1
  rcases neg_one_pow_eq_or ℝ (C.1.card-3) with h | h
  · simpa only [anchorSignedClass,h,one_smul] using
      negative_star_interpolation C.1 hsize a ha hk hkC
  · simpa only [anchorSignedClass,h,neg_one_smul,neg_neg] using
      positive_star_interpolation C.1 hsize a ha hk hkC

/-- The whole single-threshold interval of Lemma 7.8. The upper endpoint is
written as the equivalent difference of complete response capacities. Every
ambient parameter is arbitrary, and the witness has an integral complement
in exactly `k` times the original graphical zonotope. -/
theorem threshold_book_interval {s k : ℕ} (hs : 3≤ s)
    (hklo : 2^(s-1)-s+1≤ k)
    (hkhi : k≤ cliqueCapacity s-cliqueCapacity (s-1)+1) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  let a : Fin s := ⟨0,by omega⟩
  let d : AnchorBlock a → ℕ := fun C => C.1.card.choose 2-1
  have hd : ∀ C,1≤ d C := by
    intro C
    have h := Nat.choose_le_choose 2 (mem_anchorBlocks.mp C.2).2.2
    norm_num [Nat.choose] at h
    change 1≤ C.1.card.choose 2-1
    omega
  have hcard : Fintype.card (AnchorBlock a)=2^(s-1)-s := by
    simpa only [AnchorBlock,Fintype.card_coe,card_univ,Fintype.card_fin] using
      anchorBlocks_card (univ : Finset (Fin s)) a (mem_univ a)
  have hsumd : (∑ C : AnchorBlock a,d C)=cliqueCapacity s-cliqueCapacity (s-1) := by
    change (∑ C : ↥(anchorBlocks (univ : Finset (Fin s)) a),(C.1.card.choose 2-1))=_
    rw [sum_coe_sort (anchorBlocks (univ : Finset (Fin s)) a)
      (fun C : Finset (Fin s) => C.card.choose 2-1)]
    simpa only [card_univ,Fintype.card_fin] using
      anchorBlocks_dimension_sum (univ : Finset (Fin s)) a (mem_univ a)
  have hkpos : 0< k := by omega
  obtain ⟨r,hr,hrsum⟩ := positive_sum_composition d hd (n:=k-1)
    (by rw [hcard]; omega) (by rw [hsumd]; omega)
  have hP : ∀ C : AnchorBlock a,Nonempty
      (PureDecomposition C.1 (-anchorSignedClass a C) (r C)) :=
    fun C => anchor_cancellation_decomposition a C (hr C).1 (hr C).2
  let P := fun C => Classical.choice (hP C)
  let F : (Σ C : AnchorBlock a,Fin (r C)) → SetFunction (Fin s) :=
    fun j => (P j.1).functions j.2
  have hind : LinearIndependent ℝ (fun j => responseClass (F j)) :=
    pureDecompositions_independent Subtype.val Subtype.val_injective
      (fun C => by have h := (mem_anchorBlocks.mp C.2).2.2; omega)
      (fun C => -anchorSignedClass a C) r P
  have hsum : responseClass (thresholdStar a)+∑ j,responseClass (F j)=0 := by
    rw [Fintype.sum_sigma]
    have hp : ∀ C : AnchorBlock a,(∑ j : Fin (r C),responseClass (F ⟨C,j⟩))=
        -anchorSignedClass a C := fun C => (P C).sum_eq
    simp_rw [hp]
    rw [sum_neg_distrib,← threshold_response_block_sum]
    exact add_neg_cancel _
  apply lattice_book_of_anchored_circuit (by omega) (thresholdStar a) F
    (thresholdStar_boolean a) (fun j => (P j.1).monotone_boolean j.2)
    (thresholdStar_essential (by simpa using hs) a)
    (fun j => ⟨a,(P j.1).essential j.2 a (mem_anchorBlocks.mp j.1.2).2.1⟩)
    hind hsum
  simp only [Fintype.card_sigma,Fintype.card_fin,hrsum]
  omega

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart187

section BundlePart188
/- Source: Papers/GraphicalZonotopes/OneBlockCircuit.lean -/










@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace OneBlockCircuit
open Finset
open scoped BigOperators
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The columns used in the small-count construction: the indicator of a
proper set of pairs, followed by the complements of its individual pairs. -/
def column (A : Finset E) : Option ↥A → E → ℝ
  | none,e => if e∈A then 1 else 0
  | some a,e => if e=a.1 then 0 else 1

def response (A : Finset E) (t : Option ↥A → ℝ) (e : E) : ℝ :=
  ∑ j : Option ↥A,t j*column A j e

def tailSum (A : Finset E) (t : Option ↥A → ℝ) : ℝ :=
  ∑ a : ↥A,t (some a)

theorem response_outside (A : Finset E) (t : Option ↥A → ℝ)
    {e : E} (he : e∉A) : response A t e=tailSum A t := by
  rw [response,Fintype.sum_option]
  simp only [column,if_neg he,mul_zero,zero_add]
  apply sum_congr rfl
  intro a ha
  have hea : e≠ a.1:=fun h => he (h.symm ▸ a.2)
  simp only [if_neg hea,mul_one]

theorem response_at (A : Finset E) (t : Option ↥A → ℝ) (a : ↥A) :
    response A t a.1=t none+tailSum A t-t (some a) := by
  rw [response,Fintype.sum_option]
  simp only [column,if_pos a.2,mul_one]
  have hs : (∑ b : ↥A,t (some b)*(if a.1=b.1 then 0 else 1))=
      tailSum A t-t (some a) := by
    calc
      _=∑ b : ↥A,(t (some b)-(if a=b then t (some b) else 0)) := by
        apply sum_congr rfl
        intro b hb
        by_cases hab : a=b
        · subst b
          simp
        · have hv : a.1≠ b.1:=fun h => hab (Subtype.ext h)
          simp only [if_neg hv,if_neg hab,mul_one,sub_zero]
      _=tailSum A t-t (some a) := by
        rw [sum_sub_distrib]
        simp only [sum_ite_eq,mem_univ,ite_true,tailSum]
  rw [hs]
  ring

/-- A missing pair fixes the common block value. Comparing every selected
pair with it then forces every column scale to equal the first one. -/
theorem constant_response_iff (A : Finset E) (hA : ∃ e,e∉A)
    (t : Option ↥A → ℝ) :
    (∃ c : ℝ,∀ e,response A t e=c) ↔ ∃ a : ℝ,∀ j,t j=a := by
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨e₀,he₀⟩:=hA
    have hc₀ : c=tailSum A t:=(hc e₀).symm.trans (response_outside A t he₀)
    refine ⟨t none,?_⟩
    intro j
    cases j with
    | none => rfl
    | some a =>
      have ha:=hc a.1
      rw [response_at,hc₀] at ha
      linarith
  · rintro ⟨a,ha⟩
    refine ⟨tailSum A t,?_⟩
    intro e
    by_cases he : e∈A
    · have h:=response_at A t ⟨e,he⟩
      rw [ha none,ha (some ⟨e,he⟩)] at h
      linarith
    · exact response_outside A t he

theorem unit_response (A : Finset E) (e : E) :
    response A (fun _ => 1) e=(A.card : ℝ) := by
  have hs : tailSum A (fun _ => 1)=(A.card : ℝ) := by
    simp [tailSum]
  by_cases he : e∈A
  · rw [response_at A (fun _ => 1) ⟨e,he⟩,hs]
    ring
  · rw [response_outside A (fun _ => 1) he,hs]

def relationSpace (A : Finset E) : Submodule ℝ (Option ↥A → ℝ) where
  carrier:={t | ∃ c : ℝ,∀ e,response A t e=c}
  zero_mem':=by refine ⟨0,?_⟩; intro e; simp [response]
  add_mem':=by
    rintro t u ⟨c,hc⟩ ⟨d,hd⟩
    refine ⟨c+d,?_⟩
    intro e
    simp only [response,Pi.add_apply,add_mul,sum_add_distrib]
    exact congrArg₂ (·+·) (hc e) (hd e)
  smul_mem':=by
    rintro a t ⟨c,hc⟩
    refine ⟨a*c,?_⟩
    intro e
    simp only [response,Pi.smul_apply,smul_eq_mul,mul_assoc,← mul_sum]
    exact congrArg (a*·) (hc e)

theorem relationSpace_eq_span (A : Finset E) (hA : ∃ e,e∉A) :
    relationSpace A=Submodule.span ℝ {(fun _ : Option ↥A => (1 : ℝ))} := by
  ext t
  change (∃ c : ℝ,∀ e,response A t e=c) ↔ _
  rw [constant_response_iff A hA,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    funext j
    simp only [Pi.smul_apply,smul_eq_mul,mul_one]
    exact (hc j).symm
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    intro j
    have h:=congrFun hc j
    simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using h.symm

end OneBlockCircuit
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart188

section BundlePart189
/- Source: Papers/GraphicalZonotopes/SmallCountModules.lean -/







@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators Classical
variable {H : Type*} [Fintype H] [LinearOrder H]

def crossingPairs (blocks : Finset (Finset H)) : Finset (OrientedEdge (⊤ : SimpleGraph H)) :=
  univ.filter (fun e => Crosses blocks e.1.1 e.1.2)

@[simp] theorem mem_crossingPairs (blocks : Finset (Finset H))
    (e : OrientedEdge (⊤ : SimpleGraph H)) :
    e∈crossingPairs blocks ↔ Crosses blocks e.1.1 e.1.2 := by
  simp only [crossingPairs,mem_filter,mem_univ,true_and]

abbrev Branch (blocks : Finset (Finset H)) := Option ↥(crossingPairs blocks)

/-- The first outer vertex carries the complete-multipartite response;
every selected pair has its own negative pure-coordinate outer module. -/
def modules (blocks : Finset (Finset H)) : Branch blocks → SetFunction H
  | none => complementModule univ blocks
  | some e => negativePairModule univ e.1.1.1 e.1.1.2

theorem modules_boolean {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H) :
    ∀ j,IsMonotoneBoolean (modules blocks j) := by
  intro j
  cases j with
  | none => exact hb.module_boolean
  | some e =>
    exact (negativePairBlocks_family univ (by simpa using hs)
      (mem_univ _) (mem_univ _) (ne_of_lt e.1.2.1)).module_boolean

theorem modules_essential {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H) :
    ∀ j a,Essential (modules blocks j) a := by
  intro j a
  cases j with
  | none => exact hb.essential (mem_univ a)
  | some e =>
    exact negativePairModule_essential univ (by simpa using hs)
      (mem_univ _) (mem_univ _) (ne_of_lt e.1.2.1) (mem_univ a)

theorem modules_coefficients {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (j : Branch blocks) :
    rowLowerEquiv.symm (responseVector (modules blocks j))=
      fullBlock (OneBlockCircuit.column (crossingPairs blocks) j) := by
  cases j with
  | none =>
    rw [modules,complementModule_response_coefficients hb]
    funext r
    by_cases hc : rowClique r=univ <;>
      by_cases he : Crosses blocks r.1.1.1 r.1.1.2 <;>
        simp only [fullBlock,OneBlockCircuit.column,mem_crossingPairs,hc,he,
          and_self,true_and,false_and,ite_true,ite_false]
  | some e =>
    rw [modules,negativePairModule_coefficients univ (by simpa using hs)
      (mem_univ _) (mem_univ _) e.1.2.1]
    funext r
    have he : r.1=e.1 ↔ r.1.1.1=e.1.1.1 ∧ r.1.1.2=e.1.1.2 := by
      constructor
      · intro h
        exact ⟨congrArg (fun q : OrientedEdge (⊤ : SimpleGraph H) => q.1.1) h,
          congrArg (fun q : OrientedEdge (⊤ : SimpleGraph H) => q.1.2) h⟩
      · rintro ⟨h₁,h₂⟩
        exact Subtype.ext (Prod.ext h₁ h₂)
    simp only [← he]
    by_cases hc : rowClique r=univ <;> by_cases hp : r.1=e.1 <;>
      simp only [fullBlock,OneBlockCircuit.column,hc,hp,
        true_and,false_and,ite_true,ite_false,not_true_eq_false,not_false_eq_true]

theorem weighted_coefficients {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (t : Branch blocks → ℝ) :
    rowLowerEquiv.symm (weightedResponse (modules blocks) t)=
      fullBlock (OneBlockCircuit.response (crossingPairs blocks) t) := by
  rw [rowLower_symm_weightedResponse]
  simp_rw [modules_coefficients hb hs]
  funext r
  rw [Finset.sum_apply]
  by_cases hc : rowClique r=univ
  · simp only [Pi.smul_apply,smul_eq_mul,fullBlock,if_pos hc,
      OneBlockCircuit.response]
  · simp only [Pi.smul_apply,smul_eq_mul,fullBlock,if_neg hc,mul_zero,sum_const_zero]

/-- All real relations, with no positivity assumption, are exactly the
constant vectors. The unused pair is part of the actual full hub block. -/
theorem integrable_iff_constant {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks)
    (t : Branch blocks → ℝ) :
    (∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z (modules blocks) t) ↔
      ∃ c : ℝ,∀ j,t j=c := by
  letI : Nonempty (OrientedEdge (⊤ : SimpleGraph H)):=⟨hproper.choose⟩
  rw [integrable_iff_blockConstant,weighted_coefficients hb hs,
    fullBlock_constant_iff,OneBlockCircuit.constant_response_iff _ hproper]

theorem unit_integrable {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks) :
    ∃ z : SetFunction H,TranslationNormalized z ∧
      Compatible z (modules blocks) (fun _ => 1) :=
  (integrable_iff_constant hb hs hproper _).mpr ⟨1,fun _ => rfl⟩

theorem unit_unique {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks) :
    UniqueIntegrableRelation (modules blocks) (fun _ => 1) := by
  intro t ht
  obtain ⟨c,hc⟩:=(integrable_iff_constant hb hs hproper t).mp ht
  refine ⟨c,?_⟩
  funext j
  simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using hc j

theorem unit_integral_lift {blocks : Finset (Finset H)}
    (hb : ComplementFamily (univ : Finset H) blocks) (hs : 3≤ Fintype.card H)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph H),e∉crossingPairs blocks) :
    ∃ z : SetFunction H,TranslationNormalized z ∧ IntegerValued z ∧
      Compatible z (modules blocks) (fun _ => 1) := by
  have hrel : (fun _ : Branch blocks => (1 : ℝ))∈
      LinearMap.ker (quotientRelation (modules blocks)) :=
    (mem_quotientRelation_ker_iff _ _).mpr (unit_integrable hb hs hproper)
  simpa only [Int.cast_one] using integral_compatible_lift
    (modules blocks) (modules_boolean hb hs) (fun _ => (1 : ℤ))
    (by simpa only [Int.cast_one] using hrel)

end SmallCount
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart189

section BundlePart190
/- Source: Papers/GraphicalZonotopes/UnitBookGeometry.lean -/





@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

/-- Actual finite-dimensional lattice geometry for a circuit of unit-weight
Boolean columns. The normalized central lift is derived integrally from the
actual elemental response equations. -/
theorem lattice_book_of_unit_modules {s k : ℕ} (hs : 0< s) (hk : 0< k)
    (F : Fin k → SetFunction (Fin s)) (hF : ∀ i,IsMonotoneBoolean (F i))
    (hess : ∀ i a,Essential (F i) a)
    (hrel : ∃ z : SetFunction (Fin s),TranslationNormalized z ∧ Compatible z F (fun _ => 1))
    (huniq : UniqueIntegrableRelation F (fun _ => 1)) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  letI : Nonempty (Fin s):=⟨⟨0,hs⟩⟩
  letI : Nonempty (Fin k):=⟨⟨0,hk⟩⟩
  have hkrel : (fun _ : Fin k => (1 : ℝ))∈LinearMap.ker (quotientRelation F):=
    (mem_quotientRelation_ker_iff F _).mpr hrel
  obtain ⟨z,hzn,hzi,hcInt⟩:=integral_compatible_lift F hF (fun _ => (1 : ℤ))
    (by simpa only [Int.cast_one] using hkrel)
  have hc : Compatible z F (fun _ => 1):=by simpa only [Int.cast_one] using hcInt
  let f:=assembled z F (fun _ => 1)
  have hn : TranslationNormalized f:=assembled_normalized hzn F hF (fun _ => 1)
  have hi : IntegerValued f := by
    simpa only [Int.cast_one] using assembled_integerValued hzi F hF (fun _ => (1 : ℤ))
  have he : ExtremeSupermodular f:=positive_circuit_extreme hzn hF
    (fun _ => zero_le_one) ⟨⟨0,hk⟩,one_ne_zero⟩ hc huniq
  have hd : FullDimension (basePolytope f):=assembled_fullDimension hzn hF
    (fun _ => zero_lt_one) hc (essentialSpokeGraph_connected F hess)
  obtain ⟨hl,R,hR,hnR,hQR⟩:=assembled_lattice_complement hzn hzi hF
    (fun _ => (1 : ℤ)) (fun _ => zero_le_one) hcInt
  refine ⟨f,hn,hi,he,assembled_graphical z F (fun _ => 1),hd,
    he.minkowskiIndecomposable,?_,R,hR,hnR,?_⟩
  · simpa only [Int.cast_one] using hl
  · simpa only [Int.cast_one,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hQR

end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart190

section BundlePart191
/- Source: Papers/GraphicalZonotopes/SmallCountGeometry.lean -/






@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators Pointwise

/-- The complete geometric construction associated with a proper nonempty
complete-multipartite pair pattern. The finite-type transport labels exactly
one outer vertex per Boolean column; it does not change the ambient graph. -/
theorem lattice_book_of_complement_family {s k : ℕ} (hs : 3≤ s)
    (blocks : Finset (Finset (Fin s)))
    (hb : ComplementFamily (univ : Finset (Fin s)) blocks)
    (hproper : ∃ e : OrientedEdge (⊤ : SimpleGraph (Fin s)),e∉crossingPairs blocks)
    (hcard : (crossingPairs blocks).card+1=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  have hsf : 3≤ Fintype.card (Fin s):=by simpa using hs
  have hk : 0< k:=by omega
  letI : Nonempty (Fin s):=⟨⟨0,by omega⟩⟩
  letI : Nonempty (Fin k):=⟨⟨0,hk⟩⟩
  have hJ : Fintype.card (Branch blocks)=k := by
    simpa only [Branch,Fintype.card_option,Fintype.card_coe] using hcard
  let e : Fin k≃Branch blocks:=
    (finCongr hJ.symm).trans (Fintype.equivFin (Branch blocks)).symm
  let F : Fin k → SetFunction (Fin s):=fun i => modules blocks (e i)
  have hF : ∀ i,IsMonotoneBoolean (F i):=fun i => modules_boolean hb hsf (e i)
  have hess : ∀ i a,Essential (F i) a:=fun i a => modules_essential hb hsf (e i) a
  obtain ⟨z,hzn,hzc⟩:=unit_integrable hb hsf hproper
  have hc : Compatible z F (fun _ => 1) := by
    apply (compatible_reindex e z (modules blocks) (fun _ => 1)).mpr
    exact hzc
  have huniq : UniqueIntegrableRelation F (fun _ => 1) := by
    intro t ht
    obtain ⟨u,hun,huc⟩:=ht
    have hold : Compatible u (modules blocks) (fun j => t (e.symm j)) :=
      (compatible_reindex e u (modules blocks) t).mp huc
    obtain ⟨c,hc⟩:=unit_unique hb hsf hproper (fun j => t (e.symm j)) ⟨u,hun,hold⟩
    refine ⟨c,?_⟩
    funext i
    simpa only [e.symm_apply_apply,Pi.smul_apply,smul_eq_mul,mul_one] using congrFun hc (e i)
  exact lattice_book_of_unit_modules (by omega) hk F hF hess ⟨z,hzn,hc⟩ huniq

end SmallCount
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart191

section BundlePart192
/- Source: Papers/GraphicalZonotopes/MultipartitePairCounting.lean -/





@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount
open Finset
open scoped BigOperators Classical
variable {H : Type*} [Fintype H] [LinearOrder H]

def blockUnion (blocks : Finset (Finset H)) : Finset H:=blocks.biUnion id

@[simp] theorem mem_blockUnion (blocks : Finset (Finset H)) (x : H) :
    x∈blockUnion blocks ↔ ∃ B∈blocks,x∈B := by
  simp only [blockUnion,mem_biUnion,id_eq]

def orderedPairs (U : Finset H) : Finset (H×H):=
  (U×ˢU).filter (fun p => p.1< p.2)

@[simp] theorem mem_orderedPairs (U : Finset H) (p : H×H) :
    p∈orderedPairs U ↔ p.1∈U ∧ p.2∈U ∧ p.1< p.2 := by
  simp only [orderedPairs,mem_filter,mem_product,and_assoc]

theorem orderedPairs_card (U : Finset H) :
    (orderedPairs U).card=U.card.choose 2 := card_product_filter_lt

def completePairEquiv : OrientedEdge (⊤ : SimpleGraph H)≃↥(orderedPairs (univ : Finset H)) where
  toFun e:=⟨e.1,(mem_orderedPairs _ _).mpr ⟨mem_univ _,mem_univ _,e.2.1⟩⟩
  invFun p:=⟨p.1,((mem_orderedPairs _ _).mp p.2).2.2,
    (SimpleGraph.top_adj _ _).mpr (ne_of_lt ((mem_orderedPairs _ _).mp p.2).2.2)⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem completePair_card :
    Fintype.card (OrientedEdge (⊤ : SimpleGraph H))=(Fintype.card H).choose 2 := by
  rw [Fintype.card_congr completePairEquiv,Fintype.card_coe,orderedPairs_card,card_univ]

def crossingPairValues (blocks : Finset (Finset H)) : Finset (H×H):=
  (orderedPairs (blockUnion blocks)).filter (fun p => Crosses blocks p.1 p.2)

@[simp] theorem mem_crossingPairValues (blocks : Finset (Finset H)) (p : H×H) :
    p∈crossingPairValues blocks ↔ p∈orderedPairs (blockUnion blocks) ∧
      Crosses blocks p.1 p.2 := by
  simp only [crossingPairValues,mem_filter]

theorem crossingPairs_card_values (blocks : Finset (Finset H)) :
    (crossingPairs blocks).card=(crossingPairValues blocks).card := by
  apply card_bij (fun e _ => e.1)
  · intro e he
    have hcross:=(mem_crossingPairs blocks e).mp he
    obtain ⟨A,hA,B,hB,hAB,hu,hv⟩:=hcross
    exact (mem_crossingPairValues blocks _).mpr ⟨(mem_orderedPairs _ _).mpr
      ⟨(mem_blockUnion blocks _).mpr ⟨A,hA,hu⟩,
        (mem_blockUnion blocks _).mpr ⟨B,hB,hv⟩,e.2.1⟩,
      ⟨A,hA,B,hB,hAB,hu,hv⟩⟩
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro p hp
    have hp' := (mem_crossingPairValues blocks p).mp hp
    have ht:=(mem_orderedPairs _ _).mp hp'.1
    let e : OrientedEdge (⊤ : SimpleGraph H):=
      ⟨p,ht.2.2,(SimpleGraph.top_adj _ _).mpr (ne_of_lt ht.2.2)⟩
    exact ⟨e,(mem_crossingPairs blocks e).mpr hp'.2,rfl⟩

theorem orderedPairs_partition (blocks : Finset (Finset H)) :
    orderedPairs (blockUnion blocks)=crossingPairValues blocks∪blocks.biUnion orderedPairs := by
  ext p
  constructor
  · intro hp
    obtain ⟨hu,hv,hlt⟩:=(mem_orderedPairs _ _).mp hp
    obtain ⟨A,hA,huA⟩:=(mem_blockUnion blocks _).mp hu
    obtain ⟨B,hB,hvB⟩:=(mem_blockUnion blocks _).mp hv
    by_cases hAB : A=B
    · subst B
      exact mem_union_right _ (mem_biUnion.mpr ⟨A,hA,
        (mem_orderedPairs _ _).mpr ⟨huA,hvB,hlt⟩⟩)
    · exact mem_union_left _ ((mem_crossingPairValues blocks p).mpr ⟨hp,⟨A,hA,B,hB,hAB,huA,hvB⟩⟩)
  · intro hp
    rcases mem_union.mp hp with hc | hi
    · exact ((mem_crossingPairValues blocks p).mp hc).1
    · obtain ⟨A,hA,hpA⟩:=mem_biUnion.mp hi
      obtain ⟨hu,hv,hlt⟩:=(mem_orderedPairs _ _).mp hpA
      exact (mem_orderedPairs _ _).mpr
        ⟨(mem_blockUnion blocks _).mpr ⟨A,hA,hu⟩,
          (mem_blockUnion blocks _).mpr ⟨A,hA,hv⟩,hlt⟩

theorem crossing_internal_disjoint (blocks : Finset (Finset H))
    (hd : ∀ A∈blocks,∀ B∈blocks,A≠ B → Disjoint A B) :
    Disjoint (crossingPairValues blocks) (blocks.biUnion orderedPairs) := by
  apply disjoint_left.mpr
  intro p hc hi
  obtain ⟨A,hA,B,hB,hAB,huA,hvB⟩:=((mem_crossingPairValues blocks p).mp hc).2
  obtain ⟨C,hC,hpC⟩:=mem_biUnion.mp hi
  obtain ⟨huC,hvC,_⟩:=(mem_orderedPairs _ _).mp hpC
  have hAC : A=C := by
    by_contra hn
    exact (disjoint_left.mp (hd A hA C hC hn)) huA huC
  have hBC : B=C := by
    by_contra hn
    exact (disjoint_left.mp (hd B hB C hC hn)) hvB hvC
  exact hAB (hAC.trans hBC.symm)

theorem internalPairs_pairwiseDisjoint (blocks : Finset (Finset H))
    (hd : ∀ A∈blocks,∀ B∈blocks,A≠ B → Disjoint A B) :
    (blocks : Set (Finset H)).PairwiseDisjoint orderedPairs := by
  intro A hA B hB hAB
  apply disjoint_left.mpr
  intro p hpA hpB
  exact (disjoint_left.mp (hd A hA B hB hAB))
    ((mem_orderedPairs A p).mp hpA).1 ((mem_orderedPairs B p).mp hpB).1

/-- This count is for the literal ordered representatives of the unordered
crossing pairs. Every pair of active vertices is either crossing or belongs
to one uniquely determined part. -/
theorem crossingPairs_card_formula (blocks : Finset (Finset H))
    (hd : ∀ A∈blocks,∀ B∈blocks,A≠ B → Disjoint A B) :
    (crossingPairs blocks).card=(blockUnion blocks).card.choose 2-
      ∑ B∈blocks,B.card.choose 2 := by
  have he:=congrArg Finset.card (orderedPairs_partition blocks)
  rw [orderedPairs_card,card_union_of_disjoint (crossing_internal_disjoint blocks hd),
    card_biUnion (internalPairs_pairwiseDisjoint blocks hd)] at he
  simp only [orderedPairs_card] at he
  rw [crossingPairs_card_values]
  omega

theorem crossingPairs_nonempty_gives_two (blocks : Finset (Finset H))
    (hp : (crossingPairs blocks).Nonempty) : 2≤ blocks.card := by
  obtain ⟨e,he⟩:=hp
  obtain ⟨A,hA,B,hB,hAB,_,_⟩:=(mem_crossingPairs blocks e).mp he
  exact (one_lt_card.mpr ⟨A,hA,B,hB,hAB⟩)

end SmallCount
end BooleanModule
end GraphicalZonotopes

end
end
end BundlePart192

section BundlePart193
/- Source: Papers/GraphicalZonotopes/MultipartiteSizes.lean -/







@[expose] public section
namespace GraphicalZonotopes
namespace BooleanModule
namespace SmallCount

def crossCount (sizes : List ℕ) : ℕ :=
  sizes.sum.choose 2-(sizes.map (fun a => a.choose 2)).sum

/-- Every pair count up to `s.choose 2` is realized by positive multipartite
block sizes using at most `s` vertices. The unused vertices are isolated in
the response pattern, but will remain essential in its Boolean module. -/
theorem exists_multipartite_sizes (s m : ℕ) (hm : m≤ s.choose 2) :
    ∃ sizes : List ℕ,(∀ a∈sizes,0< a) ∧ sizes.sum≤ s ∧ crossCount sizes=m := by
  induction s with
  | zero =>
    have hm0 : m=0:=by simpa using hm
    subst m
    exact ⟨[],by simp,by simp,by simp [crossCount]⟩
  | succ s ih =>
    by_cases hsmall : m≤ s.choose 2
    · obtain ⟨sizes,hpos,hsize,hcount⟩:=ih hsmall
      exact ⟨sizes,hpos,hsize.trans (Nat.le_succ s),hcount⟩
    · have hchoose : (s+1).choose 2=s.choose 2+s := by
        calc
          (s+1).choose 2=s.choose 1+s.choose 2 := Nat.choose_succ_succ' s 1
          _=s.choose 2+s := by rw [Nat.choose_one_right,Nat.add_comm]
      let j:=(s+1).choose 2-m
      let q:=j/3
      let r:=j%3
      have hdecomp : j=3*q+r:=by
        dsimp only [q,r]
        exact (Nat.div_add_mod j 3).symm
      have hr : r<3:=Nat.mod_lt _ (by decide)
      have hj : j< s := by
        dsimp only [j]
        rw [hchoose]
        omega
      have hused : 3*q+2*r≤ s+1 := by omega
      let a:=s+1-(3*q+2*r)
      let sizes : List ℕ:=List.replicate q 3++List.replicate r 2++List.replicate a 1
      have hsum : sizes.sum=s+1 := by
        simp only [sizes,List.sum_append,List.sum_replicate,nsmul_eq_mul,Nat.cast_id,Nat.mul_one]
        dsimp only [a]
        omega
      have hinside : (sizes.map (fun n => n.choose 2)).sum=j := by
        simpa only [sizes,List.map_append,List.map_replicate,List.sum_append,
          List.sum_replicate,nsmul_eq_mul,
          show (3 : ℕ).choose 2=3 from by decide,
          show (2 : ℕ).choose 2=1 from by decide,
          show (1 : ℕ).choose 2=0 from by decide,
          Nat.cast_id,Nat.mul_one,Nat.mul_zero,Nat.one_mul,Nat.zero_mul,Nat.add_zero,Nat.mul_comm] using hdecomp.symm
      refine ⟨sizes,?_,by omega,?_⟩
      · intro b hb
        simp only [sizes,List.mem_append,List.mem_replicate] at hb
        rcases hb with (⟨_,rfl⟩ | ⟨_,rfl⟩) | ⟨_,rfl⟩ <;> omega
      · rw [crossCount,hsum,hinside]
        dsimp only [j]
        omega

end SmallCount
end BooleanModule
end GraphicalZonotopes

end
end BundlePart193
