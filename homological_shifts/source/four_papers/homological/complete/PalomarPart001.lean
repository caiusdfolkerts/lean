module

public meta import PalomarAudit
public import four_papers.homological.complete.PalomarPart000
import all four_papers.homological.complete.PalomarPart000
public import Aesop
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Util.CollectAxioms
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Combinatorics.Matroid.IndepAxioms
public import Mathlib.Combinatorics.Matroid.Minor.Contract
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.WithBot
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Tauto

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  PalomarAudit.createDirAll ".lake/reports/audit/homological"


@[expose] public section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "0: CommAlg.ExteriorPower.BaseChange\n"

/-! ## Source: CommAlg.ExteriorPower.BaseChange -/
section CheckedSource46

/-!
# Exact arithmetic of the Koszul deletion constraints

These identities retain natural-valued exponents throughout. Every subtraction
in the deletion slack is justified by actual lower-inequality membership.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def deletionSlack (g : RankFunction V) (a : Exponent V) (U : Finset V) : ℕ :=
  subsetSum a U - g.lower U

theorem deletionSlack_add_lower (g : RankFunction V) {a : Exponent V}
    (ha : LowerFeasible g.lower a) (U : Finset V) :
    deletionSlack g a U + g.lower U = subsetSum a U :=
  Nat.sub_add_cancel (ha U)

@[simp] theorem deletionSlack_empty (g : RankFunction V) (a : Exponent V) :
    deletionSlack g a ∅ = 0 := by simp [deletionSlack]

theorem deletionSlack_submodular (g : RankFunction V) {a : Exponent V}
    (ha : LowerFeasible g.lower a) : SubmodularNat (deletionSlack g a) := by
  intro U W
  have hMod := subsetSum_union_inter a U W
  have hSuper := g.lower_supermodular U W
  have hU := deletionSlack_add_lower g ha U
  have hW := deletionSlack_add_lower g ha W
  have hUnion := deletionSlack_add_lower g ha (U ∪ W)
  have hInter := deletionSlack_add_lower g ha (U ∩ W)
  omega

theorem deletionSlack_univ (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (hDegree : a.degree = g univ + i) : deletionSlack g a univ = i := by
  simp only [deletionSlack, subsetSum_univ, RankFunction.lower_univ, hDegree,
    Nat.add_sub_cancel_left]

theorem deletionSlack_add_complement (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) (U : Finset V) :
    deletionSlack g a U + subsetSum a Uᶜ = i + g Uᶜ := by
  have hSlack := deletionSlack_add_lower g ha U
  have hLower := g.lower_add_compl U
  have hSum := subsetSum_add_compl a U
  omega

theorem card_erase_sdiff_add_indicator (T U : Finset V) {j : V} (hj : j ∈ T) :
    ((T.erase j) \ U).card + (if j ∈ Uᶜ then 1 else 0) = (T ∩ Uᶜ).card := by
  rw [Finset.erase_sdiff_comm]
  have hSet : T \ U = T ∩ Uᶜ := by ext x; simp
  rw [hSet]
  by_cases hjU : j ∈ Uᶜ
  · rw [if_pos hjU]
    exact Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨hj, hjU⟩)
  · rw [if_neg hjU, Nat.add_zero, Finset.erase_eq_of_notMem (by simp [hjU])]

/-- A rank-formula cost is at least the target degree precisely when the
support-predecessor exponent satisfies the corresponding one-unit inequality. -/
theorem deletion_cost_ge_iff_supportPred (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i)
    {j : V} (hj : j ∈ a.support) (U : Finset V) :
    i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card ↔
      subsetSum (supportPred a) Uᶜ + (if j ∈ Uᶜ then 1 else 0) ≤ g Uᶜ := by
  have hSlack := deletionSlack_add_complement g ha hDegree U
  have hCard := card_erase_sdiff_add_indicator a.support U hj
  have hPred := subsetSum_supportPred a Uᶜ
  rw [Finset.inter_comm Uᶜ a.support] at hPred
  omega

theorem all_deletion_costs_ge_iff (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) :
    (∀ j ∈ a.support, ∀ U, i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card) ↔
      (∀ j ∈ a.support, ∀ A,
        subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A) := by
  constructor
  · intro h j hj A
    simpa only [compl_compl] using
      (deletion_cost_ge_iff_supportPred g ha hDegree hj Aᶜ).mp (h j hj Aᶜ)
  · intro h j hj U
    exact (deletion_cost_ge_iff_supportPred g ha hDegree hj U).mpr (h j hj Uᶜ)

theorem supportPred_indicator_bounds_iff (g : RankFunction V) (hg : g.Active)
    (a : Exponent V) :
    (∀ j ∈ a.support, ∀ A,
      subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A) ↔
      (∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1) := by
  constructor
  · intro h A hA
    by_cases hSupport : (A ∩ a.support).Nonempty
    · obtain ⟨j, hj⟩ := hSupport
      obtain ⟨hjA, hjSupport⟩ := Finset.mem_inter.mp hj
      have hb := h j hjSupport A
      rw [if_pos hjA] at hb
      omega
    · have hEmpty : A ∩ a.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSupport
      have hSum := subsetSum_supportPred_inter a A
      rw [hEmpty, subsetSum_empty] at hSum
      omega
  · intro h j hj A
    by_cases hjA : j ∈ A
    · have hA : A.Nonempty := ⟨j, hjA⟩
      have hb := h A hA
      have hgA := hg A hA
      rw [if_pos hjA]
      omega
    · rw [if_neg hjA, Nat.add_zero]
      by_cases hA : A.Nonempty
      · exact (h A hA).trans (Nat.sub_le _ _)
      · have he := Finset.not_nonempty_iff_eq_empty.mp hA
        simp [he]

end CommAlg.Polymatroid

end
end CheckedSource46

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "47: CommAlg.Matroid.MinorInduction\n"

/-! ## Source: CommAlg.Matroid.MinorInduction -/
section CheckedSource47


/-!
# Finite matroid deletion and contraction for homology induction

All minors are Mathlib's actual matroids. The natural rank is the finite value
of Mathlib's extended-natural rank, and every numerical formula is derived
from base cardinalities.
-/

noncomputable section

@[expose] public section

open scoped Matroid

namespace CommAlg.Matroid

open Classical Set

variable {V : Type*} {M : _root_.Matroid V} {e : V} {I : Set V}

def rank (M : _root_.Matroid V) : ℕ := M.eRank.toNat

def NoColoops (M : _root_.Matroid V) : Prop := ∀ e, ¬ M.IsColoop e

theorem rank_eq_ncard_of_isBase {B : Set V} (hB : M.IsBase B) : rank M = B.ncard := by
  exact (congrArg ENat.toNat hB.encard_eq_eRank).symm

theorem rank_delete_of_not_isColoop (he : ¬ M.IsColoop e) :
    rank (M ＼ ({e} : Set V)) = rank M := by
  have hS : M.Spanning (M.E \ {e}) := by
    by_contra h
    exact he (_root_.Matroid.isColoop_iff_sdiff_not_spanning.mpr h)
  exact congrArg ENat.toNat hS.eRank_restrict

theorem NoColoops.contract {C : Set V} (hM : NoColoops M) : NoColoops (M ／ C) := by
  intro a ha
  exact hM a (_root_.Matroid.contract_isColoop_iff.mp ha).1

theorem noColoops_iff_coloops_eq_empty : NoColoops M ↔ M.coloops = ∅ := by
  simp [NoColoops, Set.eq_empty_iff_forall_notMem,
    ← _root_.Matroid.isColoop_iff_mem_coloops]

theorem coloop_insert_indep (he : M.IsColoop e) (hI : M.Indep I) :
    M.Indep (insert e I) := he.insert_indep_of_indep hI

section Finite

variable [Finite V]

theorem indep_ncard_le_rank (hI : M.Indep I) : I.ncard ≤ rank M := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  rw [rank_eq_ncard_of_isBase hB]
  exact Set.ncard_le_ncard hIB

theorem rank_delete_le (M : _root_.Matroid V) (D : Set V) :
    rank (M ＼ D) ≤ rank M := by
  obtain ⟨B, hB⟩ := (M ＼ D).exists_isBase
  rw [rank_eq_ncard_of_isBase hB]
  exact indep_ncard_le_rank hB.indep.of_delete

theorem exists_nonloop_of_rank_pos (hr : 0 < rank M) : ∃ e, M.IsNonloop e := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [rank_eq_ncard_of_isBase hB] at hr
  obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite B)).mp hr
  exact ⟨e, hB.indep.isNonloop_of_mem he⟩

theorem rank_pos_of_nonloop (he : M.IsNonloop e) : 0 < rank M := by
  have h := indep_ncard_le_rank he.indep
  have h' : 1 ≤ rank M := by simpa using h
  omega

theorem rank_pos_iff_exists_nonloop : 0 < rank M ↔ ∃ e, M.IsNonloop e :=
  ⟨exists_nonloop_of_rank_pos, fun ⟨_, he⟩ => rank_pos_of_nonloop he⟩

theorem indep_eq_empty_of_rank_zero (hr : rank M = 0) (hI : M.Indep I) : I = ∅ := by
  have h := indep_ncard_le_rank hI
  rw [hr] at h
  exact (Set.ncard_eq_zero (Set.toFinite I)).mp (Nat.eq_zero_of_le_zero h)

theorem rank_contract_add_one (he : M.IsNonloop e) :
    rank (M ／ ({e} : Set V)) + 1 = rank M := by
  obtain ⟨B, hB⟩ := (M ／ ({e} : Set V)).exists_isBase
  obtain ⟨hBM, hBe⟩ := he.indep.contract_isBase_iff.mp hB
  have heB : e ∉ B := Set.disjoint_singleton_right.mp hBe
  rw [rank_eq_ncard_of_isBase hB, rank_eq_ncard_of_isBase hBM,
    Set.union_singleton, Set.ncard_insert_of_notMem heB]

theorem rank_contract_eq_sub_one (he : M.IsNonloop e) :
    rank (M ／ ({e} : Set V)) = rank M - 1 := by
  have h := rank_contract_add_one he
  omega

theorem rank_delete_add_one_of_isColoop (he : M.IsColoop e) :
    rank (M ＼ ({e} : Set V)) + 1 = rank M := by
  have hC : ({e} : Set V) ⊆ M.coloops := Set.singleton_subset_iff.mpr he
  rw [← _root_.Matroid.contract_eq_delete_of_subset_coloops hC]
  exact rank_contract_add_one he.isNonloop

/-- When the ground set is nonempty and rank is at most `i`, rank `i` with
no coloops is equivalent to preservation of rank `i` after every singleton
deletion. This includes `i = 0`. -/
theorem rank_eq_and_noColoops_iff_delete_rank (M : _root_.Matroid V) (i : ℕ)
    (hE : M.E.Nonempty) (hr : rank M ≤ i) :
    (rank M = i ∧ NoColoops M) ↔
      ∀ e ∈ M.E, rank (M ＼ ({e} : Set V)) = i := by
  constructor
  · rintro ⟨hRank, hM⟩ e he
    exact (rank_delete_of_not_isColoop (hM e)).trans hRank
  · intro h
    obtain ⟨e, he⟩ := hE
    have hLower := rank_delete_le M ({e} : Set V)
    rw [h e he] at hLower
    have hRank : rank M = i := Nat.le_antisymm hr hLower
    refine ⟨hRank, ?_⟩
    intro f hf
    have hDelete := h f hf.mem_ground
    have hDrop := rank_delete_add_one_of_isColoop hf
    omega

theorem delete_ground_ncard_add_one (he : e ∈ M.E) :
    (M ＼ ({e} : Set V)).E.ncard + 1 = M.E.ncard := by
  exact Set.ncard_sdiff_singleton_add_one he

theorem contract_ground_ncard_add_one (he : e ∈ M.E) :
    (M ／ ({e} : Set V)).E.ncard + 1 = M.E.ncard := by
  exact Set.ncard_sdiff_singleton_add_one he

theorem delete_ground_ncard_lt (he : e ∈ M.E) :
    (M ＼ ({e} : Set V)).E.ncard < M.E.ncard := by
  have h := delete_ground_ncard_add_one he
  omega

theorem contract_ground_ncard_lt (he : e ∈ M.E) :
    (M ／ ({e} : Set V)).E.ncard < M.E.ncard := by
  have h := contract_ground_ncard_add_one he
  omega

end Finite

section Finset

variable [DecidableEq V]

/-- Deletion is exactly deletion of a label in the independence complex. -/
theorem delete_indep_finset_iff (s : Finset V) :
    (M ＼ ({e} : Set V)).Indep (s : Set V) ↔ M.Indep (s : Set V) ∧ e ∉ s := by
  simp only [_root_.Matroid.delete_indep_iff, Set.disjoint_singleton_right,
    Finset.mem_coe]

/-- Contraction at a nonloop is exactly the link in the independence complex. -/
theorem contract_indep_finset_iff (he : M.IsNonloop e) (s : Finset V) :
    (M ／ ({e} : Set V)).Indep (s : Set V) ↔
      M.Indep ((insert e s : Finset V) : Set V) ∧ e ∉ s := by
  simpa only [Finset.coe_insert, Finset.mem_coe, and_comm] using
    he.contractElem_indep_iff (I := (s : Set V))

theorem coloop_insert_indep_finset (he : M.IsColoop e) {s : Finset V}
    (hs : M.Indep (s : Set V)) : M.Indep ((insert e s : Finset V) : Set V) := by
  simpa only [Finset.coe_insert] using he.insert_indep_of_indep hs

variable [Finite V]

theorem indep_card_le_rank {s : Finset V} (hs : M.Indep (s : Set V)) :
    s.card ≤ rank M := by
  simpa using indep_ncard_le_rank hs

theorem indep_finset_eq_empty_of_rank_zero (hr : rank M = 0) {s : Finset V}
    (hs : M.Indep (s : Set V)) : s = ∅ := by
  have h := indep_card_le_rank hs
  rw [hr] at h
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h)

end Finset

end CommAlg.Matroid

end
end
end CheckedSource47

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "48: CommAlg.Matroid.IndependenceHomology\n"

/-! ## Source: CommAlg.Matroid.IndependenceHomology -/
section CheckedSource48

/-!
# Homology of every finite matroid independence complex

The augmented chain complex is the genuine exterior-basis complex from
`CommAlg.Simplicial.Chains`. Induction removes an actual ground element,
using actual deletion and contraction matroids. No shellability, homology
concentration, or top-homology hypothesis is built into the statement.
-/

noncomputable section

open scoped Matroid

namespace CommAlg.Matroid

open Classical
open CommAlg.Simplicial

variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]

def independenceFaces (M : _root_.Matroid V) (s : Finset V) : Prop :=
  M.Indep (s : Set V)

omit [Fintype V] [LinearOrder V] in
theorem independenceFaces_downward (M : _root_.Matroid V) :
    Downward (independenceFaces M) := by
  intro s t hts hs
  exact hs.subset (by simpa using hts)

omit [Fintype V] [LinearOrder V] in
@[simp] theorem independenceFaces_empty (M : _root_.Matroid V) :
    independenceFaces M ∅ := by
  simpa only [independenceFaces, Finset.coe_empty] using M.empty_indep

omit [Fintype V] in
theorem independenceFaces_delete (M : _root_.Matroid V) (e : V) :
    independenceFaces (M ＼ ({e} : Set V)) = deletion (independenceFaces M) e := by
  funext s
  exact propext (delete_indep_finset_iff s)

omit [Fintype V] in
theorem independenceFaces_contract (M : _root_.Matroid V) {e : V} (he : M.IsNonloop e) :
    independenceFaces (M ／ ({e} : Set V)) = link (independenceFaces M) e := by
  funext s
  exact propext (contract_indep_finset_iff he s)

theorem independence_exactIn_of_coloop (M : _root_.Matroid V) {e : V}
    (he : M.IsColoop e) (i : ℕ) : ExactIn (k := k) (independenceFaces M) i := by
  apply exactIn_of_cone e
  intro s hs
  exact coloop_insert_indep_finset he hs

private theorem independence_exactIn_induction (n : ℕ) :
    ∀ M : _root_.Matroid V, M.E.ncard = n →
      ∀ i : ℕ, i ≠ rank M → ExactIn (k := k) (independenceFaces M) i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M hCard i hi
    by_cases hr : rank M = 0
    · apply exactIn_of_no_face
      intro s hs
      have hs0 : s = ∅ := indep_finset_eq_empty_of_rank_zero hr hs
      rw [hs0, Finset.card_empty]
      simpa only [hr, ne_eq, eq_comm] using hi
    by_cases hColoop : ∃ e, M.IsColoop e
    · obtain ⟨e, he⟩ := hColoop
      exact independence_exactIn_of_coloop M he i
    obtain ⟨e, he⟩ := exists_nonloop_of_rank_pos (Nat.pos_of_ne_zero hr)
    have hne : ¬ M.IsColoop e := fun h => hColoop ⟨e, h⟩
    have hDeleteRank := rank_delete_of_not_isColoop hne
    have hContractRank := rank_contract_add_one he
    have hDeleteCard : (M ＼ ({e} : Set V)).E.ncard < n := by
      rw [← hCard]
      exact delete_ground_ncard_lt he.mem_ground
    have hContractCard : (M ／ ({e} : Set V)).E.ncard < n := by
      rw [← hCard]
      exact contract_ground_ncard_lt he.mem_ground
    cases i with
    | zero =>
      apply exactIn_zero_of_vertex e
      simpa only [independenceFaces, Finset.coe_singleton] using he.indep
    | succ j =>
      have hDelete : ExactIn (k := k) (independenceFaces (M ＼ ({e} : Set V))) (j + 1) :=
        ih _ hDeleteCard _ rfl _ (by omega)
      have hContract : ExactIn (k := k) (independenceFaces (M ／ ({e} : Set V))) j :=
        ih _ hContractCard _ rfl _ (by omega)
      apply exactIn_of_deletion_link (independenceFaces_downward M) e j
      · rwa [← independenceFaces_delete M e]
      · rwa [← independenceFaces_contract M he]

/-- Every reduced homology group of a finite matroid independence complex
outside degree `rank M - 1` vanishes, expressed by explicit chain fillings.
The empty face has augmented chain degree zero. -/
theorem independence_exactIn_of_ne_rank (M : _root_.Matroid V) (i : ℕ)
    (hi : i ≠ rank M) : ExactIn (k := k) (independenceFaces M) i :=
  independence_exactIn_induction M.E.ncard M rfl i hi

section Nontrivial

variable [Nontrivial k]

private theorem independence_nonzero_top_induction (n : ℕ) :
    ∀ M : _root_.Matroid V, M.E.ncard = n → NoColoops M →
      NonzeroHomology (k := k) (independenceFaces M) (rank M) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M hCard hM
    by_cases hr : rank M = 0
    · rw [hr]
      apply nonzeroHomology_zero_of_only_empty (independenceFaces_empty M)
      intro s hs
      exact indep_finset_eq_empty_of_rank_zero hr hs
    obtain ⟨e, he⟩ := exists_nonloop_of_rank_pos (Nat.pos_of_ne_zero hr)
    have hDeleteRank := rank_delete_of_not_isColoop (hM e)
    have hContractRank := rank_contract_add_one he
    have hContractCard : (M ／ ({e} : Set V)).E.ncard < n := by
      rw [← hCard]
      exact contract_ground_ncard_lt he.mem_ground
    have hContract : NonzeroHomology (k := k)
        (independenceFaces (M ／ ({e} : Set V))) (rank (M ／ ({e} : Set V))) :=
      ih _ hContractCard _ rfl hM.contract
    have hDelete : ExactIn (k := k) (independenceFaces (M ＼ ({e} : Set V)))
        (rank (M ／ ({e} : Set V))) :=
      independence_exactIn_of_ne_rank _ _ (by omega)
    have hTop := nonzeroHomology_of_link (independenceFaces_downward M) e
      (rank (M ／ ({e} : Set V)))
      (by rwa [← independenceFaces_delete M e])
      (by rwa [← independenceFaces_contract M he])
    rwa [hContractRank] at hTop

/-- A finite matroid with no coloops has an actual nonboundary cycle in its
top augmented chain degree, over every nontrivial commutative coefficient ring. -/
theorem independence_nonzero_top (M : _root_.Matroid V) (hM : NoColoops M) :
    NonzeroHomology (k := k) (independenceFaces M) (rank M) :=
  independence_nonzero_top_induction M.E.ncard M rfl hM

/-- Full homology detection for every finite matroid, including rank zero,
loops, coloops, and all coefficient characteristics. -/
theorem independence_nonzeroHomology_iff (M : _root_.Matroid V) (i : ℕ) :
    NonzeroHomology (k := k) (independenceFaces M) i ↔ i = rank M ∧ NoColoops M := by
  constructor
  · intro h
    have hNot := (nonzeroHomology_iff_not_exactIn _ _).mp h
    refine ⟨?_, ?_⟩
    · by_contra hi
      exact hNot (independence_exactIn_of_ne_rank M i hi)
    · intro e he
      exact hNot (independence_exactIn_of_coloop M he i)
  · rintro ⟨rfl, hM⟩
    exact independence_nonzero_top M hM

theorem independence_exactIn_iff (M : _root_.Matroid V) (i : ℕ) :
    ExactIn (k := k) (independenceFaces M) i ↔ i ≠ rank M ∨ ¬ NoColoops M := by
  have h := independence_nonzeroHomology_iff (k := k) M i
  rw [nonzeroHomology_iff_not_exactIn] at h
  tauto

end Nontrivial

end CommAlg.Matroid

end
end CheckedSource48

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "49: CommAlg.Polymatroid.KoszulRankCriterion\n"

/-! ## Source: CommAlg.Polymatroid.KoszulRankCriterion -/
section CheckedSource49

/-!
# Exact rank and coloop detection for the Koszul matroid

The matroid is built from the actual nonnegative deletion slacks of a monomial
satisfying the lower rank inequalities. Its rank and coloops are Mathlib's
notions, and its homology is the actual augmented exterior-chain homology.
-/

noncomputable section

open scoped Matroid

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def koszulConstraintMatroid (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) : _root_.Matroid V :=
  constraintMatroid (deletionSlack g a) (deletionSlack_submodular g ha)
    (deletionSlack_empty g a) a.support

@[simp] theorem koszulConstraintMatroid_ground (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) :
    (koszulConstraintMatroid g a ha).E = (a.support : Set V) := rfl

@[simp] theorem koszulConstraintMatroid_indep (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (s : Finset V) :
    (koszulConstraintMatroid g a ha).Indep (s : Set V) ↔
      s ⊆ a.support ∧ ∀ U, (s ∩ U).card ≤ deletionSlack g a U :=
  constraintMatroid_indep _ _ _ _ _

theorem le_koszulConstraint_rank (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (R : Finset V) (hR : R ⊆ a.support) (i : ℕ) :
    i ≤ ((koszulConstraintMatroid g a ha).eRk (R : Set V)).toNat ↔
      ∀ U, i ≤ deletionSlack g a U + (R \ U).card := by
  obtain ⟨U, hU, hmin⟩ := constraint_rank_certificate (deletionSlack g a)
    (deletionSlack_submodular g ha) (deletionSlack_empty g a) a.support R hR
  change i ≤ ((constraintMatroid _ _ _ _).eRk (R : Set V)).toNat ↔ _
  rw [hU, ENat.toNat_natCast]
  exact ⟨fun h W => h.trans (hmin W), fun h => h U⟩

theorem koszulConstraint_rank_le (g : RankFunction V) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) :
    CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) ≤ i := by
  obtain ⟨U, hU, hmin⟩ := constraint_rank_certificate (deletionSlack g a)
    (deletionSlack_submodular g ha) (deletionSlack_empty g a)
    a.support a.support le_rfl
  have hBound := hmin univ
  have hBound' : deletionSlack g a U + (a.support \ U).card ≤ i := by
    simpa only [deletionSlack_univ g hDegree, Finset.sdiff_eq_empty_iff_subset.mpr
      (Finset.subset_univ a.support), Finset.card_empty, Nat.add_zero] using hBound
  have hRank : CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) =
      deletionSlack g a U + (a.support \ U).card := by
    unfold CommAlg.Matroid.rank
    rw [← _root_.Matroid.eRk_ground]
    change ((constraintMatroid _ _ _ _).eRk (a.support : Set V)).toNat = _
    rw [hU, ENat.toNat_natCast]
  rwa [hRank]

theorem koszulConstraint_delete_rank_eq (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (j : V) :
    CommAlg.Matroid.rank ((koszulConstraintMatroid g a ha) ＼ ({j} : Set V)) =
      ((koszulConstraintMatroid g a ha).eRk ((a.support.erase j : Finset V) : Set V)).toNat := by
  have hGround : (koszulConstraintMatroid g a ha).E \ {j} =
      ((a.support.erase j : Finset V) : Set V) := by
    ext x
    simp only [koszulConstraintMatroid_ground, Set.mem_sdiff, Finset.mem_coe,
      Set.mem_singleton_iff, Finset.mem_erase]
    tauto
  unfold CommAlg.Matroid.rank
  rw [_root_.Matroid.delete_eq_restrict, _root_.Matroid.eRank_restrict, hGround]

theorem le_koszulConstraint_delete_rank (g : RankFunction V) (a : Exponent V)
    (ha : LowerFeasible g.lower a) (j : V) (i : ℕ) :
    i ≤ CommAlg.Matroid.rank ((koszulConstraintMatroid g a ha) ＼ ({j} : Set V)) ↔
      ∀ U, i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card := by
  rw [koszulConstraint_delete_rank_eq]
  exact le_koszulConstraint_rank g a ha (a.support.erase j) (Finset.erase_subset _ _) i

/-- The full equivalence (3.1)--(3.3) for the actual Koszul constraint matroid. -/
theorem koszulConstraint_rank_and_noColoops_iff (g : RankFunction V) (hg : g.Active)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) (hSupport : a.support.Nonempty) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1 := by
  let M := koszulConstraintMatroid g a ha
  have hRank := koszulConstraint_rank_le g ha hDegree
  have hGround : M.E.Nonempty := by
    simpa only [M, koszulConstraintMatroid_ground, Finset.coe_nonempty] using hSupport
  have hDelete := CommAlg.Matroid.rank_eq_and_noColoops_iff_delete_rank M i hGround hRank
  have hStep : (CommAlg.Matroid.rank M = i ∧ CommAlg.Matroid.NoColoops M) ↔
      ∀ j ∈ a.support, ∀ U,
        i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card := by
    rw [hDelete]
    constructor
    · intro h j hj
      apply (le_koszulConstraint_delete_rank g a ha j i).mp
      exact le_of_eq (h j hj).symm
    · intro h j hj
      have hLower := (le_koszulConstraint_delete_rank g a ha j i).mpr (h j hj)
      have hUpper := (CommAlg.Matroid.rank_delete_le M ({j} : Set V)).trans hRank
      exact Nat.le_antisymm hUpper hLower
  exact hStep.trans ((all_deletion_costs_ge_iff g ha hDegree).trans
    (supportPred_indicator_bounds_iff g hg a))

omit [Fintype V] [DecidableEq V] in
theorem support_nonempty_of_degree_pos {a : Exponent V} (ha : 0 < a.degree) :
    a.support.Nonempty := by
  by_contra h
  have he : a.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hz : a = 0 := Finsupp.support_eq_empty.mp he
  simp [hz] at ha

/-- The positive-rank case used in the paper automatically has nonempty
support; no support condition is imposed on the theorem's input. -/
theorem koszulConstraint_rank_and_noColoops_iff_of_rank_pos
    (g : RankFunction V) (hg : g.Active) (hd : 0 < g univ)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, A.Nonempty → subsetSum (supportPred a) A ≤ g A - 1 :=
  koszulConstraint_rank_and_noColoops_iff g hg ha hDegree
    (support_nonempty_of_degree_pos (by omega))

/-- No coloops forces a minimizing rank certificate to contain the whole
support. Consequently the actual rank is exactly the excess total degree.
This requires neither active variables nor positive total rank. -/
theorem koszulConstraint_rank_eq_excess_of_noColoops (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a)
    (hNo : CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) :
    CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = a.degree - g univ := by
  obtain ⟨U, hU, hmin⟩ := constraint_rank_certificate (deletionSlack g a)
    (deletionSlack_submodular g ha) (deletionSlack_empty g a)
    a.support a.support le_rfl
  have hSupport : a.support ⊆ U := by
    intro j hj
    by_contra hjU
    exact hNo j (constraint_isColoop_of_minimizer (deletionSlack g a)
      (deletionSlack_submodular g ha) (deletionSlack_empty g a) a.support U hU
      (Finset.mem_sdiff.mpr ⟨hj, hjU⟩))
  have hRank : CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) =
      deletionSlack g a U := by
    unfold CommAlg.Matroid.rank
    rw [← _root_.Matroid.eRk_ground]
    change ((constraintMatroid _ _ _ _).eRk (a.support : Set V)).toNat = _
    rw [hU, Finset.sdiff_eq_empty_iff_subset.mpr hSupport, Finset.card_empty,
      Nat.add_zero, ENat.toNat_natCast]
  have hZero : subsetSum a Uᶜ = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact Finsupp.notMem_support_iff.mp (fun h => (Finset.mem_compl.mp hj) (hSupport h))
  have hSum := subsetSum_add_compl a U
  rw [hZero, Nat.add_zero] at hSum
  have hSlack := deletionSlack_add_lower g ha U
  have hLower := g.lower_le U
  have hTotal := ha univ
  simp only [RankFunction.lower_univ, subsetSum_univ] at hTotal
  have hDegree : a.degree = g univ + (a.degree - g univ) := by omega
  have hUpper := koszulConstraint_rank_le g ha hDegree
  omega

section Homology

variable [LinearOrder V] {k : Type*} [CommRing k] [Nontrivial k]

/-- Field-independent nonvanishing of the genuine augmented homology of the
Koszul matroid, expressed by the exact upper subset inequalities (3.6). -/
theorem koszulConstraint_nonzeroHomology_iff_augmented (g : RankFunction V)
    (hg : g.Active) (hd : 0 < g univ) {a : Exponent V} {i : ℕ}
    (ha : LowerFeasible g.lower a) (hDegree : a.degree = g univ + i) :
    CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i ↔
      ∀ A, subsetSum a A ≤ augmentedPartitionRank g A := by
  rw [CommAlg.Matroid.independence_nonzeroHomology_iff]
  have h := koszulConstraint_rank_and_noColoops_iff_of_rank_pos g hg hd ha hDegree
  rw [eq_comm] at h
  exact h.trans (supportPred_nonempty_bounds_iff_augmented g a)

/-- All-degree concentration follows directly from the actual constraint
matroid, without assuming a linear-resolution theorem. -/
theorem koszulConstraint_nonzeroHomology_degree (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a) {i : ℕ}
    (h : CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i) :
    a.degree = g univ + i := by
  obtain ⟨hRank, hNo⟩ := (CommAlg.Matroid.independence_nonzeroHomology_iff _ _).mp h
  have hExcess := koszulConstraint_rank_eq_excess_of_noColoops g ha hNo
  have hTotal := ha univ
  simp only [RankFunction.lower_univ, subsetSum_univ] at hTotal
  omega

end Homology

end CommAlg.Polymatroid

end
end CheckedSource49

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "50: CommAlg.KoszulComplex.FaceMatroid\n"

/-! ## Source: CommAlg.KoszulComplex.FaceMatroid -/
section CheckedSource50

/-! # The actual Koszul faces are the constraint matroid's independent sets

The proof starts from the monomial membership condition in `koszulFaces`.
It proves both the support condition and the exact simultaneous-deletion
inequalities, before identifying any homology groups.
-/

noncomputable section

namespace CommAlg.Koszul

open Classical Finset CommAlg.Polymatroid

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem faceExponent_le_iff_subset_support (s : Finset V) (a : Exponent V) :
    faceExponent s ≤ a ↔ s ⊆ a.support := by
  constructor
  · intro h j hj
    have hb := h j
    simp only [faceExponent_apply, if_pos hj] at hb
    exact Finsupp.mem_support_iff.mpr (by omega)
  · intro h j
    by_cases hj : j ∈ s
    · have hb := Finsupp.mem_support_iff.mp (h hj)
      simp only [faceExponent_apply, if_pos hj]
      omega
    · simp [hj]

theorem subsetSum_faceExponent (s U : Finset V) :
    subsetSum (faceExponent s) U = (s ∩ U).card := by
  simp only [subsetSum, faceExponent_apply, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Nat.cast_id, Finset.inter_comm]

theorem subsetSum_sub_faceExponent {s : Finset V} {a : Exponent V}
    (ha : faceExponent s ≤ a) (U : Finset V) :
    subsetSum (a - faceExponent s) U + (s ∩ U).card = subsetSum a U := by
  have he := tsub_add_cancel_of_le ha
  have hs := congrArg (fun b : Exponent V => subsetSum b U) he
  have hs' : subsetSum (a - faceExponent s) U + subsetSum (faceExponent s) U = subsetSum a U := by
    simpa only [subsetSum, Finsupp.add_apply, Finset.sum_add_distrib] using hs
  rwa [subsetSum_faceExponent] at hs'

theorem lowerFeasible_sub_faceExponent_iff (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a) {s : Finset V}
    (hs : faceExponent s ≤ a) :
    LowerFeasible g.lower (a - faceExponent s) ↔
      ∀ U, (s ∩ U).card ≤ deletionSlack g a U := by
  constructor
  · intro h U
    have hLower := h U
    have hSub := subsetSum_sub_faceExponent hs U
    have hSlack := deletionSlack_add_lower g ha U
    omega
  · intro h U
    have hBound := h U
    have hSub := subsetSum_sub_faceExponent hs U
    have hSlack := deletionSlack_add_lower g ha U
    omega

/-- Exact equality of the original upper Koszul complex's faces with the
independent sets of the actual finite constraint matroid. -/
theorem koszulFaces_eq_independenceFaces (B : Family V) (g : RankFunction V)
    (hB : ∀ a, Contains B a ↔ LowerFeasible g.lower a)
    (a : Exponent V) (ha : LowerFeasible g.lower a) :
    koszulFaces B a = CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha) := by
  funext s
  apply propext
  change (faceExponent s ≤ a ∧ Contains B (a - faceExponent s)) ↔
    (koszulConstraintMatroid g a ha).Indep (s : Set V)
  rw [koszulConstraintMatroid_indep]
  constructor
  · rintro ⟨hs, hb⟩
    exact ⟨(faceExponent_le_iff_subset_support s a).mp hs,
      (lowerFeasible_sub_faceExponent_iff g ha hs).mp ((hB _).mp hb)⟩
  · rintro ⟨hs, hb⟩
    have hs' := (faceExponent_le_iff_subset_support s a).mpr hs
    exact ⟨hs', (hB _).mpr ((lowerFeasible_sub_faceExponent_iff g ha hs').mpr hb)⟩

theorem koszulFaces_contains {B : Family V} {a : Exponent V} {s : Finset V}
    (hs : koszulFaces B a s) : Contains B a := by
  obtain ⟨b, hb, hba⟩ := hs.2
  exact ⟨b, hb, hba.trans tsub_le_self⟩

theorem koszulFaces_false_of_not_contains (B : Family V) (a : Exponent V)
    (ha : ¬ Contains B a) : koszulFaces B a = fun _ => False := by
  funext s
  exact propext ⟨fun h => ha (koszulFaces_contains h), False.elim⟩

end CommAlg.Koszul

end
end CheckedSource50

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "51: CommAlg.Polymatroid.RankBases\n"

/-! ## Source: CommAlg.Polymatroid.RankBases -/
section CheckedSource51

/-! # Finite integer base families and their actual polynomial ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsRankBase (g : RankFunction V) (a : Exponent V) : Prop :=
  a.degree = g Finset.univ ∧ UpperFeasible g a

def constExponent (n : ℕ) : Exponent V := Finsupp.equivFunOnFinite.symm (fun _ => n)

@[simp] theorem constExponent_apply (n : ℕ) (i : V) : constExponent n i = n := rfl

def rankBases (g : RankFunction V) : Family V :=
  (Finset.Iic (constExponent (g Finset.univ))).filter (IsRankBase g)

@[simp] theorem mem_rankBases (g : RankFunction V) (a : Exponent V) :
    a ∈ rankBases g ↔ IsRankBase g a := by
  simp only [rankBases, Finset.mem_filter, Finset.mem_Iic]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  intro i
  exact (coordinate_le_degree a i).trans h.1.le

theorem subsetSum_add (a b : Exponent V) (U : Finset V) :
    subsetSum (a + b) U = subsetSum a U + subsetSum b U := by
  simp [subsetSum, Finset.sum_add_distrib]

theorem rankBases_equigenerated (g : RankFunction V) :
    Equigenerated (rankBases g) (g Finset.univ) := by
  intro a ha
  exact ((mem_rankBases g a).mp ha).1

theorem rankBases_nonempty (g : RankFunction V) : (rankBases g).Nonempty := by
  have hf : LowerFeasible g.lower (constExponent (g Finset.univ)) := by
    intro U
    by_cases hU : U.Nonempty
    · obtain ⟨i, hi⟩ := hU
      exact (g.lower_le U).trans (by
        simpa only [subsetSum, constExponent_apply] using
          Finset.single_le_sum (f := fun _ : V => g Finset.univ)
            (fun j _ => Nat.zero_le _) hi)
    · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      simp [he]
  obtain ⟨a, _, hadeg, ha⟩ := exists_lower_base_below g.lower_supermodular g.lower_empty
    g.lower_univ g.lower_le hf
  exact ⟨a, (mem_rankBases g a).mpr
    ⟨hadeg, (upperFeasible_iff_lowerFeasible g hadeg).mpr ha⟩⟩

theorem rankBases_polymatroidal (g : RankFunction V) : IsPolymatroidal (rankBases g) := by
  refine ⟨⟨g Finset.univ, rankBases_equigenerated g⟩, ?_⟩
  intro a ha b hb i hi
  have ha := (mem_rankBases g a).mp ha
  have hb := (mem_rankBases g b).mp hb
  have hla := (upperFeasible_iff_lowerFeasible g ha.1).mp ha.2
  have hlb := (upperFeasible_iff_lowerFeasible g hb.1).mp hb.2
  obtain ⟨j, hj, hex⟩ := feasible_exchange g.lower_supermodular hla hlb
    (ha.1.trans hb.1.symm) hi
  have hd := (exchange_degree a i j (by omega)).trans ha.1
  exact ⟨j, hj, (mem_rankBases g _).mpr
    ⟨hd, (upperFeasible_iff_lowerFeasible g hd).mpr hex⟩⟩

theorem contains_rankBases_iff (g : RankFunction V) (a : Exponent V) :
    Contains (rankBases g) a ↔ LowerFeasible g.lower a := by
  constructor
  · rintro ⟨b, hb, hba⟩ U
    have hb := (mem_rankBases g b).mp hb
    exact ((upperFeasible_iff_lowerFeasible g hb.1).mp hb.2 U).trans
      (Finset.sum_le_sum (fun i _ => hba i))
  · intro ha
    obtain ⟨b, hba, hbdeg, hb⟩ := exists_lower_base_below g.lower_supermodular g.lower_empty
      g.lower_univ g.lower_le ha
    exact ⟨b, (mem_rankBases g b).mpr
      ⟨hbdeg, (upperFeasible_iff_lowerFeasible g hbdeg).mpr hb⟩, hba⟩

theorem rankBases_canonical (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) :
    rankBases (canonicalRank B hBne d hdeg hB) = B := by
  have htop : upperRank B Finset.univ = d := by
    obtain ⟨a, ha, he⟩ := upperRank_attained hBne Finset.univ
    simpa only [subsetSum_univ, hdeg a ha] using he.symm
  ext a
  rw [mem_rankBases, mem_iff_canonical_rank B hBne d hdeg hB]
  change (a.degree = upperRank B Finset.univ ∧ _) ↔ _
  rw [htop]
  rfl

def rankIdeal (k : Type*) [CommSemiring k] (g : RankFunction V) : Ideal (MvPolynomial V k) :=
  monomialIdeal k (rankBases g)

theorem monomial_mem_rankIdeal_iff (k : Type*) [CommSemiring k] [Nontrivial k]
    (g : RankFunction V) (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ rankIdeal k g ↔ LowerFeasible g.lower a := by
  rw [rankIdeal, monomial_mem_iff, contains_rankBases_iff]

end CommAlg.Polymatroid

end
end CheckedSource51

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "52: CommAlg.Polymatroid.FiniteMinimum\n"

/-! ## Source: CommAlg.Polymatroid.FiniteMinimum -/
section CheckedSource52

/-! # Exact minima of nonempty finite families of natural numbers -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def finiteMinimum (f : ι → ℕ) : ℕ :=
  univ.inf' univ_nonempty f

theorem finiteMinimum_le (f : ι → ℕ) (j : ι) : finiteMinimum f ≤ f j :=
  Finset.inf'_le _ (mem_univ j)

theorem le_finiteMinimum {f : ι → ℕ} {n : ℕ} (h : ∀ j, n ≤ f j) :
    n ≤ finiteMinimum f := Finset.le_inf' _ _ (fun j _ => h j)

theorem finiteMinimum_attained (f : ι → ℕ) : ∃ j, f j = finiteMinimum f := by
  obtain ⟨j, _, hj⟩ := (Finset.inf'_le_iff univ_nonempty).mp
    (le_rfl : finiteMinimum f ≤ finiteMinimum f)
  exact ⟨j, le_antisymm hj (finiteMinimum_le f j)⟩

theorem finiteMinimum_mono {f g : ι → ℕ} (h : ∀ j, f j ≤ g j) :
    finiteMinimum f ≤ finiteMinimum g := by
  obtain ⟨j, hj⟩ := finiteMinimum_attained g
  exact ((finiteMinimum_le f j).trans (h j)).trans_eq hj

theorem finiteMinimum_add_const (f : ι → ℕ) (n : ℕ) :
    finiteMinimum (fun j => n + f j) = n + finiteMinimum f := by
  obtain ⟨j, hj⟩ := finiteMinimum_attained f
  apply le_antisymm
  · exact (finiteMinimum_le (fun j => n + f j) j).trans_eq (congrArg (n + ·) hj)
  · exact le_finiteMinimum (fun j => Nat.add_le_add_left (finiteMinimum_le f j) n)

theorem finiteMinimum_min_left (f : ι → ℕ) (n : ℕ) :
    finiteMinimum (fun j => min n (f j)) = min n (finiteMinimum f) := by
  obtain ⟨j, hj⟩ := finiteMinimum_attained f
  apply le_antisymm
  · exact (finiteMinimum_le (fun j => min n (f j)) j).trans_eq (congrArg (min n) hj)
  · exact le_finiteMinimum (fun j => min_le_min_left n (finiteMinimum_le f j))

theorem le_finiteMinimum_iff (f : ι → ℕ) (n : ℕ) :
    n ≤ finiteMinimum f ↔ ∀ j, n ≤ f j :=
  ⟨fun h j => h.trans (finiteMinimum_le f j), le_finiteMinimum⟩

end CommAlg.Polymatroid

end
end CheckedSource52

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "53: CommAlg.Polymatroid.PartitionDefect\n"

/-! ## Source: CommAlg.Polymatroid.PartitionDefect -/
section CheckedSource53

/-! # Exact partition defects and the homological rank of twisted powers -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def partitionDefect (g : RankFunction V) {A : Finset V} (P : Finpartition A) : ℕ :=
  (∑ C ∈ P.parts, g C) - g A

def partitionSlack {A : Finset V} (P : Finpartition A) : ℕ := A.card - P.parts.card

theorem RankFunction.le_sum_partition (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) : g A ≤ ∑ C ∈ P.parts, g C := by
  simpa [P.biUnion_parts] using g.biUnion_marginal ∅ P.parts

theorem partitionDefect_add_rank (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) : partitionDefect g P + g A = ∑ C ∈ P.parts, g C :=
  Nat.sub_add_cancel (g.le_sum_partition P)

theorem partitionSlack_add_parts {A : Finset V} (P : Finpartition A) :
    partitionSlack P + P.parts.card = A.card := Nat.sub_add_cancel P.card_parts_le_card

theorem partitionDefect_add (g f : RankFunction V) {A : Finset V} (P : Finpartition A) :
    partitionDefect (g.add f) P = partitionDefect g P + partitionDefect f P := by
  have hg := partitionDefect_add_rank g P
  have hf := partitionDefect_add_rank f P
  have hgf := partitionDefect_add_rank (g.add f) P
  change partitionDefect (g.add f) P + (g A + f A) =
    ∑ C ∈ P.parts, (g C + f C) at hgf
  rw [Finset.sum_add_distrib] at hgf
  omega

theorem partitionDefect_scale (g : RankFunction V) (s : ℕ)
    {A : Finset V} (P : Finpartition A) :
    partitionDefect (RankFunction.scale s g) P = s * partitionDefect g P := by
  change (∑ C ∈ P.parts, s * g C) - s * g A = s * ((∑ C ∈ P.parts, g C) - g A)
  rw [← Finset.mul_sum, Nat.mul_sub_left_distrib]

theorem partitionCost_add_parts (g : RankFunction V) (hg : g.Active)
    {A : Finset V} (P : Finpartition A) :
    partitionCost g P + P.parts.card = ∑ C ∈ P.parts, g C := by
  have hp : ∀ C ∈ P.parts, (g C - 1) + 1 = g C := by
    intro C hC
    exact Nat.sub_add_cancel (hg C (P.nonempty_of_mem_parts hC))
  have hs := Finset.sum_congr rfl hp
  simpa [partitionCost, Finset.sum_add_distrib] using hs

theorem augmented_partition_cost (g : RankFunction V) (hg : g.Active)
    {A : Finset V} (P : Finpartition A) :
    A.card + partitionCost g P = g A + partitionDefect g P + partitionSlack P := by
  have hc := partitionCost_add_parts g hg P
  have hd := partitionDefect_add_rank g P
  have hs := partitionSlack_add_parts P
  omega

theorem augmentedPartitionRank_defect (g : RankFunction V) (hg : g.Active)
    (A : Finset V) :
    augmentedPartitionRank g A =
      g A + finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P) := by
  unfold augmentedPartitionRank
  change A.card + finiteMinimum (fun P : Finpartition A => partitionCost g P) = _
  rw [← finiteMinimum_add_const, ← finiteMinimum_add_const]
  congr 1
  funext P
  simpa only [Nat.add_assoc] using augmented_partition_cost g hg P

theorem homologicalRank_defect (g : RankFunction V) (hg : g.Active) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    homologicalRank g hg i A = g A +
      min i (finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P)) := by
  rw [homologicalRank_apply g hg i hA]
  change min (g A + i) (augmentedPartitionRank g A) = _
  rw [augmentedPartitionRank_defect g hg A, Nat.add_min_add_left]

def twistedPowerRank (η ρ : RankFunction V) (s : ℕ) : RankFunction V :=
  η.add (RankFunction.scale s ρ)

theorem twistedPowerRank_apply (η ρ : RankFunction V) (s : ℕ) (A : Finset V) :
    twistedPowerRank η ρ s A = η A + s * ρ A := rfl

theorem twistedPower_defect (η ρ : RankFunction V) (s : ℕ)
    {A : Finset V} (P : Finpartition A) :
    partitionDefect (twistedPowerRank η ρ s) P =
      s * partitionDefect ρ P + partitionDefect η P := by
  rw [twistedPowerRank, partitionDefect_add, partitionDefect_scale, Nat.add_comm]

/-- Formula (4.1), with arbitrary fixed twist and arbitrary finite ground set. -/
theorem twistedPower_homologicalRank (η ρ : RankFunction V) (s i : ℕ)
    (hg : (twistedPowerRank η ρ s).Active) {A : Finset V} (hA : A.Nonempty) :
    homologicalRank (twistedPowerRank η ρ s) hg i A =
      twistedPowerRank η ρ s A + min i
        (finiteMinimum (fun P : Finpartition A =>
          s * partitionDefect ρ P + partitionDefect η P + partitionSlack P)) := by
  rw [homologicalRank_defect _ hg i hA]
  simp only [twistedPower_defect]

end CommAlg.Polymatroid

end
end CheckedSource53

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "54: CommAlg.Polymatroid.UniformRank\n"

/-! ## Source: CommAlg.Polymatroid.UniformRank -/
section CheckedSource54

/-! # Uniform ranks and the singleton caps of homological ranks -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def RankFunction.truncate (g : RankFunction V) (d : ℕ) : RankFunction V where
  toFun A := min (g A) d
  empty := by simp
  monotone := fun A B h => min_le_min_right d (g.monotone h)
  submodular A B := by
    have hg := g.submodular A B
    have hiA := g.monotone (inter_subset_left : A ∩ B ⊆ A)
    have hiB := g.monotone (inter_subset_right : A ∩ B ⊆ B)
    omega

def cardinalRank (V : Type*) [DecidableEq V] : RankFunction V where
  toFun A := A.card
  empty := card_empty
  monotone := fun _ _ h => card_le_card h
  submodular A B := (card_union_add_card_inter A B).le

def uniformRank (V : Type*) [DecidableEq V] (d : ℕ) : RankFunction V :=
  (cardinalRank V).truncate d

@[simp] theorem uniformRank_apply (d : ℕ) (A : Finset V) :
    uniformRank V d A = min A.card d := rfl

def uniformPowerRank (V : Type*) [DecidableEq V] (d s : ℕ) : RankFunction V :=
  RankFunction.scale s (uniformRank V d)

@[simp] theorem uniformPowerRank_apply (d s : ℕ) (A : Finset V) :
    uniformPowerRank V d s A = s * min A.card d := rfl

theorem uniformPowerRank_active {d s : ℕ} (hd : 1 ≤ d) (hs : 1 ≤ s) :
    (uniformPowerRank V d s).Active := by
  intro A hA
  have hc : 1 ≤ A.card := card_pos.mpr hA
  have hm : 1 ≤ min A.card d := le_min hc hd
  change 1 ≤ s * min A.card d
  nlinarith

theorem RankFunction.le_sum_singletons (g : RankFunction V) (A : Finset V) :
    g A ≤ ∑ j ∈ A, g {j} := by
  simpa [Finpartition.parts_bot] using g.le_sum_partition (⊥ : Finpartition A)

theorem homologicalRank_singleton (g : RankFunction V) (hg : g.Active)
    (i : ℕ) (j : V) : homologicalRank g hg i {j} = g {j} := by
  have hD := partitionRank_le_single g (singleton_nonempty j)
  have hg1 := hg {j} (singleton_nonempty j)
  have hLo : g {j} ≤ augmentedPartitionRank g {j} :=
    RankFunction.le_of_dominates (augmentedRank_dominates g hg) {j}
  have hEq : augmentedPartitionRank g {j} = g {j} := by
    unfold augmentedPartitionRank at hLo ⊢
    simp only [card_singleton] at *
    omega
  rw [homologicalRank_apply g hg i (singleton_nonempty j)]
  change min (g {j} + i) (augmentedPartitionRank g {j}) = _
  rw [hEq, min_eq_right (Nat.le_add_right _ _)]

theorem homologicalRank_le_sum_singletons (g : RankFunction V) (hg : g.Active)
    (i : ℕ) (A : Finset V) : homologicalRank g hg i A ≤ ∑ j ∈ A, g {j} := by
  simpa only [homologicalRank_singleton] using (homologicalRank g hg i).le_sum_singletons A

@[simp] theorem subsetSum_constExponent (n : ℕ) (A : Finset V) :
    subsetSum (constExponent n : Exponent V) A = A.card * n := by
  simp [subsetSum]

@[simp] theorem degree_constExponent (n : ℕ) :
    (constExponent n : Exponent V).degree = Fintype.card V * n := by
  simp [Finsupp.degree_eq_sum]

/-- The bases of a scaled uniform rank are exactly the bounded exponent
vectors of the required total degree. This identifies the squarefree
Veronese family at `s=1` and all its powers at arbitrary `s`. -/
theorem isRankBase_uniformPower_iff (d s : ℕ) (hd : d ≤ Fintype.card V)
    (a : Exponent V) :
    IsRankBase (uniformPowerRank V d s) a ↔ a.degree = s * d ∧ ∀ j, a j ≤ s := by
  have htop : uniformPowerRank V d s univ = s * d := by simp [min_eq_right hd]
  constructor
  · rintro ⟨hdeg, hbound⟩
    refine ⟨hdeg.trans htop, fun j => ?_⟩
    have h := hbound {j}
    simp only [subsetSum, sum_singleton, uniformPowerRank_apply, card_singleton] at h
    have hm : min 1 d ≤ 1 := min_le_left _ _
    nlinarith
  · rintro ⟨hdeg, hcap⟩
    refine ⟨hdeg.trans htop.symm, fun A => ?_⟩
    have hc : subsetSum a A ≤ A.card * s := by
      simpa [subsetSum] using (Finset.sum_le_sum (s := A) (fun j _ => hcap j))
    have ht : subsetSum a A ≤ s * d := by
      have h := subsetSum_mono a (subset_univ A)
      simpa only [subsetSum_univ, hdeg] using h
    change subsetSum a A ≤ s * min A.card d
    rcases le_total A.card d with h | h
    · rw [min_eq_left h, Nat.mul_comm]
      exact hc
    · rwa [min_eq_right h]

end CommAlg.Polymatroid

end
end CheckedSource54

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "55: CommAlg.Polymatroid.UniversalRank\n"

/-! ## Source: CommAlg.Polymatroid.UniversalRank -/
section CheckedSource55

/-! # Homological ranks with all inactive coordinates retained

For every integral polymatroid rank `g`, the rank `g+|·|` is active. Its
Dilworth truncation is exactly

  u_g(A) = min over partitions P of A of Σ(C in P) (g(C)+|C|−1).

This is the same as `|A|+D_g(A)` with integer block costs, including zero
coordinates. On active ground sets it is proved equal to the earlier formula.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def cardinalLift (g : RankFunction V) : RankFunction V := g.add (cardinalRank V)

@[simp] theorem cardinalLift_apply (g : RankFunction V) (A : Finset V) :
    cardinalLift g A = g A + A.card := rfl

theorem cardinalLift_active (g : RankFunction V) : (cardinalLift g).Active := by
  intro A hA
  have hc := card_pos.mpr hA
  change 1 ≤ g A + A.card
  omega

def universalAugmentedRank (g : RankFunction V) : RankFunction V :=
  dilworthRank (cardinalLift g) (cardinalLift_active g)

@[simp] theorem universalAugmentedRank_apply (g : RankFunction V) (A : Finset V) :
    universalAugmentedRank g A = partitionRank (cardinalLift g) A := rfl

theorem universalAugmentedRank_dominates (g : RankFunction V) :
    (universalAugmentedRank g).Dominates g := by
  intro A B hAB
  have h := augmentedPartitionRank_marginal (cardinalLift g) (cardinalLift_active g) hAB
  simp only [cardinalLift_apply, augmentedPartitionRank] at h
  change g B + partitionRank (cardinalLift g) A ≤ partitionRank (cardinalLift g) B + g A
  omega

def universalHomologicalRank (g : RankFunction V) (i : ℕ) : RankFunction V :=
  g.interpolate (universalAugmentedRank g) (universalAugmentedRank_dominates g) i

@[simp] theorem universalHomologicalRank_empty (g : RankFunction V) (i : ℕ) :
    universalHomologicalRank g i ∅ = 0 := RankFunction.map_empty _

theorem universalHomologicalRank_apply (g : RankFunction V) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    universalHomologicalRank g i A = min (g A + i) (universalAugmentedRank g A) := by
  simp [universalHomologicalRank, RankFunction.interpolate_apply, shiftRankValue, hA.ne_empty]

theorem universalHomologicalRank_le_add (g : RankFunction V) (i : ℕ) (A : Finset V) :
    universalHomologicalRank g i A ≤ g A + i :=
  shiftRankValue_le_add g (universalAugmentedRank g) i A

/-- The cost identity also justifies the integer-partition interpretation
when some original rank values vanish. -/
theorem cardinalLift_cost_add_parts (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) :
    partitionCost (cardinalLift g) P + P.parts.card = A.card + ∑ C ∈ P.parts, g C := by
  have h := partitionCost_add_parts (cardinalLift g) (cardinalLift_active g) P
  simpa only [cardinalLift_apply, Finset.sum_add_distrib, P.sum_card_parts, Nat.add_comm] using h

theorem cardinalLift_cost_of_active (g : RankFunction V) (hg : g.Active)
    {A : Finset V} (P : Finpartition A) :
    partitionCost (cardinalLift g) P = A.card + partitionCost g P := by
  have h1 := cardinalLift_cost_add_parts g P
  have h2 := partitionCost_add_parts g hg P
  omega

/-- The universal rank is exactly the original active-ground-set formula. -/
theorem universalAugmentedRank_eq_active (g : RankFunction V) (hg : g.Active)
    (A : Finset V) : universalAugmentedRank g A = augmentedPartitionRank g A := by
  change finiteMinimum (fun P : Finpartition A => partitionCost (cardinalLift g) P) =
    A.card + finiteMinimum (fun P : Finpartition A => partitionCost g P)
  rw [← finiteMinimum_add_const]
  congr 1
  funext P
  exact cardinalLift_cost_of_active g hg P

theorem universalHomologicalRank_eq_active (g : RankFunction V) (hg : g.Active)
    (i : ℕ) (A : Finset V) : universalHomologicalRank g i A = homologicalRank g hg i A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hne := Finset.nonempty_iff_ne_empty.mpr hA
  rw [universalHomologicalRank_apply g i hne, homologicalRank_apply g hg i hne,
    universalAugmentedRank_eq_active g hg A]
  rfl

/-- Every simultaneous deletion inequality is equivalent to the upper
inequalities of the universal partition rank, with no activity assumption. -/
theorem universal_bounds_iff (g : RankFunction V) (a : Exponent V) :
    (∀ A, A.Nonempty → subsetSum a A ≤ g A + A.card - 1) ↔
      (∀ A, subsetSum a A ≤ universalAugmentedRank g A) := by
  exact nonempty_bounds_iff_partition_bounds (cardinalLift g) a

theorem universalAugmentedRank_le_cost (g : RankFunction V) {A : Finset V}
    (P : Finpartition A) : universalAugmentedRank g A ≤ partitionCost (cardinalLift g) P :=
  partitionRank_le _ P

theorem universalAugmentedRank_attained (g : RankFunction V) (A : Finset V) :
    ∃ P : Finpartition A, partitionCost (cardinalLift g) P = universalAugmentedRank g A :=
  partitionRank_attained _ A

end CommAlg.Polymatroid

end
end CheckedSource55

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "56: CommAlg.Polymatroid.KoszulRankUniversal\n"

/-! ## Source: CommAlg.Polymatroid.KoszulRankUniversal -/
section CheckedSource56

/-!
# The Koszul rank criterion with arbitrary loops and zero rank

The actual rank/coloop criterion is first expressed by support-sensitive
indicator inequalities. These are equivalent to inequalities on the original
exponent using `g(A) + |A| - 1`, without assuming active variables.
-/

noncomputable section

open scoped Matroid

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem supportPred_indicator_bounds_iff_lift (g : RankFunction V) (a : Exponent V) :
    (∀ j ∈ a.support, ∀ A,
      subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A) ↔
      (∀ A, A.Nonempty → subsetSum a A ≤ g A + A.card - 1) := by
  constructor
  · intro h A hA
    by_cases hW : (A ∩ a.support).Nonempty
    · obtain ⟨j, hj⟩ := hW
      obtain ⟨hjA, hjS⟩ := mem_inter.mp hj
      have hb := h j hjS A
      rw [if_pos hjA] at hb
      have he := subsetSum_supportPred a A
      have hc := card_le_card (inter_subset_left : A ∩ a.support ⊆ A)
      omega
    · have he := subsetSum_support_inter a A
      rw [not_nonempty_iff_eq_empty.mp hW, subsetSum_empty] at he
      omega
  · intro h j hj A
    by_cases hW : (A ∩ a.support).Nonempty
    · have hb := h (A ∩ a.support) hW
      have he := subsetSum_supportPred a (A ∩ a.support)
      rw [inter_eq_left.mpr inter_subset_right, subsetSum_supportPred_inter] at he
      have hg := g.monotone (inter_subset_left : A ∩ a.support ⊆ A)
      have hc : 1 ≤ (A ∩ a.support).card := card_pos.mpr hW
      split_ifs <;> omega
    · have hEmpty : A ∩ a.support = ∅ := not_nonempty_iff_eq_empty.mp hW
      have he := subsetSum_supportPred_inter a A
      rw [hEmpty, subsetSum_empty] at he
      have hjA : j ∉ A := by
        intro hjA
        have hjW := mem_inter.mpr ⟨hjA, hj⟩
        rw [hEmpty] at hjW
        exact notMem_empty j hjW
      rw [if_neg hjA]
      omega

/-- The rank and no-coloop criterion remains exact when some variables are
loops, the rank is zero, or the support is empty. -/
theorem koszulConstraint_rank_and_noColoops_iff_indicator (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ j ∈ a.support, ∀ A,
        subsetSum (supportPred a) A + (if j ∈ A then 1 else 0) ≤ g A := by
  by_cases hSupport : a.support.Nonempty
  · let M := koszulConstraintMatroid g a ha
    have hRank := koszulConstraint_rank_le g ha hDegree
    have hGround : M.E.Nonempty := by
      simpa only [M, koszulConstraintMatroid_ground, Finset.coe_nonempty] using hSupport
    have hDelete := CommAlg.Matroid.rank_eq_and_noColoops_iff_delete_rank M i hGround hRank
    have hStep : (CommAlg.Matroid.rank M = i ∧ CommAlg.Matroid.NoColoops M) ↔
        ∀ j ∈ a.support, ∀ U,
          i ≤ deletionSlack g a U + ((a.support.erase j) \ U).card := by
      rw [hDelete]
      constructor
      · intro h j hj
        apply (le_koszulConstraint_delete_rank g a ha j i).mp
        exact le_of_eq (h j hj).symm
      · intro h j hj
        have hLower := (le_koszulConstraint_delete_rank g a ha j i).mpr (h j hj)
        have hUpper := (CommAlg.Matroid.rank_delete_le M ({j} : Set V)).trans hRank
        exact Nat.le_antisymm hUpper hLower
    exact hStep.trans (all_deletion_costs_ge_iff g ha hDegree)
  · have hEmpty : a.support = ∅ := not_nonempty_iff_eq_empty.mp hSupport
    have ha0 : a = 0 := Finsupp.support_eq_empty.mp hEmpty
    have hi : i = 0 := by
      have hz : a.degree = 0 := by simp [ha0]
      omega
    have hRank := koszulConstraint_rank_le g ha hDegree
    have hNo : CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha) := by
      intro j hj
      have hjg := hj.mem_ground
      simpa only [koszulConstraintMatroid_ground, hEmpty, coe_empty,
        Set.mem_empty_iff_false] using hjg
    constructor
    · intro _ j hj
      simp [hEmpty] at hj
    · intro _
      exact ⟨by omega, hNo⟩

theorem koszulConstraint_rank_and_noColoops_iff_lift (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, A.Nonempty → subsetSum a A ≤ g A + A.card - 1 :=
  (koszulConstraint_rank_and_noColoops_iff_indicator g ha hDegree).trans
    (supportPred_indicator_bounds_iff_lift g a)

theorem koszulConstraint_rank_and_noColoops_iff_universal (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    (CommAlg.Matroid.rank (koszulConstraintMatroid g a ha) = i ∧
      CommAlg.Matroid.NoColoops (koszulConstraintMatroid g a ha)) ↔
      ∀ A, subsetSum a A ≤ universalAugmentedRank g A :=
  (koszulConstraint_rank_and_noColoops_iff_lift g ha hDegree).trans
    (universal_bounds_iff g a)

section Homology

variable [LinearOrder V] {k : Type*} [CommRing k] [Nontrivial k]

/-- The genuine chain-homology criterion, including all loop and zero-rank
cases, without an active-variable hypothesis. -/
theorem koszulConstraint_nonzeroHomology_iff_universal (g : RankFunction V)
    {a : Exponent V} {i : ℕ} (ha : LowerFeasible g.lower a)
    (hDegree : a.degree = g univ + i) :
    CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i ↔
      ∀ A, subsetSum a A ≤ universalAugmentedRank g A := by
  rw [CommAlg.Matroid.independence_nonzeroHomology_iff]
  have h := koszulConstraint_rank_and_noColoops_iff_universal g ha hDegree
  rw [eq_comm] at h
  exact h

/-- Complete degree and inequality characterization of actual nonvanishing,
valid for an arbitrary normalized monotone submodular rank. -/
theorem koszulConstraint_nonzeroHomology_iff_universal_full (g : RankFunction V)
    {a : Exponent V} (ha : LowerFeasible g.lower a) (i : ℕ) :
    CommAlg.Simplicial.NonzeroHomology (k := k)
      (CommAlg.Matroid.independenceFaces (koszulConstraintMatroid g a ha)) i ↔
      a.degree = g univ + i ∧ ∀ A, subsetSum a A ≤ universalAugmentedRank g A := by
  constructor
  · intro h
    have hDegree := koszulConstraint_nonzeroHomology_degree g ha h
    exact ⟨hDegree, (koszulConstraint_nonzeroHomology_iff_universal g ha hDegree).mp h⟩
  · rintro ⟨hDegree, hBounds⟩
    exact (koszulConstraint_nonzeroHomology_iff_universal g ha hDegree).mpr hBounds

end Homology

end CommAlg.Polymatroid

end
end CheckedSource56

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "57: CommAlg.Polymatroid.RankGreedy\n"

/-! ## Source: CommAlg.Polymatroid.RankGreedy -/
section CheckedSource57

/-! # Base extension and recovery of every canonical rank value -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def UpperTight (g : RankFunction V) (a : Exponent V) (U : Finset V) : Prop :=
  subsetSum a U = g U

theorem upper_tight_union_inter (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) {U W : Finset V}
    (hU : UpperTight g a U) (hW : UpperTight g a W) :
    UpperTight g a (U ∪ W) ∧ UpperTight g a (U ∩ W) := by
  have hm := subsetSum_union_inter a U W
  have hs := g.submodular U W
  have h1 := ha (U ∪ W)
  have h2 := ha (U ∩ W)
  unfold UpperTight at *
  omega

theorem upper_failed_increment (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) (i : V) (hbad : ¬ UpperFeasible g (a + Finsupp.single i 1)) :
    ∃ U, UpperTight g a U ∧ i ∈ U := by
  simp only [UpperFeasible, not_forall, not_le] at hbad
  obtain ⟨U, hU⟩ := hbad
  have hs : subsetSum (a + Finsupp.single i 1) U =
      subsetSum a U + (if i ∈ U then 1 else 0) := by
    rw [subsetSum_add]
    simp [subsetSum, Finsupp.single_apply]
  have hf := ha U
  have hiU : i ∈ U := by
    by_contra h
    rw [if_neg h] at hs
    omega
  rw [if_pos hiU] at hs
  exact ⟨U, by unfold UpperTight; omega, hiU⟩

theorem upper_tight_cover (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) (D : Finset V)
    (h : ∀ i ∈ D, ∃ U, UpperTight g a U ∧ i ∈ U) :
    ∃ U, UpperTight g a U ∧ D ⊆ U := by
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, by simp [UpperTight], Finset.empty_subset _⟩
  | @insert i D hi ih =>
    obtain ⟨U, hU, hDU⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨W, hW, hiW⟩ := h i (Finset.mem_insert_self _ _)
    exact ⟨U ∪ W, (upper_tight_union_inter g ha hU hW).1,
      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hiW,
        hDU.trans Finset.subset_union_left⟩⟩

theorem upperFeasible_le_const (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) : a ≤ constExponent (g Finset.univ) := by
  intro i
  have hi := ha {i}
  simp only [subsetSum, Finset.sum_singleton] at hi
  exact hi.trans (g.monotone (Finset.subset_univ _))

theorem exists_rankBase_above (g : RankFunction V) {a : Exponent V}
    (ha : UpperFeasible g a) : ∃ b, a ≤ b ∧ IsRankBase g b := by
  let T : Set (Exponent V) := {b | a ≤ b ∧ UpperFeasible g b}
  have hfin : T.Finite := (Set.finite_Iic (constExponent (g Finset.univ))).subset
    (fun _ h => upperFeasible_le_const g h.2)
  obtain ⟨b, hb, hmax⟩ := hfin.exists_maximal ⟨a, le_rfl, ha⟩
  have hcover : ∀ i ∈ (Finset.univ : Finset V), ∃ U, UpperTight g b U ∧ i ∈ U := by
    intro i hi
    apply upper_failed_increment g hb.2 i
    intro hgood
    have hmem : b + Finsupp.single i 1 ∈ T := ⟨hb.1.trans (le_add_right le_rfl), hgood⟩
    have hle := hmax hmem (le_add_right le_rfl)
    have hc := hle i
    simp at hc
  obtain ⟨U, hU, hfull⟩ := upper_tight_cover g hb.2 Finset.univ hcover
  have he : U = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ _) hfull
  have hdeg : b.degree = g Finset.univ := by
    simpa only [UpperTight, he, subsetSum_univ] using hU
  exact ⟨b, hb.1, hdeg, hb.2⟩

def RankFunction.restrict (g : RankFunction V) (A : Finset V) : RankFunction V where
  toFun U := g (U ∩ A)
  empty := by simp
  monotone := by
    intro U W hUW
    apply g.monotone
    exact Finset.inter_subset_inter_right hUW
  submodular := by
    intro U W
    have hu : (U ∪ W) ∩ A = (U ∩ A) ∪ (W ∩ A) := by ext x; simp; tauto
    have hi : (U ∩ W) ∩ A = (U ∩ A) ∩ (W ∩ A) := by ext x; simp <;> tauto
    rw [hu, hi]
    exact g.submodular _ _

/-- Every individual upper bound is attained by an integer base. -/
theorem exists_rankBase_attaining (g : RankFunction V) (U : Finset V) :
    ∃ a, IsRankBase g a ∧ subsetSum a U = g U := by
  obtain ⟨b, hb⟩ := rankBases_nonempty (g.restrict U)
  have hb := (mem_rankBases _ b).mp hb
  have hbU : project U b = b := by
    ext i
    by_cases hi : i ∈ U
    · simp [hi]
    · have hs := hb.2 {i}
      have he : ({i} : Finset V) ∩ U = ∅ := by ext j; simp; aesop
      change subsetSum b {i} ≤ g ({i} ∩ U) at hs
      simp only [subsetSum, Finset.sum_singleton, he, RankFunction.map_empty] at hs
      have hzero : b i = 0 := Nat.eq_zero_of_le_zero hs
      simp [hi, hzero]
  have hbdeg : b.degree = g U := by
    simpa only [RankFunction.restrict, Finset.univ_inter] using hb.1
  have hbupper : UpperFeasible g b := by
    intro W
    exact (hb.2 W).trans (g.monotone Finset.inter_subset_left)
  obtain ⟨a, hba, ha⟩ := exists_rankBase_above g hbupper
  have hsum : subsetSum b U = g U := by rw [← degree_project, hbU, hbdeg]
  have hsumle : subsetSum b U ≤ subsetSum a U := Finset.sum_le_sum (fun i _ => hba i)
  exact ⟨a, ha, Nat.le_antisymm (ha.2 U) (hsum ▸ hsumle)⟩

@[simp] theorem upperRank_rankBases (g : RankFunction V) (U : Finset V) :
    upperRank (rankBases g) U = g U := by
  apply le_antisymm
  · apply Finset.sup_le
    intro a ha
    exact ((mem_rankBases g a).mp ha).2 U
  · obtain ⟨a, ha, hU⟩ := exists_rankBase_attaining g U
    rw [← hU]
    exact le_upperRank ((mem_rankBases g a).mpr ha) U

theorem rankBases_injective : Function.Injective (rankBases (V := V)) := by
  intro g h he
  cases g with | mk g g0 gm gs =>
    cases h with | mk h h0 hm hs =>
      congr 1
      funext U
      have hg := upperRank_rankBases (RankFunction.mk g g0 gm gs) U
      have hh := upperRank_rankBases (RankFunction.mk h h0 hm hs) U
      rw [he] at hg
      exact hg.symm.trans hh

end CommAlg.Polymatroid

end
end CheckedSource57

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "58: CommAlg.Polymatroid.RankShiftFormula\n"

/-! ## Source: CommAlg.Polymatroid.RankShiftFormula -/
section CheckedSource58

/-! # The right-hand side of the homological-shift rank formula

`rankShiftIdeal` is the explicitly described ideal on the right-hand side of
Theorem 1.2. It is not a definition of a homological shift: the separate
graded-Tor theorem proves that the genuine homological shift equals it.
This module proves its exact monomial membership and all partition inequalities,
including inactive variables and the unit rank.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def rankShiftFamily (g : RankFunction V) (i : ℕ) : Family V :=
  if universalHomologicalRank g i univ = g univ + i then
    rankBases (universalHomologicalRank g i) else ∅

def rankShiftIdeal (k : Type*) [CommSemiring k] (g : RankFunction V) (i : ℕ) :
    Ideal (MvPolynomial V k) :=
  if universalHomologicalRank g i univ = g univ + i then
    rankIdeal k (universalHomologicalRank g i) else ⊥

theorem rankShiftIdeal_eq_monomialIdeal (k : Type*) [CommSemiring k]
    (g : RankFunction V) (i : ℕ) :
    rankShiftIdeal k g i = monomialIdeal k (rankShiftFamily g i) := by
  unfold rankShiftIdeal rankShiftFamily
  split_ifs
  · rfl
  · simp [monomialIdeal]

theorem rankShiftFamily_nonempty_iff (g : RankFunction V) (i : ℕ) :
    (rankShiftFamily g i).Nonempty ↔ universalHomologicalRank g i univ = g univ + i := by
  unfold rankShiftFamily
  split_ifs with h
  · simp [h, rankBases_nonempty]
  · simp [h]

theorem rankShiftFamily_equigenerated (g : RankFunction V) (i : ℕ) :
    Equigenerated (rankShiftFamily g i) (g univ + i) := by
  intro a ha
  unfold rankShiftFamily at ha
  split_ifs at ha with h
  · exact ((mem_rankBases _ a).mp ha).1.trans h
  · simp at ha

theorem mem_rankShiftFamily_iff (g : RankFunction V) (i : ℕ) (a : Exponent V) :
    a ∈ rankShiftFamily g i ↔
      a.degree = g univ + i ∧ UpperFeasible (universalHomologicalRank g i) a := by
  by_cases h : universalHomologicalRank g i univ = g univ + i
  · simp [rankShiftFamily, h, mem_rankBases, IsRankBase]
  · have hle := universalHomologicalRank_le_add g i univ
    simp only [rankShiftFamily, if_neg h, notMem_empty, false_iff, not_and]
    intro hdeg hbound
    have hb := hbound univ
    rw [subsetSum_univ, hdeg] at hb
    omega

theorem rankShiftFamily_polymatroidal (g : RankFunction V) (i : ℕ) :
    IsPolymatroidal (rankShiftFamily g i) := by
  unfold rankShiftFamily
  split_ifs
  · exact rankBases_polymatroidal _
  · exact ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩

theorem rankShiftFamily_upperRank (g : RankFunction V) (i : ℕ)
    (h : (rankShiftFamily g i).Nonempty) (A : Finset V) :
    upperRank (rankShiftFamily g i) A = universalHomologicalRank g i A := by
  rw [rankShiftFamily, if_pos ((rankShiftFamily_nonempty_iff g i).mp h)]
  exact upperRank_rankBases _ A

section Ideals

variable {k : Type*} [CommSemiring k] [Nontrivial k]

theorem monomial_mem_rankShiftIdeal_iff (g : RankFunction V) (i : ℕ) (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i ↔
      ∀ A, g univ + i ≤ subsetSum a Aᶜ + universalHomologicalRank g i A := by
  by_cases h : universalHomologicalRank g i univ = g univ + i
  · rw [rankShiftIdeal, if_pos h, monomial_mem_rankIdeal_iff]
    constructor
    · intro hb A
      have hB := hb Aᶜ
      have hL := (universalHomologicalRank g i).lower_add_compl Aᶜ
      simp only [compl_compl, h] at hL
      omega
    · intro hb U
      have hB := hb Uᶜ
      have hL := (universalHomologicalRank g i).lower_add_compl U
      simp only [compl_compl] at hB
      rw [h] at hL
      omega
  · rw [rankShiftIdeal, if_neg h]
    constructor
    · intro hb
      have : False := by simpa using hb
      exact this.elim
    · intro hb
      have hB := hb univ
      simp only [compl_univ, subsetSum_empty, Nat.zero_add] at hB
      have hU := universalHomologicalRank_le_add g i univ
      omega

/-- Exact expanded membership, valid even when the indicated shift is zero.
Every block is nonempty because `P` is an actual `Finpartition A`. -/
theorem monomial_mem_rankShiftIdeal_partition_iff (g : RankFunction V) (i : ℕ)
    (a : Exponent V) :
    MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i ↔
      g univ + i ≤ a.degree ∧ LowerFeasible g.lower a ∧
        ∀ A, A.Nonempty → ∀ P : Finpartition A,
          g univ + i + P.parts.card ≤ subsetSum a Aᶜ + A.card + ∑ C ∈ P.parts, g C := by
  rw [monomial_mem_rankShiftIdeal_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa using h ∅
    · intro U
      have hb := h Uᶜ
      have hR := universalHomologicalRank_le_add g i Uᶜ
      have hL := g.lower_add_compl U
      simp only [compl_compl] at hb
      omega
    · intro A hA P
      have hb := h A
      have hR : universalHomologicalRank g i A ≤ universalAugmentedRank g A :=
        shiftRankValue_le_u g (universalAugmentedRank g) i A
      have hP := universalAugmentedRank_le_cost g P
      have hCost := cardinalLift_cost_add_parts g P
      omega
  · rintro ⟨hdeg, hLower, hParts⟩ A
    by_cases hA : A = ∅
    · simpa [hA] using hdeg
    have hA' := Finset.nonempty_iff_ne_empty.mpr hA
    have hL := hLower Aᶜ
    have hLC := g.lower_add_compl Aᶜ
    simp only [compl_compl] at hLC
    obtain ⟨P, hP⟩ := universalAugmentedRank_attained g A
    have hPart := hParts A hA' P
    have hCost := cardinalLift_cost_add_parts g P
    rw [hP] at hCost
    rw [universalHomologicalRank_apply g i hA']
    omega

theorem mem_rankShiftIdeal_iff_coeff (g : RankFunction V) (i : ℕ)
    (f : MvPolynomial V k) :
    f ∈ rankShiftIdeal k g i ↔
      ∀ a ∈ f.support, MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i := by
  simp_rw [rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
  exact mem_monomialIdeal_iff _ _

theorem rankShiftIdeal_le_rankIdeal (g : RankFunction V) (i : ℕ) :
    rankShiftIdeal k g i ≤ rankIdeal k g := by
  intro f hf
  apply (mem_monomialIdeal_iff (rankBases g) f).mpr
  intro a ha
  have hmon := (mem_rankShiftIdeal_iff_coeff g i f).mp hf a ha
  exact (contains_rankBases_iff g a).mpr
    ((monomial_mem_rankShiftIdeal_partition_iff g i a).mp hmon).2.1

end Ideals

end CommAlg.Polymatroid

end
end CheckedSource58

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "59: CommAlg.Polymatroid.KoszulRankFormula\n"

/-! ## Source: CommAlg.Polymatroid.KoszulRankFormula -/
section CheckedSource59

/-! # The full rank formula for the actual upper Koszul complex

Every degree and every normalized monotone submodular rank is included.
The subsequent derived-Tor theorem transports this exact statement to
the homological shift ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

theorem mem_rankShiftFamily_iff_lower (g : RankFunction V) (i : ℕ) (a : Exponent V) :
    a ∈ rankShiftFamily g i ↔ a.degree = g univ + i ∧
      LowerFeasible g.lower a ∧ UpperFeasible (universalAugmentedRank g) a := by
  rw [mem_rankShiftFamily_iff]
  constructor
  · rintro ⟨hdeg, hb⟩
    refine ⟨hdeg, ?_, ?_⟩
    · intro U
      have hcomp := hb Uᶜ
      have hR := universalHomologicalRank_le_add g i Uᶜ
      have hL := g.lower_add_compl U
      have hS := subsetSum_add_compl a U
      omega
    · intro A
      exact (hb A).trans (shiftRankValue_le_u g (universalAugmentedRank g) i A)
  · rintro ⟨hdeg, hLower, hUpper⟩
    refine ⟨hdeg, ?_⟩
    intro A
    by_cases hA : A = ∅
    · simp [hA]
    rw [universalHomologicalRank_apply g i (Finset.nonempty_iff_ne_empty.mpr hA)]
    apply le_min
    · have hcomp := hLower Aᶜ
      have hL := g.lower_add_compl Aᶜ
      have hS := subsetSum_add_compl a A
      simp only [compl_compl] at hL
      omega
    · exact hUpper A

section Homology

variable {k : Type*} [CommRing k] [Nontrivial k]

theorem koszulFaces_nonzeroHomology_iff_rankShiftFamily
    (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Simplicial.NonzeroHomology (k := k) (Koszul.koszulFaces (rankBases g) a) i ↔
      a ∈ rankShiftFamily g i := by
  by_cases ha : Contains (rankBases g) a
  · have hLower := (contains_rankBases_iff g a).mp ha
    rw [Koszul.koszulFaces_eq_independenceFaces (rankBases g) g
      (contains_rankBases_iff g) a hLower,
      koszulConstraint_nonzeroHomology_iff_universal_full g hLower i,
      mem_rankShiftFamily_iff_lower]
    simp only [hLower, true_and]
    rfl
  · have hn : ¬ Simplicial.NonzeroHomology (k := k)
        (Koszul.koszulFaces (rankBases g) a) i := by
      rw [Simplicial.nonzeroHomology_iff_not_exactIn]
      apply not_not.mpr
      apply Simplicial.exactIn_of_no_face
      intro s hs
      exact (ha (Koszul.koszulFaces_contains hs)).elim
    have hm : a ∉ rankShiftFamily g i := by
      intro hm
      exact ha ((contains_rankBases_iff g a).mpr
        ((mem_rankShiftFamily_iff_lower g i a).mp hm).2.1)
    simp only [hn, hm]

end Homology

end CommAlg.Polymatroid

end
end CheckedSource59

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "60: CommAlg.Polymatroid.IntegerSandwich\n"

/-! ## Source: CommAlg.Polymatroid.IntegerSandwich -/
section CheckedSource60

/-! # Integral submodular / supermodular sandwich

An elementary coordinate-elimination proof, including integrality, supplies
the integer decomposition theorem needed for products of polymatroid ideals.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [DecidableEq V]

theorem integer_sandwich_on (E : Finset V) :
    ∀ (p q : Finset V → ℤ), p ∅ = 0 → q ∅ = 0 →
      (∀ A, A ⊆ E → ∀ B, B ⊆ E → p A + p B ≤ p (A ∪ B) + p (A ∩ B)) →
      (∀ A, A ⊆ E → ∀ B, B ⊆ E → q (A ∪ B) + q (A ∩ B) ≤ q A + q B) →
      (∀ A, A ⊆ E → p A ≤ q A) →
      ∃ b : V → ℤ, (∀ i, i ∉ E → b i = 0) ∧
        ∀ A, A ⊆ E → p A ≤ ∑ i ∈ A, b i ∧ (∑ i ∈ A, b i) ≤ q A := by
  induction E using Finset.induction_on with
  | empty =>
    intro p q hp0 hq0 hp hq hpq
    refine ⟨fun _ => 0, by simp, ?_⟩
    intro A hA
    have he : A = ∅ := Finset.subset_empty.mp hA
    simp [he, hp0, hq0]
  | @insert i E hi ih =>
    intro p q hp0 hq0 hp hq hpq
    have hpow : E.powerset.Nonempty := ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩
    let t : ℤ := E.powerset.sup' hpow (fun A => p (insert i A) - q A)
    have htL : ∀ A, A ⊆ E → p (insert i A) - q A ≤ t := by
      intro A hA
      exact Finset.le_sup' (fun A => p (insert i A) - q A) (Finset.mem_powerset.mpr hA)
    have htR : ∀ B, B ⊆ E → t ≤ q (insert i B) - p B := by
      intro B hB
      apply Finset.sup'_le hpow _
      intro A hA
      have hA := Finset.mem_powerset.mp hA
      have hiA : i ∉ A := fun h => hi (hA h)
      have hiB : i ∉ B := fun h => hi (hB h)
      have hps := hp (insert i A) (Finset.insert_subset_insert i hA) B
        (hB.trans (Finset.subset_insert _ _))
      have hqs := hq A (hA.trans (Finset.subset_insert _ _)) (insert i B)
        (Finset.insert_subset_insert i hB)
      have hu := hpq (insert i (A ∪ B)) (Finset.insert_subset_insert i (Finset.union_subset hA hB))
      have hin := hpq (A ∩ B) ((Finset.inter_subset_left.trans hA).trans (Finset.subset_insert _ _))
      simp only [Finset.insert_union, Finset.union_insert,
        Finset.insert_inter_of_notMem hiB, Finset.inter_insert_of_notMem hiA] at hps hqs
      omega
    have htiL := htL ∅ (Finset.empty_subset E)
    have htiR := htR ∅ (Finset.empty_subset E)
    simp only [hp0, hq0, sub_zero] at htiL htiR
    let p' : Finset V → ℤ := fun A => max (p A) (p (insert i A) - t)
    let q' : Finset V → ℤ := fun A => min (q A) (q (insert i A) - t)
    have hp0' : p' ∅ = 0 := by
      change max (p ∅) (p (insert i ∅) - t) = 0
      rw [hp0]
      exact max_eq_left (by omega)
    have hq0' : q' ∅ = 0 := by
      change min (q ∅) (q (insert i ∅) - t) = 0
      rw [hq0]
      exact min_eq_left (by omega)
    have hp' : ∀ A, A ⊆ E → ∀ B, B ⊆ E →
        p' A + p' B ≤ p' (A ∪ B) + p' (A ∩ B) := by
      intro A hA B hB
      have hiA : i ∉ A := fun h => hi (hA h)
      have hiB : i ∉ B := fun h => hi (hB h)
      have hAE : A ⊆ insert i E := hA.trans (Finset.subset_insert _ _)
      have hBE : B ⊆ insert i E := hB.trans (Finset.subset_insert _ _)
      have hAiE := Finset.insert_subset_insert (a := i) hA
      have hBiE := Finset.insert_subset_insert (a := i) hB
      have h00 := hp A hAE B hBE
      have h10 := hp (insert i A) hAiE B hBE
      have h01 := hp A hAE (insert i B) hBiE
      have h11 := hp (insert i A) hAiE (insert i B) hBiE
      have hii : insert i A ∩ insert i B = insert i (A ∩ B) := by ext x; simp; tauto
      simp only [Finset.insert_union, Finset.union_insert, Finset.insert_idem, hii,
        Finset.insert_inter_of_notMem hiB, Finset.inter_insert_of_notMem hiA] at h10 h01 h11
      dsimp [p']
      omega
    have hq' : ∀ A, A ⊆ E → ∀ B, B ⊆ E →
        q' (A ∪ B) + q' (A ∩ B) ≤ q' A + q' B := by
      intro A hA B hB
      have hiA : i ∉ A := fun h => hi (hA h)
      have hiB : i ∉ B := fun h => hi (hB h)
      have hAE : A ⊆ insert i E := hA.trans (Finset.subset_insert _ _)
      have hBE : B ⊆ insert i E := hB.trans (Finset.subset_insert _ _)
      have hAiE := Finset.insert_subset_insert (a := i) hA
      have hBiE := Finset.insert_subset_insert (a := i) hB
      have h00 := hq A hAE B hBE
      have h10 := hq (insert i A) hAiE B hBE
      have h01 := hq A hAE (insert i B) hBiE
      have h11 := hq (insert i A) hAiE (insert i B) hBiE
      have hii : insert i A ∩ insert i B = insert i (A ∩ B) := by ext x; simp; tauto
      simp only [Finset.insert_union, Finset.union_insert, Finset.insert_idem, hii,
        Finset.insert_inter_of_notMem hiB, Finset.inter_insert_of_notMem hiA] at h10 h01 h11
      dsimp [q']
      omega
    have hpq' : ∀ A, A ⊆ E → p' A ≤ q' A := by
      intro A hA
      have h0 := hpq A (hA.trans (Finset.subset_insert _ _))
      have h1 := hpq (insert i A) (Finset.insert_subset_insert i hA)
      have hL := htL A hA
      have hR := htR A hA
      dsimp [p', q']
      omega
    obtain ⟨b, hb0, hb⟩ := ih p' q' hp0' hq0' hp' hq' hpq'
    let b' := Function.update b i t
    have hsum : ∀ A, i ∉ A → (∑ j ∈ A, b' j) = ∑ j ∈ A, b j := by
      intro A hiA
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := fun he => hiA (he ▸ hj)
      simp [b', Function.update_of_ne hji]
    refine ⟨b', ?_, ?_⟩
    · intro j hj
      have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self _ _)
      have hjE : j ∉ E := fun h => hj (Finset.mem_insert_of_mem h)
      simp [b', Function.update_of_ne hji, hb0 j hjE]
    · intro A hA
      by_cases hiA : i ∈ A
      · let A' := A.erase i
        have hA'E : A' ⊆ E := by
          intro j hj
          obtain ⟨hji, hjA⟩ := Finset.mem_erase.mp hj
          exact (Finset.mem_insert.mp (hA hjA)).resolve_left hji
        have hAi : insert i A' = A := Finset.insert_erase hiA
        have hbA := hb A' hA'E
        have hsumA : (∑ j ∈ A, b' j) = t + ∑ j ∈ A', b j := by
          rw [← hAi, Finset.sum_insert (Finset.notMem_erase _ _), hsum A' (Finset.notMem_erase _ _)]
          simp [b']
        have hpl : p (insert i A') - t ≤ p' A' := le_max_right _ _
        have hqu : q' A' ≤ q (insert i A') - t := min_le_right _ _
        rw [hAi] at hpl hqu
        rw [hsumA]
        omega
      · have hAE : A ⊆ E := by
          intro j hj
          exact (Finset.mem_insert.mp (hA hj)).resolve_left (fun h => hiA (h ▸ hj))
        have hbA := hb A hAE
        have hpl : p A ≤ p' A := le_max_left _ _
        have hqu : q' A ≤ q A := min_le_left _ _
        rw [hsum A hiA]
        omega

theorem integer_sandwich [Fintype V] (p q : Finset V → ℤ) (hp0 : p ∅ = 0) (hq0 : q ∅ = 0)
    (hp : ∀ A B, p A + p B ≤ p (A ∪ B) + p (A ∩ B))
    (hq : ∀ A B, q (A ∪ B) + q (A ∩ B) ≤ q A + q B)
    (hpq : ∀ A, p A ≤ q A) :
    ∃ b : V → ℤ, ∀ A, p A ≤ ∑ i ∈ A, b i ∧ (∑ i ∈ A, b i) ≤ q A := by
  obtain ⟨b, _, hb⟩ := integer_sandwich_on Finset.univ p q hp0 hq0
    (fun A _ B _ => hp A B) (fun A _ B _ => hq A B) (fun A _ => hpq A)
  exact ⟨b, fun A => hb A (Finset.subset_univ _)⟩

end CommAlg.Polymatroid

end
end CheckedSource60

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "61: CommAlg.Polymatroid.Minkowski\n"

/-! ## Source: CommAlg.Polymatroid.Minkowski -/
section CheckedSource61

/-! # Integral Minkowski decomposition of polymatroid bases -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rank_base_decompose (g h : RankFunction V) {a : Exponent V}
    (ha : IsRankBase (g.add h) a) :
    ∃ b c : Exponent V, IsRankBase g b ∧ IsRankBase h c ∧ a = b + c := by
  let p : Finset V → ℤ := fun U => (subsetSum a U : ℤ) - h U
  let q : Finset V → ℤ := fun U => g U
  have hp0 : p ∅ = 0 := by simp [p]
  have hq0 : q ∅ = 0 := by simp [q]
  have hp : ∀ U W, p U + p W ≤ p (U ∪ W) + p (U ∩ W) := by
    intro U W
    have hs : (h (U ∪ W) : ℤ) + h (U ∩ W) ≤ h U + h W := by
      exact_mod_cast h.submodular U W
    have hm : (subsetSum a (U ∪ W) : ℤ) + subsetSum a (U ∩ W) =
        subsetSum a U + subsetSum a W := by
      exact_mod_cast (subsetSum_union_inter a U W).symm
    dsimp [p]
    omega
  have hq : ∀ U W, q (U ∪ W) + q (U ∩ W) ≤ q U + q W := by
    intro U W
    dsimp [q]
    exact_mod_cast g.submodular U W
  have hpq : ∀ U, p U ≤ q U := by
    intro U
    have hU : subsetSum a U ≤ g U + h U := ha.2 U
    have hz : (subsetSum a U : ℤ) ≤ g U + h U := by exact_mod_cast hU
    dsimp [p, q]
    omega
  obtain ⟨bZ, hbZ⟩ := integer_sandwich p q hp0 hq0 hp hq hpq
  have hadeg : a.degree = g Finset.univ + h Finset.univ := ha.1
  have hbtotal : (∑ i, bZ i) = (g Finset.univ : ℤ) := by
    have hb := hbZ Finset.univ
    dsimp [p, q] at hb
    rw [subsetSum_univ, hadeg] at hb
    push_cast at hb
    omega
  have hb0 : ∀ i, 0 ≤ bZ i := by
    intro i
    have hs := Finset.sum_erase_add Finset.univ bZ (Finset.mem_univ i)
    have hb := (hbZ (Finset.univ.erase i)).2
    have hg : (g (Finset.univ.erase i) : ℤ) ≤ g Finset.univ := by
      exact_mod_cast g.monotone (Finset.erase_subset _ _)
    change (∑ j ∈ Finset.univ.erase i, bZ j) ≤ (g (Finset.univ.erase i) : ℤ) at hb
    omega
  have hbaZ : ∀ i, bZ i ≤ (a i : ℤ) := by
    intro i
    have hs := Finset.sum_erase_add Finset.univ bZ (Finset.mem_univ i)
    have hb := (hbZ (Finset.univ.erase i)).1
    have hh : (h (Finset.univ.erase i) : ℤ) ≤ h Finset.univ := by
      exact_mod_cast h.monotone (Finset.erase_subset _ _)
    have haSum : (subsetSum a (Finset.univ.erase i) : ℤ) + a i = a.degree := by
      exact_mod_cast (show subsetSum a (Finset.univ.erase i) + a i = a.degree by
        simpa only [subsetSum, Finsupp.degree_eq_sum] using
          Finset.sum_erase_add Finset.univ a (Finset.mem_univ i))
    have hdegree : (a.degree : ℤ) = g Finset.univ + h Finset.univ := by exact_mod_cast hadeg
    dsimp [p] at hb
    omega
  let b : Exponent V := Finsupp.equivFunOnFinite.symm (fun i => (bZ i).toNat)
  have hbcast : ∀ i, (b i : ℤ) = bZ i := fun i => Int.toNat_of_nonneg (hb0 i)
  have hbsum : ∀ U, (subsetSum b U : ℤ) = ∑ i ∈ U, bZ i := by
    intro U
    simp only [subsetSum, Nat.cast_sum, hbcast]
  have hbdeg : b.degree = g Finset.univ := by
    have ht := hbsum Finset.univ
    rw [subsetSum_univ, hbtotal] at ht
    exact_mod_cast ht
  have hble : b ≤ a := by
    intro i
    have ht := hbaZ i
    rw [← hbcast i] at ht
    exact_mod_cast ht
  have hbupper : UpperFeasible g b := by
    intro U
    have ht := (hbZ U).2
    change (∑ i ∈ U, bZ i) ≤ (g U : ℤ) at ht
    rw [← hbsum U] at ht
    exact_mod_cast ht
  let c := a - b
  have hcb : c + b = a := tsub_add_cancel_of_le hble
  have hcdeg : c.degree = h Finset.univ := by
    have ht := congrArg Finsupp.degree hcb
    rw [map_add, hbdeg, hadeg] at ht
    omega
  have hcupper : UpperFeasible h c := by
    intro U
    have ht := (hbZ U).1
    have hs := congrArg (fun z : Exponent V => subsetSum z U) hcb
    rw [subsetSum_add] at hs
    have hsZ : (subsetSum c U : ℤ) + subsetSum b U = subsetSum a U := by exact_mod_cast hs
    dsimp [p] at ht
    rw [← hbsum U] at ht
    have hcZ : (subsetSum c U : ℤ) ≤ h U := by omega
    exact_mod_cast hcZ
  exact ⟨b, c, ⟨hbdeg, hbupper⟩, ⟨hcdeg, hcupper⟩, by simpa only [add_comm] using hcb.symm⟩

theorem rank_base_add {g h : RankFunction V} {b c : Exponent V}
    (hb : IsRankBase g b) (hc : IsRankBase h c) : IsRankBase (g.add h) (b + c) := by
  constructor
  · change (b + c).degree = g Finset.univ + h Finset.univ
    rw [map_add, hb.1, hc.1]
  · intro U
    change subsetSum (b + c) U ≤ g U + h U
    rw [subsetSum_add]
    exact Nat.add_le_add (hb.2 U) (hc.2 U)

theorem rank_base_minkowski (g h : RankFunction V) (a : Exponent V) :
    IsRankBase (g.add h) a ↔
      ∃ b c : Exponent V, IsRankBase g b ∧ IsRankBase h c ∧ a = b + c := by
  refine ⟨rank_base_decompose g h, ?_⟩
  rintro ⟨b, c, hb, hc, rfl⟩
  exact rank_base_add hb hc

theorem rankBases_add (g h : RankFunction V) :
    rankBases (g.add h) = ((rankBases g).product (rankBases h)).image (fun bc => bc.1 + bc.2) := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, c, hb, hc, he⟩ := rank_base_decompose g h ((mem_rankBases _ _).mp ha)
    exact Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr
      ⟨(mem_rankBases _ _).mpr hb, (mem_rankBases _ _).mpr hc⟩, he.symm⟩
  · intro ha
    obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    exact (mem_rankBases _ _).mpr (rank_base_add ((mem_rankBases _ _).mp hb)
      ((mem_rankBases _ _).mp hc))

end CommAlg.Polymatroid

end
end CheckedSource61

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "62: CommAlg.Polymatroid.IdealProducts\n"

/-! ## Source: CommAlg.Polymatroid.IdealProducts -/
section CheckedSource62

/-! # Products and powers of actual polymatroidal polynomial ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset
open scoped Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem monomialIdeal_mul (k : Type*) [CommSemiring k] (B C : Family V) :
    monomialIdeal k B * monomialIdeal k C =
      monomialIdeal k ((B.product C).image (fun bc => bc.1 + bc.2)) := by
  unfold monomialIdeal
  rw [Ideal.span_mul_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · intro hf
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hf
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨b + c, Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr ⟨hb, hc⟩, rfl⟩, ?_⟩
    simp [MvPolynomial.monomial_mul]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    refine Set.mem_mul.mpr ⟨MvPolynomial.monomial b 1, ⟨b, hb, rfl⟩,
      MvPolynomial.monomial c 1, ⟨c, hc, rfl⟩, ?_⟩
    simp [MvPolynomial.monomial_mul]

theorem rankIdeal_add (k : Type*) [CommSemiring k] (g h : RankFunction V) :
    rankIdeal k (g.add h) = rankIdeal k g * rankIdeal k h := by
  rw [rankIdeal, rankBases_add, ← monomialIdeal_mul]
  rfl

theorem RankFunction.ext_fun {g h : RankFunction V} (he : ∀ U, g U = h U) : g = h := by
  cases g with | mk g g0 gm gs =>
    cases h with | mk h h0 hm hs =>
      congr 1
      exact funext he

theorem rankIdeal_scale_zero (k : Type*) [CommSemiring k] (g : RankFunction V) :
    rankIdeal k (g.scale 0) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hb : (0 : Exponent V) ∈ rankBases (g.scale 0) := by
    rw [mem_rankBases]
    constructor
    · simp [RankFunction.scale]
    · intro U; simp [subsetSum, RankFunction.scale]
  have hm : MvPolynomial.monomial (0 : Exponent V) (1 : k) ∈ rankIdeal k (g.scale 0) :=
    Ideal.subset_span ⟨0, hb, rfl⟩
  simpa using hm

theorem rankIdeal_scale (k : Type*) [CommSemiring k] (g : RankFunction V) (s : ℕ) :
    rankIdeal k (g.scale s) = (rankIdeal k g) ^ s := by
  induction s with
  | zero => simpa using rankIdeal_scale_zero k g
  | succ s ih =>
    have hs : g.scale (s + 1) = (g.scale s).add g := by
      apply RankFunction.ext_fun
      intro U
      simp [RankFunction.scale, RankFunction.add, Nat.add_mul]
    rw [hs, rankIdeal_add, ih, pow_succ]

theorem family_eq_of_contains_iff {B C : Family V} (hB : Antichain B) (hC : Antichain C)
    (he : ∀ a, Contains B a ↔ Contains C a) : B = C := by
  apply Finset.Subset.antisymm
  · intro a ha
    obtain ⟨b, hb, hba⟩ := (he a).mp ⟨a, ha, le_rfl⟩
    obtain ⟨c, hc, hcb⟩ := (he b).mpr ⟨b, hb, le_rfl⟩
    have hca := hB c hc a ha (hcb.trans hba)
    have hab : a ≤ b := hca ▸ hcb
    have heq := le_antisymm hab hba
    rwa [heq]
  · intro a ha
    obtain ⟨b, hb, hba⟩ := (he a).mpr ⟨a, ha, le_rfl⟩
    obtain ⟨c, hc, hcb⟩ := (he b).mp ⟨b, hb, le_rfl⟩
    have hca := hC c hc a ha (hcb.trans hba)
    have hab : a ≤ b := hca ▸ hcb
    have heq := le_antisymm hab hba
    rwa [heq]

theorem rankIdeal_injective (k : Type*) [CommSemiring k] [Nontrivial k] :
    Function.Injective (rankIdeal (V := V) k) := by
  intro g h he
  apply rankBases_injective
  apply family_eq_of_contains_iff (rankBases_equigenerated g).antichain
    (rankBases_equigenerated h).antichain
  intro a
  rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k)]
  change (MvPolynomial.monomial a (1 : k) ∈ rankIdeal k g) ↔ _
  rw [he]
  rfl

end CommAlg.Polymatroid

end
end CheckedSource62

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "63: CommAlg.Polymatroid.HomologicalMain\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalMain -/
section CheckedSource63

/-! # The main homological-shift rank theorem

The left-hand sides below use the nonzero multigraded components of
Mathlib's actual derived tensor functor. The proof identifies their
homogeneous Koszul complexes with genuine matroid independence chains,
then applies the fully proved rank and coloop criterion.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- All multigraded Betti support, with no degree, activity, or rank restriction. -/
theorem gradedBettiNonzero_rankBases_iff (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Koszul.GradedBettiNonzero (k := k) (rankBases g) a i ↔ a ∈ rankShiftFamily g i := by
  rw [Koszul.gradedBettiNonzero_iff_faces]
  exact koszulFaces_nonzeroHomology_iff_rankShiftFamily g a i

/-- Theorem 1.2, including zero layers, zero rank and inactive variables. -/
theorem homologicalShift_rankBases (g : RankFunction V) (i : ℕ) :
    Koszul.homologicalShift (k := k) (rankBases g) i = rankShiftIdeal k g i := by
  simp only [Koszul.homologicalShift, rankShiftIdeal_eq_monomialIdeal, monomialIdeal,
    gradedBettiNonzero_rankBases_iff]
  rfl

/-- The paper's partition-rank presentation on the active ground set. -/
theorem homologicalShift_rankBases_active (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    Koszul.homologicalShift (k := k) (rankBases g) i =
      if homologicalRank g hg i univ = g univ + i then
        rankIdeal k (homologicalRank g hg i) else ⊥ := by
  rw [homologicalShift_rankBases, rankShiftIdeal]
  have he : universalHomologicalRank g i = homologicalRank g hg i := by
    apply RankFunction.ext_fun
    exact universalHomologicalRank_eq_active g hg i
  rw [he]

/-- Every nonempty equigenerated exchange family is covered by the rank theorem. -/
theorem homologicalShift_canonical (B : Family V) (hBne : B.Nonempty) (d : ℕ)
    (hdeg : Equigenerated B d) (hB : IsPolymatroidal B) (i : ℕ) :
    Koszul.homologicalShift (k := k) B i =
      rankShiftIdeal k (canonicalRank B hBne d hdeg hB) i := by
  simpa only [rankBases_canonical B hBne d hdeg hB] using
    (homologicalShift_rankBases (k := k) (canonicalRank B hBne d hdeg hB) i)

theorem gradedBettiNonzero_empty (a : Exponent V) (i : ℕ) :
    ¬ Koszul.GradedBettiNonzero (k := k) (∅ : Family V) a i := by
  rw [Koszul.gradedBettiNonzero_iff_faces, Simplicial.nonzeroHomology_iff_not_exactIn]
  apply not_not.mpr
  apply Simplicial.exactIn_of_no_face
  intro s hs
  obtain ⟨b, hb, _⟩ := Koszul.koszulFaces_contains hs
  exact (notMem_empty b hb).elim

/-- The zero ideal case, including every homological degree. -/
theorem homologicalShift_empty (i : ℕ) :
    Koszul.homologicalShift (k := k) (∅ : Family V) i = ⊥ := by
  simp [Koszul.homologicalShift, gradedBettiNonzero_empty]

/-- Homological shifts are polymatroidal, including the zero ideal. -/
theorem homologicalShift_polymatroidal (B : Family V) (hB : IsPolymatroidal B) (i : ℕ) :
    ∃ C : Family V, IsPolymatroidal C ∧
      Koszul.homologicalShift (k := k) B i = monomialIdeal k C := by
  by_cases hBne : B.Nonempty
  · obtain ⟨d, hdeg⟩ := hB.1
    let g := canonicalRank B hBne d hdeg hB
    refine ⟨rankShiftFamily g i, rankShiftFamily_polymatroidal g i, ?_⟩
    rw [homologicalShift_canonical B hBne d hdeg hB i, rankShiftIdeal_eq_monomialIdeal]
  · have he : B = ∅ := not_nonempty_iff_eq_empty.mp hBne
    subst B
    exact ⟨∅, hB, by simp [homologicalShift_empty, monomialIdeal]⟩

end CommAlg.Polymatroid

end
end CheckedSource63

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "64: CommAlg.Polymatroid.MultiRank\n"

/-! ## Source: CommAlg.Polymatroid.MultiRank -/
section CheckedSource64

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]

def zeroRank : RankFunction V where
  toFun _ := 0
  empty := rfl
  monotone := fun _ _ _ => le_rfl
  submodular _ _ := le_rfl

def sumRanks (F : Finset J) (ρ : J → RankFunction V) : RankFunction V where
  toFun A := ∑ j ∈ F, ρ j A
  empty := by simp
  monotone := fun _ _ h => Finset.sum_le_sum (fun j _ => (ρ j).monotone h)
  submodular A B := by
    simpa only [← Finset.sum_add_distrib] using Finset.sum_le_sum (s := F)
      (fun j _ => (ρ j).submodular A B)

@[simp] theorem zeroRank_apply (A : Finset V) : zeroRank A = 0 := rfl

@[simp] theorem sumRanks_apply (F : Finset J) (ρ : J → RankFunction V) (A : Finset V) :
    sumRanks F ρ A = ∑ j ∈ F, ρ j A := rfl

@[simp] theorem sumRanks_empty (ρ : J → RankFunction V) : sumRanks ∅ ρ = zeroRank := by
  apply RankFunction.ext_fun
  intro A
  simp

theorem sumRanks_insert (F : Finset J) (ρ : J → RankFunction V) {j : J} (hj : j ∉ F) :
    sumRanks (insert j F) ρ = (ρ j).add (sumRanks F ρ) := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.add, hj]

theorem rankIdeal_zeroRank (k : Type*) [CommSemiring k] : rankIdeal k (zeroRank (V := V)) = ⊤ := by
  have hz : (zeroRank (V := V)).scale 0 = zeroRank := by
    apply RankFunction.ext_fun
    intro A
    rfl
  rw [← hz]
  exact rankIdeal_scale_zero k _

theorem rankIdeal_sumRanks (k : Type*) [CommSemiring k] (F : Finset J)
    (ρ : J → RankFunction V) : rankIdeal k (sumRanks F ρ) = ∏ j ∈ F, rankIdeal k (ρ j) := by
  induction F using Finset.induction_on with
  | empty => simp [rankIdeal_zeroRank]
  | @insert j F hj ih =>
    rw [sumRanks_insert F ρ hj, rankIdeal_add, ih, Finset.prod_insert hj]

def multiRank [Fintype J] (ρ : J → RankFunction V) (s : J →₀ ℕ) : RankFunction V :=
  sumRanks Finset.univ (fun j => (ρ j).scale (s j))

@[simp] theorem multiRank_apply [Fintype J] (ρ : J → RankFunction V) (s : J →₀ ℕ)
    (A : Finset V) : multiRank ρ s A = ∑ j, s j * ρ j A := rfl

@[simp] theorem multiRank_zero [Fintype J] (ρ : J → RankFunction V) : multiRank ρ 0 = zeroRank := by
  apply RankFunction.ext_fun
  intro A
  simp

theorem multiRank_add [Fintype J] (ρ : J → RankFunction V) (s t : J →₀ ℕ) :
    multiRank ρ (s + t) = (multiRank ρ s).add (multiRank ρ t) := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.add, Nat.add_mul, Finset.sum_add_distrib]

@[simp] theorem multiRank_single [Fintype J] (ρ : J → RankFunction V) (j : J) (n : ℕ) :
    multiRank ρ (Finsupp.single j n) = (ρ j).scale n := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.scale, Finsupp.single_apply]

/-- Exact equality of actual products of polynomial ideals, for every multidegree. -/
theorem rankIdeal_multiRank (k : Type*) [CommSemiring k] [Fintype J]
    (ρ : J → RankFunction V) (s : J →₀ ℕ) :
    rankIdeal k (multiRank ρ s) = ∏ j, (rankIdeal k (ρ j)) ^ (s j) := by
  rw [multiRank, rankIdeal_sumRanks]
  apply Finset.prod_congr rfl
  intro j hj
  exact rankIdeal_scale k (ρ j) (s j)

end CommAlg.Polymatroid

end
end CheckedSource64

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "65: CommAlg.Polymatroid.IdealBridge\n"

/-! ## Source: CommAlg.Polymatroid.IdealBridge -/
section CheckedSource65

/-! # Polymatroidal ideals as actual polynomial ideals

The defining exchange family is unique: every equigenerated family is an
antichain, and monomial membership recovers an antichain of generators.
Consequently the homological shift below is independent of a presentation;
it is computed from the genuine derived-Tor components of the actual ideal.
This bridge includes both the zero and the unit ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

def IsPolymatroidalIdeal (I : Ideal (MvPolynomial V k)) : Prop :=
  ∃ B : Family V, IsPolymatroidal B ∧ I = monomialIdeal k B

theorem monomialIdeal_family_unique {B C : Family V}
    (hB : IsPolymatroidal B) (hC : IsPolymatroidal C)
    (he : monomialIdeal k B = monomialIdeal k C) : B = C := by
  obtain ⟨d, hd⟩ := hB.1
  obtain ⟨e, heq⟩ := hC.1
  apply family_eq_of_contains_iff hd.antichain heq.antichain
  intro a
  rw [← monomial_mem_iff (k := k), ← monomial_mem_iff (k := k), he]

def idealGenerators (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I) : Family V :=
  hI.choose

theorem idealGenerators_polymatroidal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) : IsPolymatroidal (idealGenerators I hI) :=
  hI.choose_spec.1

theorem monomialIdeal_idealGenerators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) : monomialIdeal k (idealGenerators I hI) = I :=
  hI.choose_spec.2.symm

theorem idealGenerators_eq_of_presentation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (B : Family V) (hB : IsPolymatroidal B)
    (he : I = monomialIdeal k B) : idealGenerators I hI = B :=
  monomialIdeal_family_unique (idealGenerators_polymatroidal I hI) hB
    ((monomialIdeal_idealGenerators I hI).trans he)

theorem isPolymatroidalIdeal_monomialIdeal (B : Family V) (hB : IsPolymatroidal B) :
    IsPolymatroidalIdeal (monomialIdeal k B) := ⟨B, hB, rfl⟩

theorem isPolymatroidalIdeal_rankIdeal (g : RankFunction V) :
    IsPolymatroidalIdeal (rankIdeal k g) :=
  ⟨rankBases g, rankBases_polymatroidal g, rfl⟩

theorem isPolymatroidalIdeal_bot : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)) := by
  refine ⟨∅, ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩, ?_⟩
  simp [monomialIdeal]

theorem isPolymatroidalIdeal_top : IsPolymatroidalIdeal (⊤ : Ideal (MvPolynomial V k)) := by
  simpa only [rankIdeal_zeroRank] using
    (isPolymatroidalIdeal_rankIdeal (k := k) (zeroRank (V := V)))

theorem IsPolymatroidalIdeal.eq_bot_or_rank {I : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) : I = ⊥ ∨ ∃ g : RankFunction V, I = rankIdeal k g := by
  obtain ⟨B, hB, rfl⟩ := hI
  by_cases hne : B.Nonempty
  · obtain ⟨d, hd⟩ := hB.1
    refine Or.inr ⟨canonicalRank B hne d hd hB, ?_⟩
    rw [rankIdeal, rankBases_canonical B hne d hd hB]
  · have he := not_nonempty_iff_eq_empty.mp hne
    exact Or.inl (by simp [he, monomialIdeal])

theorem IsPolymatroidalIdeal.exists_rank {I : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (hne : I ≠ ⊥) : ∃ g : RankFunction V, I = rankIdeal k g :=
  hI.eq_bot_or_rank.resolve_left hne

theorem IsPolymatroidalIdeal.mul {I J : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J) :
    IsPolymatroidalIdeal (I * J) := by
  rcases hI.eq_bot_or_rank with rfl | ⟨g, rfl⟩
  · simpa using (isPolymatroidalIdeal_bot (V := V) (k := k))
  rcases hJ.eq_bot_or_rank with rfl | ⟨h, rfl⟩
  · simpa using (isPolymatroidalIdeal_bot (V := V) (k := k))
  rw [← rankIdeal_add]
  exact isPolymatroidalIdeal_rankIdeal _

theorem IsPolymatroidalIdeal.pow {I : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (s : ℕ) : IsPolymatroidalIdeal (I ^ s) := by
  induction s with
  | zero => simpa using (isPolymatroidalIdeal_top (V := V) (k := k))
  | succ s ih => simpa only [pow_succ] using ih.mul hI

theorem IsPolymatroidalIdeal.prod {J : Type*} (F : Finset J)
    (I : J → Ideal (MvPolynomial V k)) (hI : ∀ j ∈ F, IsPolymatroidalIdeal (I j)) :
    IsPolymatroidalIdeal (∏ j ∈ F, I j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using (isPolymatroidalIdeal_top (V := V) (k := k))
  | @insert j F hj ih =>
    rw [Finset.prod_insert hj]
    exact (hI j (mem_insert_self _ _)).mul (ih (fun x hx => hI x (mem_insert_of_mem hx)))

/-- The homological shift of an actual polymatroidal ideal. The uniquely
determined generator family only supplies the finite presentation used to
construct its standard multigrading on genuine derived Tor. -/
def homologicalShiftIdeal (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) : Ideal (MvPolynomial V k) :=
  Koszul.homologicalShift (k := k) (idealGenerators I hI) i

theorem homologicalShiftIdeal_of_presentation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (B : Family V) (hB : IsPolymatroidal B)
    (he : I = monomialIdeal k B) (i : ℕ) :
    homologicalShiftIdeal I hI i = Koszul.homologicalShift (k := k) B i := by
  unfold homologicalShiftIdeal
  rw [idealGenerators_eq_of_presentation I hI B hB he]

theorem homologicalShiftIdeal_eq_rankShiftIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) (i : ℕ) :
    homologicalShiftIdeal I hI i = rankShiftIdeal k g i := by
  rw [homologicalShiftIdeal_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he,
    homologicalShift_rankBases]

@[simp] theorem homologicalShiftIdeal_bot (hI : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)))
    (i : ℕ) : homologicalShiftIdeal ⊥ hI i = ⊥ := by
  rw [homologicalShiftIdeal_of_presentation _ hI ∅
    ⟨⟨0, by simp [Equigenerated]⟩, by simp [ExchangeAxiom]⟩ (by simp [monomialIdeal]),
    homologicalShift_empty]

theorem homologicalShiftIdeal_congr {I J : Ideal (MvPolynomial V k)}
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J) (he : I = J) (i : ℕ) :
    homologicalShiftIdeal I hI i = homologicalShiftIdeal J hJ i := by
  subst J
  rfl

theorem homologicalShiftIdeal_polymatroidal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : IsPolymatroidalIdeal (homologicalShiftIdeal I hI i) := by
  obtain ⟨B, hB, he⟩ := homologicalShift_polymatroidal (k := k) (idealGenerators I hI)
    (idealGenerators_polymatroidal I hI) i
  exact ⟨B, hB, he⟩

end CommAlg.Polymatroid

end
end CheckedSource65

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "66: CommAlg.Polymatroid.AffineMinimum\n"

/-! ## Source: CommAlg.Polymatroid.AffineMinimum -/
section CheckedSource66

/-! # Exact stabilization of capped minima of integer affine functions -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def cappedAffineMinimum (κ : ℕ) (δ b : ι → ℕ) (s : ℕ) : ℕ :=
  min κ (finiteMinimum (fun j => s * δ j + b j))

/-- Every positive integer slope has passed the cap once `s ≥ κ`. -/
theorem cappedAffineMinimum_stable (κ : ℕ) (δ b : ι → ℕ) {s : ℕ} (hs : κ ≤ s) :
    cappedAffineMinimum κ δ b (s + 1) = cappedAffineMinimum κ δ b s := by
  unfold cappedAffineMinimum
  rw [← finiteMinimum_min_left, ← finiteMinimum_min_left]
  congr 1
  funext j
  by_cases hd : δ j = 0
  · simp [hd]
  · have hp : 1 ≤ δ j := by omega
    have h0 : κ ≤ s * δ j + b j := by nlinarith
    have h1 : κ ≤ (s + 1) * δ j + b j := by nlinarith
    simp [min_eq_left h0, min_eq_left h1]

/-- The maximum of the clamped ceiling thresholds, with a zero entry for
each zero slope. `⌈/⌉` is Mathlib's exact natural ceiling division. -/
def affineThreshold (κ : ℕ) (δ b : ι → ℕ) : ℕ :=
  univ.sup (fun j => if δ j = 0 then 0 else (κ - b j) ⌈/⌉ δ j)

theorem affineThreshold_le_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    affineThreshold κ δ b ≤ s ↔ ∀ j, κ ≤ s * δ j + b j := by
  simp only [affineThreshold, Finset.sup_le_iff, Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro j
  by_cases hd : δ j = 0
  · simp [hd, hz j hd]
  · rw [if_neg hd, ceilDiv_le_iff_le_mul (by omega : 0 < δ j)]
    rw [Nat.mul_comm (δ j) s]
    omega

theorem affineThreshold_le_cap (κ : ℕ) (δ b : ι → ℕ) :
    affineThreshold κ δ b ≤ κ := by
  apply Finset.sup_le
  intro j hj
  by_cases hd : δ j = 0
  · simp [hd]
  · rw [if_neg hd, ceilDiv_le_iff_le_mul (by omega : 0 < δ j)]
    have hp : 1 ≤ δ j := by omega
    nlinarith [Nat.sub_le κ (b j)]

theorem cappedAffineMinimum_le_cap (κ : ℕ) (δ b : ι → ℕ) (s : ℕ) :
    cappedAffineMinimum κ δ b s ≤ κ := min_le_left _ _

theorem cappedAffineMinimum_eq_cap_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    cappedAffineMinimum κ δ b s = κ ↔ affineThreshold κ δ b ≤ s := by
  rw [cappedAffineMinimum, min_eq_left_iff, le_finiteMinimum_iff,
    affineThreshold_le_iff κ δ b hz s]

theorem cappedAffineMinimum_lt_cap_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    cappedAffineMinimum κ δ b s < κ ↔ s < affineThreshold κ δ b := by
  have he := cappedAffineMinimum_eq_cap_iff κ δ b hz s
  have hl := cappedAffineMinimum_le_cap κ δ b s
  omega

theorem cappedAffineMinimum_mono (κ : ℕ) (δ b : ι → ℕ) :
    Monotone (cappedAffineMinimum κ δ b) := by
  intro s t hst
  exact min_le_min_left κ (finiteMinimum_mono (fun j => by
    exact Nat.add_le_add_right (Nat.mul_le_mul_right (δ j) hst) (b j)))

/-- There are no gaps before stabilization: the value strictly increases
at every integer step below the exact ceiling threshold. -/
theorem cappedAffineMinimum_strict_step (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) {s : ℕ} (hs : s < affineThreshold κ δ b) :
    cappedAffineMinimum κ δ b s < cappedAffineMinimum κ δ b (s + 1) := by
  have hlt := (cappedAffineMinimum_lt_cap_iff κ δ b hz s).mpr hs
  by_cases hn : κ ≤ finiteMinimum (fun j => (s + 1) * δ j + b j)
  · simpa only [cappedAffineMinimum, min_eq_left hn] using hlt
  · obtain ⟨j, hj⟩ := finiteMinimum_attained (fun j => (s + 1) * δ j + b j)
    have hsmall : (s + 1) * δ j + b j < κ := by omega
    have hd : δ j ≠ 0 := by
      intro heq
      have hzj := hz j heq
      simp only [heq, Nat.mul_zero, Nat.zero_add] at hsmall
      omega
    have hprev : cappedAffineMinimum κ δ b s ≤ s * δ j + b j :=
      (min_le_right _ _).trans (finiteMinimum_le _ j)
    have hnext : cappedAffineMinimum κ δ b (s + 1) =
        finiteMinimum (fun j => (s + 1) * δ j + b j) := min_eq_right (by omega)
    rw [hnext, ← hj]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem cappedAffineMinimum_step_eq_iff (κ : ℕ) (δ b : ι → ℕ)
    (hz : ∀ j, δ j = 0 → κ ≤ b j) (s : ℕ) :
    cappedAffineMinimum κ δ b (s + 1) = cappedAffineMinimum κ δ b s ↔
      affineThreshold κ δ b ≤ s := by
  constructor
  · intro heq
    by_contra hn
    have hlt := cappedAffineMinimum_strict_step κ δ b hz (by omega : s < affineThreshold κ δ b)
    omega
  · intro hs
    rw [(cappedAffineMinimum_eq_cap_iff κ δ b hz s).mpr hs,
      (cappedAffineMinimum_eq_cap_iff κ δ b hz (s + 1)).mpr (by omega)]

end CommAlg.Polymatroid

end
end CheckedSource66

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "67: CommAlg.Polymatroid.PowerStabilization\n"

/-! ## Source: CommAlg.Polymatroid.PowerStabilization -/
section CheckedSource67

/-! # The exact rank identity behind uniform stabilization of twisted powers -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem twistedPower_active (η ρ : RankFunction V)
    (h : (twistedPowerRank η ρ 1).Active) {s : ℕ} (hs : 1 ≤ s) :
    (twistedPowerRank η ρ s).Active := by
  intro A hA
  have h1 := h A hA
  simp only [twistedPowerRank_apply, Nat.one_mul] at h1 ⊢
  nlinarith

/-- Uniform stabilization retains arbitrary fixed twists and the entire
range `s ≥ i`. Its application to shift ideals uses the separate Tor theorem. -/
theorem twistedPower_homologicalRank_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) (h0 : (twistedPowerRank η ρ s).Active)
    (h1 : (twistedPowerRank η ρ (s + 1)).Active) (A : Finset V) :
    homologicalRank (twistedPowerRank η ρ (s + 1)) h1 i A =
      ρ A + homologicalRank (twistedPowerRank η ρ s) h0 i A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hA' := Finset.nonempty_iff_ne_empty.mpr hA
  rw [twistedPower_homologicalRank η ρ (s + 1) i h1 hA',
    twistedPower_homologicalRank η ρ s i h0 hA']
  have hcap := cappedAffineMinimum_stable i
    (fun P : Finpartition A => partitionDefect ρ P)
    (fun P => partitionDefect η P + partitionSlack P) hs
  simp only [cappedAffineMinimum, ← Nat.add_assoc] at hcap
  rw [hcap]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

/-- The total-rank nonvanishing conditions agree for consecutive powers
throughout the uniform stabilization range. -/
theorem twistedPower_total_rank_eq_iff (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) (h0 : (twistedPowerRank η ρ s).Active)
    (h1 : (twistedPowerRank η ρ (s + 1)).Active) :
    homologicalRank (twistedPowerRank η ρ (s + 1)) h1 i univ =
        twistedPowerRank η ρ (s + 1) univ + i ↔
      homologicalRank (twistedPowerRank η ρ s) h0 i univ =
        twistedPowerRank η ρ s univ + i := by
  rw [twistedPower_homologicalRank_succ η ρ i s hs h0 h1 univ]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

end CommAlg.Polymatroid

end
end CheckedSource67

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "68: CommAlg.Polymatroid.PartitionThreshold\n"

/-! ## Source: CommAlg.Polymatroid.PartitionThreshold -/
section CheckedSource68

/-! # Exact ceiling thresholds for every subset and every homological degree

The finite maximum over zero-defect partitions is the paper's `c_ρ(A)`;
the ceiling maximum is its `τ_i(A)`.  No degree or ground-set bound is used.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def zeroDefectPartitions (ρ : RankFunction V) (A : Finset V) : Finset (Finpartition A) :=
  univ.filter (fun P => partitionDefect ρ P = 0)

theorem zeroDefectPartitions_nonempty (ρ : RankFunction V) (A : Finset V) :
    (zeroDefectPartitions ρ A).Nonempty := by
  by_cases hA : A = ∅
  · subst A
    refine ⟨Finpartition.empty (Finset V), ?_⟩
    simp [zeroDefectPartitions, partitionDefect]
  · refine ⟨Finpartition.indiscrete hA, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [partitionDefect, Finpartition.indiscrete]

def zeroDefectComponents (ρ : RankFunction V) (A : Finset V) : ℕ :=
  (zeroDefectPartitions ρ A).sup (fun P => P.parts.card)

theorem zeroDefectComponents_le_card (ρ : RankFunction V) (A : Finset V) :
    zeroDefectComponents ρ A ≤ A.card :=
  Finset.sup_le (fun P _ => P.card_parts_le_card)

theorem zeroDefectComponents_attained (ρ : RankFunction V) (A : Finset V) :
    ∃ P : Finpartition A, partitionDefect ρ P = 0 ∧
      P.parts.card = zeroDefectComponents ρ A := by
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image
    (zeroDefectPartitions ρ A) (fun P => P.parts.card) (zeroDefectPartitions_nonempty ρ A)
  refine ⟨P, (mem_filter.mp hP).2, ?_⟩
  change P.parts.card = (zeroDefectPartitions ρ A).sup (fun Q => Q.parts.card)
  exact le_antisymm (Finset.le_sup (f := fun Q : Finpartition A => Q.parts.card) hP)
    (Finset.sup_le (fun Q hQ => hmax Q hQ))

def eventualOffset (ρ : RankFunction V) (A : Finset V) : ℕ :=
  A.card - zeroDefectComponents ρ A

theorem eventualOffset_le_slack (ρ : RankFunction V) {A : Finset V}
    (P : Finpartition A) (hP : partitionDefect ρ P = 0) :
    eventualOffset ρ A ≤ partitionSlack P := by
  have hc : P.parts.card ≤ zeroDefectComponents ρ A := by
    change P.parts.card ≤ (zeroDefectPartitions ρ A).sup (fun Q => Q.parts.card)
    have hm : P ∈ zeroDefectPartitions ρ A := mem_filter.mpr ⟨mem_univ P, hP⟩
    exact Finset.le_sup (f := fun Q : Finpartition A => Q.parts.card) hm
  exact Nat.sub_le_sub_left hc A.card

theorem eventualOffset_attained (ρ : RankFunction V) (A : Finset V) :
    ∃ P : Finpartition A, partitionDefect ρ P = 0 ∧ partitionSlack P = eventualOffset ρ A := by
  obtain ⟨P, hd, hc⟩ := zeroDefectComponents_attained ρ A
  exact ⟨P, hd, congrArg (A.card - ·) hc⟩

def eventualCorrection (ρ : RankFunction V) (i : ℕ) (A : Finset V) : ℕ :=
  min i (eventualOffset ρ A)

def powerCorrection (ρ : RankFunction V) (i s : ℕ) (A : Finset V) : ℕ :=
  cappedAffineMinimum i (fun P : Finpartition A => partitionDefect ρ P)
    partitionSlack s

def powerThreshold (ρ : RankFunction V) (i : ℕ) (A : Finset V) : ℕ :=
  affineThreshold (eventualCorrection ρ i A)
    (fun P : Finpartition A => partitionDefect ρ P) partitionSlack

theorem eventualCorrection_le_zero_slack (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    ∀ P : Finpartition A, partitionDefect ρ P = 0 →
      eventualCorrection ρ i A ≤ partitionSlack P := by
  intro P hP
  exact (min_le_right _ _).trans (eventualOffset_le_slack ρ P hP)

theorem powerCorrection_recap (ρ : RankFunction V) (i s : ℕ) (A : Finset V) :
    powerCorrection ρ i s A =
      cappedAffineMinimum (eventualCorrection ρ i A)
        (fun P : Finpartition A => partitionDefect ρ P) partitionSlack s := by
  obtain ⟨P, hd, hb⟩ := eventualOffset_attained ρ A
  have hmin : finiteMinimum (fun P : Finpartition A => s * partitionDefect ρ P + partitionSlack P) ≤
      eventualOffset ρ A := by
    have h := finiteMinimum_le (fun P : Finpartition A =>
      s * partitionDefect ρ P + partitionSlack P) P
    simpa [hd, hb] using h
  unfold powerCorrection cappedAffineMinimum eventualCorrection
  rw [min_assoc, min_eq_right hmin]

theorem powerThreshold_le (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A ≤ i :=
  (affineThreshold_le_cap _ _ _).trans (min_le_left _ _)

theorem powerCorrection_eq_eventual_iff (ρ : RankFunction V) (i s : ℕ) (A : Finset V) :
    powerCorrection ρ i s A = eventualCorrection ρ i A ↔ powerThreshold ρ i A ≤ s := by
  rw [powerCorrection_recap]
  exact cappedAffineMinimum_eq_cap_iff _ _ _ (eventualCorrection_le_zero_slack ρ i A) s

theorem powerCorrection_step_eq_iff (ρ : RankFunction V) (i s : ℕ) (A : Finset V) :
    powerCorrection ρ i (s + 1) A = powerCorrection ρ i s A ↔ powerThreshold ρ i A ≤ s := by
  rw [powerCorrection_recap ρ i (s + 1), powerCorrection_recap ρ i s]
  exact cappedAffineMinimum_step_eq_iff _ _ _ (eventualCorrection_le_zero_slack ρ i A) s

theorem powerCorrection_strict_step (ρ : RankFunction V) (i s : ℕ) (A : Finset V)
    (hs : s < powerThreshold ρ i A) :
    powerCorrection ρ i s A < powerCorrection ρ i (s + 1) A := by
  rw [powerCorrection_recap ρ i s, powerCorrection_recap ρ i (s + 1)]
  exact cappedAffineMinimum_strict_step _ _ _ (eventualCorrection_le_zero_slack ρ i A) hs

@[simp] theorem powerCorrection_zero (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerCorrection ρ i 0 A = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := finiteMinimum_le
    (fun P : Finpartition A => 0 * partitionDefect ρ P + partitionSlack P) (⊥ : Finpartition A)
  have hb : partitionSlack (⊥ : Finpartition A) = 0 := by simp [partitionSlack, Finpartition.card_bot]
  have hbound : powerCorrection ρ i 0 A ≤
      finiteMinimum (fun P : Finpartition A => 0 * partitionDefect ρ P + partitionSlack P) :=
    min_le_right _ _
  simpa [hb] using hbound.trans h

@[simp] theorem powerThreshold_empty (ρ : RankFunction V) (i : ℕ) :
    powerThreshold ρ i ∅ = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := affineThreshold_le_cap (eventualCorrection ρ i ∅)
    (fun P : Finpartition (∅ : Finset V) => partitionDefect ρ P) partitionSlack
  simpa [eventualCorrection, eventualOffset, powerThreshold] using h

theorem powerThreshold_pos (ρ : RankFunction V) {i : ℕ} (hi : 0 < i)
    {A : Finset V} (hA : i ≤ eventualOffset ρ A) : 1 ≤ powerThreshold ρ i A := by
  have he := powerCorrection_eq_eventual_iff ρ i 0 A
  have hκ : eventualCorrection ρ i A = i := min_eq_left hA
  rw [powerCorrection_zero, hκ] at he
  omega

theorem powerCorrection_eq_degree_iff (ρ : RankFunction V) (i s : ℕ) (A : Finset V)
    (hA : i ≤ eventualOffset ρ A) :
    powerCorrection ρ i s A = i ↔ powerThreshold ρ i A ≤ s := by
  have he := powerCorrection_eq_eventual_iff ρ i s A
  simpa only [eventualCorrection, min_eq_left hA] using he

theorem powerCorrection_lt_degree (ρ : RankFunction V) (i s : ℕ) (A : Finset V)
    (hA : eventualOffset ρ A < i) : powerCorrection ρ i s A < i := by
  rw [powerCorrection_recap]
  have h := cappedAffineMinimum_le_cap (eventualCorrection ρ i A)
    (fun P : Finpartition A => partitionDefect ρ P) partitionSlack s
  have hκ : eventualCorrection ρ i A = eventualOffset ρ A := min_eq_right hA.le
  omega

/-- The paper's maximum over all nonempty subsets; the empty subset contributes zero. -/
def globalPowerThreshold (ρ : RankFunction V) (i : ℕ) : ℕ :=
  univ.sup (powerThreshold ρ i)

theorem powerThreshold_le_global (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A ≤ globalPowerThreshold ρ i := Finset.le_sup (mem_univ A)

theorem globalPowerThreshold_le (ρ : RankFunction V) (i : ℕ) :
    globalPowerThreshold ρ i ≤ i := Finset.sup_le (fun A _ => powerThreshold_le ρ i A)

theorem all_powerCorrection_step_eq_iff (ρ : RankFunction V) (i s : ℕ) :
    (∀ A, powerCorrection ρ i (s + 1) A = powerCorrection ρ i s A) ↔
      globalPowerThreshold ρ i ≤ s := by
  simp only [powerCorrection_step_eq_iff, globalPowerThreshold, Finset.sup_le_iff,
    Finset.mem_univ, forall_true_left]

theorem exists_strict_powerCorrection (ρ : RankFunction V) (i s : ℕ)
    (hs : s < globalPowerThreshold ρ i) :
    ∃ A : Finset V, A.Nonempty ∧
      powerCorrection ρ i s A < powerCorrection ρ i (s + 1) A := by
  have hex : ∃ A, s < powerThreshold ρ i A := by
    by_contra hn
    push Not at hn
    have hle : globalPowerThreshold ρ i ≤ s := Finset.sup_le (fun A _ => hn A)
    omega
  obtain ⟨A, hA⟩ := hex
  have hne : A ≠ ∅ := by intro heq; simp [heq] at hA
  exact ⟨A, Finset.nonempty_iff_ne_empty.mpr hne, powerCorrection_strict_step ρ i s A hA⟩

end CommAlg.Polymatroid

end
end CheckedSource68

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "69: CommAlg.Polymatroid.ShiftMultiplication\n"

/-! ## Source: CommAlg.Polymatroid.ShiftMultiplication -/
section CheckedSource69

/-! # Multiplication of rank-shift ideals, including all inactive coordinates

These are genuine ideal inclusions. The proof uses the exact partition
membership inequalities and is transported to homological shifts by the
separate graded-Tor rank formula.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem RankFunction.lower_add (f g : RankFunction V) (U : Finset V) :
    (f.add g).lower U = f.lower U + g.lower U := by
  have hf := f.lower_add_compl U
  have hg := g.lower_add_compl U
  have hfg := (f.add g).lower_add_compl U
  change (f.add g).lower U + (f Uᶜ + g Uᶜ) = f univ + g univ at hfg
  omega

section Ideals

variable {k : Type*} [CommSemiring k] [Nontrivial k]

theorem monomial_add_mem_rankShiftIdeal (f g : RankFunction V) (i : ℕ)
    (b a : Exponent V) (hb : LowerFeasible f.lower b)
    (ha : MvPolynomial.monomial a (1 : k) ∈ rankShiftIdeal k g i) :
    MvPolynomial.monomial (b + a) (1 : k) ∈ rankShiftIdeal k (f.add g) i := by
  obtain ⟨haDeg, haLower, haPart⟩ := (monomial_mem_rankShiftIdeal_partition_iff g i a).mp ha
  apply (monomial_mem_rankShiftIdeal_partition_iff (f.add g) i (b + a)).mpr
  refine ⟨?_, ?_, ?_⟩
  · have hbDeg := hb univ
    simp only [RankFunction.lower_univ, subsetSum_univ] at hbDeg
    change (f univ + g univ) + i ≤ (b + a).degree
    rw [map_add]
    omega
  · intro U
    rw [RankFunction.lower_add, subsetSum_add]
    exact Nat.add_le_add (hb U) (haLower U)
  · intro A hA P
    have hpa := haPart A hA P
    have hbf := hb Aᶜ
    have hfcomp := f.lower_add_compl Aᶜ
    simp only [compl_compl] at hfcomp
    have hfpart := f.le_sum_partition P
    change (f univ + g univ) + i + P.parts.card ≤
      subsetSum (b + a) Aᶜ + A.card + ∑ C ∈ P.parts, (f C + g C)
    rw [subsetSum_add, Finset.sum_add_distrib]
    omega

/-- Lemma 3.4 for the exact formula ideals, with no positivity or activity
restriction on either rank. -/
theorem rankIdeal_mul_rankShiftIdeal_le (f g : RankFunction V) (i : ℕ) :
    rankIdeal k f * rankShiftIdeal k g i ≤ rankShiftIdeal k (f.add g) i := by
  rw [rankIdeal, rankShiftIdeal_eq_monomialIdeal, monomialIdeal_mul]
  apply Ideal.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨⟨b, c⟩, hbc, rfl⟩ := mem_image.mp ha
  obtain ⟨hb, hc⟩ := mem_product.mp hbc
  have hb' : LowerFeasible f.lower b :=
    (contains_rankBases_iff f b).mp ⟨b, hb, le_rfl⟩
  have hc' : MvPolynomial.monomial c (1 : k) ∈ rankShiftIdeal k g i := by
    rw [rankShiftIdeal_eq_monomialIdeal]
    exact Ideal.subset_span ⟨c, hc, rfl⟩
  exact monomial_add_mem_rankShiftIdeal f g i b c hb' hc'

end Ideals

end CommAlg.Polymatroid

end
end CheckedSource69

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "70: CommAlg.Polymatroid.PowerShiftInterval\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftInterval -/
section CheckedSource70

/-!
# Exact nonvanishing and consecutive ideal equality for power shifts

The partition thresholds are connected here to the actual polynomial ideals
on the right-hand side of the graded-Tor formula. Canonical ranks, recovered
from their integer bases, detect equality of those ideals.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem RankFunction.Active.scale {ρ : RankFunction V} (hρ : ρ.Active)
    {s : ℕ} (hs : 1 ≤ s) : (RankFunction.scale s ρ).Active := by
  intro A hA
  have h := hρ A hA
  change 1 ≤ s * ρ A
  nlinarith

@[simp] theorem powerCorrection_empty (ρ : RankFunction V) (i s : ℕ) :
    powerCorrection ρ i s ∅ = 0 := by
  have h := (powerCorrection_eq_eventual_iff ρ i s ∅).mpr (by simp)
  simpa [eventualCorrection, eventualOffset] using h

theorem power_homologicalRank (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) {s : ℕ} (hs : 1 ≤ s) (A : Finset V) :
    universalHomologicalRank (RankFunction.scale s ρ) i A =
      s * ρ A + powerCorrection ρ i s A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hne := nonempty_iff_ne_empty.mpr hA
  rw [universalHomologicalRank_eq_active _ (hρ.scale hs),
    homologicalRank_defect _ (hρ.scale hs) i hne]
  simp only [partitionDefect_scale]
  rfl

theorem powerShiftFamily_nonempty_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    (rankShiftFamily (RankFunction.scale s ρ) i).Nonempty ↔
      powerCorrection ρ i s univ = i := by
  rw [rankShiftFamily_nonempty_iff, power_homologicalRank ρ hρ i hs univ]
  change s * ρ univ + powerCorrection ρ i s univ = s * ρ univ + i ↔ _
  exact Nat.add_left_cancel_iff

theorem powerShiftFamily_nonempty_iff_threshold (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ} (hs : 1 ≤ s) :
    (rankShiftFamily (RankFunction.scale s ρ) i).Nonempty ↔
      powerThreshold ρ i univ ≤ s := by
  rw [powerShiftFamily_nonempty_iff ρ hρ i hs,
    powerCorrection_eq_degree_iff ρ i s univ hi]

theorem powerShiftFamily_empty_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) {s : ℕ} (hs : 1 ≤ s) :
    rankShiftFamily (RankFunction.scale s ρ) i = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rw [powerShiftFamily_nonempty_iff ρ hρ i hs]
  exact ne_of_lt (powerCorrection_lt_degree ρ i s univ hi)

theorem power_homologicalRank_add_eq_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    ρ.add (universalHomologicalRank (RankFunction.scale s ρ) i) =
        universalHomologicalRank (RankFunction.scale (s + 1) ρ) i ↔
      globalPowerThreshold ρ i ≤ s := by
  rw [← all_powerCorrection_step_eq_iff]
  constructor
  · intro h A
    have he := congrArg (fun g : RankFunction V => g A) h
    change ρ A + universalHomologicalRank (RankFunction.scale s ρ) i A =
      universalHomologicalRank (RankFunction.scale (s + 1) ρ) i A at he
    rw [power_homologicalRank ρ hρ i hs,
      power_homologicalRank ρ hρ i (by omega)] at he
    nlinarith
  · intro h
    apply RankFunction.ext_fun
    intro A
    change ρ A + universalHomologicalRank (RankFunction.scale s ρ) i A =
      universalHomologicalRank (RankFunction.scale (s + 1) ρ) i A
    rw [power_homologicalRank ρ hρ i hs,
      power_homologicalRank ρ hρ i (by omega), h A]
    nlinarith

section Ideals

variable {k : Type*} [CommSemiring k] [Nontrivial k]

theorem monomialIdeal_ne_bot_iff (B : Family V) :
    monomialIdeal k B ≠ ⊥ ↔ B.Nonempty := by
  constructor
  · intro h
    by_contra hn
    have he := not_nonempty_iff_eq_empty.mp hn
    exact h (by simp [he, monomialIdeal])
  · rintro ⟨a, ha⟩ hbot
    have hm : MvPolynomial.monomial a (1 : k) ∈ monomialIdeal k B :=
      Ideal.subset_span ⟨a, ha, rfl⟩
    rw [hbot] at hm
    simpa using hm

theorem rankShiftIdeal_ne_bot_iff (g : RankFunction V) (i : ℕ) :
    rankShiftIdeal k g i ≠ ⊥ ↔ (rankShiftFamily g i).Nonempty := by
  rw [rankShiftIdeal_eq_monomialIdeal, monomialIdeal_ne_bot_iff]

theorem powerShiftIdeal_ne_bot_iff_threshold (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ} (hs : 1 ≤ s) :
    rankShiftIdeal k (RankFunction.scale s ρ) i ≠ ⊥ ↔
      powerThreshold ρ i univ ≤ s := by
  rw [rankShiftIdeal_ne_bot_iff, powerShiftFamily_nonempty_iff_threshold ρ hρ i hi hs]

theorem powerShiftIdeal_eq_bot_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) {s : ℕ} (hs : 1 ≤ s) :
    rankShiftIdeal k (RankFunction.scale s ρ) i = ⊥ := by
  rw [rankShiftIdeal_eq_monomialIdeal, powerShiftFamily_empty_of_above ρ hρ i hi hs]
  simp [monomialIdeal]

theorem powerShiftIdeal_mul_le (ρ : RankFunction V) (i n s : ℕ) :
    (rankIdeal k ρ) ^ n * rankShiftIdeal k (RankFunction.scale s ρ) i ≤
      rankShiftIdeal k (RankFunction.scale (n + s) ρ) i := by
  have h := rankIdeal_mul_rankShiftIdeal_le (k := k)
    (RankFunction.scale n ρ) (RankFunction.scale s ρ) i
  have he : (RankFunction.scale n ρ).add (RankFunction.scale s ρ) =
      RankFunction.scale (n + s) ρ := by
    apply RankFunction.ext_fun
    intro A
    change n * ρ A + s * ρ A = (n + s) * ρ A
    exact (Nat.add_mul n s (ρ A)).symm
  rwa [rankIdeal_scale, he] at h

/-- After the first nonzero piece, consecutive actual ideals agree under
the Rees action exactly at and beyond the global threshold. -/
theorem powerShiftIdeal_mul_eq_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ} (hs : 1 ≤ s)
    (hr : powerThreshold ρ i univ ≤ s) :
    rankIdeal k ρ * rankShiftIdeal k (RankFunction.scale s ρ) i =
        rankShiftIdeal k (RankFunction.scale (s + 1) ρ) i ↔
      globalPowerThreshold ρ i ≤ s := by
  have h0 := (rankShiftFamily_nonempty_iff _ i).mp
    ((powerShiftFamily_nonempty_iff_threshold ρ hρ i hi hs).mpr hr)
  have h1 := (rankShiftFamily_nonempty_iff _ i).mp
    ((powerShiftFamily_nonempty_iff_threshold ρ hρ i hi (by omega)).mpr
      (show powerThreshold ρ i univ ≤ s + 1 by omega))
  rw [rankShiftIdeal, if_pos h0, rankShiftIdeal, if_pos h1, ← rankIdeal_add]
  rw [(rankIdeal_injective k).eq_iff]
  exact power_homologicalRank_add_eq_iff ρ hρ i hs

end Ideals

end CommAlg.Polymatroid

end
end CheckedSource70

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "71: CommAlg.KoszulComplex.TorGrading\n"

/-! ## Source: CommAlg.KoszulComplex.TorGrading -/
section CheckedSource71

/-! # Completeness and independence of the genuine Tor multigrading

Every derived Tor class is a finite sum of the degree components defined in `GradedTor`.
The projections onto distinct components annihilate one another, so this is a genuine
internal grading of the actual derived tensor module.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false

namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Distinct multidegrees have orthogonal chain projections. -/
lemma homogeneousInclusion_retraction_ne (B : Family V) (a b : Exponent V)
    (hab : a ≠ b) :
    homogeneousInclusion (k := k) B a ≫ homogeneousRetraction (k := k) B b = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact Grading.projection_eq_zero (Ne.symm hab) z.property

/-- The chain endomorphism projecting to one degree and including it again. -/
def homogeneousProjector (B : Family V) (a : Exponent V) :
    underlyingComplex (k := k) B ⟶ underlyingComplex (k := k) B :=
  homogeneousRetraction (k := k) B a ≫ homogeneousInclusion (k := k) B a

@[simp] lemma homogeneousProjector_f (B : Family V) (a : Exponent V) (i : ℕ) :
    (homogeneousProjector (k := k) B a).f i =
      ModuleCat.ofHom (homogeneousProjection (k := k) B a i) := rfl

/-- Every actual Koszul homology class is a finite sum of its homogeneous projections. -/
lemma homogeneous_homology_decomposition (B : Family V) (i : ℕ)
    (x : (underlyingComplex (k := k) B).homology i) :
    ∃ s : Finset (Exponent V),
      ∑ a ∈ s, HomologicalComplex.homologyMap (homogeneousProjector (k := k) B a) i x = x := by
  let K := underlyingComplex (k := k) B
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance x
  let s := ((monomialCoefficientBasis (k := k) B i).repr (K.iCycles i z)).support.image
    monomialDegree
  have hz : ∑ a ∈ s, HomologicalComplex.cyclesMap
      (homogeneousProjector (k := k) B a) i z = z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    rw [map_sum]
    calc
      ∑ a ∈ s, K.iCycles i
          (HomologicalComplex.cyclesMap (homogeneousProjector (k := k) B a) i z) =
          ∑ a ∈ s, homogeneousProjection (k := k) B a i (K.iCycles i z) := by
        apply Finset.sum_congr rfl
        intro a ha
        have h := congrArg (fun f : K.cycles i ⟶ K.X i => f z)
          (HomologicalComplex.cyclesMap_i (homogeneousProjector (k := k) B a) i)
        exact h
      _ = _ := homogeneous_decomposition B i (K.iCycles i z)
  refine ⟨s, ?_⟩
  calc
    ∑ a ∈ s, HomologicalComplex.homologyMap (homogeneousProjector (k := k) B a) i
        (K.homologyπ i z) =
        ∑ a ∈ s, K.homologyπ i
          (HomologicalComplex.cyclesMap (homogeneousProjector (k := k) B a) i z) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact congrArg (fun f : K.cycles i ⟶ K.homology i => f z)
        (HomologicalComplex.homologyπ_naturality (homogeneousProjector (k := k) B a) i)
    _ = K.homologyπ i
        (∑ a ∈ s, HomologicalComplex.cyclesMap
          (homogeneousProjector (k := k) B a) i z) := (map_sum _ _ _).symm
    _ = _ := congrArg (K.homologyπ i) hz

variable [Nontrivial k]

/-- A nonzero multigraded Betti component forces the genuine derived Tor module to be nonzero. -/
lemma derivedTor_nonzero_of_graded (B : Family V) (a : Exponent V) (i : ℕ)
    (h : GradedBettiNonzero (k := k) B a i) :
    ¬ IsZero (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) := by
  intro hz
  letI : Subsingleton (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  apply h
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  apply Subtype.ext
  exact Subsingleton.elim (α := finitePolynomialTor i
    (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) x.val y.val

end CommAlg.Koszul

end
end CheckedSource71

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "72: CommAlg.KoszulComplex.BettiNumbers\n"

/-! ## Source: CommAlg.KoszulComplex.BettiNumbers -/
section CheckedSource72

/-! # Genuine finite multigraded Betti numbers

Over a field, every homogeneous component of the derived Tor module is finite-dimensional.
Its dimension therefore has positive support exactly at the degree components used to define
homological shift ideals.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

instance homogeneousPiece_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (homogeneousPiece (k := k) B a i) := by
  letI : FiniteDimensional k (Simplicial.Chains (k := k) (koszulFaces B a) i) :=
    (faceChainBasis (k := k) B a i).finiteDimensional_of_finite
  exact FiniteDimensional.of_injective (faceHomogeneousEquiv (k := k) B a i).symm.toLinearMap
    (faceHomogeneousEquiv (k := k) B a i).symm.injective

instance homogeneousHomology_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k ((homogeneousComplex (k := k) B a).homology i) := by
  let K := homogeneousComplex (k := k) B a
  letI : FiniteDimensional k (K.X i) := homogeneousPiece_finite B a i
  letI : FiniteDimensional k (K.cycles i) :=
    FiniteDimensional.of_injective (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance)
  exact FiniteDimensional.of_surjective (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance)

instance gradedTor_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (gradedTor (k := k) B a i) := by
  exact FiniteDimensional.of_injective (gradedTorIso (k := k) B a i).inv.hom
    ((ModuleCat.mono_iff_injective (gradedTorIso (k := k) B a i).inv).mp inferInstance)

/-- The actual multigraded Betti number: dimension of the corresponding derived Tor component. -/
def bettiNumber (B : Family V) (a : Exponent V) (i : ℕ) : ℕ :=
  Module.finrank k (gradedTor (k := k) B a i)

lemma bettiNumber_pos_iff (B : Family V) (a : Exponent V) (i : ℕ) :
    0 < bettiNumber (k := k) B a i ↔ GradedBettiNonzero (k := k) B a i := by
  unfold bettiNumber GradedBettiNonzero
  rw [Nat.pos_iff_ne_zero]
  have he : Module.finrank k (gradedTor (k := k) B a i) = 0 ↔
      Subsingleton (gradedTor (k := k) B a i) :=
    Module.finrank_zero_iff (R := k) (M := gradedTor (k := k) B a i)
  exact (not_congr he).trans (not_congr (ModuleCat.isZero_iff_subsingleton
    (M := ModuleCat.of k (gradedTor (k := k) B a i))).symm)

lemma bettiNumber_pos_iff_faces (B : Family V) (a : Exponent V) (i : ℕ) :
    0 < bettiNumber (k := k) B a i ↔
      Simplicial.NonzeroHomology (k := k) (koszulFaces B a) i := by
  rw [bettiNumber_pos_iff, gradedBettiNonzero_iff_faces]

end CommAlg.Koszul

end
end CheckedSource72

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "73: CommAlg.Polymatroid.HomologicalRankTheorem\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalRankTheorem -/
section CheckedSource73

/-! # The ideal-level rank formula and numerical Betti correspondence -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- Theorem 1.2 as a literal equality of actual homological-shift ideals. -/
theorem homologicalShiftIdeal_partitionFormula (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g)
    (hg : g.Active) (i : ℕ) :
    homologicalShiftIdeal I hI i =
      if homologicalRank g hg i univ = g univ + i then
        rankIdeal k (homologicalRank g hg i) else ⊥ := by
  rw [homologicalShiftIdeal_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he]
  exact homologicalShift_rankBases_active g hg i

theorem homologicalShiftIdeal_generators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) (i : ℕ) :
    idealGenerators (homologicalShiftIdeal I hI i) (homologicalShiftIdeal_polymatroidal I hI i) =
      rankShiftFamily g i := by
  apply idealGenerators_eq_of_presentation _ _ _ (rankShiftFamily_polymatroidal g i)
  rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g he i, rankShiftIdeal_eq_monomialIdeal]

/-- The rank displayed in the main theorem is the canonical rank of the
actual minimal generators whenever the homological shift is nonzero. -/
theorem homologicalShiftIdeal_canonicalRank (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) (i : ℕ)
    (hne : homologicalShiftIdeal I hI i ≠ ⊥) (A : Finset V) :
    upperRank (idealGenerators (homologicalShiftIdeal I hI i)
      (homologicalShiftIdeal_polymatroidal I hI i)) A = universalHomologicalRank g i A := by
  rw [homologicalShiftIdeal_generators I hI g he i]
  apply rankShiftFamily_upperRank
  rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g he i] at hne
  exact (rankShiftIdeal_ne_bot_iff g i).mp hne

section Field

variable {l : Type u} [Field l]

/-- The numerical multigraded Betti numbers have precisely the stated
rank-family support; finite-dimensionality is independently proved. -/
theorem bettiNumber_rankBases_pos_iff (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    0 < Koszul.bettiNumber (k := l) (rankBases g) a i ↔ a ∈ rankShiftFamily g i := by
  rw [Koszul.bettiNumber_pos_iff, gradedBettiNonzero_rankBases_iff]

theorem bettiNumber_ideal_pos_iff (I : Ideal (MvPolynomial V l))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal l g)
    (a : Exponent V) (i : ℕ) :
    0 < Koszul.bettiNumber (k := l) (idealGenerators I hI) a i ↔
      a ∈ rankShiftFamily g i := by
  rw [idealGenerators_eq_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he,
    bettiNumber_rankBases_pos_iff]

end Field

end CommAlg.Polymatroid

end
end CheckedSource73

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "74: CommAlg.Polymatroid.UniversalPowerStabilization\n"

/-! ## Source: CommAlg.Polymatroid.UniversalPowerStabilization -/
section CheckedSource74

/-! # Uniform stabilization without an activity restriction

The universal partition rank treats inactive variables with their correct
integer block costs. Its defect formula proves the entire range `s ≥ i` for
arbitrary twists, and the resulting identities are equalities of actual
polynomial ideals, including the vanishing shift cases.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cardinalLift_partition_cost_defect (g : RankFunction V)
    {A : Finset V} (P : Finpartition A) :
    partitionCost (cardinalLift g) P = g A + partitionDefect g P + partitionSlack P := by
  have hc := cardinalLift_cost_add_parts g P
  have hd := partitionDefect_add_rank g P
  have hs := partitionSlack_add_parts P
  omega

theorem universalAugmentedRank_defect (g : RankFunction V) (A : Finset V) :
    universalAugmentedRank g A =
      g A + finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P) := by
  change finiteMinimum (fun P : Finpartition A => partitionCost (cardinalLift g) P) = _
  rw [← finiteMinimum_add_const]
  congr 1
  funext P
  simpa only [Nat.add_assoc] using cardinalLift_partition_cost_defect g P

theorem universalHomologicalRank_defect (g : RankFunction V) (i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    universalHomologicalRank g i A = g A +
      min i (finiteMinimum (fun P : Finpartition A => partitionDefect g P + partitionSlack P)) := by
  rw [universalHomologicalRank_apply g i hA, universalAugmentedRank_defect,
    Nat.add_min_add_left]

theorem twistedPower_universalHomologicalRank (η ρ : RankFunction V) (s i : ℕ)
    {A : Finset V} (hA : A.Nonempty) :
    universalHomologicalRank (twistedPowerRank η ρ s) i A =
      twistedPowerRank η ρ s A + min i
        (finiteMinimum (fun P : Finpartition A =>
          s * partitionDefect ρ P + partitionDefect η P + partitionSlack P)) := by
  rw [universalHomologicalRank_defect _ i hA]
  simp only [twistedPower_defect]

/-- The rank identity is valid for all ranks, including loops and the unit
ideal, with no deletion of coordinates. -/
theorem twistedPower_universalHomologicalRank_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) (A : Finset V) :
    universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i A =
      ρ A + universalHomologicalRank (twistedPowerRank η ρ s) i A := by
  by_cases hA : A = ∅
  · simp [hA]
  have hA' := Finset.nonempty_iff_ne_empty.mpr hA
  rw [twistedPower_universalHomologicalRank η ρ (s + 1) i hA',
    twistedPower_universalHomologicalRank η ρ s i hA']
  have hcap := cappedAffineMinimum_stable i
    (fun P : Finpartition A => partitionDefect ρ P)
    (fun P => partitionDefect η P + partitionSlack P) hs
  simp only [cappedAffineMinimum, ← Nat.add_assoc] at hcap
  rw [hcap]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

theorem twistedPower_universalRank_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) :
    universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i =
      ρ.add (universalHomologicalRank (twistedPowerRank η ρ s) i) := by
  apply RankFunction.ext_fun
  exact twistedPower_universalHomologicalRank_succ η ρ i s hs

theorem twistedPower_universalTotal_rank_eq_iff (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) :
    universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i univ =
        twistedPowerRank η ρ (s + 1) univ + i ↔
      universalHomologicalRank (twistedPowerRank η ρ s) i univ =
        twistedPowerRank η ρ s univ + i := by
  rw [twistedPower_universalHomologicalRank_succ η ρ i s hs univ]
  simp only [twistedPowerRank_apply, Nat.add_mul, Nat.one_mul]
  omega

section Ideals

variable (k : Type*) [CommSemiring k]

/-- The complete ideal identity underlying Theorem 1.1, including arbitrary
fixed twists and all zero shift layers. -/
theorem twistedPower_rankShiftIdeal_succ (η ρ : RankFunction V) (i s : ℕ)
    (hs : i ≤ s) :
    rankShiftIdeal k (twistedPowerRank η ρ (s + 1)) i =
      rankIdeal k ρ * rankShiftIdeal k (twistedPowerRank η ρ s) i := by
  by_cases h0 : universalHomologicalRank (twistedPowerRank η ρ s) i univ =
      twistedPowerRank η ρ s univ + i
  · have h1 := (twistedPower_universalTotal_rank_eq_iff η ρ i s hs).mpr h0
    rw [rankShiftIdeal, if_pos h1, rankShiftIdeal, if_pos h0,
      twistedPower_universalRank_succ η ρ i s hs, rankIdeal_add]
  · have h1 : ¬ universalHomologicalRank (twistedPowerRank η ρ (s + 1)) i univ =
        twistedPowerRank η ρ (s + 1) univ + i :=
      fun h => h0 ((twistedPower_universalTotal_rank_eq_iff η ρ i s hs).mp h)
    simp [rankShiftIdeal, h1, h0]

theorem rankIdeal_twistedPower (η ρ : RankFunction V) (s : ℕ) :
    rankIdeal k (twistedPowerRank η ρ s) = rankIdeal k η * rankIdeal k ρ ^ s := by
  rw [twistedPowerRank, rankIdeal_add, rankIdeal_scale]

theorem power_rankShiftIdeal_succ (ρ : RankFunction V) (i s : ℕ) (hs : i ≤ s) :
    rankShiftIdeal k (ρ.scale (s + 1)) i =
      rankIdeal k ρ * rankShiftIdeal k (ρ.scale s) i := by
  have he (n : ℕ) : twistedPowerRank zeroRank ρ n = ρ.scale n := by
    apply RankFunction.ext_fun
    intro A
    simp [twistedPowerRank_apply, RankFunction.scale]
  simpa only [he] using twistedPower_rankShiftIdeal_succ k zeroRank ρ i s hs

end Ideals

section SeveralColors

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem multiRank_erase_decompose (ρ : J → RankFunction V) (s : J →₀ ℕ) (j : J) :
    multiRank ρ s = (multiRank ρ (s.erase j)).add ((ρ j).scale (s j)) := by
  have he : s.erase j + Finsupp.single j (s j) = s := by
    ext x
    by_cases hx : x = j
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  conv_lhs => rw [← he]
  rw [multiRank_add, multiRank_single]

theorem twistedMultiRank_erase_decompose (η : RankFunction V)
    (ρ : J → RankFunction V) (s : J →₀ ℕ) (j : J) :
    η.add (multiRank ρ s) =
      twistedPowerRank (η.add (multiRank ρ (s.erase j))) (ρ j) (s j) := by
  rw [multiRank_erase_decompose ρ s j]
  apply RankFunction.ext_fun
  intro A
  change η A + (multiRank ρ (s.erase j) A + s j * ρ j A) =
    (η A + multiRank ρ (s.erase j) A) + s j * ρ j A
  omega

theorem twistedMultiRank_succ_decompose (η : RankFunction V)
    (ρ : J → RankFunction V) (s : J →₀ ℕ) (j : J) :
    η.add (multiRank ρ (s + Finsupp.single j 1)) =
      twistedPowerRank (η.add (multiRank ρ (s.erase j))) (ρ j) (s j + 1) := by
  rw [twistedMultiRank_erase_decompose η ρ (s + Finsupp.single j 1) j]
  have he : (s + Finsupp.single j 1).erase j = s.erase j := by
    ext x
    by_cases hx : x = j
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  simp only [he, Finsupp.add_apply, Finsupp.single_eq_same]

/-- Corollary 4.1 at the rank-ideal level: each coordinate stabilizes in the
same complete range, with all other colors absorbed into an arbitrary twist. -/
theorem multi_rankShiftIdeal_succ (k : Type*) [CommSemiring k]
    (η : RankFunction V) (ρ : J → RankFunction V) (s : J →₀ ℕ)
    (i : ℕ) (j : J) (hs : i ≤ s j) :
    rankShiftIdeal k (η.add (multiRank ρ (s + Finsupp.single j 1))) i =
      rankIdeal k (ρ j) * rankShiftIdeal k (η.add (multiRank ρ s)) i := by
  rw [twistedMultiRank_succ_decompose, twistedMultiRank_erase_decompose η ρ s j]
  exact twistedPower_rankShiftIdeal_succ k _ _ i (s j) hs

end SeveralColors

end CommAlg.Polymatroid

end
end CheckedSource74

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "75: CommAlg.IntegralClosure.Weight\n"

/-! ## Source: CommAlg.IntegralClosure.Weight -/
section CheckedSource75

/-! # Linear-weight bounds and initial forms in polynomial domains -/

noncomputable section

namespace CommAlg.Weight

open Classical Finset
open scoped Pointwise

variable {V k : Type*} [DecidableEq V] [CommRing k]

def Bound (w : V → ℤ) (c : ℤ) (p : MvPolynomial V k) : Prop :=
  ∀ a, p.coeff a ≠ 0 → c ≤ Finsupp.weight w a

theorem bound_zero (w : V → ℤ) (c : ℤ) : Bound w c (0 : MvPolynomial V k) := by
  intro a ha
  simp at ha

theorem Bound.mono {w : V → ℤ} {c d : ℤ} {p : MvPolynomial V k}
    (hp : Bound w c p) (hd : d ≤ c) : Bound w d p := fun a ha => hd.trans (hp a ha)

theorem Bound.add {w : V → ℤ} {c : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w c p) (hq : Bound w c q) : Bound w c (p + q) := by
  intro a ha
  by_cases hpa : p.coeff a = 0
  · apply hq a
    simpa only [MvPolynomial.coeff_add, hpa, zero_add] using ha
  · exact hp a hpa

theorem Bound.neg {w : V → ℤ} {c : ℤ} {p : MvPolynomial V k}
    (hp : Bound w c p) : Bound w c (-p) := by
  intro a ha
  exact hp a (by simpa using ha)

theorem Bound.mul {w : V → ℤ} {c d : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w c p) (hq : Bound w d q) : Bound w (c + d) (p * q) := by
  intro a ha
  have hm := MvPolynomial.support_mul p q (MvPolynomial.mem_support_iff.mpr ha)
  obtain ⟨b, hb, e, he, rfl⟩ := Finset.mem_add.mp hm
  rw [map_add]
  exact add_le_add (hp b (MvPolynomial.mem_support_iff.mp hb))
    (hq e (MvPolynomial.mem_support_iff.mp he))

theorem bound_one (w : V → ℤ) : Bound w 0 (1 : MvPolynomial V k) := by
  intro a ha
  by_cases h : a = 0
  · subst a; simp
  · simp [MvPolynomial.coeff_one, h, Ne.symm h] at ha

theorem Bound.pow {w : V → ℤ} {c : ℤ} {p : MvPolynomial V k}
    (hp : Bound w c p) (n : ℕ) : Bound w ((n : ℤ) * c) (p ^ n) := by
  induction n with
  | zero => simpa using bound_one w
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hp

theorem bound_sum {ι : Type*} (w : V → ℤ) (c : ℤ) (s : Finset ι)
    (f : ι → MvPolynomial V k) (hf : ∀ i ∈ s, Bound w c (f i)) :
    Bound w c (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using bound_zero w c
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem exists_minimum (w : V → ℤ) {p : MvPolynomial V k} (hp : p ≠ 0) :
    ∃ m : ℤ, Bound w m p ∧ ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m := by
  have hS := MvPolynomial.support_nonempty.mpr hp
  let m := p.support.inf' hS (Finsupp.weight w)
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_inf' hS (Finsupp.weight w)
  refine ⟨m, ?_, a, MvPolynomial.mem_support_iff.mp ha, he.symm⟩
  intro b hb
  exact Finset.inf'_le _ (MvPolynomial.mem_support_iff.mpr hb)

abbrev initial (w : V → ℤ) (m : ℤ) (p : MvPolynomial V k) : MvPolynomial V k :=
  MvPolynomial.weightedHomogeneousComponent w m p

theorem initial_ne_zero {w : V → ℤ} {m : ℤ} {p : MvPolynomial V k}
    (h : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m) : initial w m p ≠ 0 := by
  obtain ⟨a, ha, haw⟩ := h
  intro he
  have hc := congrArg (fun q : MvPolynomial V k => q.coeff a) he
  apply ha
  simpa only [initial, MvPolynomial.coeff_weightedHomogeneousComponent, haw,
    ↓reduceIte, MvPolynomial.coeff_zero, Finsupp.zero_apply] using hc

/-- The lowest nonzero weighted homogeneous components multiply exactly. -/
theorem initial_mul {w : V → ℤ} {m n : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w m p) (hq : Bound w n q) :
    initial w (m + n) (p * q) = initial w m p * initial w n q := by
  ext a
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_mul]
  by_cases haw : Finsupp.weight w a = m + n
  · rw [if_pos haw]
    apply Finset.sum_congr rfl
    rintro ⟨b, c⟩ hbc
    have hsum : b + c = a := Finset.mem_antidiagonal.mp hbc
    by_cases hb : p.coeff b = 0
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hb]
    by_cases hc : q.coeff c = 0
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hc]
    have hbw := hp b hb
    have hcw := hq c hc
    have hsumw : Finsupp.weight w b + Finsupp.weight w c = m + n := by
      rw [← map_add, hsum, haw]
    have hbm : Finsupp.weight w b = m := by omega
    have hcn : Finsupp.weight w c = n := by omega
    simp [MvPolynomial.coeff_weightedHomogeneousComponent, hbm, hcn]
  · rw [if_neg haw]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨b, c⟩ hbc
    have hsum : b + c = a := Finset.mem_antidiagonal.mp hbc
    by_cases hbm : Finsupp.weight w b = m
    · have hcn : Finsupp.weight w c ≠ n := by
        intro hcn
        apply haw
        rw [← hsum, map_add, hbm, hcn]
      simp [MvPolynomial.coeff_weightedHomogeneousComponent, hcn]
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hbm]

theorem minimum_mul [IsDomain k] {w : V → ℤ} {m n : ℤ} {p q : MvPolynomial V k}
    (hp : Bound w m p) (hq : Bound w n q)
    (hpm : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m)
    (hqn : ∃ a, q.coeff a ≠ 0 ∧ Finsupp.weight w a = n) :
    ∃ a, (p * q).coeff a ≠ 0 ∧ Finsupp.weight w a = m + n := by
  have hn : initial w (m + n) (p * q) ≠ 0 := by
    rw [initial_mul hp hq]
    exact mul_ne_zero (initial_ne_zero hpm) (initial_ne_zero hqn)
  obtain ⟨a, ha⟩ := MvPolynomial.support_nonempty.mpr hn
  have hc := MvPolynomial.mem_support_iff.mp ha
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hc
  split_ifs at hc with haw
  · exact ⟨a, hc, haw⟩
  · exact (hc rfl).elim

theorem minimum_pow [IsDomain k] {w : V → ℤ} {m : ℤ} {p : MvPolynomial V k}
    (hp : Bound w m p) (hpm : ∃ a, p.coeff a ≠ 0 ∧ Finsupp.weight w a = m) (n : ℕ) :
    ∃ a, (p ^ n).coeff a ≠ 0 ∧ Finsupp.weight w a = (n : ℤ) * m := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha, haw⟩ := minimum_mul (hp.pow n) hp ih hpm
    exact ⟨a, by simpa only [pow_succ] using ha, by
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using haw⟩

end CommAlg.Weight

end
end CheckedSource75

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "76: CommAlg.IntegralClosure.Ideal\n"

/-! ## Source: CommAlg.IntegralClosure.Ideal -/
section CheckedSource76

/-! # Integral closure of ideals cut out by integer linear weights

Mathlib's ring-integrality theory does not yet define integrality over an
ideal.  The definition here is the usual monic equation
`x^n + ∑_{i<n} c_i*x^i = 0`, with `c_i ∈ I^(n-i)`.
-/

noncomputable section

namespace CommAlg

open Classical Finset

variable {R : Type*} [CommRing R]

/-- The standard monic-equation definition of integrality over an ideal. -/
def IntegralOverIdeal (I : Ideal R) (x : R) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ c : ℕ → R,
    (∀ i < n, c i ∈ I ^ (n - i)) ∧ x ^ n + ∑ i ∈ Finset.range n, c i * x ^ i = 0

def IsIntegrallyClosedIdeal (I : Ideal R) : Prop :=
  ∀ x : R, IntegralOverIdeal I x → x ∈ I

theorem integralOverIdeal_of_mem {I : Ideal R} {x : R} (hx : x ∈ I) :
    IntegralOverIdeal I x := by
  refine ⟨1, by omega, fun _ => -x, ?_, ?_⟩
  · intro i hi
    have he : i = 0 := by omega
    simpa [he] using I.neg_mem hx
  · simp

namespace Weight

variable {V k : Type*} [DecidableEq V] [CommRing k]

def cutIdeal (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℤ) : Ideal R where
  carrier := {x | Bound w c (f x)}
  zero_mem' := by simpa using bound_zero w c
  add_mem' hx hy := by simpa using hx.add hy
  smul_mem' r x hx := by
    change Bound w c (f (r * x))
    simpa only [smul_eq_mul, map_mul, zero_add] using (h0 r).mul hx

@[simp] theorem mem_cutIdeal (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℤ) (x : R) :
    x ∈ cutIdeal f w h0 c ↔ Bound w c (f x) := Iff.rfl

theorem bound_of_mem_pow (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (I : Ideal R) (c : ℤ)
    (hI : ∀ x ∈ I, Bound w c (f x)) (n : ℕ) {x : R} (hx : x ∈ I ^ n) :
    Bound w ((n : ℤ) * c) (f x) := by
  induction n generalizing x with
  | zero => simpa using h0 x
  | succ n ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on (C := fun y => Bound w ((↑(n + 1) : ℤ) * c) (f y)) hx ?_ ?_
    · intro a ha b hb
      have h := (ih ha).mul (hI b hb)
      simpa only [map_mul, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h
    · intro a b ha hb
      simpa only [map_add] using ha.add hb

theorem bound_of_integral [IsDomain k] (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (I : Ideal R) (c : ℤ)
    (hI : ∀ x ∈ I, Bound w c (f x)) {x : R} (hx : IntegralOverIdeal I x) :
    Bound w c (f x) := by
  by_contra hn
  simp only [Bound, not_forall, not_le] at hn
  obtain ⟨a₀, ha₀, hbad⟩ := hn
  have hfx : f x ≠ 0 := by intro he; simp [he] at ha₀
  obtain ⟨m, hm, hmin⟩ := exists_minimum w hfx
  have hmc : m < c := (hm a₀ ha₀).trans_lt hbad
  obtain ⟨n, hn, b, hb, heq⟩ := hx
  obtain ⟨a, hap, haw⟩ := minimum_pow hm hmin n
  have hsum : Bound w ((n : ℤ) * m + 1)
      (∑ i ∈ Finset.range n, f (b i) * (f x) ^ i) := by
    apply bound_sum
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hbnd := (bound_of_mem_pow f w h0 I c hI (n - i) (hb i hin)).mul (hm.pow i)
    apply hbnd.mono
    have hni : ((n - i : ℕ) : ℤ) + i = n := by
      exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hin)
    have hpos : (0 : ℤ) < ((n - i : ℕ) : ℤ) := by
      exact_mod_cast Nat.sub_pos_of_lt hin
    have hprod : (0 : ℤ) < ((n - i : ℕ) : ℤ) * (c - m) := mul_pos hpos (by omega)
    have hprod1 : (1 : ℤ) ≤ ((n - i : ℕ) : ℤ) * (c - m) := by omega
    rw [← hni]
    nlinarith
  have hsumcoeff : (∑ i ∈ Finset.range n, f (b i) * (f x) ^ i).coeff a = 0 := by
    by_contra hne
    have h := hsum a hne
    rw [haw] at h
    omega
  have heq' : (f x) ^ n + ∑ i ∈ Finset.range n, f (b i) * (f x) ^ i = 0 := by
    simpa only [map_add, map_pow, map_sum, map_mul, map_zero] using congrArg f heq
  have hc := congrArg (fun p : MvPolynomial V k => p.coeff a) heq'
  apply hap
  simpa only [MvPolynomial.coeff_add, hsumcoeff, add_zero,
    MvPolynomial.coeff_zero, Finsupp.zero_apply] using hc

theorem cutIdeal_integrallyClosed [IsDomain k] (f : R →+* MvPolynomial V k) (w : V → ℤ)
    (h0 : ∀ x, Bound w 0 (f x)) (c : ℤ) : IsIntegrallyClosedIdeal (cutIdeal f w h0 c) := by
  intro x hx
  exact bound_of_integral f w h0 _ c (fun _ h => h) hx

/-- An arbitrary intersection of linear-weight cuts is integrally closed.
The coefficient ring may be any domain, in particular any field. -/
theorem integrallyClosed_of_weight_bounds [IsDomain k] {J : Type*}
    (f : R →+* MvPolynomial V k) (w : J → V → ℤ) (c : J → ℤ)
    (h0 : ∀ j x, Bound (w j) 0 (f x)) (I : Ideal R)
    (hmem : ∀ x, x ∈ I ↔ ∀ j, Bound (w j) (c j) (f x)) : IsIntegrallyClosedIdeal I := by
  intro x hx
  apply (hmem x).mpr
  intro j
  exact bound_of_integral f (w j) (h0 j) I (c j) (fun y hy => (hmem y).mp hy j) hx

end Weight

end CommAlg

end
end CheckedSource76

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "77: CommAlg.IntegralClosure.SemigroupAlgebra\n"

/-! ## Source: CommAlg.IntegralClosure.SemigroupAlgebra -/
section CheckedSource77

/-! # Actual polynomial subalgebras supported on additive exponent semigroups -/

noncomputable section

namespace CommAlg

open Classical Finset
open scoped Pointwise

variable {V k : Type*} [DecidableEq V] [CommRing k]

def supportedSubalgebra (k : Type*) [CommRing k] (S : AddSubmonoid (V →₀ ℕ)) :
    Subalgebra k (MvPolynomial V k) where
  carrier := {p | ∀ a ∈ p.support, a ∈ S}
  zero_mem' := by simp
  one_mem' := by
    intro a ha
    have hm : a ∈ (MvPolynomial.monomial (0 : V →₀ ℕ) (1 : k)).support := by simpa using ha
    have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
    simpa only [he] using S.zero_mem
  add_mem' hp hq := by
    intro a ha
    rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with ha | ha
    · exact hp a ha
    · exact hq a ha
  mul_mem' hp hq := by
    intro a ha
    obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ ha)
    exact S.add_mem (hp b hb) (hq c hc)
  algebraMap_mem' r := by
    intro a ha
    have hm : a ∈ (MvPolynomial.monomial (0 : V →₀ ℕ) r).support := ha
    have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
    simpa only [he] using S.zero_mem

@[simp] theorem mem_supportedSubalgebra (S : AddSubmonoid (V →₀ ℕ)) (p : MvPolynomial V k) :
    p ∈ supportedSubalgebra k S ↔ ∀ a ∈ p.support, a ∈ S := Iff.rfl

theorem monomial_mem_supportedSubalgebra (S : AddSubmonoid (V →₀ ℕ))
    {a : V →₀ ℕ} (ha : a ∈ S) (r : k) :
    MvPolynomial.monomial a r ∈ supportedSubalgebra k S := by
  intro b hb
  simpa only [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)] using ha

@[simp] theorem monomial_one_mem_supportedSubalgebra_iff [Nontrivial k]
    (S : AddSubmonoid (V →₀ ℕ)) (a : V →₀ ℕ) :
    MvPolynomial.monomial a (1 : k) ∈ supportedSubalgebra k S ↔ a ∈ S := by
  constructor
  · intro h
    exact h a (by simp [MvPolynomial.support_monomial])
  · exact fun h => monomial_mem_supportedSubalgebra S h 1

theorem supportedSubalgebra_eq_adjoin (S : AddSubmonoid (V →₀ ℕ)) :
    supportedSubalgebra k S = Algebra.adjoin k
      ((fun a => MvPolynomial.monomial a (1 : k)) '' (S : Set (V →₀ ℕ))) := by
  apply le_antisymm
  · intro p hp
    rw [p.as_sum]
    apply Subalgebra.sum_mem
    intro a ha
    have hm : MvPolynomial.monomial a (1 : k) ∈ Algebra.adjoin k
        ((fun a => MvPolynomial.monomial a (1 : k)) '' (S : Set (V →₀ ℕ))) := by
      apply Algebra.subset_adjoin
      exact ⟨a, hp a ha, rfl⟩
    have hc := (Algebra.adjoin k
      ((fun a => MvPolynomial.monomial a (1 : k)) '' (S : Set (V →₀ ℕ)))).algebraMap_mem (p.coeff a)
    have hmul := Subalgebra.mul_mem _ hc hm
    simpa [MvPolynomial.C_mul_monomial] using hmul
  · apply Algebra.adjoin_le
    rintro _ ⟨a, ha, rfl⟩
    exact monomial_mem_supportedSubalgebra S ha 1

/-- The support model agrees with the usual subalgebra generated by monomials. -/
theorem supported_closure_eq_adjoin (G : Set (V →₀ ℕ)) :
    supportedSubalgebra k (AddSubmonoid.closure G) =
      Algebra.adjoin k ((fun a => MvPolynomial.monomial a (1 : k)) '' G) := by
  rw [supportedSubalgebra_eq_adjoin]
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨a, ha, rfl⟩
    induction ha using AddSubmonoid.closure_induction with
    | mem a ha => exact Algebra.subset_adjoin ⟨a, ha, rfl⟩
    | zero => simpa using (Algebra.adjoin k
        ((fun a => MvPolynomial.monomial a (1 : k)) '' G)).one_mem
    | add a b ha hb iha ihb =>
      have hmul := Subalgebra.mul_mem _ iha ihb
      simpa using hmul
  · apply Algebra.adjoin_mono
    exact Set.image_mono AddSubmonoid.subset_closure

theorem nonnegative_weight_closure (G : Set (V →₀ ℕ)) (w : V → ℤ)
    (hG : ∀ a ∈ G, 0 ≤ Finsupp.weight w a) :
    ∀ a ∈ AddSubmonoid.closure G, 0 ≤ Finsupp.weight w a := by
  intro a ha
  induction ha using AddSubmonoid.closure_induction with
  | mem a ha => exact hG a ha
  | zero => simp
  | add a b ha hb iha ihb => simpa using add_nonneg iha ihb

theorem supported_weight_nonnegative (S : AddSubmonoid (V →₀ ℕ)) (w : V → ℤ)
    (hS : ∀ a ∈ S, 0 ≤ Finsupp.weight w a) (p : supportedSubalgebra k S) :
    Weight.Bound w 0 p.val := by
  intro a ha
  exact hS a (p.property a (MvPolynomial.mem_support_iff.mpr ha))

theorem supported_ideal_integrallyClosed [IsDomain k] {J : Type*}
    (S : AddSubmonoid (V →₀ ℕ)) (w : J → V → ℤ) (c : J → ℤ)
    (hS : ∀ j a, a ∈ S → 0 ≤ Finsupp.weight (w j) a)
    (I : Ideal (supportedSubalgebra k S))
    (hmem : ∀ p, p ∈ I ↔ ∀ j, Weight.Bound (w j) (c j) p.val) :
    IsIntegrallyClosedIdeal I :=
  Weight.integrallyClosed_of_weight_bounds (supportedSubalgebra k S).val.toRingHom w c
    (fun j p => supported_weight_nonnegative S (w j) (hS j) p) I hmem

end CommAlg

end
end CheckedSource77

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "78: CommAlg.IntegralClosure.MultiRees\n"

/-! ## Source: CommAlg.IntegralClosure.MultiRees -/
section CheckedSource78

/-! # The actual multi-Rees subalgebra and its homogeneous ideals

The definition is the ordinary subalgebra of a polynomial ring whose
multidegree-s coefficient lies in the product of ideal powers.
-/

noncomputable section

namespace CommAlg

open Classical Finset

variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

def powerProduct (I : J → Ideal R) (s : J →₀ ℕ) : Ideal R := ∏ j, (I j) ^ (s j)

@[simp] theorem powerProduct_zero (I : J → Ideal R) : powerProduct I 0 = ⊤ := by
  simp [powerProduct]

theorem powerProduct_add (I : J → Ideal R) (s t : J →₀ ℕ) :
    powerProduct I (s + t) = powerProduct I s * powerProduct I t := by
  simp only [powerProduct, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

end CommAlg

namespace CommAlg.PalomarMultiReesSupport
section
open Classical Finset
universe uColorSupport uRingSupport
variable {C : Type uColorSupport} {S : Type uRingSupport}
  [Fintype C] [DecidableEq C] [CommRing S]
/-- Exact existing multi-Rees zero closure proposition. -/
theorem zero (I : C → Ideal S) :
    ∀ s, (0 : MvPolynomial C S).coeff s ∈ powerProduct I s := by simp
/-- Exact existing multi-Rees one closure proposition. -/
theorem one (I : C → Ideal S) :
    ∀ s, (1 : MvPolynomial C S).coeff s ∈ powerProduct I s := by
  intro s
  by_cases hs : s = 0
  · subst s; simp only [powerProduct_zero, Submodule.mem_top]
  · simp [MvPolynomial.coeff_one, hs, Ne.symm hs]
/-- Exact existing multi-Rees add closure proposition. -/
theorem add (I : C → Ideal S) {p q : MvPolynomial C S}
    (hp : ∀ s, p.coeff s ∈ powerProduct I s) (hq : ∀ s, q.coeff s ∈ powerProduct I s) :
    ∀ s, (p + q).coeff s ∈ powerProduct I s := by
  intro s
  simpa only [MvPolynomial.coeff_add] using Ideal.add_mem _ (hp s) (hq s)
/-- Exact existing multi-Rees mul closure proposition. -/
theorem mul (I : C → Ideal S) {p q : MvPolynomial C S}
    (hp : ∀ s, p.coeff s ∈ powerProduct I s) (hq : ∀ s, q.coeff s ∈ powerProduct I s) :
    ∀ s, (p * q).coeff s ∈ powerProduct I s := by
  intro s
  rw [MvPolynomial.coeff_mul]
  apply Ideal.sum_mem
  intro uv huv
  have he : uv.1 + uv.2 = s := Finset.mem_antidiagonal.mp huv
  have h := Ideal.mul_mem_mul (hp uv.1) (hq uv.2)
  rwa [← powerProduct_add, he] at h
/-- Exact existing multi-Rees algebraMap closure proposition. -/
theorem algebraMap (I : C → Ideal S) (r : S) :
    ∀ s, (MvPolynomial.C r).coeff s ∈ powerProduct I s := by
  intro s
  by_cases hs : s = 0
  · subst s; simp only [powerProduct_zero, Submodule.mem_top]
  · simp [MvPolynomial.coeff_C, hs, Ne.symm hs]
end
end CommAlg.PalomarMultiReesSupport

namespace CommAlg
open Classical Finset
variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]
def multiReesAlgebra (I : J → Ideal R) : Subalgebra R (MvPolynomial J R) where
  carrier := {p | ∀ s, p.coeff s ∈ powerProduct I s}
  zero_mem' := PalomarMultiReesSupport.zero I
  one_mem' := PalomarMultiReesSupport.one I
  add_mem' := PalomarMultiReesSupport.add I
  mul_mem' := PalomarMultiReesSupport.mul I
  algebraMap_mem' := PalomarMultiReesSupport.algebraMap I

@[simp] theorem mem_multiReesAlgebra (I : J → Ideal R) (p : MvPolynomial J R) :
    p ∈ multiReesAlgebra I ↔ ∀ s, p.coeff s ∈ powerProduct I s := Iff.rfl

@[simp] theorem monomial_mem_multiReesAlgebra (I : J → Ideal R) (s : J →₀ ℕ) (r : R) :
    MvPolynomial.monomial s r ∈ multiReesAlgebra I ↔ r ∈ powerProduct I s := by
  constructor
  · intro h
    simpa using h s
  · intro h t
    by_cases ht : t = s
    · subst t; simpa using h
    · simp [MvPolynomial.coeff_monomial, ht, Ne.symm ht]

def multiReesIdeal (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) : Ideal (multiReesAlgebra I) where
  carrier := {p | ∀ s, p.val.coeff s ∈ K s}
  zero_mem' := by simp
  add_mem' hp hq := fun s => by
    simpa only [Subalgebra.coe_add, MvPolynomial.coeff_add] using (K s).add_mem (hp s) (hq s)
  smul_mem' r p hp := by
    intro s
    change (r.val * p.val).coeff s ∈ K s
    rw [MvPolynomial.coeff_mul]
    apply Ideal.sum_mem
    intro uv huv
    have he : uv.1 + uv.2 = s := Finset.mem_antidiagonal.mp huv
    rw [← he]
    exact hact uv.1 uv.2 (Ideal.mul_mem_mul (r.property uv.1) (hp uv.2))

@[simp] theorem mem_multiReesIdeal (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) (p : multiReesAlgebra I) :
    p ∈ multiReesIdeal I K hact ↔ ∀ s, p.val.coeff s ∈ K s := Iff.rfl

section Polynomial

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k]

def reesDegree (e : J ⊕ V →₀ ℕ) : J →₀ ℕ :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp e).1

def ordinaryDegree (e : J ⊕ V →₀ ℕ) : V →₀ ℕ :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp e).2

@[simp] theorem reesDegree_apply (e : J ⊕ V →₀ ℕ) (j : J) : reesDegree e j = e (.inl j) := rfl

@[simp] theorem ordinaryDegree_apply (e : J ⊕ V →₀ ℕ) (v : V) : ordinaryDegree e v = e (.inr v) := rfl

theorem coeff_sumAlgEquiv (p : MvPolynomial (J ⊕ V) k) (s : J →₀ ℕ) (a : V →₀ ℕ) :
    (((MvPolynomial.sumAlgEquiv k J V) p).coeff s).coeff a =
      p.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)) := by
  change ((AddMonoidAlgebra.domCongr k k Finsupp.sumFinsuppAddEquivProdFinsupp p).coeff (s,a)) = _
  exact AddMonoidAlgebra.coeff_domCongr _ _ _

theorem coeff_flatten (p : MvPolynomial J (MvPolynomial V k)) (s : J →₀ ℕ) (a : V →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff
      (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)) = (p.coeff s).coeff a := by
  have h := coeff_sumAlgEquiv ((MvPolynomial.sumAlgEquiv k J V).symm p) s a
  simpa only [AlgEquiv.apply_symm_apply] using h.symm

theorem coeff_flatten_at (p : MvPolynomial J (MvPolynomial V k)) (e : J ⊕ V →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff e =
      (p.coeff (reesDegree e)).coeff (ordinaryDegree e) := by
  have h := coeff_flatten p (reesDegree e) (ordinaryDegree e)
  simpa only [reesDegree, ordinaryDegree, Prod.mk.eta, AddEquiv.symm_apply_apply] using h

def multiReesFlatten (I : J → Ideal (MvPolynomial V k)) :
    multiReesAlgebra I →+* MvPolynomial (J ⊕ V) k :=
  (MvPolynomial.sumAlgEquiv k J V).symm.toRingHom.comp (multiReesAlgebra I).val.toRingHom

theorem multiReesFlatten_injective (I : J → Ideal (MvPolynomial V k)) :
    Function.Injective (multiReesFlatten I) :=
  (MvPolynomial.sumAlgEquiv k J V).symm.injective.comp Subtype.val_injective

theorem multiReesFlatten_coeff (I : J → Ideal (MvPolynomial V k))
    (p : multiReesAlgebra I) (e : J ⊕ V →₀ ℕ) :
    (multiReesFlatten I p).coeff e = (p.val.coeff (reesDegree e)).coeff (ordinaryDegree e) :=
  coeff_flatten_at p.val e

theorem mem_polymatroid_multiRees (ρ : J → Polymatroid.RankFunction V)
    (p : MvPolynomial J (MvPolynomial V k)) :
    p ∈ multiReesAlgebra (fun j => Polymatroid.rankIdeal k (ρ j)) ↔
      ∀ e, ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff e ≠ 0 →
        Polymatroid.LowerFeasible (Polymatroid.multiRank ρ (reesDegree e)).lower (ordinaryDegree e) := by
  simp only [mem_multiReesAlgebra, powerProduct, ← Polymatroid.rankIdeal_multiRank]
  constructor
  · intro hp e he
    have hm := (Polymatroid.mem_monomialIdeal_iff _ _).mp (hp (reesDegree e))
    exact (Polymatroid.contains_rankBases_iff _ _).mp
      (hm _ (MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten_at] at he)))
  · intro hp s
    apply (Polymatroid.mem_monomialIdeal_iff _ _).mpr
    intro a ha
    let e := Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)
    have he : ((MvPolynomial.sumAlgEquiv k J V).symm p).coeff e ≠ 0 := by
      rw [coeff_flatten]
      exact MvPolynomial.mem_support_iff.mp ha
    have h := hp e he
    have hs : reesDegree e = s := by simp [e, reesDegree]
    have ha' : ordinaryDegree e = a := by simp [e, ordinaryDegree]
    rw [hs, ha'] at h
    exact (Polymatroid.contains_rankBases_iff _ _).mpr h

end Polynomial

end CommAlg

end
end CheckedSource78

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "79: CommAlg.Rees.BoxGeneration\n"

/-! ## Source: CommAlg.Rees.BoxGeneration -/
section CheckedSource79

/-! # Generating an actual multigraded Rees ideal in a finite box

The conclusion is equality with an ideal span inside the actual multi-Rees
algebra. It follows from coordinatewise stabilization by induction on the
sum of the Rees exponents and the polynomial's homogeneous decomposition.
-/

noncomputable section

namespace CommAlg

open Classical Finset

variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

@[simp] theorem powerProduct_single (I : J → Ideal R) (j : J) (n : ℕ) :
    powerProduct I (Finsupp.single j n) = (I j) ^ n := by
  unfold powerProduct
  rw [Finset.prod_eq_single j]
  · simp
  · intro x hx hxj
    simp [Finsupp.single_apply, hxj, Ne.symm hxj]
  · simp

/-- The coefficient ideal of homogeneous monomials that already belong to an
ideal of the actual Rees algebra. -/
def homogeneousCoefficientIdeal (I : J → Ideal R) (L : Ideal (multiReesAlgebra I))
    (s : J →₀ ℕ) : Ideal R where
  carrier := {r | ∃ p ∈ L, p.val = MvPolynomial.monomial s r}
  zero_mem' := ⟨0, L.zero_mem, by simp⟩
  add_mem' := by
    rintro r t ⟨p, hp, he⟩ ⟨q, hq, hf⟩
    refine ⟨p + q, L.add_mem hp hq, ?_⟩
    change p.val + q.val = _
    rw [he, hf, map_add]
  smul_mem' := by
    intro a r
    rintro ⟨p, hp, he⟩
    refine ⟨(algebraMap R (multiReesAlgebra I) a) * p,
      L.mul_mem_left _ hp, ?_⟩
    change MvPolynomial.C a * p.val = MvPolynomial.monomial s (a * r)
    rw [he, MvPolynomial.C_mul_monomial]

@[simp] theorem mem_homogeneousCoefficientIdeal (I : J → Ideal R)
    (L : Ideal (multiReesAlgebra I)) (s : J →₀ ℕ) (r : R) :
    r ∈ homogeneousCoefficientIdeal I L s ↔
      ∃ p ∈ L, p.val = MvPolynomial.monomial s r := Iff.rfl

/-- Multiplication here is the actual multiplication of homogeneous
polynomials inside the Rees subalgebra. -/
theorem homogeneousCoefficientIdeal_action (I : J → Ideal R)
    (L : Ideal (multiReesAlgebra I)) (s t : J →₀ ℕ) :
    powerProduct I s * homogeneousCoefficientIdeal I L t ≤
      homogeneousCoefficientIdeal I L (s + t) := by
  apply Ideal.mul_le.mpr
  intro r hr q hq
  obtain ⟨p, hp, he⟩ := hq
  let x : multiReesAlgebra I :=
    ⟨MvPolynomial.monomial s r, (monomial_mem_multiReesAlgebra I s r).mpr hr⟩
  refine ⟨x * p, L.mul_mem_left x hp, ?_⟩
  change MvPolynomial.monomial s r * p.val = _
  rw [he, MvPolynomial.monomial_mul_monomial]

/-- All homogeneous module elements whose Rees multidegree belongs to the
closed coordinate box. Polynomial coefficients are unrestricted elements of
the corresponding actual coefficient ideal. -/
def reesBoxGenerators (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R) (i : ℕ) :
    Set (multiReesAlgebra I) :=
  {p | ∃ s r, (∀ j, s j ≤ i) ∧ r ∈ K s ∧ p.val = MvPolynomial.monomial s r}

theorem reesBoxGenerators_subset (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t)) (i : ℕ) :
    reesBoxGenerators I K i ⊆ multiReesIdeal I K hact := by
  rintro p ⟨s, r, hs, hr, he⟩ t
  rw [he]
  by_cases ht : t = s
  · subst t; simpa using hr
  · simp [MvPolynomial.coeff_monomial, ht, Ne.symm ht]

/-- Coordinate stabilization implies equality with the span of the actual
homogeneous elements in the finite Rees-degree box. -/
theorem multiReesIdeal_span_box (I : J → Ideal R) (K : (J →₀ ℕ) → Ideal R)
    (hact : ∀ s t, powerProduct I s * K t ≤ K (s + t))
    (hsub : ∀ s, K s ≤ powerProduct I s) (i : ℕ)
    (hstep : ∀ s j, i ≤ s j → K (s + Finsupp.single j 1) = I j * K s) :
    multiReesIdeal I K hact = Ideal.span (reesBoxGenerators I K i) := by
  let L : Ideal (multiReesAlgebra I) := Ideal.span (reesBoxGenerators I K i)
  have hc : ∀ n : ℕ, ∀ s : J →₀ ℕ, s.degree = n →
      K s ≤ homogeneousCoefficientIdeal I L s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      by_cases hbox : ∀ j, s j ≤ i
      · intro r hr
        let p : multiReesAlgebra I :=
          ⟨MvPolynomial.monomial s r, (monomial_mem_multiReesAlgebra I s r).mpr (hsub s hr)⟩
        exact ⟨p, Ideal.subset_span ⟨s, r, hbox, hr, rfl⟩, rfl⟩
      · push_neg at hbox
        obtain ⟨j, hj⟩ := hbox
        let t := s - Finsupp.single j 1
        have he : t + Finsupp.single j 1 = s := by
          apply tsub_add_cancel_of_le
          intro x
          by_cases hx : x = j
          · subst x
            simpa using (show 1 ≤ s j by omega)
          · simp [Finsupp.single_apply, hx, Ne.symm hx]
        have htj : i ≤ t j := by
          change i ≤ s j - (Finsupp.single j 1) j
          simp only [Finsupp.single_eq_same]
          omega
        have htdeg : t.degree < n := by
          have hh := congrArg Finsupp.degree he
          simp only [map_add, Finsupp.degree_single, hs] at hh
          omega
        have hit := ih t.degree htdeg t rfl
        rw [← he, hstep t j htj]
        calc
          I j * K t ≤ I j * homogeneousCoefficientIdeal I L t := Ideal.mul_mono le_rfl hit
          _ ≤ homogeneousCoefficientIdeal I L (t + Finsupp.single j 1) := by
            have hh := homogeneousCoefficientIdeal_action I L (Finsupp.single j 1) t
            simpa only [powerProduct_single, pow_one, add_comm] using hh
  apply le_antisymm
  · intro p hp
    have hh : ∀ s, ∃ q ∈ L, q.val =
        MvPolynomial.monomial s (p.val.coeff s) := fun s => hc s.degree s rfl (hp s)
    choose q hq he using hh
    have hsum : ∑ s ∈ p.val.support, q s ∈ L :=
      L.sum_mem (fun s hs => hq s)
    have heq : (∑ s ∈ p.val.support, q s) = p := by
      apply Subtype.ext
      change (multiReesAlgebra I).val (∑ s ∈ p.val.support, q s) = p.val
      rw [map_sum]
      calc
        (∑ s ∈ p.val.support, (q s).val) =
            ∑ s ∈ p.val.support, MvPolynomial.monomial s (p.val.coeff s) :=
          Finset.sum_congr rfl (fun s hs => he s)
        _ = p.val := (MvPolynomial.as_sum p.val).symm
    rwa [heq] at hsum
  · exact Ideal.span_le.mpr (reesBoxGenerators_subset I K hact i)

end CommAlg

end
end CheckedSource79

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "80: CommAlg.Polymatroid.HomologicalStabilization\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalStabilization -/
section CheckedSource80

/-! # Stabilization for actual polynomial ideals

These statements use the genuine derived-Tor homological shift of the actual
ideal powers and products. The zero ideal is included explicitly, as are
arbitrary inactive variables, the unit ideal, and fixed polymatroidal twists.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- The complete twisted equality of Theorem 1.1, for actual ideals.
The degree-zero case is also valid. -/
theorem homologicalShift_twistedPowers (I J : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J)
    (i s : ℕ) (hs : i ≤ s) :
    homologicalShiftIdeal (J * I ^ (s + 1)) (hJ.mul (hI.pow (s + 1))) i =
      I * homologicalShiftIdeal (J * I ^ s) (hJ.mul (hI.pow s)) i := by
  rcases hI.eq_bot_or_rank with rfl | ⟨ρ, rfl⟩
  · simp
  rcases hJ.eq_bot_or_rank with rfl | ⟨η, rfl⟩
  · simp
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (twistedPowerRank η ρ (s + 1))
      (rankIdeal_twistedPower k η ρ (s + 1)).symm,
    homologicalShiftIdeal_eq_rankShiftIdeal _ _ (twistedPowerRank η ρ s)
      (rankIdeal_twistedPower k η ρ s).symm]
  exact twistedPower_rankShiftIdeal_succ k η ρ i s hs

/-- Theorem 1.1: no loss of parameter range and no additional activity
hypothesis on the original ideal. -/
theorem homologicalShift_powers (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i s : ℕ) (hs : i ≤ s) :
    homologicalShiftIdeal (I ^ (s + 1)) (hI.pow (s + 1)) i =
      I * homologicalShiftIdeal (I ^ s) (hI.pow s) i := by
  simpa using homologicalShift_twistedPowers I ⊤ hI isPolymatroidalIdeal_top i s hs

section SeveralColors

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem IsPolymatroidalIdeal.powerProduct (I : C → Ideal (MvPolynomial V k))
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (s : C →₀ ℕ) :
    IsPolymatroidalIdeal (CommAlg.powerProduct I s) :=
  IsPolymatroidalIdeal.prod univ (fun c => I c ^ (s c)) (fun c hc => (hI c).pow (s c))

theorem powerProduct_erase_decompose (I : C → Ideal (MvPolynomial V k))
    (s : C →₀ ℕ) (c : C) :
    CommAlg.powerProduct I s = CommAlg.powerProduct I (s.erase c) * I c ^ (s c) := by
  have he : s.erase c + Finsupp.single c (s c) = s := by
    ext x
    by_cases hx : x = c
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  conv_lhs => rw [← he]
  rw [CommAlg.powerProduct_add, CommAlg.powerProduct_single]

theorem twistedPowerProduct_erase_decompose (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (s : C →₀ ℕ) (c : C) :
    J * CommAlg.powerProduct I s =
      (J * CommAlg.powerProduct I (s.erase c)) * I c ^ (s c) := by
  rw [powerProduct_erase_decompose I s c, mul_assoc]

theorem twistedPowerProduct_succ_decompose (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (s : C →₀ ℕ) (c : C) :
    J * CommAlg.powerProduct I (s + Finsupp.single c 1) =
      (J * CommAlg.powerProduct I (s.erase c)) * I c ^ (s c + 1) := by
  rw [twistedPowerProduct_erase_decompose I J (s + Finsupp.single c 1) c]
  have he : (s + Finsupp.single c 1).erase c = s.erase c := by
    ext x
    by_cases hx : x = c
    · subst x; simp
    · simp [Finsupp.erase_apply, hx, Ne.symm hx]
  simp only [he, Finsupp.add_apply, Finsupp.single_eq_same]

/-- The full several-colors equality of Corollary 4.1 on actual ideals,
including zero factors, arbitrary fixed twists and zero exponents. -/
theorem homologicalShift_severalColors (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (s : C →₀ ℕ) (i : ℕ) (c : C) (hs : i ≤ s c) :
    homologicalShiftIdeal (J * CommAlg.powerProduct I (s + Finsupp.single c 1))
        (hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)) i =
      I c * homologicalShiftIdeal (J * CommAlg.powerProduct I s)
        (hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)) i := by
  let K := J * CommAlg.powerProduct I (s.erase c)
  have hK : IsPolymatroidalIdeal K :=
    hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)
  calc
    _ = homologicalShiftIdeal (K * I c ^ (s c + 1)) (hK.mul ((hI c).pow _)) i :=
      homologicalShiftIdeal_congr _ _ (twistedPowerProduct_succ_decompose I J s c) i
    _ = I c * homologicalShiftIdeal (K * I c ^ (s c)) (hK.mul ((hI c).pow _)) i :=
      homologicalShift_twistedPowers (I c) K (hI c) hK i (s c) hs
    _ = _ := congrArg (I c * ·)
      (homologicalShiftIdeal_congr _ _ (twistedPowerProduct_erase_decompose I J s c).symm i)

end SeveralColors

end CommAlg.Polymatroid

end
end CheckedSource80

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "81: CommAlg.IntegralClosure.ShiftWeights\n"

/-! ## Source: CommAlg.IntegralClosure.ShiftWeights -/
section CheckedSource81

/-! # The exact linear inequalities of homological-shift Rees ideals

There are two families of integer weights: the ordinary polymatroid lower
bounds, and one weight for every partition. The empty partition supplies
the total-degree inequality. No positivity assumption on ranks is used.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

def ShiftCut (V : Type*) [DecidableEq V] :=
  Finset V ⊕ (Σ A : Finset V, Finpartition A)

def cutWeight (c : J → ℤ) (A : Finset V) : J ⊕ V → ℤ :=
  Sum.elim c (fun v => if v ∈ Aᶜ then 1 else 0)

theorem weight_cutWeight (c : J → ℤ) (A : Finset V) (e : J ⊕ V →₀ ℕ) :
    Finsupp.weight (cutWeight c A) e =
      (∑ j, (reesDegree e j : ℤ) * c j) + (subsetSum (ordinaryDegree e) Aᶜ : ℤ) := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_sum_type]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply sum_congr rfl
    intro j hj
    simp [cutWeight, nsmul_eq_mul]
  · simp only [cutWeight, Sum.elim_inr, nsmul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem]
    simp [subsetSum]

def shiftWeight (ρ : J → RankFunction V) : ShiftCut V → J ⊕ V → ℤ
  | .inl A => cutWeight (fun j => (ρ j A : ℤ) - ρ j univ) A
  | .inr ⟨A, P⟩ => cutWeight (fun j => (∑ C ∈ P.parts, (ρ j C : ℤ)) - ρ j univ) A

def shiftThreshold (η : RankFunction V) (i : ℕ) : ShiftCut V → ℤ
  | .inl A => (η univ : ℤ) - η A
  | .inr ⟨A, P⟩ => (η univ : ℤ) + i + P.parts.card - A.card - ∑ C ∈ P.parts, (η C : ℤ)

theorem shiftWeight_lower (ρ : J → RankFunction V) (A : Finset V)
    (e : J ⊕ V →₀ ℕ) :
    Finsupp.weight (shiftWeight ρ (.inl A)) e =
      (subsetSum (ordinaryDegree e) Aᶜ : ℤ) +
        multiRank ρ (reesDegree e) A - multiRank ρ (reesDegree e) univ := by
  rw [shiftWeight, weight_cutWeight]
  simp only [mul_sub, sum_sub_distrib, multiRank_apply, Nat.cast_sum, Nat.cast_mul]
  ring

theorem shiftWeight_partition (ρ : J → RankFunction V) (A : Finset V)
    (P : Finpartition A) (e : J ⊕ V →₀ ℕ) :
    Finsupp.weight (shiftWeight ρ (.inr ⟨A, P⟩)) e =
      (subsetSum (ordinaryDegree e) Aᶜ : ℤ) +
        (∑ C ∈ P.parts, (multiRank ρ (reesDegree e) C : ℤ)) -
          multiRank ρ (reesDegree e) univ := by
  rw [shiftWeight, weight_cutWeight]
  simp only [mul_sub, sum_sub_distrib, mul_sum, multiRank_apply, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_comm (s := univ) (t := P.parts)]
  ring

theorem shiftWeight_nonneg (ρ : J → RankFunction V) (e : J ⊕ V →₀ ℕ)
    (he : LowerFeasible (multiRank ρ (reesDegree e)).lower (ordinaryDegree e))
    (t : ShiftCut V) : 0 ≤ Finsupp.weight (shiftWeight ρ t) e := by
  rcases t with A | ⟨A, P⟩
  · rw [shiftWeight_lower]
    have hb := he Aᶜ
    have hL := (multiRank ρ (reesDegree e)).lower_add_compl Aᶜ
    simp only [compl_compl] at hL
    omega
  · rw [shiftWeight_partition]
    have hb := he Aᶜ
    have hL := (multiRank ρ (reesDegree e)).lower_add_compl Aᶜ
    have hP := (multiRank ρ (reesDegree e)).le_sum_partition P
    simp only [compl_compl] at hL
    have hPz : (multiRank ρ (reesDegree e) A : ℤ) ≤
        ∑ C ∈ P.parts, (multiRank ρ (reesDegree e) C : ℤ) := by exact_mod_cast hP
    omega

theorem shiftWeight_bounds_iff {k : Type*} [CommSemiring k] [Nontrivial k]
    (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ)
    (e : J ⊕ V →₀ ℕ) :
    (∀ t, shiftThreshold η i t ≤ Finsupp.weight (shiftWeight ρ t) e) ↔
      MvPolynomial.monomial (ordinaryDegree e) (1 : k) ∈
        rankShiftIdeal k (η.add (multiRank ρ (reesDegree e))) i := by
  rw [monomial_mem_rankShiftIdeal_partition_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hc := h (.inr ⟨∅, Finpartition.empty (Finset V)⟩)
      rw [shiftWeight_partition] at hc
      simp only [shiftThreshold, Finpartition.empty_parts, card_empty, sum_empty,
        compl_empty, subsetSum_univ, Nat.cast_zero, add_zero, sub_zero] at hc
      change η univ + multiRank ρ (reesDegree e) univ + i ≤ (ordinaryDegree e).degree
      omega
    · intro U
      have hc := h (.inl Uᶜ)
      rw [shiftWeight_lower] at hc
      simp only [shiftThreshold, compl_compl] at hc
      have hL := (η.add (multiRank ρ (reesDegree e))).lower_add_compl U
      change (η.add (multiRank ρ (reesDegree e))).lower U +
        (η Uᶜ + multiRank ρ (reesDegree e) Uᶜ) =
          η univ + multiRank ρ (reesDegree e) univ at hL
      omega
    · intro A hA P
      have hc := h (.inr ⟨A, P⟩)
      rw [shiftWeight_partition] at hc
      simp only [shiftThreshold, ← Nat.cast_sum] at hc
      change η univ + multiRank ρ (reesDegree e) univ + i + P.parts.card ≤
        subsetSum (ordinaryDegree e) Aᶜ + A.card +
          ∑ C ∈ P.parts, (η C + multiRank ρ (reesDegree e) C)
      rw [sum_add_distrib]
      omega
  · rintro ⟨hdeg, hLower, hPart⟩ t
    rcases t with A | ⟨A, P⟩
    · rw [shiftWeight_lower]
      simp only [shiftThreshold]
      have hb := hLower Aᶜ
      have hL := (η.add (multiRank ρ (reesDegree e))).lower_add_compl Aᶜ
      simp only [compl_compl] at hL
      change (η.add (multiRank ρ (reesDegree e))).lower Aᶜ +
        (η A + multiRank ρ (reesDegree e) A) =
          η univ + multiRank ρ (reesDegree e) univ at hL
      omega
    · rw [shiftWeight_partition]
      simp only [shiftThreshold, ← Nat.cast_sum]
      by_cases hA : A = ∅
      · subst A
        have hP : P.parts = ∅ := P.parts_eq_empty_iff.mpr rfl
        simp only [hP, card_empty, sum_empty, compl_empty, subsetSum_univ,
          Nat.cast_zero, add_zero, sub_zero]
        change η univ + multiRank ρ (reesDegree e) univ + i ≤
          (ordinaryDegree e).degree at hdeg
        omega
      · have hp := hPart A (Finset.nonempty_iff_ne_empty.mpr hA) P
        change η univ + multiRank ρ (reesDegree e) univ + i + P.parts.card ≤
          subsetSum (ordinaryDegree e) Aᶜ + A.card +
            ∑ C ∈ P.parts, (η C + multiRank ρ (reesDegree e) C) at hp
        rw [sum_add_distrib] at hp
        omega

end CommAlg

end
end CheckedSource81

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "82: CommAlg.IntegralClosure.ShiftRees\n"

/-! ## Source: CommAlg.IntegralClosure.ShiftRees -/
section CheckedSource82

/-! # Integral closure of the actual multi-Rees coefficient ideal

The carrier is the literal coefficientwise direct sum in the multi-Rees
subalgebra. Its equality with the ideal of genuine homological shifts is
obtained from the separately proved graded-Tor rank formula.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {k : Type*} [CommRing k] [Nontrivial k]

def rankShiftMultiFamily (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ)
    (s : J →₀ ℕ) : Ideal (MvPolynomial V k) :=
  rankShiftIdeal k (η.add (multiRank ρ s)) i

theorem rankShiftMulti_action (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ)
    (s t : J →₀ ℕ) :
    powerProduct (fun j => rankIdeal k (ρ j)) s * rankShiftMultiFamily η ρ i t ≤
      rankShiftMultiFamily η ρ i (s + t) := by
  rw [powerProduct, ← rankIdeal_multiRank]
  have hr : (multiRank ρ s).add (η.add (multiRank ρ t)) =
      η.add (multiRank ρ (s + t)) := by
    apply RankFunction.ext_fun
    intro A
    simp only [multiRank_add, RankFunction.add]
    omega
  unfold rankShiftMultiFamily
  rw [← hr]
  exact rankIdeal_mul_rankShiftIdeal_le _ _ i

def rankShiftMultiIdeal (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ) :
    Ideal (multiReesAlgebra (fun j => rankIdeal k (ρ j))) :=
  multiReesIdeal (fun j => rankIdeal k (ρ j)) (rankShiftMultiFamily η ρ i)
    (rankShiftMulti_action η ρ i)

@[simp] theorem mem_rankShiftMultiIdeal (η : RankFunction V) (ρ : J → RankFunction V)
    (i : ℕ) (p : multiReesAlgebra (fun j => rankIdeal k (ρ j))) :
    p ∈ rankShiftMultiIdeal η ρ i ↔
      ∀ s, p.val.coeff s ∈ rankShiftIdeal k (η.add (multiRank ρ s)) i := Iff.rfl

theorem rankShiftMulti_mem_iff_weights (η : RankFunction V) (ρ : J → RankFunction V)
    (i : ℕ) (p : multiReesAlgebra (fun j => rankIdeal k (ρ j))) :
    p ∈ rankShiftMultiIdeal η ρ i ↔
      ∀ t, Weight.Bound (shiftWeight ρ t) (shiftThreshold η i t)
        (multiReesFlatten (fun j => rankIdeal k (ρ j)) p) := by
  rw [mem_rankShiftMultiIdeal]
  constructor
  · intro hp t e he
    have ha : ordinaryDegree e ∈ (p.val.coeff (reesDegree e)).support := by
      apply MvPolynomial.mem_support_iff.mpr
      rwa [multiReesFlatten_coeff] at he
    have hm := (mem_rankShiftIdeal_iff_coeff _ i _).mp (hp (reesDegree e))
      (ordinaryDegree e) ha
    exact (shiftWeight_bounds_iff η ρ i e).mpr hm t
  · intro hp s
    apply (mem_rankShiftIdeal_iff_coeff _ i _).mpr
    intro a ha
    let e := Finsupp.sumFinsuppAddEquivProdFinsupp.symm (s, a)
    have hs : reesDegree e = s := by simp [e, reesDegree]
    have ha' : ordinaryDegree e = a := by simp [e, ordinaryDegree]
    have he : (multiReesFlatten (fun j => rankIdeal k (ρ j)) p).coeff e ≠ 0 := by
      rw [multiReesFlatten_coeff, hs, ha']
      exact MvPolynomial.mem_support_iff.mp ha
    have hm := (shiftWeight_bounds_iff (k := k) η ρ i e).mp (fun t => hp t e he)
    simpa only [hs, ha'] using hm

theorem shiftWeight_bound_zero (ρ : J → RankFunction V) (t : ShiftCut V)
    (p : multiReesAlgebra (fun j => rankIdeal k (ρ j))) :
    Weight.Bound (shiftWeight ρ t) 0
      (multiReesFlatten (fun j => rankIdeal k (ρ j)) p) := by
  intro e he
  apply shiftWeight_nonneg ρ e _ t
  exact (mem_polymatroid_multiRees ρ p.val).mp p.property e he

/-- The multi-Rees ideal described by the exact shift-rank formula is
integrally closed over every domain. This includes every field, all
multidegrees, fixed twists, unit ideals, and inactive variables. -/
theorem rankShiftMultiIdeal_integrallyClosed [IsDomain k]
    (η : RankFunction V) (ρ : J → RankFunction V) (i : ℕ) :
    IsIntegrallyClosedIdeal (rankShiftMultiIdeal (k := k) η ρ i) := by
  apply Weight.integrallyClosed_of_weight_bounds
    (multiReesFlatten (fun j => rankIdeal k (ρ j)))
    (shiftWeight ρ) (shiftThreshold η i)
    (shiftWeight_bound_zero ρ)
  exact rankShiftMulti_mem_iff_weights η ρ i

end CommAlg

end
end CheckedSource82

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "83: CommAlg.Polymatroid.PowerShiftRees\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftRees -/
section CheckedSource83

/-!
# The actual power-shift Rees ideal and its minimal monomials

The degree-zero component is zero, as in the module in Theorem 4.4.
Minimality means divisibility by another module monomial through a monomial
of the genuine Rees algebra. This includes degree-zero polynomial factors.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

def powerShiftPiece (ρ : RankFunction V) (i s : ℕ) : Ideal (MvPolynomial V k) :=
  if s = 0 then ⊥ else rankShiftIdeal k (RankFunction.scale s ρ) i

@[simp] theorem powerShiftPiece_zero (ρ : RankFunction V) (i : ℕ) :
    powerShiftPiece (k := k) ρ i 0 = ⊥ := by simp [powerShiftPiece]

theorem powerShiftPiece_pos (ρ : RankFunction V) (i : ℕ) {s : ℕ} (hs : 0 < s) :
    powerShiftPiece (k := k) ρ i s = rankShiftIdeal k (RankFunction.scale s ρ) i := by
  simp [powerShiftPiece, Nat.ne_of_gt hs]

theorem powerShiftPiece_le_pow (ρ : RankFunction V) (i s : ℕ) :
    powerShiftPiece (k := k) ρ i s ≤ (rankIdeal k ρ) ^ s := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [powerShiftPiece, if_neg hs, ← rankIdeal_scale]
    exact rankShiftIdeal_le_rankIdeal _ _

theorem powerShiftPiece_action (ρ : RankFunction V) (i n s : ℕ) :
    (rankIdeal k ρ) ^ n * powerShiftPiece ρ i s ≤ powerShiftPiece ρ i (n + s) := by
  by_cases hs : s = 0
  · simp [hs]
  · have hns : n + s ≠ 0 := by omega
    simp only [powerShiftPiece, if_neg hs, if_neg hns]
    exact powerShiftIdeal_mul_le ρ i n s

/-- The ordinary coefficientwise ideal inside Mathlib's actual Rees algebra.
Its underlying graded module is precisely the direct sum of the positive
power-shift pieces. -/
def shiftReesIdeal (ρ : RankFunction V) (i : ℕ) : Ideal (reesAlgebra (rankIdeal k ρ)) where
  carrier := {p | ∀ s, p.val.coeff s ∈ powerShiftPiece ρ i s}
  zero_mem' := by simp
  add_mem' hp hq := fun s => by
    simpa only [Subalgebra.coe_add, Polynomial.coeff_add] using
      (powerShiftPiece ρ i s).add_mem (hp s) (hq s)
  smul_mem' r p hp := by
    intro s
    change (r.val * p.val).coeff s ∈ powerShiftPiece ρ i s
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨n, t⟩ hnt
    rw [← Finset.mem_antidiagonal.mp hnt]
    exact powerShiftPiece_action ρ i n t
      (Ideal.mul_mem_mul (r.property n) (hp t))

@[simp] theorem mem_shiftReesIdeal (ρ : RankFunction V) (i : ℕ)
    (p : reesAlgebra (rankIdeal k ρ)) :
    p ∈ shiftReesIdeal ρ i ↔ ∀ s, p.val.coeff s ∈ powerShiftPiece ρ i s := Iff.rfl

def shiftReesMonomial (ρ : RankFunction V) (i s : ℕ) (a : Exponent V)
    (ha : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s) :
    reesAlgebra (rankIdeal k ρ) :=
  ⟨Polynomial.monomial s (MvPolynomial.monomial a 1),
    reesAlgebra.monomial_mem.mpr (powerShiftPiece_le_pow ρ i s ha)⟩

theorem shiftReesMonomial_mem (ρ : RankFunction V) (i s : ℕ) (a : Exponent V)
    (ha : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s) :
    shiftReesMonomial ρ i s a ha ∈ shiftReesIdeal ρ i := by
  intro t
  change (Polynomial.monomial s (MvPolynomial.monomial a 1)).coeff t ∈ _
  by_cases ht : t = s
  · subst t
    simpa using ha
  · simp [Polynomial.coeff_monomial, ht, Ne.symm ht]

/-- The exponent factorization is literal multiplication of monomials in
the ambient polynomial ring, not a stipulated combinatorial action. -/
theorem rees_monomial_factorization {s r : ℕ} (hrs : r ≤ s)
    {a b : Exponent V} (hba : b ≤ a) :
    Polynomial.monomial (s - r) (MvPolynomial.monomial (a - b) (1 : k)) *
      Polynomial.monomial r (MvPolynomial.monomial b 1) =
        Polynomial.monomial s (MvPolynomial.monomial a 1) := by
  rw [Polynomial.monomial_mul_monomial, MvPolynomial.monomial_mul]
  simp only [Nat.sub_add_cancel hrs, tsub_add_cancel_of_le hba, one_mul]

/-- A genuine minimal module monomial: every divisor that belongs to the
module and whose quotient belongs to the Rees algebra is the same monomial.
The pair `(s,a)` records its actual Rees and ordinary multidegrees. -/
def IsMinimalShiftReesMonomial (ρ : RankFunction V) (i s : ℕ) (a : Exponent V) : Prop :=
  MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s ∧
    ∀ r b, r ≤ s → b ≤ a →
      MvPolynomial.monomial b (1 : k) ∈ powerShiftPiece ρ i r →
      MvPolynomial.monomial (a - b) (1 : k) ∈ (rankIdeal k ρ) ^ (s - r) →
      r = s ∧ b = a

theorem minimalShiftRees_positive {ρ : RankFunction V} {i s : ℕ} {a : Exponent V}
    (h : IsMinimalShiftReesMonomial (k := k) ρ i s a) : 0 < s := by
  by_contra hn
  have hs : s = 0 := by omega
  have hm := h.1
  simp [hs] at hm

theorem earlier_powerShift_product_le (ρ : RankFunction V) (i : ℕ) {r s : ℕ}
    (hrs : r < s) :
    (rankIdeal k ρ) ^ (s - r) * powerShiftPiece ρ i r ≤
      rankIdeal k ρ * powerShiftPiece ρ i (s - 1) := by
  have he : s - r = 1 + (s - 1 - r) := by omega
  have ht : s - 1 - r + r = s - 1 := by omega
  rw [he, pow_add, pow_one, mul_assoc]
  have h := powerShiftPiece_action (k := k) ρ i (s - 1 - r) r
  rw [ht] at h
  exact Ideal.mul_mono le_rfl h

/-- Exact intrinsic criterion for the new minimal monomials in a positive
Rees degree: ordinary minimal bases outside the preceding Rees product. -/
theorem minimalShiftRees_iff (ρ : RankFunction V) (i : ℕ) {s : ℕ} (hs : 0 < s)
    (a : Exponent V) :
    IsMinimalShiftReesMonomial (k := k) ρ i s a ↔
      a ∈ rankShiftFamily (RankFunction.scale s ρ) i ∧
        MvPolynomial.monomial a (1 : k) ∉ rankIdeal k ρ * powerShiftPiece ρ i (s - 1) := by
  have hpiece := powerShiftPiece_pos (k := k) ρ i hs
  constructor
  · intro h
    have ha := h.1
    rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff] at ha
    obtain ⟨b, hb, hba⟩ := ha
    have hbPiece : MvPolynomial.monomial b (1 : k) ∈ powerShiftPiece ρ i s := by
      rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
      exact ⟨b, hb, le_rfl⟩
    have he := (h.2 s b le_rfl hba hbPiece (by simp)).2
    refine ⟨he ▸ hb, ?_⟩
    intro hp
    by_cases hs1 : s = 1
    · simp [hs1] at hp
    have hprev : 0 < s - 1 := by omega
    rw [powerShiftPiece_pos ρ i hprev, rankIdeal, rankShiftIdeal_eq_monomialIdeal,
      monomialIdeal_mul, monomial_mem_iff] at hp
    obtain ⟨c, hc, hca⟩ := hp
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.mp hc
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    have hya : y ≤ a := (le_add_left le_rfl).trans hca
    have hxa : x ≤ a - y := by
      intro j
      have hj := hca j
      simp only [Finsupp.add_apply] at hj
      change x j ≤ a j - y j
      omega
    have hyPiece : MvPolynomial.monomial y (1 : k) ∈ powerShiftPiece ρ i (s - 1) := by
      rw [powerShiftPiece_pos ρ i hprev, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
      exact ⟨y, hy, le_rfl⟩
    have hxPower : MvPolynomial.monomial (a - y) (1 : k) ∈ (rankIdeal k ρ) ^ (s - (s - 1)) := by
      rw [show s - (s - 1) = 1 by omega, pow_one]
      exact (monomial_mem_iff (rankBases ρ) (a - y)).mpr ⟨x, hx, hxa⟩
    have he := (h.2 (s - 1) y (by omega) hya hyPiece hxPower).1
    omega
  · rintro ⟨ha, hnew⟩
    refine ⟨?_, ?_⟩
    · rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff]
      exact ⟨a, ha, le_rfl⟩
    · intro r b hrs hba hb hf
      by_cases hrsEq : r = s
      · subst r
        rw [hpiece, rankShiftIdeal_eq_monomialIdeal, monomial_mem_iff] at hb
        obtain ⟨c, hc, hcb⟩ := hb
        have he := (rankShiftFamily_equigenerated (RankFunction.scale s ρ) i).antichain
          c hc a ha (hcb.trans hba)
        exact ⟨rfl, le_antisymm hba (he ▸ hcb)⟩
      · have hrsLt : r < s := by omega
        have hp := Ideal.mul_mem_mul hf hb
        have hp' : MvPolynomial.monomial a (1 : k) ∈
            (rankIdeal k ρ) ^ (s - r) * powerShiftPiece ρ i r := by
          simpa only [MvPolynomial.monomial_mul, one_mul, tsub_add_cancel_of_le hba] using hp
        exact (hnew (earlier_powerShift_product_le ρ i hrsLt hp')).elim

end CommAlg.Polymatroid

end
end CheckedSource83

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "84: CommAlg.IntegralClosure.OrdinaryRees\n"

/-! ## Source: CommAlg.IntegralClosure.OrdinaryRees -/
section CheckedSource84

/-! # The ordinary Rees algebra and the positive-power shift ideal

This module applies the full weight proof inside Mathlib's ordinary
`reesAlgebra`. The comparison with one-variable multigrading is an actual
algebra homomorphism with an exact coefficient formula.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

variable {R : Type*} [CommRing R]

def reesToMulti (I : Ideal R) : reesAlgebra I →ₐ[R] multiReesAlgebra (fun _ : Unit => I) :=
  ((MvPolynomial.uniqueAlgEquiv R Unit).symm.toAlgHom.comp (reesAlgebra I).val).codRestrict
    (multiReesAlgebra (fun _ : Unit => I)) (by
      intro p s
      change ((MvPolynomial.uniqueAlgEquiv R Unit).symm p.val).coeff s ∈
        powerProduct (fun _ : Unit => I) s
      rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
      simpa [powerProduct] using p.property (s ()))

@[simp] theorem reesToMulti_coeff (I : Ideal R) (p : reesAlgebra I) (s : Unit →₀ ℕ) :
    ((reesToMulti I p).val).coeff s = p.val.coeff (s ()) :=
  MvPolynomial.coeff_uniqueAlgEquiv_symm _ p.val s

section Ranks

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

theorem universalAugmentedRank_zero (A : Finset V) :
    universalAugmentedRank (zeroRank : RankFunction V) A = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h := universalAugmentedRank_le_cost (zeroRank : RankFunction V) (⊥ : Finpartition A)
  simpa [partitionCost, Finpartition.parts_bot, cardinalLift, RankFunction.add,
    cardinalRank] using h

theorem rankShiftIdeal_zeroRank_pos (i : ℕ) (hi : 0 < i) :
    rankShiftIdeal k (zeroRank : RankFunction V) i = ⊥ := by
  have hu : universalHomologicalRank (zeroRank : RankFunction V) i univ = 0 := by
    apply Nat.eq_zero_of_le_zero
    have h := shiftRankValue_le_u (zeroRank : RankFunction V)
      (universalAugmentedRank zeroRank) i univ
    change universalHomologicalRank (zeroRank : RankFunction V) i univ ≤
      universalAugmentedRank zeroRank univ at h
    simpa only [universalAugmentedRank_zero] using h
  simp [rankShiftIdeal, hu, Nat.ne_of_lt hi]

theorem oneColor_rank (ρ : RankFunction V) (s : Unit →₀ ℕ) :
    (zeroRank : RankFunction V).add (multiRank (fun _ : Unit => ρ) s) = ρ.scale (s ()) := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.add, multiRank_apply, RankFunction.scale]

theorem positivePowerPiece_eq_oneColor (ρ : RankFunction V) (i : ℕ) (hi : 0 < i)
    (s : Unit →₀ ℕ) :
    powerShiftPiece (k := k) ρ i (s ()) =
      rankShiftIdeal k (zeroRank.add (multiRank (fun _ : Unit => ρ) s)) i := by
  rw [oneColor_rank]
  by_cases hs : s () = 0
  · rw [hs, powerShiftPiece_zero]
    have he : ρ.scale 0 = (zeroRank : RankFunction V) := by
      apply RankFunction.ext_fun
      intro A
      simp [RankFunction.scale]
    rw [he, rankShiftIdeal_zeroRank_pos i hi]
  · simp [powerShiftPiece, hs]

theorem mem_shiftReesIdeal_iff_oneColor (ρ : RankFunction V) (i : ℕ) (hi : 0 < i)
    (p : reesAlgebra (rankIdeal k ρ)) :
    p ∈ shiftReesIdeal ρ i ↔
      reesToMulti (rankIdeal k ρ) p ∈ rankShiftMultiIdeal zeroRank (fun _ : Unit => ρ) i := by
  rw [mem_shiftReesIdeal, mem_rankShiftMultiIdeal]
  simp only [reesToMulti_coeff, ← positivePowerPiece_eq_oneColor ρ i hi]
  constructor
  · intro h s
    exact h (s ())
  · intro h n
    simpa using h (Finsupp.single () n)

/-- Theorem 6.1 for the formula ideals, in Mathlib's actual ordinary Rees
algebra and with exactly the positive power layers. -/
theorem shiftReesIdeal_integrallyClosed [IsDomain k] (ρ : RankFunction V)
    (i : ℕ) (hi : 0 < i) : IsIntegrallyClosedIdeal (shiftReesIdeal (k := k) ρ i) := by
  let f := (multiReesFlatten (fun _ : Unit => rankIdeal k ρ)).comp
    (reesToMulti (rankIdeal k ρ)).toRingHom
  apply Weight.integrallyClosed_of_weight_bounds f
    (shiftWeight (fun _ : Unit => ρ)) (shiftThreshold zeroRank i)
    (fun t p => shiftWeight_bound_zero (fun _ : Unit => ρ) t (reesToMulti (rankIdeal k ρ) p))
  intro p
  rw [mem_shiftReesIdeal_iff_oneColor ρ i hi, rankShiftMulti_mem_iff_weights]
  rfl

end Ranks

theorem integrallyClosed_bot [IsDomain R] : IsIntegrallyClosedIdeal (⊥ : Ideal R) := by
  intro x hx
  obtain ⟨n, hn, c, hc, he⟩ := hx
  have hcz : ∀ j ∈ range n, c j = 0 := by
    intro j hj
    have hjn := mem_range.mp hj
    have hp : n - j ≠ 0 := by omega
    simpa only [Ideal.bot_pow hp, Ideal.mem_bot] using hc j hjn
  have hz : x ^ n = 0 := by
    have hs : ∑ j ∈ range n, c j * x ^ j = 0 :=
      sum_eq_zero (fun j hj => by rw [hcz j hj, zero_mul])
    simpa only [hs, add_zero] using he
  exact Ideal.mem_bot.mpr (eq_zero_of_pow_eq_zero hz)

end CommAlg

end
end CheckedSource84

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "85: CommAlg.Polymatroid.HomologicalMultiplication\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalMultiplication -/
section CheckedSource85

/-! # Multiplication and containment for genuine homological shifts of ideals -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

theorem homologicalShiftIdeal_le (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : homologicalShiftIdeal I hI i ≤ I := by
  rcases hI.eq_bot_or_rank with h0 | ⟨g, hg⟩
  · subst I
    simp
  · rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g hg i, hg]
    exact rankShiftIdeal_le_rankIdeal g i

/-- Lemma 3.4 for actual polynomial ideals, including both zero ideals. -/
theorem homologicalShiftIdeal_mul_le (I J : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J) (i : ℕ) :
    I * homologicalShiftIdeal J hJ i ≤ homologicalShiftIdeal (I * J) (hI.mul hJ) i := by
  rcases hI.eq_bot_or_rank with h0 | ⟨g, hg⟩
  · subst I
    simp
  rcases hJ.eq_bot_or_rank with h0 | ⟨f, hf⟩
  · subst J
    simp
  have hp : I * J = rankIdeal k (g.add f) := by rw [hg, hf, rankIdeal_add]
  rw [homologicalShiftIdeal_eq_rankShiftIdeal J hJ f hf i,
    homologicalShiftIdeal_eq_rankShiftIdeal (I * J) (hI.mul hJ) (g.add f) hp i, hg]
  exact rankIdeal_mul_rankShiftIdeal_le g f i

end CommAlg.Polymatroid

end
end CheckedSource85

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "86: CommAlg.IntegralClosure.HomologicalRees\n"

/-! ## Source: CommAlg.IntegralClosure.HomologicalRees -/
section CheckedSource86

/-! # Integral closure of the genuine homological-shift Rees ideals

Every homogeneous coefficient below is the homological shift of an actual
polynomial ideal, defined through its genuine derived-Tor components.
The weight proof is applied only after proving exact equality of carriers.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
variable {C : Type*} [Fintype C] [DecidableEq C]

theorem polymatroidal_powerProduct (I : C → Ideal (MvPolynomial V k))
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (s : C →₀ ℕ) :
    IsPolymatroidalIdeal (powerProduct I s) :=
  IsPolymatroidalIdeal.prod univ (fun j => I j ^ s j) (fun j _ => (hI j).pow (s j))

def homologicalMultiPiece (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) (s : C →₀ ℕ) :
    Ideal (MvPolynomial V k) :=
  homologicalShiftIdeal (J * powerProduct I s) (hJ.mul (polymatroidal_powerProduct I hI s)) i

theorem homologicalMultiPiece_action (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) (s t : C →₀ ℕ) :
    powerProduct I s * homologicalMultiPiece J I hJ hI i t ≤
      homologicalMultiPiece J I hJ hI i (s + t) := by
  have he : powerProduct I s * (J * powerProduct I t) = J * powerProduct I (s + t) := by
    rw [powerProduct_add]
    ac_rfl
  have h := homologicalShiftIdeal_mul_le (powerProduct I s) (J * powerProduct I t)
    (polymatroidal_powerProduct I hI s) (hJ.mul (polymatroidal_powerProduct I hI t)) i
  rw [homologicalShiftIdeal_congr _ (hJ.mul (polymatroidal_powerProduct I hI (s + t))) he i] at h
  exact h

def homologicalMultiIdeal (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) : Ideal (multiReesAlgebra I) :=
  multiReesIdeal I (homologicalMultiPiece J I hJ hI i)
    (homologicalMultiPiece_action J I hJ hI i)

@[simp] theorem mem_homologicalMultiIdeal (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) (p : multiReesAlgebra I) :
    p ∈ homologicalMultiIdeal J I hJ hI i ↔
      ∀ s, p.val.coeff s ∈ homologicalMultiPiece J I hJ hI i s := Iff.rfl

theorem homologicalMultiPiece_rank (η : RankFunction V) (ρ : C → RankFunction V)
    (hJ : IsPolymatroidalIdeal (rankIdeal k η))
    (hI : ∀ j, IsPolymatroidalIdeal (rankIdeal k (ρ j))) (i : ℕ) (s : C →₀ ℕ) :
    homologicalMultiPiece (rankIdeal k η) (fun j => rankIdeal k (ρ j)) hJ hI i s =
      rankShiftMultiFamily η ρ i s := by
  unfold homologicalMultiPiece rankShiftMultiFamily
  apply homologicalShiftIdeal_eq_rankShiftIdeal
  rw [powerProduct, ← rankIdeal_multiRank, rankIdeal_add]

theorem homologicalMultiIdeal_rank (η : RankFunction V) (ρ : C → RankFunction V)
    (hJ : IsPolymatroidalIdeal (rankIdeal k η))
    (hI : ∀ j, IsPolymatroidalIdeal (rankIdeal k (ρ j))) (i : ℕ) :
    homologicalMultiIdeal (rankIdeal k η) (fun j => rankIdeal k (ρ j)) hJ hI i =
      rankShiftMultiIdeal η ρ i := by
  ext p
  simp only [mem_homologicalMultiIdeal, homologicalMultiPiece_rank,
    mem_rankShiftMultiIdeal, rankShiftMultiFamily]

theorem homologicalMultiIdeal_zero_twist (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k)))
    (hI : ∀ j, IsPolymatroidalIdeal (I j)) (i : ℕ) :
    homologicalMultiIdeal ⊥ I hJ hI i = ⊥ := by
  ext p
  simp only [mem_homologicalMultiIdeal, homologicalMultiPiece, Ideal.bot_mul,
    homologicalShiftIdeal_bot, Ideal.mem_bot]
  constructor
  · intro hp
    apply Subtype.ext
    apply MvPolynomial.ext
    simpa using hp
  · rintro rfl
    simp

/-- Corollary 6.2: the entire twisted multi-Rees ideal of genuine
homological shifts is integrally closed. Zero coordinates and the unit
ideal are included; a zero twist gives the zero ideal. -/
theorem homologicalMultiIdeal_integrallyClosed [IsDomain k]
    (J : Ideal (MvPolynomial V k)) (I : C → Ideal (MvPolynomial V k))
    (hJ : IsPolymatroidalIdeal J) (hI : ∀ j, IsPolymatroidalIdeal (I j))
    (hIne : ∀ j, I j ≠ ⊥) (i : ℕ) :
    IsIntegrallyClosedIdeal (homologicalMultiIdeal J I hJ hI i) := by
  rcases hJ.eq_bot_or_rank with h0 | ⟨η, hη⟩
  · subst J
    rw [homologicalMultiIdeal_zero_twist]
    exact integrallyClosed_bot
  · choose ρ hρ using fun j => (hI j).exists_rank (hIne j)
    have he : I = fun j => rankIdeal k (ρ j) := funext hρ
    subst J
    subst I
    rw [homologicalMultiIdeal_rank]
    exact rankShiftMultiIdeal_integrallyClosed η ρ i

def homologicalPowerPiece (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i s : ℕ) : Ideal (MvPolynomial V k) :=
  if s = 0 then ⊥ else homologicalShiftIdeal (I ^ s) (hI.pow s) i

theorem homologicalPowerPiece_action (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i n s : ℕ) :
    I ^ n * homologicalPowerPiece I hI i s ≤ homologicalPowerPiece I hI i (n + s) := by
  by_cases hs : s = 0
  · simp [homologicalPowerPiece, hs]
  · have hns : n + s ≠ 0 := by omega
    simp only [homologicalPowerPiece, if_neg hs, if_neg hns]
    have h := homologicalShiftIdeal_mul_le (I ^ n) (I ^ s) (hI.pow n) (hI.pow s) i
    rw [homologicalShiftIdeal_congr _ (hI.pow (n + s)) (pow_add I n s).symm i] at h
    exact h

def homologicalPowerIdeal (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ s, p.val.coeff s ∈ homologicalPowerPiece I hI i s}
  zero_mem' := by simp
  add_mem' hp hq := fun s => by
    simpa only [Subalgebra.coe_add, Polynomial.coeff_add] using
      (homologicalPowerPiece I hI i s).add_mem (hp s) (hq s)
  smul_mem' r p hp := by
    intro s
    change (r.val * p.val).coeff s ∈ homologicalPowerPiece I hI i s
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨n, t⟩ hnt
    rw [← Finset.mem_antidiagonal.mp hnt]
    exact homologicalPowerPiece_action I hI i n t
      (Ideal.mul_mem_mul (r.property n) (hp t))

@[simp] theorem mem_homologicalPowerIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (p : reesAlgebra I) :
    p ∈ homologicalPowerIdeal I hI i ↔
      ∀ s, p.val.coeff s ∈ homologicalPowerPiece I hI i s := Iff.rfl

theorem homologicalPowerPiece_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i s : ℕ) :
    homologicalPowerPiece (rankIdeal k ρ) hI i s = powerShiftPiece ρ i s := by
  by_cases hs : s = 0
  · simp [homologicalPowerPiece, powerShiftPiece, hs]
  · simp only [homologicalPowerPiece, powerShiftPiece, if_neg hs]
    exact homologicalShiftIdeal_eq_rankShiftIdeal _ _ (ρ.scale s)
      (rankIdeal_scale k ρ s).symm i

theorem homologicalPowerIdeal_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i : ℕ) :
    homologicalPowerIdeal (rankIdeal k ρ) hI i = shiftReesIdeal ρ i := by
  ext p
  simp only [mem_homologicalPowerIdeal, homologicalPowerPiece_rank, mem_shiftReesIdeal]

theorem homologicalPowerIdeal_bot
    (hI : IsPolymatroidalIdeal (⊥ : Ideal (MvPolynomial V k))) (i : ℕ) :
    homologicalPowerIdeal ⊥ hI i = ⊥ := by
  have hp (s : ℕ) : homologicalPowerPiece ⊥ hI i s = ⊥ := by
    by_cases hs : s = 0
    · simp [homologicalPowerPiece, hs]
    · simp [homologicalPowerPiece, hs, Ideal.bot_pow hs]
  ext p
  simp only [mem_homologicalPowerIdeal, hp, Ideal.mem_bot]
  constructor
  · intro h
    apply Subtype.ext
    apply Polynomial.ext
    simpa using h
  · rintro rfl
    simp

/-- Theorem 6.1 in its literal ideal form: the positive-power direct sum of
genuine homological shifts is an integrally closed ideal of Mathlib's
ordinary Rees algebra, for every polymatroidal ideal and every `i > 0`. -/
theorem homologicalPowerIdeal_integrallyClosed [IsDomain k]
    (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) (hi : 0 < i) : IsIntegrallyClosedIdeal (homologicalPowerIdeal I hI i) := by
  rcases hI.eq_bot_or_rank with h0 | ⟨ρ, hρ⟩
  · subst I
    rw [homologicalPowerIdeal_bot]
    exact integrallyClosed_bot
  · subst I
    rw [homologicalPowerIdeal_rank]
    exact shiftReesIdeal_integrallyClosed ρ i hi

end CommAlg

end
end CheckedSource86

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "87: CommAlg.Rees.OneColor\n"

/-! ## Source: CommAlg.Rees.OneColor -/
section CheckedSource87

/-! # The actual equivalence between ordinary and one-color Rees algebras -/

noncomputable section

namespace CommAlg

open Classical

variable {R : Type*} [CommRing R]

theorem reesToMulti_injective (I : Ideal R) : Function.Injective (reesToMulti I) := by
  intro p q h
  apply Subtype.ext
  apply (MvPolynomial.uniqueAlgEquiv R Unit).symm.injective
  exact congrArg Subtype.val h

theorem reesToMulti_surjective (I : Ideal R) : Function.Surjective (reesToMulti I) := by
  intro q
  have hp : (MvPolynomial.uniqueAlgEquiv R Unit) q.val ∈ reesAlgebra I := by
    intro n
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    simpa [powerProduct] using q.property (Finsupp.single () n)
  refine ⟨⟨(MvPolynomial.uniqueAlgEquiv R Unit) q.val, hp⟩, ?_⟩
  apply Subtype.ext
  exact (MvPolynomial.uniqueAlgEquiv R Unit).symm_apply_apply q.val

/-- Ordinary polynomial grading and the one-color multigrading define
isomorphic Rees algebras, with their actual coefficient conditions. -/
def reesMultiEquiv (I : Ideal R) : reesAlgebra I ≃ₐ[R] multiReesAlgebra (fun _ : Unit => I) :=
  AlgEquiv.ofBijective (reesToMulti I) ⟨reesToMulti_injective I, reesToMulti_surjective I⟩

@[simp] theorem reesMultiEquiv_apply (I : Ideal R) (p : reesAlgebra I) :
    reesMultiEquiv I p = reesToMulti I p := rfl

theorem reesMultiEquiv_symm_val (I : Ideal R)
    (q : multiReesAlgebra (fun _ : Unit => I)) :
    ((reesMultiEquiv I).symm q).val = (MvPolynomial.uniqueAlgEquiv R Unit) q.val := by
  have h := congrArg Subtype.val ((reesMultiEquiv I).apply_symm_apply q)
  change (MvPolynomial.uniqueAlgEquiv R Unit).symm ((reesMultiEquiv I).symm q).val = q.val at h
  have hh := congrArg (MvPolynomial.uniqueAlgEquiv R Unit) h
  simpa only [AlgEquiv.apply_symm_apply] using hh

end CommAlg

end
end CheckedSource87

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "88: CommAlg.Rees.HomologicalGeneration\n"

/-! ## Source: CommAlg.Rees.HomologicalGeneration -/
section CheckedSource88

/-! # Full generation bounds for the genuine homological-shift modules

The conclusions are literal ideal-span equalities inside the actual ordinary
and multi-Rees algebras. They include every polynomial element of the modules,
all fixed twists, zero ideals and inactive coordinates.
-/

noncomputable section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CommAlg

open Classical Finset Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
variable {C : Type*} [Fintype C] [DecidableEq C]

theorem homologicalMultiPiece_le_powerProduct (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ) (s : C →₀ ℕ) :
    homologicalMultiPiece J I hJ hI i s ≤ powerProduct I s :=
  (homologicalShiftIdeal_le _ _ i).trans Ideal.mul_le_right

/-- The complete module-generation assertion of Corollary 4.1, for the
actual ideal of genuine homological shifts in the actual multi-Rees ring. -/
theorem homologicalMultiIdeal_generated_in_box (J : Ideal (MvPolynomial V k))
    (I : C → Ideal (MvPolynomial V k)) (hJ : IsPolymatroidalIdeal J)
    (hI : ∀ c, IsPolymatroidalIdeal (I c)) (i : ℕ) :
    homologicalMultiIdeal J I hJ hI i =
      Ideal.span (reesBoxGenerators I (homologicalMultiPiece J I hJ hI i) i) := by
  apply multiReesIdeal_span_box _ _ (homologicalMultiPiece_action J I hJ hI i)
    (homologicalMultiPiece_le_powerProduct J I hJ hI i)
  intro s c hs
  exact homologicalShift_severalColors I J hI hJ s i c hs

theorem homologicalShiftIdeal_top_pos
    (hS : IsPolymatroidalIdeal (⊤ : Ideal (MvPolynomial V k))) (i : ℕ) (hi : 0 < i) :
    homologicalShiftIdeal ⊤ hS i = ⊥ := by
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ hS zeroRank (rankIdeal_zeroRank k).symm i]
  exact rankShiftIdeal_zeroRank_pos i hi

theorem homologicalMultiPiece_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (s : Unit →₀ ℕ) :
    homologicalMultiPiece ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i s =
      homologicalShiftIdeal (I ^ (s ())) (hI.pow _) i := by
  apply homologicalShiftIdeal_congr
  simp [powerProduct]

theorem homologicalPowerPiece_eq_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) (s : Unit →₀ ℕ) :
    homologicalPowerPiece I hI i (s ()) =
      homologicalMultiPiece ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i s := by
  rw [homologicalMultiPiece_oneColor]
  by_cases hs : s () = 0
  · simp only [homologicalPowerPiece, hs, ite_true, pow_zero, Ideal.one_eq_top]
    exact (homologicalShiftIdeal_top_pos _ i hi).symm
  · simp [homologicalPowerPiece, hs]

theorem mem_homologicalPowerIdeal_iff_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) (p : reesAlgebra I) :
    p ∈ homologicalPowerIdeal I hI i ↔
      reesMultiEquiv I p ∈ homologicalMultiIdeal ⊤ (fun _ : Unit => I)
        isPolymatroidalIdeal_top (fun _ => hI) i := by
  rw [mem_homologicalPowerIdeal, mem_homologicalMultiIdeal]
  simp only [reesMultiEquiv_apply, reesToMulti_coeff,
    ← homologicalPowerPiece_eq_oneColor I hI i hi]
  constructor
  · intro h s
    exact h (s ())
  · intro h n
    simpa using h (Finsupp.single () n)

theorem homologicalPowerIdeal_eq_map_oneColor (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    homologicalPowerIdeal I hI i = Ideal.map (reesMultiEquiv I).symm.toRingHom
      (homologicalMultiIdeal ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i) := by
  calc
    _ = Ideal.comap (reesMultiEquiv I).toRingHom
        (homologicalMultiIdeal ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i) := by
      ext p
      exact mem_homologicalPowerIdeal_iff_oneColor I hI i hi p
    _ = _ := (Ideal.map_comap_of_equiv (reesMultiEquiv I).symm.toRingEquiv).symm

/-- Homogeneous elements of the actual positive-power shift module in Rees
degrees at most `i`. Its degree-zero component is zero by definition. -/
def homologicalPowerBoxGenerators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s r, s ≤ i ∧ r ∈ homologicalPowerPiece I hI i s ∧
    p.val = Polynomial.monomial s r}

theorem oneColor_box_image (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    (reesMultiEquiv I).symm '' reesBoxGenerators (fun _ : Unit => I)
      (homologicalMultiPiece ⊤ (fun _ : Unit => I) isPolymatroidalIdeal_top (fun _ => hI) i) i =
        homologicalPowerBoxGenerators I hI i := by
  ext p
  constructor
  · rintro ⟨q, ⟨s, r, hs, hr, he⟩, rfl⟩
    refine ⟨s (), r, hs (), ?_, ?_⟩
    · rwa [homologicalPowerPiece_eq_oneColor I hI i hi s]
    · rw [reesMultiEquiv_symm_val, he, MvPolynomial.uniqueAlgEquiv_monomial]
  · rintro ⟨n, r, hn, hr, he⟩
    refine ⟨reesMultiEquiv I p, ?_, (reesMultiEquiv I).symm_apply_apply p⟩
    refine ⟨Finsupp.single () n, r, ?_, ?_, ?_⟩
    · intro c
      cases c
      simpa using hn
    · rw [← homologicalPowerPiece_eq_oneColor I hI i hi (Finsupp.single () n)]
      simpa using hr
    · change (MvPolynomial.uniqueAlgEquiv (MvPolynomial V k) Unit).symm p.val = _
      rw [he]
      simpa using (MvPolynomial.uniqueAlgEquiv_symm_monomial
        (R := MvPolynomial V k) (d := Finsupp.single () n) (r := r))

/-- The full module-generation conclusion of Theorem 1.1, as a literal span
inside Mathlib's ordinary Rees algebra. It holds for all polymatroidal ideals,
including zero and unit ideals, over every field. -/
theorem homologicalPowerIdeal_generated_le (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    homologicalPowerIdeal I hI i = Ideal.span (homologicalPowerBoxGenerators I hI i) := by
  rw [homologicalPowerIdeal_eq_map_oneColor I hI i hi,
    homologicalMultiIdeal_generated_in_box, Ideal.map_span]
  exact congrArg Ideal.span (oneColor_box_image I hI i hi)

end CommAlg

end
end CheckedSource88

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "89: CommAlg.Polymatroid.UniformSharpness\n"

/-! ## Source: CommAlg.Polymatroid.UniformSharpness -/
section CheckedSource89

/-!
# Uniform-matroid sharpness in every positive homological degree

For a ground set of size `i + 1`, the rank-`i` uniform matroid gives the
squarefree Veronese example. Below the `i`th power its homological rank
cannot reach the required degree. At that power the only base exponent is
the constant vector `i`.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem uniform_homologicalRank_cap (i s : ℕ) (hi : 1 ≤ i) (hs : 1 ≤ s)
    (A : Finset V) :
    homologicalRank (uniformPowerRank V i s) (uniformPowerRank_active hi hs) i A ≤
      A.card * s := by
  have h := homologicalRank_le_sum_singletons (uniformPowerRank V i s)
    (uniformPowerRank_active hi hs) i A
  simpa only [uniformPowerRank_apply, card_singleton, min_eq_left hi,
    Nat.mul_one, sum_const_nat] using h

/-- The total rank is too small at every positive power below `i`. -/
theorem uniform_homologicalRank_lt {i s : ℕ} (hi : 1 ≤ i) (hs : 1 ≤ s)
    (hsi : s < i) (hcard : Fintype.card V = i + 1) :
    homologicalRank (uniformPowerRank V i s) (uniformPowerRank_active hi hs) i univ <
      uniformPowerRank V i s univ + i := by
  have h := uniform_homologicalRank_cap (V := V) i s hi hs univ
  simp only [card_univ, hcard, uniformPowerRank_apply,
    min_eq_right (Nat.le_succ i)] at h ⊢
  nlinarith

theorem uniform_threshold_supportPred_bound {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) {A : Finset V} (hA : A.Nonempty) :
    subsetSum (supportPred (constExponent i : Exponent V)) A ≤
      uniformPowerRank V i i A - 1 := by
  have hc : 1 ≤ A.card := card_pos.mpr hA
  have hcn : A.card ≤ i + 1 := by
    simpa only [hcard] using card_le_univ A
  have him : i - 1 + 1 = i := Nat.sub_add_cancel hi
  have hsum : subsetSum (supportPred (constExponent i : Exponent V)) A =
      A.card * (i - 1) := by
    simp [subsetSum]
  rw [hsum, uniformPowerRank_apply]
  rcases le_total A.card i with h | h
  · rw [min_eq_left h]
    have hp : 1 ≤ i * A.card := by nlinarith
    have hs := Nat.sub_add_cancel hp
    nlinarith
  · rw [min_eq_right h]
    have hp : 1 ≤ i * i := by nlinarith
    have hs := Nat.sub_add_cancel hp
    nlinarith

/-- The constant exponent satisfies every augmented partition inequality. -/
theorem uniform_threshold_augmented_feasible {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    ∀ A, subsetSum (constExponent i : Exponent V) A ≤
      augmentedPartitionRank (uniformPowerRank V i i) A :=
  (supportPred_nonempty_bounds_iff_augmented (uniformPowerRank V i i)
    (constExponent i)).mp (fun _ hA => uniform_threshold_supportPred_bound hi hcard hA)

theorem uniform_threshold_upperFeasible {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    UpperFeasible
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i)
      (constExponent i) := by
  intro A
  by_cases hA : A.Nonempty
  · rw [homologicalRank_apply _ _ _ hA]
    change subsetSum (constExponent i) A ≤
      min (uniformPowerRank V i i A + i) (augmentedPartitionRank _ A)
    refine le_min ?_ (uniform_threshold_augmented_feasible hi hcard A)
    rw [subsetSum_constExponent, uniformPowerRank_apply]
    have hc : A.card ≤ i + 1 := by simpa only [hcard] using card_le_univ A
    rcases le_total A.card i with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h]
      nlinarith
  · have he := not_nonempty_iff_eq_empty.mp hA
    simp [he, subsetSum]

/-- At the `i`th power the required total degree is attained. -/
theorem uniform_homologicalRank_top {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i univ =
      uniformPowerRank V i i univ + i := by
  have hLo := uniform_threshold_upperFeasible hi hcard univ
  have hHi := uniform_homologicalRank_cap (V := V) i i hi hi univ
  simp only [subsetSum_constExponent, card_univ, hcard] at hLo hHi
  simp only [uniformPowerRank_apply, card_univ, hcard,
    min_eq_right (Nat.le_succ i)]
  nlinarith

theorem uniform_threshold_isRankBase {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    IsRankBase
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i)
      (constExponent i) := by
  refine ⟨?_, uniform_threshold_upperFeasible hi hcard⟩
  rw [degree_constExponent, uniform_homologicalRank_top hi hcard]
  simp only [hcard, uniformPowerRank_apply, card_univ,
    min_eq_right (Nat.le_succ i)]
  nlinarith

/-- The exact unique base at the sharp threshold, with no restriction on the
positive homological degree. -/
theorem uniform_threshold_isRankBase_iff {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) (a : Exponent V) :
    IsRankBase
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i) a ↔
      a = constExponent i := by
  constructor
  · intro ha
    have hcap : a ≤ constExponent i := by
      intro j
      have h := ha.2 {j}
      rw [homologicalRank_singleton] at h
      simpa only [subsetSum, sum_singleton, uniformPowerRank_apply, card_singleton,
        min_eq_left hi, Nat.mul_one, constExponent_apply] using h
    apply eq_of_le_of_degree_eq hcap
    exact ha.1.trans (uniform_threshold_isRankBase hi hcard).1.symm
  · rintro rfl
    exact uniform_threshold_isRankBase hi hcard

theorem uniform_threshold_rankBases {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    rankBases
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i) =
      {constExponent i} := by
  ext a
  rw [mem_rankBases, uniform_threshold_isRankBase_iff hi hcard, mem_singleton]

end CommAlg.Polymatroid

end
end CheckedSource89

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "90: CommAlg.Polymatroid.HomologicalSharpness\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalSharpness -/
section CheckedSource90

/-! # The sharp uniform-Veronese example in every positive degree

The ideal is the squarefree Veronese ideal in `i+1` variables. Its exact
generators are identified, and every homological shift assertion uses
the genuine derived-Tor definition on actual powers of that ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

def squarefreeVeroneseIdeal (k : Type u) [CommRing k] (V : Type u)
    [Fintype V] [LinearOrder V] (d : ℕ) : Ideal (MvPolynomial V k) :=
  rankIdeal k (uniformRank V d)

theorem squarefreeVeronese_polymatroidal (d : ℕ) :
    IsPolymatroidalIdeal (squarefreeVeroneseIdeal k V d) :=
  isPolymatroidalIdeal_rankIdeal _

/-- The generating monomials are exactly the squarefree monomials of
degree `d`, whenever `d` is at most the number of variables. -/
theorem squarefreeVeronese_generators (d : ℕ) (hd : d ≤ Fintype.card V) (a : Exponent V) :
    a ∈ rankBases (uniformRank V d) ↔ a.degree = d ∧ ∀ j, a j ≤ 1 := by
  have he : uniformPowerRank V d 1 = uniformRank V d := by
    apply RankFunction.ext_fun
    intro A
    simp
  rw [← he, mem_rankBases, isRankBase_uniformPower_iff d 1 hd]
  simp

theorem squarefreeVeronese_power_rank (d s : ℕ) :
    squarefreeVeroneseIdeal k V d ^ s = rankIdeal k (uniformPowerRank V d s) :=
  (rankIdeal_scale k (uniformRank V d) s).symm

/-- Proposition 4.2, vanishing at every positive power strictly below `i`. -/
theorem squarefreeVeronese_shift_below {i s : ℕ} (hi : 1 ≤ i) (hs : 1 ≤ s)
    (hsi : s < i) (hcard : Fintype.card V = i + 1) :
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ s)
      ((squarefreeVeronese_polymatroidal i).pow s) i = ⊥ := by
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (uniformPowerRank V i s)
    (squarefreeVeronese_power_rank i s) i]
  have he : universalHomologicalRank (uniformPowerRank V i s) i =
      homologicalRank (uniformPowerRank V i s) (uniformPowerRank_active hi hs) i := by
    apply RankFunction.ext_fun
    exact universalHomologicalRank_eq_active _ _ i
  have hlt := uniform_homologicalRank_lt hi hs hsi hcard
  simp only [rankShiftIdeal, he, if_neg (Nat.ne_of_lt hlt)]

theorem monomial_constExponent_eq_prod_pow (i : ℕ) :
    MvPolynomial.monomial (constExponent i : Exponent V) (1 : k) =
      (∏ j : V, MvPolynomial.X j) ^ i := by
  rw [← Finset.prod_pow]
  rw [MvPolynomial.prod_X_pow]
  have he : (constExponent i : Exponent V) = Finsupp.indicator univ (fun _ _ => i) := by
    ext j
    simp
  exact congrArg (fun a : Exponent V => MvPolynomial.monomial a (1 : k)) he

/-- Proposition 4.2, the exact principal ideal at the sharp threshold. -/
theorem squarefreeVeronese_shift_at_threshold {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ i)
      ((squarefreeVeronese_polymatroidal i).pow i) i =
        Ideal.span {(∏ j : V, (MvPolynomial.X j : MvPolynomial V k)) ^ i} := by
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (uniformPowerRank V i i)
    (squarefreeVeronese_power_rank i i) i]
  have he : universalHomologicalRank (uniformPowerRank V i i) i =
      homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i := by
    apply RankFunction.ext_fun
    exact universalHomologicalRank_eq_active _ _ i
  rw [rankShiftIdeal, he, if_pos (uniform_homologicalRank_top hi hcard), rankIdeal,
    uniform_threshold_rankBases hi hcard, monomialIdeal]
  simp only [Finset.coe_singleton, Set.image_singleton, monomial_constExponent_eq_prod_pow]

theorem squarefreeVeronese_shift_at_threshold_ne_bot {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ i)
      ((squarefreeVeronese_polymatroidal i).pow i) i ≠ ⊥ := by
  rw [squarefreeVeronese_shift_at_threshold hi hcard,
    ← monomial_constExponent_eq_prod_pow]
  intro he
  have hm : MvPolynomial.monomial (constExponent i : Exponent V) (1 : k) ∈
      Ideal.span {MvPolynomial.monomial (constExponent i : Exponent V) (1 : k)} :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [he, Ideal.mem_bot] at hm
  simpa using hm

end CommAlg.Polymatroid

end
end CheckedSource90

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "91: CommAlg.Polymatroid.Revlex\n"

/-! ## Source: CommAlg.Polymatroid.Revlex -/
section CheckedSource91

/-! # Reverse lexicographic exchange and the colon variables

The strict comparison records the largest differing variable. This convention
orders equigenerated monomials in decreasing reverse lexicographic order.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

def RevlexBefore (a b : Exponent V) : Prop :=
  ∃ i, a i < b i ∧ ∀ j, i < j → a j = b j

theorem revlexBefore_irrefl (a : Exponent V) : ¬ RevlexBefore a a := by
  rintro ⟨i, hi, _⟩
  exact (lt_irrefl _ hi)

theorem revlexBefore_trans {a b c : Exponent V}
    (hab : RevlexBefore a b) (hbc : RevlexBefore b c) : RevlexBefore a c := by
  obtain ⟨i, hi, he⟩ := hab
  obtain ⟨j, hj, hf⟩ := hbc
  rcases lt_trichotomy i j with hij | rfl | hji
  · refine ⟨j, ?_, fun x hx => (he x (hij.trans hx)).trans (hf x hx)⟩
    rw [he j hij]
    exact hj
  · exact ⟨i, hi.trans hj, fun x hx => (he x hx).trans (hf x hx)⟩
  · refine ⟨i, ?_, fun x hx => (he x hx).trans (hf x (hji.trans hx))⟩
    rw [← hf i hji]
    exact hi

theorem revlexBefore_asymm {a b : Exponent V} (hab : RevlexBefore a b) :
    ¬ RevlexBefore b a := fun hba => revlexBefore_irrefl a (revlexBefore_trans hab hba)

theorem revlexBefore_total {a b : Exponent V} (hab : a ≠ b) :
    RevlexBefore a b ∨ RevlexBefore b a := by
  let D := univ.filter (fun i => a i ≠ b i)
  have hD : D.Nonempty := by
    by_contra h
    apply hab
    ext i
    by_contra hi
    exact h ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  let i := D.max' hD
  have hi : a i ≠ b i := (mem_filter.mp (D.max'_mem hD)).2
  have he : ∀ j, i < j → a j = b j := by
    intro j hij
    by_contra hj
    have hjD : j ∈ D := mem_filter.mpr ⟨mem_univ j, hj⟩
    exact (not_lt_of_ge (D.le_max' j hjD)) hij
  rcases lt_or_gt_of_ne hi with h | h
  · exact Or.inl ⟨i, h, he⟩
  · exact Or.inr ⟨i, h, fun j hj => (he j hj).symm⟩

def revlexBeforeFamily (B : Family V) (b : Exponent V) : Family V :=
  B.filter (fun a => RevlexBefore a b)

@[simp] theorem mem_revlexBeforeFamily (B : Family V) (a b : Exponent V) :
    a ∈ revlexBeforeFamily B b ↔ a ∈ B ∧ RevlexBefore a b := by
  simp [revlexBeforeFamily]

def revlexColonVariables (B : Family V) (b : Exponent V) : Finset V :=
  univ.filter (fun j => ∃ i, j < i ∧ 0 < b i ∧ exchange b i j ∈ B)

@[simp] theorem mem_revlexColonVariables (B : Family V) (b : Exponent V) (j : V) :
    j ∈ revlexColonVariables B b ↔
      ∃ i, j < i ∧ 0 < b i ∧ exchange b i j ∈ B := by
  simp [revlexColonVariables]

theorem exchange_revlexBefore (b : Exponent V) {i j : V}
    (hji : j < i) (hi : 0 < b i) : RevlexBefore (exchange b i j) b := by
  refine ⟨i, ?_, ?_⟩
  · simp only [exchange_apply, ite_true, if_neg (ne_of_gt hji)]
    omega
  · intro x hix
    simp [exchange_apply, ne_of_gt hix, ne_of_gt (hji.trans hix)]

/-- A preceding generator supplies a colon variable which divides its quotient
by the gcd with the current generator. -/
theorem revlex_exchange {B : Family V} (hB : ExchangeAxiom B)
    {a b : Exponent V} (ha : a ∈ B) (hb : b ∈ B) (hab : RevlexBefore a b) :
    ∃ j ∈ revlexColonVariables B b, b j < a j := by
  obtain ⟨i, hi, he⟩ := hab
  obtain ⟨j, hj, hex⟩ := hB b hb a ha i hi
  have hji : j < i := by
    rcases lt_trichotomy j i with h | rfl | h
    · exact h
    · omega
    · have := he j h
      omega
  exact ⟨j, (mem_revlexColonVariables B b j).mpr ⟨i, hji, by omega, hex⟩, hj⟩

/-- Exact divisibility criterion for the preceding generators, before passing
to polynomial ideals. -/
theorem contains_revlexBefore_add_iff {B : Family V} (hB : ExchangeAxiom B)
    {b : Exponent V} (hb : b ∈ B) (a : Exponent V) :
    Contains (revlexBeforeFamily B b) (a + b) ↔
      ∃ j ∈ revlexColonVariables B b, 0 < a j := by
  constructor
  · rintro ⟨c, hc, hca⟩
    obtain ⟨hcB, hcb⟩ := (mem_revlexBeforeFamily B c b).mp hc
    obtain ⟨j, hj, hbj⟩ := revlex_exchange hB hcB hb hcb
    refine ⟨j, hj, ?_⟩
    have hle := hca j
    simp only [Finsupp.add_apply] at hle
    omega
  · rintro ⟨j, hj, haj⟩
    obtain ⟨i, hji, hbi, hex⟩ := (mem_revlexColonVariables B b j).mp hj
    refine ⟨exchange b i j, (mem_revlexBeforeFamily B _ b).mpr
      ⟨hex, exchange_revlexBefore b hji hbi⟩, ?_⟩
    intro x
    simp only [exchange_apply, Finsupp.add_apply]
    by_cases hxj : x = j
    · subst x
      simp only [if_neg (ne_of_lt hji), ite_true]
      omega
    · simp only [if_neg hxj]
      split <;> omega

end CommAlg.Polymatroid

end
end CheckedSource91

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "92: CommAlg.Polymatroid.LinearQuotients\n"

/-! ## Source: CommAlg.Polymatroid.LinearQuotients -/
section CheckedSource92

/-! # Actual linear quotients of polymatroidal monomial ideals

The colon ideal is the ordinary ideal quotient in the polynomial ring, and
its generators are actual variables. The coefficient calculation proves that
no non-monomial elements are lost in the passage to exponent divisibility.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {k : Type*} [CommSemiring k]

theorem mem_monomialIdeal_colon_iff (B : Family V) (b : Exponent V)
    (f : MvPolynomial V k) :
    f ∈ (monomialIdeal k B).colon {MvPolynomial.monomial b 1} ↔
      ∀ a ∈ f.support, Contains B (a + b) := by
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mem_monomialIdeal_iff]
  constructor
  · intro h a ha
    apply h
    simpa only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul_monomial,
      mul_one] using (MvPolynomial.mem_support_iff.mp ha)
  · intro h c hc
    have hc' := MvPolynomial.mem_support_iff.mp hc
    have hbc : b ≤ c := by
      by_contra hbc
      rw [MvPolynomial.coeff_mul_monomial', if_neg hbc] at hc'
      exact hc' rfl
    have ha : c - b ∈ f.support := by
      rw [MvPolynomial.mem_support_iff]
      simpa only [MvPolynomial.coeff_mul_monomial', if_pos hbc, mul_one] using hc'
    have hh := h (c - b) ha
    rwa [tsub_add_cancel_of_le hbc] at hh

/-- The ideal generated by the indicated polynomial variables. -/
def variableIdeal (C : Finset V) : Ideal (MvPolynomial V k) :=
  Ideal.span (MvPolynomial.X '' (C : Set V))

theorem variableIdeal_eq_monomialIdeal (C : Finset V) :
    variableIdeal (k := k) C =
      monomialIdeal k (C.image (fun j => Finsupp.single j 1)) := by
  unfold variableIdeal monomialIdeal
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Finsupp.single j 1, mem_image.mpr ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
    exact ⟨j, hj, rfl⟩

theorem contains_variableFamily_iff (C : Finset V) (a : Exponent V) :
    Contains (C.image (fun j => Finsupp.single j 1)) a ↔
      ∃ j ∈ C, 0 < a j := by
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
    refine ⟨j, hj, ?_⟩
    have := hba j
    simpa only [Finsupp.single_eq_same, Nat.succ_le_iff] using this
  · rintro ⟨j, hj, haj⟩
    refine ⟨Finsupp.single j 1, mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
    intro x
    by_cases hx : x = j
    · subst x
      simpa using (show 1 ≤ a j by omega)
    · simp [Finsupp.single_apply, hx, Ne.symm hx]

theorem mem_variableIdeal_iff (C : Finset V) (f : MvPolynomial V k) :
    f ∈ variableIdeal (k := k) C ↔
      ∀ a ∈ f.support, ∃ j ∈ C, 0 < a j := by
  rw [variableIdeal_eq_monomialIdeal, mem_monomialIdeal_iff]
  simp_rw [contains_variableFamily_iff]

/-- The exact reverse-lexicographic linear quotient of every polymatroidal
family. This includes the first generator, whose colon has no variables. -/
theorem revlex_colon_eq_variableIdeal {B : Family V} (hB : ExchangeAxiom B)
    {b : Exponent V} (hb : b ∈ B) :
    (monomialIdeal k (revlexBeforeFamily B b)).colon {MvPolynomial.monomial b 1} =
      variableIdeal (k := k) (revlexColonVariables B b) := by
  ext f
  rw [mem_monomialIdeal_colon_iff, mem_variableIdeal_iff]
  simp_rw [contains_revlexBefore_add_iff hB hb]

/-- The form with the principal ideal in the denominator. -/
theorem revlex_colon_span_eq_variableIdeal {B : Family V} (hB : ExchangeAxiom B)
    {b : Exponent V} (hb : b ∈ B) :
    (monomialIdeal k (revlexBeforeFamily B b)).colon
        (Ideal.span {MvPolynomial.monomial b (1 : k)}) =
      variableIdeal (k := k) (revlexColonVariables B b) := by
  rw [Ideal.colon_span, revlex_colon_eq_variableIdeal hB hb]

theorem rankBases_revlex_colon_eq (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    (monomialIdeal k (revlexBeforeFamily (rankBases g) b)).colon
        {MvPolynomial.monomial b 1} =
      variableIdeal (k := k) (revlexColonVariables (rankBases g) b) :=
  revlex_colon_eq_variableIdeal (rankBases_polymatroidal g).2 hb

end CommAlg.Polymatroid

end
end CheckedSource92

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "93: CommAlg.ProjectiveDimension.KoszulBound\n"

/-! ## Source: CommAlg.ProjectiveDimension.KoszulBound -/
section CheckedSource93

/-!
# Actual projective-dimension bounds from the finite Koszul resolution

These are bounds on Mathlib's Ext-defined projective dimension. No residue-Tor
vanishing criterion or local-ring hypothesis is used for the upper bound.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace CommAlg.ProjectiveDimension

universe u v w

theorem le_of_resolution {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {X : C} (P : ProjectiveResolution X) (N : ℕ)
    (h : ∀ n, N < n → IsZero (P.complex.X n)) :
    projectiveDimension X ≤ N := by
  rw [projectiveDimension_le_iff]
  apply HasProjectiveDimensionLT.mk
  intro n hn Y e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 1) rfl
  have hf0 : f = 0 := (h n (by omega)).eq_of_src _ _
  subst f
  exact P.extMk_zero (n + 1) rfl

variable {R : Type u} [CommRing R]

theorem exteriorPower_fin_isZero (m n : ℕ) (h : m < n) :
    IsZero (ModuleCat.of R (⋀[R]^n (Fin m → R))) := by
  letI : IsEmpty (Set.powersetCard (Fin m) n) := ⟨fun s => by
    have hc := Finset.card_le_univ s.val
    have he : s.val.card = n := s.property
    simp only [Fintype.card_fin] at hc
    omega⟩
  haveI : Subsingleton (⋀[R]^n (Fin m → R)) := ⟨fun x y =>
    ((Pi.basisFun R (Fin m)).exteriorPower n).repr.injective (Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

theorem regularSequence_quotient_le (l : List R)
    (hl : RingTheory.Sequence.IsRegular R l) :
    projectiveDimension (ModuleCat.of R (R ⧸ Ideal.ofList l)) ≤ l.length := by
  letI := HasExt.standard (ModuleCat.{u} R)
  apply le_of_resolution (CommAlg.Koszul.regularSequenceResolution l hl) l.length
  intro n hn
  change IsZero (ModuleCat.of R (⋀[R]^n (Fin l.length → R)))
  exact exteriorPower_fin_isZero l.length n hn

variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem variableIdeal_quotient_le (A : Finset V) :
    projectiveDimension
      (ModuleCat.of (MvPolynomial V k)
        (MvPolynomial V k ⧸ CommAlg.Polymatroid.variableIdeal (k := k) A)) ≤ A.card := by
  let l : List (MvPolynomial V k) := A.toList.map MvPolynomial.X
  have hreg := CommAlg.Koszul.variables_regular (k := k) A.toList A.nodup_toList
  have he : Ideal.ofList l = CommAlg.Polymatroid.variableIdeal (k := k) A := by
    apply congrArg Ideal.span
    ext f
    simp [l, CommAlg.Polymatroid.variableIdeal]
  have h := regularSequence_quotient_le l hreg
  have hlen : l.length = A.card := by simp [l]
  rw [he, hlen] at h
  exact h

end CommAlg.ProjectiveDimension

end
end CheckedSource93

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "94: CommAlg.ProjectiveDimension.IdealGeneratorExact\n"

/-! ## Source: CommAlg.ProjectiveDimension.IdealGeneratorExact -/
section CheckedSource94

/-! # The exact sequence for adjoining one ideal generator

For every commutative ring, this constructs the literal short exact sequence
`0 → J → J + (m) → R/(J:m) → 0`. No regularity assumption on `m` is needed.
-/

noncomputable section

namespace CommAlg

open Classical CategoryTheory

variable {R : Type*} [CommRing R]

def generatorExtension (J : Ideal R) (m : R) : Ideal R := J ⊔ Ideal.span {m}

def generatorSubmodule (J : Ideal R) (m : R) : Submodule R (generatorExtension J m) :=
  Submodule.comap (generatorExtension J m).subtype (J : Submodule R R)

abbrev generatorQuotient (J : Ideal R) (m : R) :=
  generatorExtension J m ⧸ generatorSubmodule J m

def mulToGeneratorExtension (J : Ideal R) (m : R) : R →ₗ[R] generatorExtension J m where
  toFun r := ⟨r * m, (show Ideal.span {m} ≤ generatorExtension J m from le_sup_right)
    (Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩)⟩
  map_add' r s := Subtype.ext (add_mul r s m)
  map_smul' r s := Subtype.ext (by simp [mul_assoc])

def generatorQuotientMap (J : Ideal R) (m : R) : R →ₗ[R] generatorQuotient J m :=
  (generatorSubmodule J m).mkQ.comp (mulToGeneratorExtension J m)

theorem generatorQuotientMap_ker (J : Ideal R) (m : R) :
    LinearMap.ker (generatorQuotientMap J m) = J.colon {m} := by
  ext r
  simp only [LinearMap.mem_ker, generatorQuotientMap, LinearMap.comp_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_colon_singleton,
    smul_eq_mul]
  rfl

theorem generatorQuotientMap_surjective (J : Ideal R) (m : R) :
    Function.Surjective (generatorQuotientMap J m) := by
  intro q
  obtain ⟨x, rfl⟩ := (generatorSubmodule J m).mkQ_surjective q
  obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp x.property
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨r, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change r * m - x.val ∈ J
  rw [← he, ← hr]
  simpa using J.neg_mem hy

/-- The actual quotient by the previously generated ideal is the quotient by
the ordinary colon ideal. -/
def generatorQuotientEquiv (J : Ideal R) (m : R) :
    generatorQuotient J m ≃ₗ[R] R ⧸ J.colon {m} :=
  (LinearMap.quotKerEquivOfSurjective (generatorQuotientMap J m)
    (generatorQuotientMap_surjective J m)).symm.trans
      (Submodule.quotEquivOfEq _ _ (generatorQuotientMap_ker J m))

def generatorInclusion (J : Ideal R) (m : R) : J →ₗ[R] generatorExtension J m :=
  Submodule.inclusion le_sup_left

def generatorProjection (J : Ideal R) (m : R) :
    generatorExtension J m →ₗ[R] R ⧸ J.colon {m} :=
  (generatorQuotientEquiv J m).toLinearMap.comp (generatorSubmodule J m).mkQ

@[simp] theorem generatorProjection_eq_zero_iff (J : Ideal R) (m : R)
    (x : generatorExtension J m) : generatorProjection J m x = 0 ↔ x.val ∈ J := by
  change (generatorQuotientEquiv J m) ((generatorSubmodule J m).mkQ x) = 0 ↔ _
  rw [(generatorQuotientEquiv J m).map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

theorem generatorProjection_comp_inclusion (J : Ideal R) (m : R) :
    (generatorProjection J m).comp (generatorInclusion J m) = 0 := by
  ext x
  apply (generatorProjection_eq_zero_iff J m _).mpr
  exact x.property

/-- The genuine categorical exact sequence used for induction along a linear
quotient ordering. -/
def generatorExact (J : Ideal R) (m : R) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (generatorInclusion J m) (generatorProjection J m)
    (generatorProjection_comp_inclusion J m)

theorem generatorExact_shortExact (J : Ideal R) (m : R) :
    (generatorExact J m).ShortExact := by
  unfold generatorExact
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (generatorInclusion J m) (generatorProjection J m)
    intro x
    rw [generatorProjection_eq_zero_iff]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  · change Function.Injective (generatorInclusion J m)
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : generatorExtension J m => z.val) hxy)
  · exact (generatorQuotientEquiv J m).surjective.comp
      (generatorSubmodule J m).mkQ_surjective

/-- The projective-dimension bound has exactly the two terms needed in the
linear-quotient induction. -/
theorem generatorExtension_projectiveDimension_le (J : Ideal R) (m : R) :
    projectiveDimension (ModuleCat.of R (generatorExtension J m)) ≤
      projectiveDimension (ModuleCat.of R J) ⊔
        projectiveDimension (ModuleCat.of R (R ⧸ J.colon {m})) :=
  (generatorExact_shortExact J m).projectiveDimension_X₂_le_sup

end CommAlg

end
end CheckedSource94

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "95: CommAlg.Polymatroid.HomogenizedRank\n"

/-! ## Source: CommAlg.Polymatroid.HomogenizedRank -/
section CheckedSource95

/-! # Homogenization of ranks with ordered marginal increments

`none` denotes the additional coordinate `z`; `some j` denotes an original
coordinate.  Both branches of the rank formula are proved for every subset.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def rankGap (g u : RankFunction V) : ℕ := u univ - g univ

theorem RankFunction.gap_bound {g u : RankFunction V} (h : u.Dominates g)
    (A : Finset V) : u A ≤ rankGap g u + g A := by
  have hE := RankFunction.le_of_dominates h univ
  have hm := h A univ (subset_univ A)
  unfold rankGap
  omega

def homogenizedRankValue (g u : RankFunction V) (A : Finset (Option V)) : ℕ :=
  if none ∈ A then rankGap g u + g A.eraseNone else u A.eraseNone

/-- The second interpolation in Lemma 3.3, on the ground set extended by one
genuine new coordinate. -/
def RankFunction.homogenize (g u : RankFunction V) (h : u.Dominates g) :
    RankFunction (Option V) where
  toFun := homogenizedRankValue g u
  empty := by simp [homogenizedRankValue]
  monotone := by
    intro A B hAB
    have hm : A.eraseNone ⊆ B.eraseNone := Finset.eraseNone.monotone hAB
    by_cases hA : none ∈ A
    · have hB := hAB hA
      simp only [homogenizedRankValue, if_pos hA, if_pos hB]
      exact Nat.add_le_add_left (g.monotone hm) _
    · by_cases hB : none ∈ B
      · simp only [homogenizedRankValue, if_neg hA, if_pos hB]
        exact (RankFunction.gap_bound h A.eraseNone).trans
          (Nat.add_le_add_left (g.monotone hm) _)
      · simp only [homogenizedRankValue, if_neg hA, if_neg hB]
        exact u.monotone hm
  submodular := by
    intro A B
    have hg := g.submodular A.eraseNone B.eraseNone
    have hu := u.submodular A.eraseNone B.eraseNone
    have hm := RankFunction.mixed_submodular h A.eraseNone B.eraseNone
    have hm' := RankFunction.mixed_submodular h B.eraseNone A.eraseNone
    rw [Finset.union_comm B.eraseNone A.eraseNone,
      Finset.inter_comm B.eraseNone A.eraseNone] at hm'
    by_cases hA : none ∈ A <;> by_cases hB : none ∈ B <;>
      simp [homogenizedRankValue, hA, hB] <;> omega

@[simp] theorem RankFunction.homogenize_apply (g u : RankFunction V)
    (h : u.Dominates g) (A : Finset (Option V)) :
    g.homogenize u h A = homogenizedRankValue g u A := rfl

@[simp] theorem RankFunction.homogenize_some (g u : RankFunction V)
    (h : u.Dominates g) (A : Finset V) :
    g.homogenize u h (A.image some) = u A := by
  simp [homogenizedRankValue]

@[simp] theorem RankFunction.homogenize_insertNone (g u : RankFunction V)
    (h : u.Dominates g) (A : Finset V) :
    g.homogenize u h A.insertNone = rankGap g u + g A := by
  simp [homogenizedRankValue]

@[simp] theorem RankFunction.homogenize_singleton_none (g u : RankFunction V)
    (h : u.Dominates g) :
    g.homogenize u h {none} = rankGap g u := by
  simp [homogenizedRankValue]

@[simp] theorem RankFunction.homogenize_univ (g u : RankFunction V)
    (h : u.Dominates g) :
    g.homogenize u h univ = u univ := by
  have hg := RankFunction.le_of_dominates h univ
  have he : (univ : Finset (Option V)).eraseNone = univ := by ext x; simp
  simp [homogenizedRankValue, he, rankGap, Nat.sub_add_cancel hg]

end CommAlg.Polymatroid

end
end CheckedSource95

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "96: CommAlg.Polymatroid.HomogenizedBases\n"

/-! ## Source: CommAlg.Polymatroid.HomogenizedBases -/
section CheckedSource96

/-! # Homogenizing all homological-shift rank ideals

The extra variable is `none`. The results below identify every base of the
homogenized rank, and then identify the actual polynomial ideal generated by
all the powers of this variable times the renamed shift ideals. No topological
or homological support is built into the definition of these rank ideals.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem subsetSum_image_some (e : Exponent (Option V)) (A : Finset V) :
    subsetSum e (A.image some) = subsetSum e.some A := by
  unfold subsetSum
  rw [Finset.sum_image]
  · rfl
  · intro x hx y hy hxy
    exact Option.some.inj hxy

@[simp] theorem subsetSum_insertNone (e : Exponent (Option V)) (A : Finset V) :
    subsetSum e A.insertNone = e none + subsetSum e.some A := by
  exact Finset.sum_insertNone e A

theorem degree_option (e : Exponent (Option V)) :
    e.degree = e none + e.some.degree := by
  rw [← subsetSum_univ, univ_option, subsetSum_insertNone, subsetSum_univ]

@[simp] theorem degree_optionElim (a : Exponent V) (z : ℕ) :
    (a.optionElim z).degree = z + a.degree := by
  rw [degree_option]
  simp

theorem upperFeasible_homogenize_iff (g u : RankFunction V) (h : u.Dominates g)
    (e : Exponent (Option V)) :
    UpperFeasible (g.homogenize u h) e ↔
      UpperFeasible u e.some ∧
        ∀ A, e none + subsetSum e.some A ≤ rankGap g u + g A := by
  constructor
  · intro he
    constructor
    · intro A
      simpa only [subsetSum_image_some, RankFunction.homogenize_some] using he (A.image some)
    · intro A
      simpa only [subsetSum_insertNone, RankFunction.homogenize_insertNone] using he A.insertNone
  · rintro ⟨hu, hg⟩ C
    by_cases hC : none ∈ C
    · have hEq : C.eraseNone.insertNone = C := by
        rw [Finset.insertNone_eraseNone, Finset.insert_eq_of_mem hC]
      rw [← hEq, subsetSum_insertNone, RankFunction.homogenize_insertNone]
      exact hg _
    · have hEq : C.eraseNone.image some = C := by
        rw [Finset.image_some_eraseNone, Finset.erase_eq_of_notMem hC]
      rw [← hEq, subsetSum_image_some, RankFunction.homogenize_some]
      exact hu _

/-- The rank function occurring in Theorem 5.1, including ranks with loops. -/
def homogenizedShiftRank (g : RankFunction V) : RankFunction (Option V) :=
  g.homogenize (universalAugmentedRank g) (universalAugmentedRank_dominates g)

/-- Its degree excess over the original ideal, eventually identified with the
projective dimension by the genuine Tor support theorem. -/
def shiftLength (g : RankFunction V) : ℕ := rankGap g (universalAugmentedRank g)

theorem shiftLength_add_degree (g : RankFunction V) :
    shiftLength g + g univ = universalAugmentedRank g univ := by
  exact Nat.sub_add_cancel
    (RankFunction.le_of_dominates (universalAugmentedRank_dominates g) univ)

theorem isRankBase_homogenizedShift_iff (g : RankFunction V)
    (e : Exponent (Option V)) :
    IsRankBase (homogenizedShiftRank g) e ↔
      ∃ i ≤ shiftLength g, ∃ a ∈ rankShiftFamily g i,
        e = a.optionElim (shiftLength g - i) := by
  constructor
  · rintro ⟨hdeg, he⟩
    have hsplit := (upperFeasible_homogenize_iff g (universalAugmentedRank g)
      (universalAugmentedRank_dominates g) e).mp he
    have hz : e none ≤ shiftLength g := by
      have hz := hsplit.2 ∅
      simpa [shiftLength] using hz
    have htotal : e none + e.some.degree = shiftLength g + g univ := by
      rw [← degree_option, hdeg]
      exact (RankFunction.homogenize_univ g _ _).trans (shiftLength_add_degree g).symm
    refine ⟨shiftLength g - e none, Nat.sub_le _ _, e.some, ?_, ?_⟩
    · rw [mem_rankShiftFamily_iff]
      refine ⟨by omega, ?_⟩
      intro A
      by_cases hA : A = ∅
      · simp [hA]
      · rw [universalHomologicalRank_apply g _ (Finset.nonempty_iff_ne_empty.mpr hA)]
        have hb := hsplit.2 A
        change e none + subsetSum e.some A ≤ shiftLength g + g A at hb
        exact le_min (by omega) (hsplit.1 A)
    · have hez : shiftLength g - (shiftLength g - e none) = e none := by omega
      rw [hez, Finsupp.optionElim_some]
  · rintro ⟨i, hi, a, ha, rfl⟩
    obtain ⟨haDeg, haBound⟩ := (mem_rankShiftFamily_iff g i a).mp ha
    constructor
    · rw [degree_optionElim, haDeg]
      change shiftLength g - i + (g univ + i) =
        g.homogenize (universalAugmentedRank g) (universalAugmentedRank_dominates g) univ
      rw [RankFunction.homogenize_univ, ← shiftLength_add_degree]
      omega
    · change UpperFeasible (g.homogenize (universalAugmentedRank g)
        (universalAugmentedRank_dominates g)) _
      rw [upperFeasible_homogenize_iff]
      simp only [Finsupp.some_optionElim, Finsupp.optionElim_apply_none]
      constructor
      · intro A
        exact (haBound A).trans
          (shiftRankValue_le_u g (universalAugmentedRank g) i A)
      · intro A
        have hb := (haBound A).trans (universalHomologicalRank_le_add g i A)
        change shiftLength g - i + subsetSum a A ≤ shiftLength g + g A
        omega

theorem rankBases_homogenizedShift (g : RankFunction V) :
    rankBases (homogenizedShiftRank g) =
      (Finset.range (shiftLength g + 1)).biUnion (fun i =>
        (rankShiftFamily g i).image (fun a => a.optionElim (shiftLength g - i))) := by
  ext e
  simp only [mem_rankBases, isRankBase_homogenizedShift_iff,
    Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Nat.lt_succ_iff]
  constructor
  · rintro ⟨i, hi, a, ha, he⟩
    exact ⟨i, hi, a, ha, he.symm⟩
  · rintro ⟨i, hi, a, ha, he⟩
    exact ⟨i, hi, a, ha, he.symm⟩

end CommAlg.Polymatroid

end
end CheckedSource96

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "97: CommAlg.Polymatroid.RevlexColonCardinality\n"

/-! ## Source: CommAlg.Polymatroid.RevlexColonCardinality -/
section CheckedSource97

/-! # Bounding every actual linear quotient by the homological rank gap

For a base `b`, add one to each colon variable. The resulting exponent obeys
the full partition inequalities. The key strict inequality on a nonempty set
of colon variables follows by choosing its largest variable: a legal transfer
into that variable must have its donor still larger.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

@[simp] theorem subsetSum_faceExponent (C A : Finset V) :
    subsetSum (Koszul.faceExponent C) A = (A ∩ C).card := by
  simp [subsetSum, Koszul.faceExponent_apply, ← Finset.sum_filter]

@[simp] theorem degree_faceExponent (C : Finset V) :
    (Koszul.faceExponent C).degree = C.card := by
  rw [← subsetSum_univ, subsetSum_faceExponent, univ_inter]

def revlexColonWitness (B : Family V) (b : Exponent V) : Exponent V :=
  b + Koszul.faceExponent (revlexColonVariables B b)

/-- A nonempty set of colon variables cannot be tight at the current base. -/
theorem rankBase_strict_on_colon_subset (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) {A : Finset V} (hA : A.Nonempty)
    (hAC : A ⊆ revlexColonVariables (rankBases g) b) : subsetSum b A < g A := by
  have hbound := ((mem_rankBases g b).mp hb).2 A
  by_contra hbad
  have htight : subsetSum b A = g A := by omega
  let j := A.max' hA
  have hjA : j ∈ A := A.max'_mem hA
  obtain ⟨i, hji, hbi, hex⟩ :=
    (mem_revlexColonVariables (rankBases g) b j).mp (hAC hjA)
  have hiA : i ∈ A := by
    by_contra hiA
    have hs := subsetSum_exchange b i j hbi A
    rw [if_neg hiA, if_pos hjA] at hs
    have hc := ((mem_rankBases g _).mp hex).2 A
    omega
  exact (not_lt_of_ge (A.le_max' i hiA)) hji

theorem revlexColonWitness_subset_bound (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) {A : Finset V} (hA : A.Nonempty) :
    subsetSum (revlexColonWitness (rankBases g) b) A ≤ g A + A.card - 1 := by
  rw [revlexColonWitness, subsetSum_add, subsetSum_faceExponent]
  have hbA := ((mem_rankBases g b).mp hb).2 A
  have hc : (A ∩ revlexColonVariables (rankBases g) b).card ≤ A.card :=
    card_le_card inter_subset_left
  by_cases hAC : A ⊆ revlexColonVariables (rankBases g) b
  · have hlt := rankBase_strict_on_colon_subset g hb hA hAC
    omega
  · have hlt : (A ∩ revlexColonVariables (rankBases g) b).card < A.card := by
      by_contra h
      have he : A ∩ revlexColonVariables (rankBases g) b = A :=
        eq_of_subset_of_card_le inter_subset_left (by omega)
      apply hAC
      rw [← he]
      exact inter_subset_right
    omega

theorem revlexColonWitness_upperFeasible (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    UpperFeasible (universalAugmentedRank g) (revlexColonWitness (rankBases g) b) :=
  (universal_bounds_iff g _).mp (fun _ hA => revlexColonWitness_subset_bound g hb hA)

/-- The size of each genuine colon generating set is bounded by the exact
partition-rank gap. There is no activity hypothesis. -/
theorem revlexColonVariables_card_le_shiftLength (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    (revlexColonVariables (rankBases g) b).card ≤ shiftLength g := by
  have h := revlexColonWitness_upperFeasible g hb univ
  rw [subsetSum_univ, revlexColonWitness, map_add, degree_faceExponent,
    ((mem_rankBases g b).mp hb).1] at h
  have hp := shiftLength_add_degree g
  omega

/-- The same construction is a base in the exact shift layer of the colon
cardinality, which later gives a genuine Tor nonvanishing witness. -/
theorem revlexColonWitness_mem_shiftFamily (g : RankFunction V)
    {b : Exponent V} (hb : b ∈ rankBases g) :
    revlexColonWitness (rankBases g) b ∈
      rankShiftFamily g (revlexColonVariables (rankBases g) b).card := by
  rw [mem_rankShiftFamily_iff]
  constructor
  · rw [revlexColonWitness, map_add, degree_faceExponent, ((mem_rankBases g b).mp hb).1]
  · intro A
    by_cases hA : A = ∅
    · simp [hA]
    rw [universalHomologicalRank_apply g _ (nonempty_iff_ne_empty.mpr hA)]
    refine le_min ?_ (revlexColonWitness_upperFeasible g hb A)
    rw [revlexColonWitness, subsetSum_add, subsetSum_faceExponent]
    exact Nat.add_le_add (((mem_rankBases g b).mp hb).2 A)
      (card_le_card inter_subset_right)

end CommAlg.Polymatroid

end
end CheckedSource97

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "98: CommAlg.ProjectiveDimension.RankIdealUpper\n"

/-! ## Source: CommAlg.ProjectiveDimension.RankIdealUpper -/
section CheckedSource98

/-!
# Actual projective dimension: the upper bound from linear quotients

Finite induction follows initial segments of the genuine reverse lexicographic
order. The quotient at each step is the actual quotient by its colon ideal.
-/

noncomputable section

namespace CommAlg.ProjectiveDimension

open Classical Finset CategoryTheory CategoryTheory.Limits CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem exists_revlex_greatest (C : Family V) (hC : C.Nonempty) :
    ∃ b ∈ C, ∀ a ∈ C, a = b ∨ RevlexBefore a b := by
  induction C using Finset.induction_on with
  | empty => simp at hC
  | @insert b C hb ih =>
    by_cases hne : C.Nonempty
    · obtain ⟨c, hc, hmax⟩ := ih hne
      by_cases hbc : b = c
      · refine ⟨c, mem_insert_of_mem hc, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inl hbc
        · exact hmax a ha
      rcases revlexBefore_total hbc with hbc | hcb
      · refine ⟨c, mem_insert_of_mem hc, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inr hbc
        · exact hmax a ha
      · refine ⟨b, mem_insert_self _ _, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inl rfl
        · rcases hmax a ha with rfl | hac
          · exact Or.inr hcb
          · exact Or.inr (revlexBefore_trans hac hcb)
    · have he := not_nonempty_iff_eq_empty.mp hne
      subst C
      exact ⟨b, by simp, fun a ha => Or.inl (by simpa using ha)⟩

theorem monomialIdeal_insert_generator (C : Family V) (b : Exponent V) :
    monomialIdeal k (insert b C) =
      CommAlg.generatorExtension (monomialIdeal k C) (MvPolynomial.monomial b 1) := by
  simp [monomialIdeal, CommAlg.generatorExtension,
    Ideal.span_insert, sup_comm]

/-- Every initial segment has projective dimension bounded by the final
partition-rank gap. The proof uses actual short exact module sequences. -/
theorem initialSegment_projectiveDimension_le (g : RankFunction V) (C : Family V)
    (hCB : C ⊆ rankBases g)
    (hdown : ∀ a ∈ C, ∀ b ∈ rankBases g, RevlexBefore b a → b ∈ C) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) (monomialIdeal k C)) ≤
      shiftLength g := by
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases hne : C.Nonempty
    · obtain ⟨b, hb, hmax⟩ := exists_revlex_greatest C hne
      let D := C.erase b
      have hDC : D ⊂ C := erase_ssubset hb
      have hDB : D ⊆ rankBases g := (erase_subset _ _).trans hCB
      have hDdown : ∀ a ∈ D, ∀ c ∈ rankBases g, RevlexBefore c a → c ∈ D := by
        intro a ha c hc hca
        obtain ⟨hab, haC⟩ := mem_erase.mp ha
        apply mem_erase.mpr
        refine ⟨?_, hdown a haC c hc hca⟩
        intro hcb
        subst c
        rcases hmax a haC with he | habefore
        · exact hab he
        · exact revlexBefore_asymm habefore hca
      have hDpd := ih D hDC hDB hDdown
      have hDeq : D = revlexBeforeFamily (rankBases g) b := by
        ext a
        constructor
        · intro ha
          obtain ⟨hab, haC⟩ := mem_erase.mp ha
          refine (mem_revlexBeforeFamily _ _ _).mpr ⟨hCB haC, ?_⟩
          exact (hmax a haC).resolve_left hab
        · intro ha
          obtain ⟨haB, hab⟩ := (mem_revlexBeforeFamily _ _ _).mp ha
          apply mem_erase.mpr
          refine ⟨?_, hdown b hb a haB hab⟩
          intro he
          subst a
          exact revlexBefore_irrefl b hab
      have hcolon : (monomialIdeal k D).colon {MvPolynomial.monomial b 1} =
          variableIdeal (k := k) (revlexColonVariables (rankBases g) b) := by
        rw [hDeq]
        exact rankBases_revlex_colon_eq g (hCB hb)
      have hquot : projectiveDimension
          (ModuleCat.of (MvPolynomial V k)
            (MvPolynomial V k ⧸ (monomialIdeal k D).colon {MvPolynomial.monomial b 1})) ≤
          shiftLength g := by
        rw [hcolon]
        exact (variableIdeal_quotient_le _).trans
          (by exact_mod_cast revlexColonVariables_card_le_shiftLength g (hCB hb))
      have he : monomialIdeal k C =
          CommAlg.generatorExtension (monomialIdeal k D) (MvPolynomial.monomial b 1) := by
        have hIns : insert b D = C := insert_erase hb
        calc
          monomialIdeal k C = monomialIdeal k (insert b D) :=
            congrArg (monomialIdeal k) hIns.symm
          _ = _ := monomialIdeal_insert_generator D b
      rw [he]
      exact (CommAlg.generatorExtension_projectiveDimension_le _ _).trans (sup_le hDpd hquot)
    · have he : C = ∅ := not_nonempty_iff_eq_empty.mp hne
      subst C
      have he0 : monomialIdeal k (∅ : Family V) = ⊥ := by simp [monomialIdeal]
      haveI : Subsingleton (monomialIdeal k (∅ : Family V)) := by
        rw [he0]
        infer_instance
      have hz : IsZero (ModuleCat.of (MvPolynomial V k) (monomialIdeal k (∅ : Family V))) :=
        ModuleCat.isZero_iff_subsingleton.mpr inferInstance
      rw [(projectiveDimension_eq_bot_iff _).mpr hz]
      exact bot_le

/-- The actual Ext-defined projective dimension of every polymatroid rank
ideal is at most the universal partition-rank gap, including loops and rank zero. -/
theorem rankIdeal_projectiveDimension_le (g : RankFunction V) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) (rankIdeal k g)) ≤
      shiftLength g :=
  initialSegment_projectiveDimension_le g (rankBases g) le_rfl
    (fun _ _ _ hb _ => hb)

end CommAlg.ProjectiveDimension

end
end CheckedSource98

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "99: CommAlg.KoszulComplex.CoefficientProjectiveDimension\n"

/-! ## Source: CommAlg.KoszulComplex.CoefficientProjectiveDimension -/
section CheckedSource99

/-! # Genuine projective-dimension detection by coefficient Koszul homology

This proves the needed vanishing theorem directly from a projective presentation and
its homology long exact sequence. No balance theorem for `Tor` and `Tor'` is assumed.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

/-- Tensor a fixed chain complex with a variable coefficient module. -/
def tensorCoefficientFunctor (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} R) ℕ where
  obj M := (((tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj K
  map f := (((tensoringRight (ModuleCat R)).map f).mapHomologicalComplex
    (ComplexShape.down ℕ)).app K
  map_id M := by simp
  map_comp f g := by simp

instance tensorCoefficientFunctor_preservesZero (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (tensorCoefficientFunctor K).PreservesZeroMorphisms where
  map_zero X Y := by
    apply HomologicalComplex.Hom.ext
    funext i
    change (tensorLeft (K.X i)).map (0 : X ⟶ Y) = 0
    exact Functor.map_zero _ _ _

/-- Flat chain groups preserve short exact coefficient sequences degree by degree. -/
lemma tensorCoefficient_shortExact (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) : (S.map (tensorCoefficientFunctor K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  letI : Module.Flat R (K.X i) := hflat i
  change (S.map (tensorLeft (K.X i))).ShortExact
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  refine ShortComplex.ShortExact.mk'
    (Module.Flat.lTensor_shortComplex_exact (K.X i) S hS.exact) ?_ ?_
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := K.X i) S.f.hom
      ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.lTensor_surjective (K.X i)
      ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

/-- Tensoring an exact positive-degree complex with a projective coefficient module preserves exactness. -/
lemma tensorCoefficient_isZero_of_projective
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (hexact : ∀ i, K.ExactAt (i + 1))
    (M : ModuleCat.{u} R) [Projective M] (i : ℕ) :
    IsZero (((tensorCoefficientFunctor K).obj M).homology (i + 1)) := by
  letI : Module.Flat R M := inferInstance
  apply HomologicalComplex.ExactAt.isZero_homology
  change ((K.sc (i + 1)).map (tensorRight M)).Exact
  exact Module.Flat.rTensor_shortComplex_exact M (K.sc (i + 1)) (hexact i)

/-- If the actual projective dimension is below `n`, coefficient homology vanishes in degree `n`.
The induction uses actual projective presentations and actual homology connecting maps. -/
lemma tensorCoefficient_isZero_of_hasProjectiveDimensionLT
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (hexact : ∀ i, K.ExactAt (i + 1))
    (n : ℕ) (M : ModuleCat.{u} R) (hM : HasProjectiveDimensionLT M n) :
    IsZero (((tensorCoefficientFunctor K).obj M).homology n) := by
  induction n generalizing M with
  | zero =>
      have hz : IsZero M := (hasProjectiveDimensionLT_zero_iff_isZero M).mp hM
      exact (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 0).map_isZero
        ((tensorCoefficientFunctor K).map_isZero hz)
  | succ n ih =>
      cases n with
      | zero =>
          letI : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
          exact tensorCoefficient_isZero_of_projective K hexact M 0
      | succ n =>
          let ⟨p⟩ := EnoughProjectives.presentation M
          let S := ShortComplex.mk (kernel.ι p.f) p.f (kernel.condition p.f)
          have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p.f }
          have hKer : HasProjectiveDimensionLT S.X₁ (n + 1) :=
            (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hM
          have hleft := tensorCoefficient_isZero_of_projective K hexact S.X₂ (n + 1)
          have hright := ih S.X₁ hKer
          have ht := tensorCoefficient_shortExact K hflat S hS
          have he := ht.homology_exact₃ (n + 2) (n + 1) (by rfl)
          exact he.isZero_X₂ (hleft.eq_of_src _ _) (hright.eq_of_tgt _ _)

/-- Nonzero coefficient homology supplies a lower bound for Mathlib's actual projective dimension. -/
lemma tensorCoefficient_nonzero_le_projectiveDimension
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hflat : ∀ i, Module.Flat R (K.X i)) (hexact : ∀ i, K.ExactAt (i + 1))
    (M : ModuleCat.{u} R) (n : ℕ)
    (h : ¬ IsZero (((tensorCoefficientFunctor K).obj M).homology n)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  rw [projectiveDimension_ge_iff]
  exact fun hM => h (tensorCoefficient_isZero_of_hasProjectiveDimensionLT K hflat hexact n M hM)

variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- Genuine coefficient Koszul homology cannot occur above the actual projective dimension. -/
lemma familyCoefficient_nonzero_le_projectiveDimension
    (M : ModuleCat.{u} (MvPolynomial V k)) (n : ℕ)
    (h : ¬ IsZero ((familyCoefficientComplex (MvPolynomial.X : V → MvPolynomial V k) M).homology n)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  apply tensorCoefficient_nonzero_le_projectiveDimension
    (koszulComplex (Fintype.linearCombination (MvPolynomial V k) MvPolynomial.X))
    (fun i => by
      change Module.Flat (MvPolynomial V k) (⋀[MvPolynomial V k]^i (V → MvPolynomial V k))
      infer_instance) ?_ M n h
  intro i
  exact (koszulComplex.exactAt_of_isRegular
    (finiteVariableList (V := V) (k := k)) finite_variables_regular (i + 1) (by omega)).of_iso
    finiteVariableKoszulIso

/-- The same bound for Mathlib's actual first-factor derived Tor module. -/
lemma finitePolynomialTor_nonzero_le_projectiveDimension
    (M : ModuleCat.{u} (MvPolynomial V k)) (n : ℕ)
    (h : ¬ IsZero (finitePolynomialTor n M)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension M := by
  apply familyCoefficient_nonzero_le_projectiveDimension M n
  exact fun hz => h ((finitePolynomialTorIso n M).isZero_iff.mpr hz)

end CommAlg.Koszul

end
end CheckedSource99

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "100: CommAlg.ProjectiveDimension.RankIdeal\n"

/-! ## Source: CommAlg.ProjectiveDimension.RankIdeal -/
section CheckedSource100

/-!
# The actual projective dimension of a polymatroidal ideal

The upper bound is obtained from actual linear-quotient exact sequences.
The lower bound uses a nonzero multigraded component of Mathlib's derived
tensor functor and the proved coefficient-complex dimension-shift theorem.
Neither projective dimension nor Tor nonvanishing is defined by the rank formula.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rankShiftFamily_nonempty_iff_le_shiftLength (g : RankFunction V) (i : ℕ) :
    (rankShiftFamily g i).Nonempty ↔ i ≤ shiftLength g := by
  rw [rankShiftFamily_nonempty_iff]
  have hd := shiftLength_add_degree g
  by_cases hE : (univ : Finset V).Nonempty
  · rw [universalHomologicalRank_apply g i hE]
    omega
  · have he : (univ : Finset V) = ∅ := not_nonempty_iff_eq_empty.mp hE
    simp only [he, RankFunction.map_empty] at hd ⊢
    omega

theorem top_rankShiftFamily_nonempty (g : RankFunction V) :
    (rankShiftFamily g (shiftLength g)).Nonempty :=
  (rankShiftFamily_nonempty_iff_le_shiftLength g _).mpr le_rfl

end CommAlg.Polymatroid

namespace CommAlg.ProjectiveDimension

open Classical Finset CategoryTheory CategoryTheory.Limits CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The exact categorical projective dimension, including the unit ideal and loops. -/
theorem rankIdeal_projectiveDimension (g : RankFunction V) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) (rankIdeal k g)) =
      (shiftLength g : WithBot ℕ∞) := by
  apply le_antisymm (rankIdeal_projectiveDimension_le g)
  obtain ⟨a, ha⟩ := top_rankShiftFamily_nonempty g
  have hβ := (gradedBettiNonzero_rankBases_iff (k := k) g a (shiftLength g)).mpr ha
  exact Koszul.finitePolynomialTor_nonzero_le_projectiveDimension _ _
    (Koszul.derivedTor_nonzero_of_graded _ _ _ hβ)

/-- The same statement for an actual polynomial ideal with its proved rank presentation. -/
theorem polymatroidalIdeal_projectiveDimension (I : Ideal (MvPolynomial V k))
    (g : RankFunction V) (hI : I = rankIdeal k g) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) I) =
      (shiftLength g : WithBot ℕ∞) := by
  subst I
  exact rankIdeal_projectiveDimension g

end CommAlg.ProjectiveDimension

end
end CheckedSource100

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "101: CommAlg.ProjectiveDimension.PowerFormula\n"

/-! ## Source: CommAlg.ProjectiveDimension.PowerFormula -/
section CheckedSource101

/-! # Corollary 4.3: exact projective dimensions of powers

The left-hand side is Mathlib's categorical projective dimension of the
actual polynomial ideal. The minimum ranges over every set partition.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem shiftLength_active_defect (g : RankFunction V) (hg : g.Active) :
    shiftLength g =
      finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        partitionDefect g P + partitionSlack P) := by
  have h := shiftLength_add_degree g
  rw [universalAugmentedRank_eq_active g hg,
    augmentedPartitionRank_defect g hg] at h
  omega

theorem shiftLength_scale_partition (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : 1 ≤ s) :
    shiftLength (ρ.scale s) =
      finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) := by
  rw [shiftLength_active_defect _ (hρ.scale hs)]
  simp only [partitionDefect_scale]

theorem partitionMinimum_eq_eventual (ρ : RankFunction V) (s : ℕ)
    (hs : eventualOffset ρ (univ : Finset V) ≤ s) :
    finiteMinimum (fun P : Finpartition (univ : Finset V) =>
      s * partitionDefect ρ P + partitionSlack P) = eventualOffset ρ univ := by
  apply le_antisymm
  · obtain ⟨P, hd, hb⟩ := eventualOffset_attained ρ (univ : Finset V)
    simpa only [hd, hb, Nat.mul_zero, Nat.zero_add] using
      finiteMinimum_le (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) P
  · apply le_finiteMinimum
    intro P
    by_cases hd : partitionDefect ρ P = 0
    · exact (eventualOffset_le_slack ρ P hd).trans (Nat.le_add_left _ _)
    · have hpos : 1 ≤ partitionDefect ρ P := by omega
      nlinarith

theorem shiftLength_scale_eventual (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    shiftLength (ρ.scale s) = eventualOffset ρ univ := by
  rw [shiftLength_scale_partition ρ hρ s ((le_max_left _ _).trans hs)]
  exact partitionMinimum_eq_eventual ρ s ((le_max_right _ _).trans hs)

end CommAlg.Polymatroid

namespace CommAlg.ProjectiveDimension

open Classical Finset CategoryTheory CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Formula (4.3), with no additional restriction on the number of variables or powers. -/
theorem rankIdeal_power_projectiveDimension (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : 1 ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥((rankIdeal k ρ) ^ s)) =
      (finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) : WithBot ℕ∞) := by
  rw [← rankIdeal_scale, rankIdeal_projectiveDimension,
    shiftLength_scale_partition ρ hρ s hs]

/-- The eventual projective dimension is attained by the paper's stated uniform bound. -/
theorem rankIdeal_power_projectiveDimension_eventual (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥((rankIdeal k ρ) ^ s)) =
      (eventualOffset ρ univ : WithBot ℕ∞) := by
  rw [← rankIdeal_scale, rankIdeal_projectiveDimension,
    shiftLength_scale_eventual ρ hρ s hs]

/-- Literal ideal form of Corollary 4.3 for any proved rank presentation. -/
theorem polymatroidal_power_projectiveDimension (I : Ideal (MvPolynomial V k))
    (ρ : RankFunction V) (hI : I = rankIdeal k ρ) (hρ : ρ.Active)
    (s : ℕ) (hs : 1 ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥(I ^ s)) =
      (finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) : WithBot ℕ∞) := by
  subst I
  exact rankIdeal_power_projectiveDimension ρ hρ s hs

theorem polymatroidal_power_projectiveDimension_eventual (I : Ideal (MvPolynomial V k))
    (ρ : RankFunction V) (hI : I = rankIdeal k ρ) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) ↥(I ^ s)) =
      (eventualOffset ρ univ : WithBot ℕ∞) := by
  subst I
  exact rankIdeal_power_projectiveDimension_eventual ρ hρ s hs

end CommAlg.ProjectiveDimension

end
end CheckedSource101

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "102: CommAlg.Polymatroid.PowerShiftGenerators\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftGenerators -/
section CheckedSource102

/-! # Exact degrees of the minimal monomial generators of the actual Rees ideal -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

theorem exists_monomial_generator_notMem_iff (B : Family V)
    (J : Ideal (MvPolynomial V k)) (hJ : J ≤ monomialIdeal k B) :
    (∃ a ∈ B, MvPolynomial.monomial a (1 : k) ∉ J) ↔ J ≠ monomialIdeal k B := by
  constructor
  · rintro ⟨a, ha, hn⟩ he
    apply hn
    rw [he]
    exact Ideal.subset_span ⟨a, ha, rfl⟩
  · intro h
    by_contra hn
    push_neg at hn
    apply h
    apply le_antisymm hJ
    apply Ideal.span_le.mpr
    rintro f ⟨a, ha, rfl⟩
    exact hn a ha

theorem preceding_powerShift_product_le (ρ : RankFunction V) (i : ℕ)
    {s : ℕ} (hs : 0 < s) :
    rankIdeal k ρ * powerShiftPiece ρ i (s - 1) ≤ powerShiftPiece ρ i s := by
  have h := powerShiftPiece_action (k := k) ρ i 1 (s - 1)
  simpa only [pow_one, Nat.add_sub_of_le hs] using h

theorem exists_minimalShiftRees_iff (ρ : RankFunction V) (i : ℕ)
    {s : ℕ} (hs : 0 < s) :
    (∃ a, IsMinimalShiftReesMonomial (k := k) ρ i s a) ↔
      rankIdeal k ρ * powerShiftPiece ρ i (s - 1) ≠ powerShiftPiece ρ i s := by
  simp_rw [minimalShiftRees_iff ρ i hs]
  have he : powerShiftPiece (k := k) ρ i s =
      monomialIdeal k (rankShiftFamily (RankFunction.scale s ρ) i) := by
    rw [powerShiftPiece_pos ρ i hs, rankShiftIdeal_eq_monomialIdeal]
  rw [he]
  exact exists_monomial_generator_notMem_iff _ _
    (he ▸ preceding_powerShift_product_le ρ i hs)

theorem powerShiftPiece_eq_bot_before (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : i ≤ eventualOffset ρ univ) {s : ℕ}
    (hs : s < powerThreshold ρ i univ) : powerShiftPiece (k := k) ρ i s = ⊥ := by
  by_cases hs0 : s = 0
  · simp [hs0]
  · rw [powerShiftPiece_pos ρ i (by omega)]
    by_contra hn
    have hr := (powerShiftIdeal_ne_bot_iff_threshold ρ hρ i hi (by omega)).mp hn
    omega

theorem powerShiftPiece_ne_bot_at (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) :
    powerShiftPiece (k := k) ρ i (powerThreshold ρ i univ) ≠ ⊥ := by
  have hr := powerThreshold_pos ρ hi0 hi
  rw [powerShiftPiece_pos ρ i hr]
  exact (powerShiftIdeal_ne_bot_iff_threshold ρ hρ i hi hr).mpr le_rfl

/-- Theorem 4.4's exact interval, for semantic minimal monomials of the genuine
Rees ideal. Every degree in the interval occurs and every other degree is absent. -/
theorem minimalShiftRees_degree_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (s : ℕ) :
    (∃ a, IsMinimalShiftReesMonomial (k := k) ρ i s a) ↔
      powerThreshold ρ i univ ≤ s ∧ s ≤ globalPowerThreshold ρ i := by
  have hr : 1 ≤ powerThreshold ρ i univ := powerThreshold_pos ρ hi0 hi
  have hrS := powerThreshold_le_global ρ i univ
  by_cases hs0 : s = 0
  · subst s
    constructor
    · rintro ⟨a, ha⟩
      have hp := minimalShiftRees_positive ha
      omega
    · omega
  have hs : 0 < s := by omega
  rw [exists_minimalShiftRees_iff ρ i hs]
  by_cases hsr : s < powerThreshold ρ i univ
  · have hz := powerShiftPiece_eq_bot_before (k := k) ρ hρ i hi hsr
    have hp : rankIdeal k ρ * powerShiftPiece ρ i (s - 1) = ⊥ := by
      apply le_antisymm _ bot_le
      exact hz ▸ preceding_powerShift_product_le ρ i hs
    rw [hz, hp]
    constructor
    · intro h
      exact (h rfl).elim
    · intro h
      omega
  by_cases hsrEq : s = powerThreshold ρ i univ
  · have hp : powerShiftPiece (k := k) ρ i (s - 1) = ⊥ :=
      powerShiftPiece_eq_bot_before ρ hρ i hi (by omega)
    have hn : powerShiftPiece (k := k) ρ i s ≠ ⊥ := by
      rw [hsrEq]
      exact powerShiftPiece_ne_bot_at ρ hρ i hi0 hi
    rw [hp, Ideal.mul_bot]
    constructor
    · intro _
      omega
    · intro _ he
      exact hn he.symm
  have hprev : 1 ≤ s - 1 := by omega
  have hprevr : powerThreshold ρ i univ ≤ s - 1 := by omega
  have he := powerShiftIdeal_mul_eq_iff (k := k) ρ hρ i hi hprev hprevr
  rw [powerShiftPiece_pos ρ i hprev, powerShiftPiece_pos ρ i hs]
  have hsucc : s - 1 + 1 = s := by omega
  rw [hsucc] at he
  simp only [ne_eq, he]
  omega

theorem powerShiftPiece_eq_bot_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) (s : ℕ) :
    powerShiftPiece (k := k) ρ i s = ⊥ := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [powerShiftPiece_pos ρ i (by omega)]
    exact powerShiftIdeal_eq_bot_of_above ρ hρ i hi (by omega)

/-- Above the eventual projective-dimension offset the entire actual Rees
ideal, and therefore its graded module, is zero. -/
theorem shiftReesIdeal_eq_bot_of_above (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) : shiftReesIdeal (k := k) ρ i = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply Subtype.ext
  apply Polynomial.ext
  intro s
  have h := hp s
  rw [powerShiftPiece_eq_bot_of_above ρ hρ i hi s] at h
  simpa using h

/-- The endpoints satisfy all of the quantitative bounds in Theorem 4.4. -/
theorem powerShift_generator_endpoints (ρ : RankFunction V) (i : ℕ)
    (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) :
    1 ≤ powerThreshold ρ i univ ∧
      powerThreshold ρ i univ ≤ globalPowerThreshold ρ i ∧
      globalPowerThreshold ρ i ≤ i :=
  ⟨powerThreshold_pos ρ hi0 hi, powerThreshold_le_global ρ i univ,
    globalPowerThreshold_le ρ i⟩

end CommAlg.Polymatroid

end
end CheckedSource102

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "103: CommAlg.Polymatroid.PowerShiftSpanning\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftSpanning -/
section CheckedSource103

/-! # Minimal Rees monomials really generate the coefficientwise ideal -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

def minimalShiftReesSet (ρ : RankFunction V) (i : ℕ) : Set (reesAlgebra (rankIdeal k ρ)) :=
  {p | ∃ s a, ∃ h : IsMinimalShiftReesMonomial (k := k) ρ i s a,
    p = shiftReesMonomial ρ i s a h.1}

theorem shiftReesMonomial_mem_span_minimal (ρ : RankFunction V) (i s : ℕ)
    (a : Exponent V) (ha : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s) :
    shiftReesMonomial ρ i s a ha ∈ Ideal.span (minimalShiftReesSet ρ i) := by
  generalize hn : s + a.degree = n
  induction n using Nat.strong_induction_on generalizing s a with
  | h n ih =>
    by_cases hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a
    · exact Ideal.subset_span ⟨s, a, hmin, rfl⟩
    · have hnmin : ¬ ∀ r b, r ≤ s → b ≤ a →
          MvPolynomial.monomial b (1 : k) ∈ powerShiftPiece ρ i r →
          MvPolynomial.monomial (a - b) (1 : k) ∈ (rankIdeal k ρ) ^ (s - r) →
          r = s ∧ b = a := fun h => hmin ⟨ha, h⟩
      push_neg at hnmin
      obtain ⟨r, b, hrs, hba, hb, hf, hne⟩ := hnmin
      have hd := degree_mono hba
      have hmeasure : r + b.degree < n := by
        by_contra hbad
        have heR : r = s := by omega
        have heD : b.degree = a.degree := by omega
        exact hne heR (eq_of_le_of_degree_eq hba heD)
      have hbSpan := ih (r + b.degree) hmeasure r b hb rfl
      let q : reesAlgebra (rankIdeal k ρ) :=
        ⟨Polynomial.monomial (s - r) (MvPolynomial.monomial (a - b) 1),
          reesAlgebra.monomial_mem.mpr hf⟩
      have he : q * shiftReesMonomial ρ i r b hb = shiftReesMonomial ρ i s a ha := by
        apply Subtype.ext
        exact rees_monomial_factorization hrs hba
      rw [← he]
      exact Ideal.mul_mem_left _ q hbSpan

def liftReesCoefficient (ρ : RankFunction V) (s : ℕ) (f : MvPolynomial V k)
    (hf : f ∈ (rankIdeal k ρ) ^ s) : reesAlgebra (rankIdeal k ρ) :=
  ⟨Polynomial.monomial s f, reesAlgebra.monomial_mem.mpr hf⟩

theorem liftReesCoefficient_mem_of_bases (ρ : RankFunction V) (i : ℕ)
    {s : ℕ} (hs : 0 < s) (J : Ideal (reesAlgebra (rankIdeal k ρ)))
    (hgen : ∀ a ∈ rankShiftFamily (RankFunction.scale s ρ) i,
      ∀ ha : MvPolynomial.monomial a (1 : k) ∈ (rankIdeal k ρ) ^ s,
        liftReesCoefficient ρ s (MvPolynomial.monomial a 1) ha ∈ J)
    (f : MvPolynomial V k) (hf : f ∈ powerShiftPiece ρ i s)
    (hfPow : f ∈ (rankIdeal k ρ) ^ s) : liftReesCoefficient ρ s f hfPow ∈ J := by
  have hpiece : powerShiftPiece (k := k) ρ i s =
      monomialIdeal k (rankShiftFamily (RankFunction.scale s ρ) i) := by
    rw [powerShiftPiece_pos ρ i hs, rankShiftIdeal_eq_monomialIdeal]
  have hbound : monomialIdeal k (rankShiftFamily (RankFunction.scale s ρ) i) ≤
      (rankIdeal k ρ) ^ s := hpiece ▸ powerShiftPiece_le_pow ρ i s
  rw [hpiece] at hf
  suffices h : ∀ f, f ∈ monomialIdeal k (rankShiftFamily (RankFunction.scale s ρ) i) →
      ∀ hfPow, liftReesCoefficient ρ s f hfPow ∈ J from h f hf hfPow
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, rfl⟩ := hf
    exact hgen a ha
  | zero =>
    intro hzero
    have he : liftReesCoefficient ρ s 0 hzero = 0 := by
      apply Subtype.ext
      simp [liftReesCoefficient]
    simpa only [he] using J.zero_mem
  | add x y hx hy ihx ihy =>
    intro hxy
    have he : liftReesCoefficient ρ s (x + y) hxy =
        liftReesCoefficient ρ s x (hbound hx) + liftReesCoefficient ρ s y (hbound hy) := by
      apply Subtype.ext
      simp [liftReesCoefficient]
    rw [he]
    exact J.add_mem (ihx _) (ihy _)
  | smul r x hx ih =>
    intro hrx
    have he : liftReesCoefficient ρ s (r • x) hrx =
        algebraMap (MvPolynomial V k) (reesAlgebra (rankIdeal k ρ)) r *
          liftReesCoefficient ρ s x (hbound hx) := by
      apply Subtype.ext
      change Polynomial.monomial s (r * x) = Polynomial.C r * Polynomial.monomial s x
      rw [Polynomial.C_mul_monomial]
    rw [he]
    exact J.mul_mem_left _ (ih _)

/-- Every polynomial element of the Rees ideal is generated by its genuine
minimal monomials. This proves actual module generation, in addition to the
combinatorial degree characterization. -/
theorem shiftReesIdeal_eq_span_minimal (ρ : RankFunction V) (i : ℕ) :
    shiftReesIdeal (k := k) ρ i = Ideal.span (minimalShiftReesSet ρ i) := by
  apply le_antisymm
  · intro p hp
    rw [reesAlgebra.as_sum_support p]
    apply Ideal.sum_mem
    intro s hs
    change liftReesCoefficient ρ s (p.val.coeff s) (p.property s) ∈ _
    by_cases hs0 : s = 0
    · have hz := hp s
      rw [hs0, powerShiftPiece_zero] at hz
      have hf0 : p.val.coeff 0 = 0 := hz
      have he : liftReesCoefficient ρ s (p.val.coeff s) (p.property s) = 0 := by
        apply Subtype.ext
        simp [liftReesCoefficient, hs0, hf0]
      rw [he]
      exact Ideal.zero_mem _
    · apply liftReesCoefficient_mem_of_bases ρ i (by omega) _ _ _ (hp s)
      intro a ha haPow
      have hmem : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s := by
        rw [powerShiftPiece_pos ρ i (by omega), rankShiftIdeal_eq_monomialIdeal,
          monomial_mem_iff]
        exact ⟨a, ha, le_rfl⟩
      exact shiftReesMonomial_mem_span_minimal ρ i s a hmem
  · apply Ideal.span_le.mpr
    rintro p ⟨s, a, ha, rfl⟩
    exact shiftReesMonomial_mem ρ i s a ha.1

def boundedShiftReesSet (ρ : RankFunction V) (i q : ℕ) : Set (reesAlgebra (rankIdeal k ρ)) :=
  {p | ∃ s a, ∃ ha : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s,
    s ≤ q ∧ p = shiftReesMonomial ρ i s a ha}

/-- The exact endpoint is an actual generation bound in the Rees algebra. -/
theorem shiftReesIdeal_generated_at_threshold (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) :
    shiftReesIdeal (k := k) ρ i =
      Ideal.span (boundedShiftReesSet ρ i (globalPowerThreshold ρ i)) := by
  apply le_antisymm
  · rw [shiftReesIdeal_eq_span_minimal]
    apply Ideal.span_mono
    rintro p ⟨s, a, ha, rfl⟩
    have hs := ((minimalShiftRees_degree_iff ρ hρ i hi0 hi s).mp ⟨a, ha⟩).2
    exact ⟨s, a, ha.1, hs, rfl⟩
  · apply Ideal.span_le.mpr
    rintro p ⟨s, a, ha, _, rfl⟩
    exact shiftReesMonomial_mem ρ i s a ha

end CommAlg.Polymatroid

end
end CheckedSource103

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "104: CommAlg.Polymatroid.PowerShiftLeastGeneration\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftLeastGeneration -/
section CheckedSource104

/-!
# The exact threshold is the least actual Rees generation bound

A coefficient of a minimal module monomial cannot be created by multiplying
module elements in which that coefficient is zero. This gives an intrinsic
obstruction to generation in any smaller Rees degrees.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

theorem monomial_mem_powerShiftPiece_of_coeff (ρ : RankFunction V) (i s : ℕ)
    {f : MvPolynomial V k} (hf : f ∈ powerShiftPiece ρ i s) {a : Exponent V}
    (ha : f.coeff a ≠ 0) : MvPolynomial.monomial a (1 : k) ∈ powerShiftPiece ρ i s := by
  by_cases hs : s = 0
  · simp only [hs, powerShiftPiece_zero, Submodule.mem_bot] at hf
    simp [hf] at ha
  · rw [powerShiftPiece_pos ρ i (by omega)] at hf ⊢
    exact (mem_rankShiftIdeal_iff_coeff _ _ f).mp hf a (MvPolynomial.mem_support_iff.mpr ha)

theorem monomial_mem_rankIdeal_power_of_coeff (ρ : RankFunction V) (s : ℕ)
    {f : MvPolynomial V k} (hf : f ∈ (rankIdeal k ρ) ^ s) {a : Exponent V}
    (ha : f.coeff a ≠ 0) : MvPolynomial.monomial a (1 : k) ∈ (rankIdeal k ρ) ^ s := by
  rw [← rankIdeal_scale] at hf ⊢
  exact (monomial_mem_iff (rankBases (RankFunction.scale s ρ)) a).mpr
    ((mem_monomialIdeal_iff _ f).mp hf a (MvPolynomial.mem_support_iff.mpr ha))

def reesCoefficient (ρ : RankFunction V) (s : ℕ) (a : Exponent V)
    (p : reesAlgebra (rankIdeal k ρ)) : k := (p.val.coeff s).coeff a

@[simp] theorem reesCoefficient_zero (ρ : RankFunction V) (s : ℕ) (a : Exponent V) :
    reesCoefficient (k := k) ρ s a 0 = 0 := by simp [reesCoefficient]

@[simp] theorem reesCoefficient_add (ρ : RankFunction V) (s : ℕ) (a : Exponent V)
    (p q : reesAlgebra (rankIdeal k ρ)) :
    reesCoefficient ρ s a (p + q) = reesCoefficient ρ s a p + reesCoefficient ρ s a q := by
  simp [reesCoefficient]

theorem minimalShiftRees_coefficient_mul_zero (ρ : RankFunction V) (i s : ℕ)
    (a : Exponent V) (hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a)
    (p : reesAlgebra (rankIdeal k ρ)) (hp : p ∈ shiftReesIdeal ρ i)
    (hz : reesCoefficient ρ s a p = 0) (r : reesAlgebra (rankIdeal k ρ)) :
    reesCoefficient ρ s a (r * p) = 0 := by
  change ((r.val * p.val).coeff s).coeff a = 0
  rw [Polynomial.coeff_mul, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  rintro ⟨n, t⟩ hnt
  have hntEq : n + t = s := mem_antidiagonal.mp hnt
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨c, b⟩ hcb
  have hcbEq : c + b = a := mem_antidiagonal.mp hcb
  by_cases hr : (r.val.coeff n).coeff c = 0
  · simp [hr]
  by_cases hpb : (p.val.coeff t).coeff b = 0
  · simp [hpb]
  have hrMon := monomial_mem_rankIdeal_power_of_coeff ρ n (r.property n) hr
  have hpMon := monomial_mem_powerShiftPiece_of_coeff ρ i t (hp t) hpb
  have hba : b ≤ a := hcbEq ▸ le_add_left le_rfl
  have hquot : MvPolynomial.monomial (a - b) (1 : k) ∈ (rankIdeal k ρ) ^ (s - t) := by
    have haSub : a - b = c := by rw [← hcbEq, add_tsub_cancel_right]
    rw [haSub, show s - t = n by omega]
    exact hrMon
  obtain ⟨ht, hb⟩ := hmin.2 t b (by omega) hba hpMon hquot
  subst t
  subst b
  exact (hpb hz).elim

theorem coefficient_zero_on_span_bounded (ρ : RankFunction V) (i s q : ℕ)
    (a : Exponent V) (hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a)
    (hqs : q < s) (p : reesAlgebra (rankIdeal k ρ))
    (hp : p ∈ Ideal.span (boundedShiftReesSet ρ i q)) :
    reesCoefficient ρ s a p = 0 := by
  have h : p ∈ shiftReesIdeal ρ i ∧ reesCoefficient ρ s a p = 0 := by
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨t, b, hb, ht, rfl⟩ := hp
      refine ⟨shiftReesMonomial_mem ρ i t b hb, ?_⟩
      have hst : s ≠ t := by omega
      simp [reesCoefficient, shiftReesMonomial, Polynomial.coeff_monomial, hst, Ne.symm hst]
    | zero => exact ⟨Ideal.zero_mem _, by simp⟩
    | add p r hp hr ihp ihr =>
      exact ⟨Ideal.add_mem _ ihp.1 ihr.1, by simp [ihp.2, ihr.2]⟩
    | smul r p hp ih =>
      exact ⟨Ideal.mul_mem_left _ r ih.1,
        minimalShiftRees_coefficient_mul_zero ρ i s a hmin p ih.1 ih.2 r⟩
  exact h.2

/-- No lower-degree monomial generating set can generate a minimal monomial
in a larger Rees degree. The obstruction is a literal polynomial coefficient. -/
theorem minimalShiftRees_notMem_span_bounded (ρ : RankFunction V) (i s q : ℕ)
    (a : Exponent V) (hmin : IsMinimalShiftReesMonomial (k := k) ρ i s a)
    (hqs : q < s) :
    shiftReesMonomial ρ i s a hmin.1 ∉ Ideal.span (boundedShiftReesSet ρ i q) := by
  intro hp
  have hz := coefficient_zero_on_span_bounded ρ i s q a hmin hqs _ hp
  simpa [reesCoefficient, shiftReesMonomial] using hz

/-- Theorem 4.4's exact least generation bound, stated as equality with an
actual ideal span in the ordinary Rees algebra. -/
theorem shiftReesIdeal_generation_bound_iff (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (q : ℕ) :
    shiftReesIdeal (k := k) ρ i = Ideal.span (boundedShiftReesSet ρ i q) ↔
      globalPowerThreshold ρ i ≤ q := by
  constructor
  · intro he
    by_contra hq
    have hq' : q < globalPowerThreshold ρ i := by omega
    obtain ⟨a, ha⟩ := (minimalShiftRees_degree_iff (k := k) ρ hρ i hi0 hi
      (globalPowerThreshold ρ i)).mpr ⟨powerThreshold_le_global ρ i univ, le_rfl⟩
    have hp := shiftReesMonomial_mem ρ i (globalPowerThreshold ρ i) a ha.1
    rw [he] at hp
    exact minimalShiftRees_notMem_span_bounded ρ i _ q a ha hq' hp
  · intro hq
    apply le_antisymm
    · rw [shiftReesIdeal_generated_at_threshold ρ hρ i hi0 hi]
      apply Ideal.span_mono
      rintro p ⟨s, a, ha, hs, rfl⟩
      exact ⟨s, a, ha, hs.trans hq, rfl⟩
    · apply Ideal.span_le.mpr
      rintro p ⟨s, a, ha, _, rfl⟩
      exact shiftReesMonomial_mem ρ i s a ha

end CommAlg.Polymatroid

end
end CheckedSource104

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "105: CommAlg.Polymatroid.PowerShiftNewGenerators\n"

/-! ## Source: CommAlg.Polymatroid.PowerShiftNewGenerators -/
section CheckedSource105

/-! # The explicit inequalities selecting new minimal Rees generators -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V k : Type*} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

/-- The post-Theorem-4.4 criterion identifies each individual new generator,
not only the degrees in which generators exist. -/
theorem minimalShiftRees_iff_rank_violation (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (s : ℕ)
    (hrs : powerThreshold ρ i univ < s) (a : Exponent V)
    (ha : a ∈ rankShiftFamily (ρ.scale s) i) :
    IsMinimalShiftReesMonomial (k := k) ρ i s a ↔
      ∃ A : Finset V, A.Nonempty ∧
        s * ρ A + powerCorrection ρ i (s - 1) A < subsetSum a A := by
  have hr := powerThreshold_pos ρ hi0 hi
  have hs : 0 < s := by omega
  have hs1 : 1 ≤ s - 1 := by omega
  have hprev : (rankShiftFamily (ρ.scale (s - 1)) i).Nonempty :=
    (powerShiftFamily_nonempty_iff_threshold ρ hρ i hi hs1).mpr (by omega)
  have htotal := (rankShiftFamily_nonempty_iff _ _).mp hprev
  let g := ρ.add (universalHomologicalRank (ρ.scale (s - 1)) i)
  have hdeg : a.degree = g univ := by
    have haD := rankShiftFamily_equigenerated (ρ.scale s) i a ha
    change a.degree = ρ univ + universalHomologicalRank (ρ.scale (s - 1)) i univ
    rw [htotal]
    change a.degree = ρ univ + ((s - 1) * ρ univ + i)
    change a.degree = s * ρ univ + i at haD
    have hss : s - 1 + 1 = s := by omega
    nlinarith
  have hprod : rankIdeal k ρ * powerShiftPiece ρ i (s - 1) = rankIdeal k g := by
    rw [powerShiftPiece_pos ρ i hs1, rankShiftIdeal, if_pos htotal, ← rankIdeal_add]
  have hg (A : Finset V) : g A = s * ρ A + powerCorrection ρ i (s - 1) A := by
    change ρ A + universalHomologicalRank (ρ.scale (s - 1)) i A = _
    rw [power_homologicalRank ρ hρ i hs1]
    have hss : s - 1 + 1 = s := by omega
    nlinarith
  rw [minimalShiftRees_iff ρ i hs a, and_iff_right ha, hprod,
    monomial_mem_rankIdeal_iff, ← upperFeasible_iff_lowerFeasible g hdeg]
  change (¬ ∀ A, subsetSum a A ≤ g A) ↔ _
  constructor
  · intro hn
    obtain ⟨A, hA⟩ := not_forall.mp hn
    have hne : A.Nonempty := by
      by_contra h
      have he := not_nonempty_iff_eq_empty.mp h
      simp [he] at hA
    exact ⟨A, hne, by simpa [hg A] using Nat.lt_of_not_ge hA⟩
  · rintro ⟨A, _, hA⟩ hb
    have h := hb A
    rw [hg] at h
    omega

end CommAlg.Polymatroid

end
end CheckedSource105

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "106: CommAlg.Polymatroid.HomologicalInterval\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalInterval -/
section CheckedSource106

/-!
# Theorem 4.4 for genuine homological shifts in the ordinary Rees algebra

All module pieces below are the homological shifts defined by the nonzero
multigraded components of the actual derived tensor functor. Minimality means
minimality under divisibility by actual Rees monomials, including degree-zero
polynomial factors. Generation is an equality of actual ideal spans.
-/

noncomputable section

namespace CommAlg

open Classical Finset Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

def IsMinimalHomologicalPowerMonomial (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i s : ℕ) (a : Exponent V) : Prop :=
  MvPolynomial.monomial a (1 : k) ∈ homologicalPowerPiece I hI i s ∧
    ∀ r b, r ≤ s → b ≤ a →
      MvPolynomial.monomial b (1 : k) ∈ homologicalPowerPiece I hI i r →
      MvPolynomial.monomial (a - b) (1 : k) ∈ I ^ (s - r) →
      r = s ∧ b = a

/-- The actual module monomials through a specified Rees degree. -/
def boundedHomologicalPowerMonomials (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i q : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s a, MvPolynomial.monomial a (1 : k) ∈ homologicalPowerPiece I hI i s ∧
    s ≤ q ∧ p.val = Polynomial.monomial s (MvPolynomial.monomial a 1)}

def minimalHomologicalPowerMonomials (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) : Set (reesAlgebra I) :=
  {p | ∃ s a, IsMinimalHomologicalPowerMonomial I hI i s a ∧
    p.val = Polynomial.monomial s (MvPolynomial.monomial a 1)}

theorem isMinimalHomologicalPowerMonomial_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i s : ℕ) (a : Exponent V) :
    IsMinimalHomologicalPowerMonomial (rankIdeal k ρ) hI i s a ↔
      IsMinimalShiftReesMonomial (k := k) ρ i s a := by
  simp only [IsMinimalHomologicalPowerMonomial, IsMinimalShiftReesMonomial,
    homologicalPowerPiece_rank]

theorem boundedHomologicalPowerMonomials_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i q : ℕ) :
    boundedHomologicalPowerMonomials (rankIdeal k ρ) hI i q =
      boundedShiftReesSet (k := k) ρ i q := by
  ext p
  constructor
  · rintro ⟨s, a, ha, hs, he⟩
    rw [homologicalPowerPiece_rank] at ha
    exact ⟨s, a, ha, hs, Subtype.ext he⟩
  · rintro ⟨s, a, ha, hs, rfl⟩
    exact ⟨s, a, by simpa only [homologicalPowerPiece_rank] using ha, hs, rfl⟩

theorem minimalHomologicalPowerMonomials_rank (ρ : RankFunction V)
    (hI : IsPolymatroidalIdeal (rankIdeal k ρ)) (i : ℕ) :
    minimalHomologicalPowerMonomials (rankIdeal k ρ) hI i =
      minimalShiftReesSet (k := k) ρ i := by
  ext p
  constructor
  · rintro ⟨s, a, ha, he⟩
    have ha' := (isMinimalHomologicalPowerMonomial_rank ρ hI i s a).mp ha
    exact ⟨s, a, ha', Subtype.ext he⟩
  · rintro ⟨s, a, ha, rfl⟩
    exact ⟨s, a, (isMinimalHomologicalPowerMonomial_rank ρ hI i s a).mpr ha, rfl⟩

/-- The semantic minimal monomials really generate the whole homological Rees ideal. -/
theorem homologicalPowerIdeal_eq_span_minimal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (i : ℕ) :
    homologicalPowerIdeal I hI i = Ideal.span (minimalHomologicalPowerMonomials I hI i) := by
  subst I
  rw [homologicalPowerIdeal_rank, minimalHomologicalPowerMonomials_rank]
  exact shiftReesIdeal_eq_span_minimal ρ i

/-- The zero-module branch of Theorem 4.4, for the genuine homological Rees ideal. -/
theorem homologicalPowerIdeal_eq_bot_of_above (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi : eventualOffset ρ univ < i) :
    homologicalPowerIdeal I hI i = ⊥ := by
  subst I
  rw [homologicalPowerIdeal_rank]
  exact shiftReesIdeal_eq_bot_of_above ρ hρ i hi

/-- Every positive power has a nonzero shift exactly at and after the first threshold. -/
theorem homologicalShift_power_nonzero_iff (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi : i ≤ eventualOffset ρ univ)
    (s : ℕ) (hs : 1 ≤ s) :
    homologicalShiftIdeal (I ^ s) (hI.pow s) i ≠ ⊥ ↔ powerThreshold ρ i univ ≤ s := by
  subst I
  rw [homologicalShiftIdeal_eq_rankShiftIdeal _ _ (ρ.scale s)
    (rankIdeal_scale k ρ s).symm]
  exact powerShiftIdeal_ne_bot_iff_threshold ρ hρ i hi hs

/-- The exact interval of actual minimal monomial module-generator degrees. -/
theorem homologicalPower_minimal_degree_iff (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (s : ℕ) :
    (∃ a, IsMinimalHomologicalPowerMonomial I hI i s a) ↔
      powerThreshold ρ i univ ≤ s ∧ s ≤ globalPowerThreshold ρ i := by
  subst I
  simp only [isMinimalHomologicalPowerMonomial_rank]
  exact minimalShiftRees_degree_iff ρ hρ i hi0 hi s

/-- The exact least bound is an equality of spans in Mathlib's ordinary Rees algebra. -/
theorem homologicalPower_generation_bound_iff (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) (q : ℕ) :
    homologicalPowerIdeal I hI i = Ideal.span (boundedHomologicalPowerMonomials I hI i q) ↔
      globalPowerThreshold ρ i ≤ q := by
  subst I
  rw [homologicalPowerIdeal_rank, boundedHomologicalPowerMonomials_rank]
  exact shiftReesIdeal_generation_bound_iff ρ hρ i hi0 hi q

/-- The paper's individual new-generator criterion, with genuine Betti support as input. -/
theorem homologicalPower_minimal_iff_rank_violation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (ρ : RankFunction V) (he : I = rankIdeal k ρ)
    (hρ : ρ.Active) (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ)
    (s : ℕ) (hrs : powerThreshold ρ i univ < s) (a : Exponent V)
    (ha : Koszul.GradedBettiNonzero (k := k) (rankBases (ρ.scale s)) a i) :
    IsMinimalHomologicalPowerMonomial I hI i s a ↔
      ∃ A : Finset V, A.Nonempty ∧
        s * ρ A + powerCorrection ρ i (s - 1) A < subsetSum a A := by
  subst I
  rw [isMinimalHomologicalPowerMonomial_rank]
  exact minimalShiftRees_iff_rank_violation ρ hρ i hi0 hi s hrs a
    ((gradedBettiNonzero_rankBases_iff _ _ _).mp ha)

end CommAlg

end
end CheckedSource106

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "107: CommAlg.Polymatroid.HomogenizedIdeal\n"

/-! ## Source: CommAlg.Polymatroid.HomogenizedIdeal -/
section CheckedSource107

/-! # The actual homogenized polynomial ideal

This is the algebraic identity in Theorem 5.1. Extension of an ideal to the
polynomial ring with one extra variable is `Ideal.map` under the actual
variable-renaming homomorphism. Multiplication by the specified power of the
new variable is multiplication by its principal ideal.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset
open scoped Pointwise

variable {V : Type*} [Fintype V] [DecidableEq V]

section Semiring

variable (k : Type*) [CommSemiring k]

theorem monomialIdeal_union (B C : Family V) :
    monomialIdeal k (B ∪ C) = monomialIdeal k B + monomialIdeal k C := by
  simp only [monomialIdeal, Finset.coe_union, Set.image_union, Ideal.span_union,
    Ideal.add_eq_sup]

theorem monomialIdeal_biUnion {J : Type*} [DecidableEq J]
    (s : Finset J) (B : J → Family V) :
    monomialIdeal k (s.biUnion B) = ∑ j ∈ s, monomialIdeal k (B j) := by
  induction s using Finset.induction_on with
  | empty => simp [monomialIdeal]
  | @insert j s hj ih =>
    rw [Finset.biUnion_insert, monomialIdeal_union, Finset.sum_insert hj, ih]

theorem monomial_optionElim (a : Exponent V) (z : ℕ) :
    MvPolynomial.X (R := k) none ^ z *
        MvPolynomial.rename some (MvPolynomial.monomial a 1) =
      MvPolynomial.monomial (a.optionElim z) 1 := by
  have he : Finsupp.single none z + a.mapDomain some = a.optionElim z := by
    change Finsupp.single none z + a.mapDomain (Function.Embedding.some : V ↪ Option V) = _
    rw [← Finsupp.embDomain_eq_mapDomain]
    ext x
    cases x <;> simp
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.rename_monomial,
    MvPolynomial.monomial_mul, one_mul, he]

theorem monomialIdeal_optionElim (B : Family V) (z : ℕ) :
    Ideal.span {MvPolynomial.X (R := k) none ^ z} *
      Ideal.map (MvPolynomial.rename some).toRingHom (monomialIdeal k B) =
        monomialIdeal k (B.image (fun a => a.optionElim z)) := by
  unfold monomialIdeal
  rw [Ideal.map_span, Ideal.span_mul_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · intro hf
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hf
    obtain rfl := Set.mem_singleton_iff.mp hx
    obtain ⟨q, hq, rfl⟩ := hy
    obtain ⟨a, ha, rfl⟩ := hq
    refine ⟨a.optionElim z, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    exact (monomial_optionElim k a z).symm
  · rintro ⟨e, he, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact Set.mem_mul.mpr ⟨_, Set.mem_singleton _, _,
      ⟨MvPolynomial.monomial a 1, ⟨a, ha, rfl⟩, rfl⟩, monomial_optionElim k a z⟩

/-- The displayed sum in Theorem 5.1, at this stage with the explicit rank
formula in place of the separately defined genuine homological-shift ideal. -/
def homogenizedShiftIdeal (g : RankFunction V) : Ideal (MvPolynomial (Option V) k) :=
  ∑ i ∈ Finset.range (shiftLength g + 1),
    Ideal.span {MvPolynomial.X (R := k) none ^ (shiftLength g - i)} *
      Ideal.map (MvPolynomial.rename some).toRingHom (rankShiftIdeal k g i)

/-- Every generator in every shift layer occurs, and there are no additional
minimal generators. This is an equality of actual polynomial ideals. -/
theorem homogenizedShiftIdeal_eq_rankIdeal (g : RankFunction V) :
    homogenizedShiftIdeal k g = rankIdeal k (homogenizedShiftRank g) := by
  rw [rankIdeal, rankBases_homogenizedShift, monomialIdeal_biUnion]
  unfold homogenizedShiftIdeal
  apply Finset.sum_congr rfl
  intro i hi
  rw [rankShiftIdeal_eq_monomialIdeal, monomialIdeal_optionElim]

end Semiring

/-- The canonical upper rank of the precise union of homogenized shift bases. -/
theorem homogenizedShiftFamily_upperRank (g : RankFunction V)
    (A : Finset (Option V)) :
    upperRank ((Finset.range (shiftLength g + 1)).biUnion (fun i =>
      (rankShiftFamily g i).image (fun a => a.optionElim (shiftLength g - i)))) A =
        homogenizedShiftRank g A := by
  rw [← rankBases_homogenizedShift, upperRank_rankBases]

/-- The full union of homogenized shift bases satisfies the ordinary discrete
polymatroid exchange axiom. -/
theorem homogenizedShiftFamily_polymatroidal (g : RankFunction V) :
    IsPolymatroidal ((Finset.range (shiftLength g + 1)).biUnion (fun i =>
      (rankShiftFamily g i).image (fun a => a.optionElim (shiftLength g - i)))) := by
  rw [← rankBases_homogenizedShift]
  exact rankBases_polymatroidal _

end CommAlg.Polymatroid

end
end CheckedSource107

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "108: CommAlg.Polymatroid.HomologicalHomogenization\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalHomogenization -/
section CheckedSource108

/-! # Homogenization of the genuine total Betti support

This module proves the actual polynomial-ideal identity, the exact derived-Tor
base description, its degree, exchange property, and canonical rank. The
projective-dimension identification of the rank gap is supplied separately by
the checked projective-resolution and linear-quotient argument.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

local instance : LinearOrder (Option V) := (inferInstance : LinearOrder (WithBot V))

/-- The literal sum in Theorem 5.1 in the polynomial ring with the extra
variable `none`. Original variables are included by `some`. -/
def homogenizedHomologicalIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (p : ℕ) : Ideal (MvPolynomial (Option V) k) :=
  ∑ i ∈ Finset.range (p + 1),
    Ideal.span {MvPolynomial.X (R := k) none ^ (p - i)} *
      Ideal.map (MvPolynomial.rename some).toRingHom (homologicalShiftIdeal I hI i)

/-- The equality is between actual ideals, and the summands are the genuine
homological-shift ideals defined from Mathlib's derived Tor. -/
theorem homogenizedHomologicalIdeal_eq_rankIdeal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    homogenizedHomologicalIdeal I hI (shiftLength g) =
      rankIdeal k (homogenizedShiftRank g) := by
  unfold homogenizedHomologicalIdeal
  simp_rw [homologicalShiftIdeal_eq_rankShiftIdeal I hI g he]
  exact homogenizedShiftIdeal_eq_rankIdeal k g

/-- The precise base description in terms of all nonzero actual Tor
multidegrees, with both implications checked. -/
theorem homogenized_rankBase_iff_actualBetti (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g)
    (e : Exponent (Option V)) :
    IsRankBase (homogenizedShiftRank g) e ↔
      ∃ i ≤ shiftLength g, ∃ a : Exponent V,
        Koszul.GradedBettiNonzero (k := k) (idealGenerators I hI) a i ∧
          e = a.optionElim (shiftLength g - i) := by
  rw [idealGenerators_eq_of_presentation I hI (rankBases g) (rankBases_polymatroidal g) he]
  simp_rw [gradedBettiNonzero_rankBases_iff]
  exact isRankBase_homogenizedShift_iff g e

theorem homogenizedHomologicalIdeal_polymatroidal (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI (shiftLength g)) := by
  rw [homogenizedHomologicalIdeal_eq_rankIdeal I hI g he]
  exact isPolymatroidalIdeal_rankIdeal _

theorem homogenizedHomologicalIdeal_generators (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    idealGenerators (homogenizedHomologicalIdeal I hI (shiftLength g))
      (homogenizedHomologicalIdeal_polymatroidal I hI g he) =
        rankBases (homogenizedShiftRank g) :=
  idealGenerators_eq_of_presentation _ _ _ (rankBases_polymatroidal _)
    (homogenizedHomologicalIdeal_eq_rankIdeal I hI g he)

/-- Every minimal generator has precisely the asserted total degree. -/
theorem homogenizedHomologicalIdeal_degree (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    Equigenerated (idealGenerators (homogenizedHomologicalIdeal I hI (shiftLength g))
      (homogenizedHomologicalIdeal_polymatroidal I hI g he)) (g univ + shiftLength g) := by
  rw [homogenizedHomologicalIdeal_generators I hI g he]
  have hd := rankBases_equigenerated (homogenizedShiftRank g)
  have hr : homogenizedShiftRank g univ = g univ + shiftLength g := by
    rw [homogenizedShiftRank, RankFunction.homogenize_univ, ← shiftLength_add_degree]
    omega
  rwa [hr] at hd

/-- The displayed rank is canonical, recovered by maximization over the
actual minimal generator exponents. -/
theorem homogenizedHomologicalIdeal_canonicalRank (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g)
    (A : Finset (Option V)) :
    upperRank (idealGenerators (homogenizedHomologicalIdeal I hI (shiftLength g))
      (homogenizedHomologicalIdeal_polymatroidal I hI g he)) A = homogenizedShiftRank g A := by
  rw [homogenizedHomologicalIdeal_generators I hI g he, upperRank_rankBases]

@[simp] theorem homogenizedShiftRank_on_original (g : RankFunction V) (A : Finset V) :
    homogenizedShiftRank g (A.image some) = universalAugmentedRank g A := by
  exact RankFunction.homogenize_some g _ _ A

@[simp] theorem homogenizedShiftRank_with_new_variable (g : RankFunction V) (A : Finset V) :
    homogenizedShiftRank g A.insertNone = shiftLength g + g A := by
  exact RankFunction.homogenize_insertNone g _ _ A

theorem homogenizedShiftRank_active_original (g : RankFunction V) (hg : g.Active)
    (A : Finset V) : homogenizedShiftRank g (A.image some) = A.card + partitionRank g A := by
  rw [homogenizedShiftRank_on_original, universalAugmentedRank_eq_active g hg A]
  rfl

/-- The exact Betti support is independent of the coefficient field (in fact,
it is independent of every nontrivial commutative coefficient ring). -/
theorem gradedBettiNonzero_rankBases_field_independent
    {l : Type u} [CommRing l] [Nontrivial l] (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Koszul.GradedBettiNonzero (k := k) (rankBases g) a i ↔
      Koszul.GradedBettiNonzero (k := l) (rankBases g) a i := by
  rw [gradedBettiNonzero_rankBases_iff, gradedBettiNonzero_rankBases_iff]

end CommAlg.Polymatroid

end
end CheckedSource108

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "109: CommAlg.Polymatroid.HomologicalHomogenizationPD\n"

/-! ## Source: CommAlg.Polymatroid.HomologicalHomogenizationPD -/
section CheckedSource109

/-! # Theorem 5.1 with the actual projective dimension

This final statement combines the genuine Tor support, the actual ideal sum,
and Mathlib's categorical projective dimension.  All conclusions refer to the
unique minimal monomial generators of that sum.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset CategoryTheory

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

local instance : LinearOrder (Option V) := (inferInstance : LinearOrder (WithBot V))

/-- The complete homogenization assertion, including the actual projective
dimension and both directions of the characterization of every minimal
generator by a nonzero actual Tor multidegree.  Loops and the unit ideal are
allowed in addition to the paper's nonzero proper active case. -/
theorem homological_homogenization (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (g : RankFunction V) (he : I = rankIdeal k g) :
    ∃ p : ℕ,
      p = shiftLength g ∧
      projectiveDimension (ModuleCat.of (MvPolynomial V k) I) = (p : WithBot ℕ∞) ∧
      ∃ hH : IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI p),
        Equigenerated (idealGenerators (homogenizedHomologicalIdeal I hI p) hH)
          (g univ + p) ∧
        (∀ A : Finset (Option V),
          upperRank (idealGenerators (homogenizedHomologicalIdeal I hI p) hH) A =
            homogenizedShiftRank g A) ∧
        (∀ e : Exponent (Option V),
          e ∈ idealGenerators (homogenizedHomologicalIdeal I hI p) hH ↔
            ∃ i ≤ p, ∃ a : Exponent V,
              Koszul.GradedBettiNonzero (k := k) (idealGenerators I hI) a i ∧
                e = a.optionElim (p - i)) := by
  refine ⟨shiftLength g, rfl,
    CommAlg.ProjectiveDimension.polymatroidalIdeal_projectiveDimension I g he,
    homogenizedHomologicalIdeal_polymatroidal I hI g he,
    homogenizedHomologicalIdeal_degree I hI g he,
    homogenizedHomologicalIdeal_canonicalRank I hI g he, ?_⟩
  intro e
  rw [homogenizedHomologicalIdeal_generators I hI g he, mem_rankBases]
  exact homogenized_rankBase_iff_actualBetti I hI g he e

/-- No rank presentation is an additional hypothesis on an actual nonzero
polymatroidal ideal: it is constructed from its exchange generators. -/
theorem homological_homogenization_exists_rank (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hne : I ≠ ⊥) :
    ∃ g : RankFunction V, I = rankIdeal k g ∧
      projectiveDimension (ModuleCat.of (MvPolynomial V k) I) =
        (shiftLength g : WithBot ℕ∞) ∧
      IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI (shiftLength g)) := by
  obtain ⟨g, he⟩ := hI.exists_rank hne
  exact ⟨g, he,
    CommAlg.ProjectiveDimension.polymatroidalIdeal_projectiveDimension I g he,
    homogenizedHomologicalIdeal_polymatroidal I hI g he⟩

end CommAlg.Polymatroid

end
end CheckedSource109

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "110: CommAlg.Polymatroid.ThresholdCorrespondence\n"

/-! ## Source: CommAlg.Polymatroid.ThresholdCorrespondence -/
section CheckedSource110

/-! # Exact correspondence with the paper's signed rational ceilings

Natural subtraction in the implementation clamps the numerator at zero.
The first theorem verifies that this is exactly the nonnegative part of the
ordinary rational ceiling, even when the paper's signed numerator is negative.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

theorem signedCeiling_toNat_eq_ceilDiv (κ b δ : ℕ) (hδ : 0 < δ) :
    (Int.ceil (((κ : ℚ) - b) / δ)).toNat = (κ - b) ⌈/⌉ δ := by
  apply eq_of_forall_ge_iff
  intro s
  have hδQ : (0 : ℚ) < δ := by exact_mod_cast hδ
  calc
    (Int.ceil (((κ : ℚ) - b) / δ)).toNat ≤ s ↔
        ((κ : ℚ) - b) / δ ≤ s := by
      rw [Int.toNat_le, Int.ceil_le]
      simp only [Int.cast_natCast]
    _ ↔ (κ : ℚ) ≤ s * δ + b := by rw [div_le_iff₀ hδQ, sub_le_iff_le_add]
    _ ↔ κ ≤ s * δ + b := by norm_cast
    _ ↔ (κ - b) ⌈/⌉ δ ≤ s := by
      rw [ceilDiv_le_iff_le_mul hδ, Nat.mul_comm δ s]
      omega

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The implemented threshold is the paper's maximum over positive-defect
partitions of the nonnegative part of its displayed rational ceiling. -/
theorem powerThreshold_eq_rationalCeiling (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A = Finset.univ.sup (fun P : Finpartition A =>
      if 0 < partitionDefect ρ P then
        (Int.ceil ((((eventualCorrection ρ i A : ℕ) : ℚ) - partitionSlack P) /
          (partitionDefect ρ P : ℚ))).toNat else 0) := by
  unfold powerThreshold affineThreshold
  apply Finset.sup_congr rfl
  intro P hP
  by_cases hd : partitionDefect ρ P = 0
  · simp [hd]
  · have hp : 0 < partitionDefect ρ P := by omega
    simp only [if_neg hd, if_pos hp]
    exact (signedCeiling_toNat_eq_ceilDiv _ _ _ hp).symm

end CommAlg.Polymatroid

end
end CheckedSource110

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "111: CommAlg.KoszulComplex.DerivedDecomposition\n"

/-! ## Source: CommAlg.KoszulComplex.DerivedDecomposition -/
section CheckedSource111

/-! # Every genuine derived Tor class is a finite sum of multigraded classes -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- A canonical component of a derived Tor element, regarded as a member of its true degree submodule. -/
def derivedComponent (B : Family V) (i : ℕ)
    (x : (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))))
    (a : Exponent V) : gradedTor (k := k) B a i :=
  ⟨toDerivedTor (k := k) B a i
    (HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i
      ((coefficientTorIso (k := k) B i).hom x)), ⟨_, rfl⟩⟩

/-- Completeness of the multigrading: every actual derived Tor class is a finite sum of its components. -/
lemma derivedTor_decomposition (B : Family V) (i : ℕ)
    (x : (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)))) :
    ∃ s : Finset (Exponent V), ∑ a ∈ s, (derivedComponent (k := k) B i x a).val = x := by
  obtain ⟨s, hs⟩ := homogeneous_homology_decomposition (k := k) B i
    ((coefficientTorIso (k := k) B i).hom x)
  refine ⟨s, ?_⟩
  apply (coefficientTorIso (k := k) B i).toLinearEquiv.injective
  change (coefficientTorIso (k := k) B i).hom _ = _
  rw [map_sum]
  calc
    ∑ a ∈ s, (coefficientTorIso (k := k) B i).hom
        (derivedComponent (k := k) B i x a).val =
      ∑ a ∈ s, HomologicalComplex.homologyMap
        (homogeneousProjector (k := k) B a) i ((coefficientTorIso (k := k) B i).hom x) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [derivedComponent, toDerivedTor, ModuleCat.comp_apply,
        ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
        homogeneousProjector, HomologicalComplex.homologyMap_comp, Category.assoc,
        Iso.inv_hom_id_assoc, Category.comp_id]
    _ = _ := hs

/-- The actual degree submodules span all of derived Tor. -/
lemma iSup_gradedTor (B : Family V) (i : ℕ) :
    (⨆ a : Exponent V, gradedTor (k := k) B a i) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i x
  rw [← hs]
  apply Submodule.sum_mem
  intro a ha
  exact (le_iSup (fun a : Exponent V => gradedTor (k := k) B a i) a)
    (derivedComponent (k := k) B i x a).property

/-- Nonzero derived Tor has some nonzero multidegree, and conversely. -/
lemma derivedTor_nonzero_iff (B : Family V) (i : ℕ) :
    ¬ IsZero (finitePolynomialTor i
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ↔
      ∃ a, GradedBettiNonzero (k := k) B a i := by
  constructor
  · contrapose!
    intro h
    apply ModuleCat.isZero_iff_subsingleton.mpr
    constructor
    intro x y
    have hx : x = 0 := by
      obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i x
      rw [← hs]
      apply Finset.sum_eq_zero
      intro a ha
      have hz := ModuleCat.isZero_iff_subsingleton.mp (not_not.mp (h a))
      exact congrArg Subtype.val (hz.elim (derivedComponent (k := k) B i x a) 0)
    have hy : y = 0 := by
      obtain ⟨s, hs⟩ := derivedTor_decomposition (k := k) B i y
      rw [← hs]
      apply Finset.sum_eq_zero
      intro a ha
      have hz := ModuleCat.isZero_iff_subsingleton.mp (not_not.mp (h a))
      exact congrArg Subtype.val (hz.elim (derivedComponent (k := k) B i y a) 0)
    exact hx.trans hy.symm
  · rintro ⟨a, ha⟩
    exact derivedTor_nonzero_of_graded (k := k) B a i ha

end CommAlg.Koszul

end
end CheckedSource111

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "112: CommAlg.KoszulComplex.InternalGrading\n"

/-! ## Source: CommAlg.KoszulComplex.InternalGrading -/
section CheckedSource112

/-! # The multigraded pieces form an actual internal direct sum of derived Tor -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]

/-- The canonical projection from derived Tor onto a homogeneous homology group. -/
def fromDerivedTor (B : Family V) (a : Exponent V) (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor i (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ⟶
      (homogeneousComplex (k := k) B a).homology i :=
  (coefficientTorIso (k := k) B i).hom ≫
    HomologicalComplex.homologyMap (homogeneousRetraction (k := k) B a) i

lemma toDerivedTor_from_same (B : Family V) (a : Exponent V) (i : ℕ) :
    toDerivedTor (k := k) B a i ≫ fromDerivedTor (k := k) B a i = 𝟙 _ := by
  simp only [toDerivedTor, fromDerivedTor, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp, homogeneousInclusion_retraction,
    HomologicalComplex.homologyMap_id]

lemma toDerivedTor_from_ne (B : Family V) (a b : Exponent V) (i : ℕ) (hab : a ≠ b) :
    toDerivedTor (k := k) B a i ≫ fromDerivedTor (k := k) B b i = 0 := by
  simp only [toDerivedTor, fromDerivedTor, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp,
    homogeneousInclusion_retraction_ne B a b hab, HomologicalComplex.homologyMap_zero]

/-- The genuine degree projection, as an endomorphism of actual derived Tor. -/
def derivedProjection (B : Family V) (a : Exponent V) (i : ℕ) :=
  (fromDerivedTor (k := k) B a i ≫ toDerivedTor (k := k) B a i).hom

lemma derivedProjection_self (B : Family V) (a : Exponent V) (i : ℕ)
    {x} (hx : x ∈ gradedTor (k := k) B a i) : derivedProjection (k := k) B a i x = x := by
  obtain ⟨y, rfl⟩ := hx
  change (fromDerivedTor (k := k) B a i ≫ toDerivedTor (k := k) B a i)
    (toDerivedTor (k := k) B a i y) = toDerivedTor (k := k) B a i y
  rw [← ModuleCat.comp_apply, ← Category.assoc, toDerivedTor_from_same, Category.id_comp]

lemma derivedProjection_other (B : Family V) (a b : Exponent V) (i : ℕ)
    (hab : a ≠ b) {x} (hx : x ∈ gradedTor (k := k) B b i) :
    derivedProjection (k := k) B a i x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  change (fromDerivedTor (k := k) B a i ≫ toDerivedTor (k := k) B a i)
    (toDerivedTor (k := k) B b i y) = 0
  rw [← ModuleCat.comp_apply, ← Category.assoc,
    toDerivedTor_from_ne B b a i (Ne.symm hab), zero_comp]
  rfl

lemma gradedTor_independent (B : Family V) (i : ℕ) :
    iSupIndep (fun a : Exponent V => gradedTor (k := k) B a i) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hs a ha
  have h := congrArg (derivedProjection (k := k) B a i) hs
  rw [map_sum, map_zero] at h
  rw [Finset.sum_eq_single a] at h
  · rwa [derivedProjection_self B a i (hv a ha)] at h
  · intro b hb hba
    exact derivedProjection_other B a b i (Ne.symm hba) (hv b hb)
  · exact fun hnot => (hnot ha).elim

/-- The degree pieces used to define Betti support are a genuine internal direct sum of derived Tor. -/
theorem gradedTor_isInternal (B : Family V) (i : ℕ) :
    DirectSum.IsInternal (fun a : Exponent V => gradedTor (k := k) B a i) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradedTor_independent B i) (iSup_gradedTor B i)

end CommAlg.Koszul

end
end CheckedSource112

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "113: CommAlg.KoszulComplex.ResidueCoefficients\n"

/-! ## Source: CommAlg.KoszulComplex.ResidueCoefficients -/
section CheckedSource113

/-! # The residue quotient is the coefficient field with its intended polynomial action -/

noncomputable section
namespace CommAlg.Koszul
open CategoryTheory MvPolynomial
universe u
variable {V k : Type u} [CommRing k]

/-- The coefficient ring, with polynomial action by evaluation at zero. -/
def residueCoefficientModule : ModuleCat.{u} (MvPolynomial V k) :=
  (ModuleCat.restrictScalars (constantCoeff : MvPolynomial V k →+* k)).obj (ModuleCat.of k k)

/-- The quotient by all variables agrees as a polynomial module with the coefficient ring. -/
def residueCoefficientEquiv :
    FiniteResidue V k ≃ₗ[MvPolynomial V k] residueCoefficientModule (V := V) (k := k) where
  toFun := (residueRingEquiv (V := V) (k := k))
  invFun := (residueRingEquiv (V := V) (k := k)).symm
  left_inv := (residueRingEquiv (V := V) (k := k)).left_inv
  right_inv := (residueRingEquiv (V := V) (k := k)).right_inv
  map_add' := (residueRingEquiv (V := V) (k := k)).map_add
  map_smul' f q := by
    change (residueRingEquiv (V := V) (k := k)) (f • q) = constantCoeff f * (residueRingEquiv (V := V) (k := k)) q
    refine Quotient.inductionOn' q ?_
    intro p
    change (residueRingEquiv (V := V) (k := k))
      (Ideal.Quotient.mk (idealOfVars V k) (f * p)) =
      constantCoeff f * (residueRingEquiv (V := V) (k := k))
        (Ideal.Quotient.mk (idealOfVars V k) p)
    simp only [residueRingEquiv_mk, map_mul]

/-- Canonical polynomial-module isomorphism to the actual coefficient ring. -/
def residueCoefficientIso :
    ModuleCat.of (MvPolynomial V k) (FiniteResidue V k) ≅
      residueCoefficientModule (V := V) (k := k) :=
  residueCoefficientEquiv.toModuleIso

variable [Fintype V] [LinearOrder V]

/-- The derived Tor groups used throughout are isomorphic to derived Tor with the coefficient ring
itself, carrying precisely its standard evaluation-at-zero polynomial action. -/
def finitePolynomialTorCoefficientIso (i : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) :
    finitePolynomialTor i M ≅
      ((Tor' (ModuleCat (MvPolynomial V k)) i).obj
        (residueCoefficientModule (V := V) (k := k))).obj M :=
  ((Functor.flip (Tor' (ModuleCat (MvPolynomial V k)) i)).obj M).mapIso residueCoefficientIso

end CommAlg.Koszul

end
end CheckedSource113

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "114: CommAlg\n"

/-! ## Source: CommAlg -/
section CheckedSource114

/-! Complete principal theorem library for Rank formulas for homological shifts of polymatroidal ideals. -/

end CheckedSource114

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "115: FourPapers.Homological.Main\n"

/-! ## Source: FourPapers.Homological.Main -/
section CheckedSource115

/-!
# Principal results of the attached homological-shifts manuscript

This public entry point specializes the more general verified library to fields,
as in the manuscript. The underlying homological shifts use genuine multigraded
pieces of Mathlib's derived tensor functor. No expected rank formula occurs in
their definition.

Manuscript: `14_homological_shifts(9).pdf`, SHA-256
`de8e82538734073169d46a02e8a142dc9f898f90863425ecdfc1a82e39f15341`.
-/

set_option autoImplicit false

noncomputable section

namespace FourPapers.Homological

open Classical Finset CommAlg CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- Theorem 1.1: stabilization for every ideal and every `s ≥ i > 0`. -/
theorem theorem_1_1 (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i s : ℕ) (_hi : 0 < i) (hs : i ≤ s) :
    homologicalShiftIdeal (I ^ (s + 1)) (hI.pow (s + 1)) i =
      I * homologicalShiftIdeal (I ^ s) (hI.pow s) i :=
  homologicalShift_powers I hI i s hs

/-- The fixed-polymatroidal-twist clause of Theorem 1.1. -/
theorem theorem_1_1_twisted (I J : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (hJ : IsPolymatroidalIdeal J)
    (i s : ℕ) (_hi : 0 < i) (hs : i ≤ s) :
    homologicalShiftIdeal (J * I ^ (s + 1)) (hJ.mul (hI.pow (s + 1))) i =
      I * homologicalShiftIdeal (J * I ^ s) (hJ.mul (hI.pow s)) i :=
  homologicalShift_twistedPowers I J hI hJ i s hs

/-- The actual ordinary Rees-module generation assertion of Theorem 1.1. -/
theorem theorem_1_1_generation (I : Ideal (MvPolynomial V k))
    (hI : IsPolymatroidalIdeal I) (i : ℕ) (hi : 0 < i) :
    homologicalPowerIdeal I hI i = Ideal.span (homologicalPowerBoxGenerators I hI i) :=
  homologicalPowerIdeal_generated_le I hI i hi

/-- Theorem 1.2: the exact partition formula on the active ground set.
The right-hand side rank is a proved `RankFunction`, hence includes all
normalization, monotonicity, integrality, and submodularity assertions. -/
theorem theorem_1_2 (g : RankFunction V) (hg : g.Active) (i : ℕ) :
    homologicalShiftIdeal (rankIdeal k g) (isPolymatroidalIdeal_rankIdeal g) i =
      if homologicalRank g hg i univ = g univ + i then
        rankIdeal k (homologicalRank g hg i) else ⊥ :=
  homologicalShiftIdeal_partitionFormula _ _ g rfl hg i

/-- The canonicality clause of Theorem 1.2; the left side takes the maximum
over the actual minimal monomial generator exponents. -/
theorem theorem_1_2_canonical (g : RankFunction V) (hg : g.Active) (i : ℕ)
    (hne : homologicalShiftIdeal (rankIdeal k g)
      (isPolymatroidalIdeal_rankIdeal g) i ≠ ⊥) (A : Finset V) :
    upperRank (idealGenerators
      (homologicalShiftIdeal (rankIdeal k g) (isPolymatroidalIdeal_rankIdeal g) i)
      (homologicalShiftIdeal_polymatroidal _ _ i)) A = homologicalRank g hg i A := by
  rw [homologicalShiftIdeal_canonicalRank _ _ g rfl i hne]
  exact universalHomologicalRank_eq_active g hg i A

/-- Proposition 4.2: the universal sharpness family in all positive degrees. -/
theorem proposition_4_2 (i : ℕ) (hi : 1 ≤ i) (hcard : Fintype.card V = i + 1) :
    (∀ s : ℕ, 1 ≤ s → s < i →
      homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ s)
        ((squarefreeVeronese_polymatroidal i).pow s) i = ⊥) ∧
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ i)
      ((squarefreeVeronese_polymatroidal i).pow i) i =
        Ideal.span {(∏ j : V, (MvPolynomial.X j : MvPolynomial V k)) ^ i} ∧
    homologicalShiftIdeal (squarefreeVeroneseIdeal k V i ^ i)
      ((squarefreeVeronese_polymatroidal i).pow i) i ≠ ⊥ :=
  ⟨fun _ hs hsi => squarefreeVeronese_shift_below hi hs hsi hcard,
    squarefreeVeronese_shift_at_threshold hi hcard,
    squarefreeVeronese_shift_at_threshold_ne_bot hi hcard⟩

/-- Corollary 4.3: actual categorical projective dimension, with the minimum
ranging over every partition of the entire active ground set. -/
theorem corollary_4_3 (ρ : RankFunction V) (hρ : ρ.Active) (s : ℕ) (hs : 1 ≤ s) :
    CategoryTheory.projectiveDimension
        (ModuleCat.of (MvPolynomial V k) ↥((rankIdeal k ρ) ^ s)) =
      (finiteMinimum (fun P : Finpartition (univ : Finset V) =>
        s * partitionDefect ρ P + partitionSlack P) : WithBot ℕ∞) :=
  CommAlg.ProjectiveDimension.rankIdeal_power_projectiveDimension ρ hρ s hs

/-- The eventual projective-dimension assertion in Corollary 4.3. -/
theorem corollary_4_3_eventual (ρ : RankFunction V) (hρ : ρ.Active)
    (s : ℕ) (hs : max 1 (eventualOffset ρ univ) ≤ s) :
    CategoryTheory.projectiveDimension
        (ModuleCat.of (MvPolynomial V k) ↥((rankIdeal k ρ) ^ s)) =
      (eventualOffset ρ univ : WithBot ℕ∞) :=
  CommAlg.ProjectiveDimension.rankIdeal_power_projectiveDimension_eventual ρ hρ s hs

/-- The zero-module case of Theorem 4.4. -/
theorem theorem_4_4_zero (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi : eventualOffset ρ univ < i) :
    homologicalPowerIdeal (rankIdeal k ρ) (isPolymatroidalIdeal_rankIdeal ρ) i = ⊥ :=
  homologicalPowerIdeal_eq_bot_of_above _ _ ρ rfl hρ i hi

/-- Theorem 4.4: the exact interval of actual minimal monomial Rees-module
generators, its endpoints, first nonzero piece, and exact least generation bound. -/
theorem theorem_4_4 (ρ : RankFunction V) (hρ : ρ.Active)
    (i : ℕ) (hi0 : 0 < i) (hi : i ≤ eventualOffset ρ univ) :
    (1 ≤ powerThreshold ρ i univ ∧
      powerThreshold ρ i univ ≤ globalPowerThreshold ρ i ∧
      globalPowerThreshold ρ i ≤ i) ∧
    (∀ s : ℕ, 1 ≤ s →
      (homologicalShiftIdeal (rankIdeal k ρ ^ s)
        ((isPolymatroidalIdeal_rankIdeal ρ).pow s) i ≠ ⊥ ↔
          powerThreshold ρ i univ ≤ s)) ∧
    (∀ s : ℕ,
      (∃ a, IsMinimalHomologicalPowerMonomial (rankIdeal k ρ)
        (isPolymatroidalIdeal_rankIdeal ρ) i s a) ↔
          powerThreshold ρ i univ ≤ s ∧ s ≤ globalPowerThreshold ρ i) ∧
    (∀ q : ℕ,
      homologicalPowerIdeal (rankIdeal k ρ) (isPolymatroidalIdeal_rankIdeal ρ) i =
        Ideal.span (boundedHomologicalPowerMonomials (rankIdeal k ρ)
          (isPolymatroidalIdeal_rankIdeal ρ) i q) ↔
            globalPowerThreshold ρ i ≤ q) :=
  ⟨powerShift_generator_endpoints ρ i hi0 hi,
    fun s hs => homologicalShift_power_nonzero_iff (rankIdeal k ρ) (isPolymatroidalIdeal_rankIdeal ρ) ρ rfl hρ i hi s hs,
    fun s => homologicalPower_minimal_degree_iff _ _ ρ rfl hρ i hi0 hi s,
    fun q => homologicalPower_generation_bound_iff _ _ ρ rfl hρ i hi0 hi q⟩

/-- The threshold used in Theorem 4.4 is exactly the paper's signed rational
ceiling formula, including negative numerators and empty index collections. -/
theorem theorem_4_4_threshold_formula (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A = Finset.univ.sup (fun P : Finpartition A =>
      if 0 < partitionDefect ρ P then
        (Int.ceil ((((eventualCorrection ρ i A : ℕ) : ℚ) - partitionSlack P) /
          (partitionDefect ρ P : ℚ))).toNat else 0) :=
  powerThreshold_eq_rationalCeiling ρ i A

local instance : LinearOrder (Option V) := (inferInstance : LinearOrder (WithBot V))

/-- Theorem 5.1: the total-support ideal, its genuine projective dimension,
degree, canonical rank, and exact actual-Tor description of every generator. -/
theorem theorem_5_1 (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (g : RankFunction V) (he : I = rankIdeal k g) :
    ∃ p : ℕ,
      p = shiftLength g ∧
      CategoryTheory.projectiveDimension (ModuleCat.of (MvPolynomial V k) I) =
        (p : WithBot ℕ∞) ∧
      ∃ hH : IsPolymatroidalIdeal (homogenizedHomologicalIdeal I hI p),
        Equigenerated (idealGenerators (homogenizedHomologicalIdeal I hI p) hH)
          (g univ + p) ∧
        (∀ A : Finset (Option V),
          upperRank (idealGenerators (homogenizedHomologicalIdeal I hI p) hH) A =
            homogenizedShiftRank g A) ∧
        (∀ e : Exponent (Option V),
          e ∈ idealGenerators (homogenizedHomologicalIdeal I hI p) hH ↔
            ∃ i ≤ p, ∃ a : Exponent V,
              Koszul.GradedBettiNonzero (k := k) (idealGenerators I hI) a i ∧
                e = a.optionElim (p - i)) :=
  homological_homogenization I hI g he

/-- The two displayed formulas for the canonical rank in Theorem 5.1. -/
theorem theorem_5_1_rank (g : RankFunction V) (hg : g.Active) (A : Finset V) :
    homogenizedShiftRank g (A.image some) = A.card + partitionRank g A ∧
      homogenizedShiftRank g A.insertNone = shiftLength g + g A :=
  ⟨homogenizedShiftRank_active_original g hg A,
    homogenizedShiftRank_with_new_variable g A⟩

/-- The final field-independence assertion in Theorem 5.1, on the exact
nonzero multigraded pieces of genuine derived Tor. -/
theorem theorem_5_1_field_independent {l : Type u} [Field l]
    (g : RankFunction V) (a : Exponent V) (i : ℕ) :
    Koszul.GradedBettiNonzero (k := k) (rankBases g) a i ↔
      Koszul.GradedBettiNonzero (k := l) (rankBases g) a i :=
  gradedBettiNonzero_rankBases_field_independent g a i

/-- Theorem 6.1: integral closure inside the actual ordinary Rees algebra. -/
theorem theorem_6_1 (I : Ideal (MvPolynomial V k)) (hI : IsPolymatroidalIdeal I)
    (i : ℕ) (hi : 0 < i) :
    IsIntegrallyClosedIdeal (homologicalPowerIdeal I hI i) :=
  homologicalPowerIdeal_integrallyClosed I hI i hi

section SeveralColors

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Corollary 4.1: the full coordinatewise stabilization equality. -/
theorem corollary_4_1 (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (s : C →₀ ℕ) (i : ℕ)
    (c : C) (_hi : 0 < i) (hs : i ≤ s c) :
    homologicalShiftIdeal (J * powerProduct I (s + Finsupp.single c 1))
        (hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)) i =
      I c * homologicalShiftIdeal (J * powerProduct I s)
        (hJ.mul (IsPolymatroidalIdeal.powerProduct I hI _)) i :=
  homologicalShift_severalColors I J hI hJ s i c hs

/-- The full multigraded module-generation clause of Corollary 4.1. -/
theorem corollary_4_1_generation (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (i : ℕ) :
    homologicalMultiIdeal J I hJ hI i =
      Ideal.span (reesBoxGenerators I (homologicalMultiPiece J I hJ hI i) i) :=
  homologicalMultiIdeal_generated_in_box J I hJ hI i

/-- Corollary 6.2: arbitrary finite colors, fixed twists, and zero coordinates. -/
theorem corollary_6_2 (I : C → Ideal (MvPolynomial V k))
    (J : Ideal (MvPolynomial V k)) (hI : ∀ c, IsPolymatroidalIdeal (I c))
    (hJ : IsPolymatroidalIdeal J) (hIne : ∀ c, I c ≠ ⊥) (i : ℕ) :
    IsIntegrallyClosedIdeal (homologicalMultiIdeal J I hJ hI i) :=
  homologicalMultiIdeal_integrallyClosed J I hJ hI hIne i

end SeveralColors

end FourPapers.Homological

end
end CheckedSource115

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "116: CommAlg.AuditSupport\n"

/-! ## Source: CommAlg.AuditSupport -/
section CheckedSource116

/-! # Reproducible transitive proof audits

These elaborator commands inspect the checked Lean environment. They do
not introduce mathematical declarations or axioms. The axiom guard fails
if any audited result uses anything beyond Lean's three standard axioms.
-/

open Lean Elab Command

elab "audit_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axs ← Lean.collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in axs do
    unless allowed.contains ax do
      throwError "Unapproved transitive axiom {ax} in {name}"
  logInfo m!"AXIOM AUDIT PASSED: {name}: {axs}"

meta def dependencyModule (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

meta def isProjectModule (name : Name) : Bool :=
  let s := name.toString
  s.startsWith "CommAlg." || s == "CommAlg" || s.startsWith "TauCeti." ||
    s.startsWith "FourPapers." || s == "FourPapers" || s.startsWith "four_papers."

/-- Export the exact transitive declaration graph through every locally
proved module, stopping only at the pinned Lean/Mathlib library boundary. -/
elab "export_proof_dependencies " path:str "[" ns:ident,* "]" : command => do
  let roots ← ns.getElems.mapM fun n => liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let env := (← getEnv).setExporting false
  let mut todo := roots
  let mut cursor := 0
  let mut seen : NameSet := {}
  let mut nodes : Array Json := #[]
  let mut rootInfo : Array Json := #[]
  for name in roots do
    let axs ← Lean.collectAxioms name
    let some info := env.checked.get.find? name | throwError "Missing checked root {name}"
    let ty ← liftTermElabM <| Meta.ppExpr info.type
    rootInfo := rootInfo.push <| Json.mkObj
      [("name", toJson name.toString), ("type", toJson ty.pretty),
       ("axioms", toJson (axs.map Name.toString))]
  while cursor < todo.size do
    let name := todo[cursor]!
    cursor := cursor + 1
    if seen.contains name then continue
    seen := seen.insert name
    let modName := dependencyModule env name
    let boundary := !isProjectModule modName
    let some info := env.checked.get.find? name | throwError "Missing checked dependency {name}"
    let deps := if boundary then #[] else info.getUsedConstantsAsSet.toArray.qsort Name.lt
    todo := todo ++ deps
    nodes := nodes.push <| Json.mkObj
      [("name", toJson name.toString), ("module", toJson modName.toString),
       ("library_boundary", toJson boundary), ("dependencies", toJson (deps.map Name.toString))]
  let document := Json.mkObj
    [("format", toJson "Lean checked-environment dependency graph, version 1"),
     ("boundary", toJson "All FourPapers, CommAlg, and vendored TauCeti declarations are expanded; pinned Lean/Mathlib declarations are leaves."),
     ("roots", Json.arr rootInfo), ("nodes", Json.arr nodes)]
  let target : System.FilePath := path.getString
  if let some parent := target.parent then liftIO <| PalomarAudit.createDirAll parent
  liftIO <| PalomarAudit.writeFile target (document.pretty ++ "\n")
  logInfo m!"DEPENDENCY GRAPH: {nodes.size} checked declarations written to {path.getString}"

end CheckedSource116

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "117: CommAlg.AuditCore\n"

/-! ## Source: CommAlg.AuditCore -/
section CheckedSource117

/-! Kernel-environment audits of the main rank, stabilization, sharpness, homogenization, and normalization theorems. -/

set_option maxHeartbeats 0
set_option maxRecDepth 10000

audit_standard_axioms CommAlg.Polymatroid.homologicalShiftIdeal_partitionFormula
audit_standard_axioms CommAlg.Polymatroid.homologicalShiftIdeal_canonicalRank
audit_standard_axioms CommAlg.Polymatroid.bettiNumber_ideal_pos_iff
audit_standard_axioms CommAlg.Polymatroid.homologicalShift_powers
audit_standard_axioms CommAlg.Polymatroid.homologicalShift_twistedPowers
audit_standard_axioms CommAlg.Polymatroid.homologicalShift_severalColors
audit_standard_axioms CommAlg.Polymatroid.homologicalShiftIdeal_mul_le
audit_standard_axioms CommAlg.Polymatroid.squarefreeVeronese_shift_below
audit_standard_axioms CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold
audit_standard_axioms CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold_ne_bot
audit_standard_axioms CommAlg.Polymatroid.homogenizedHomologicalIdeal_eq_rankIdeal
audit_standard_axioms CommAlg.Polymatroid.homogenized_rankBase_iff_actualBetti
audit_standard_axioms CommAlg.Polymatroid.homogenizedHomologicalIdeal_polymatroidal
audit_standard_axioms CommAlg.Polymatroid.homogenizedHomologicalIdeal_degree
audit_standard_axioms CommAlg.Polymatroid.homogenizedHomologicalIdeal_canonicalRank
audit_standard_axioms CommAlg.Polymatroid.homogenizedShiftRank_on_original
audit_standard_axioms CommAlg.Polymatroid.homogenizedShiftRank_with_new_variable
audit_standard_axioms CommAlg.Polymatroid.gradedBettiNonzero_rankBases_field_independent
audit_standard_axioms CommAlg.homologicalPowerIdeal_integrallyClosed
audit_standard_axioms CommAlg.homologicalMultiIdeal_integrallyClosed

export_proof_dependencies ".lake/reports/audit/core_dependencies.json" [
  CommAlg.Polymatroid.homologicalShiftIdeal_partitionFormula,
  CommAlg.Polymatroid.homologicalShiftIdeal_canonicalRank,
  CommAlg.Polymatroid.bettiNumber_ideal_pos_iff,
  CommAlg.Polymatroid.homologicalShift_powers,
  CommAlg.Polymatroid.homologicalShift_twistedPowers,
  CommAlg.Polymatroid.homologicalShift_severalColors,
  CommAlg.Polymatroid.homologicalShiftIdeal_mul_le,
  CommAlg.Polymatroid.squarefreeVeronese_shift_below,
  CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold,
  CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold_ne_bot,
  CommAlg.Polymatroid.homogenizedHomologicalIdeal_eq_rankIdeal,
  CommAlg.Polymatroid.homogenized_rankBase_iff_actualBetti,
  CommAlg.Polymatroid.homogenizedHomologicalIdeal_polymatroidal,
  CommAlg.Polymatroid.homogenizedHomologicalIdeal_degree,
  CommAlg.Polymatroid.homogenizedHomologicalIdeal_canonicalRank,
  CommAlg.Polymatroid.homogenizedShiftRank_on_original,
  CommAlg.Polymatroid.homogenizedShiftRank_with_new_variable,
  CommAlg.Polymatroid.gradedBettiNonzero_rankBases_field_independent,
  CommAlg.homologicalPowerIdeal_integrallyClosed,
  CommAlg.homologicalMultiIdeal_integrallyClosed
]

end CheckedSource117

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "118: CommAlg.AuditConsequences\n"

/-! ## Source: CommAlg.AuditConsequences -/
section CheckedSource118

/-! Complete audits of actual projective dimensions, module generation, exact intervals, total support, and Tor foundations. -/

set_option maxHeartbeats 0
set_option maxRecDepth 10000

audit_standard_axioms CommAlg.ProjectiveDimension.rankIdeal_projectiveDimension
audit_standard_axioms CommAlg.ProjectiveDimension.polymatroidal_power_projectiveDimension
audit_standard_axioms CommAlg.ProjectiveDimension.polymatroidal_power_projectiveDimension_eventual
audit_standard_axioms CommAlg.homologicalPowerIdeal_generated_le
audit_standard_axioms CommAlg.homologicalMultiIdeal_generated_in_box
audit_standard_axioms CommAlg.homologicalPowerIdeal_eq_bot_of_above
audit_standard_axioms CommAlg.homologicalShift_power_nonzero_iff
audit_standard_axioms CommAlg.homologicalPower_minimal_degree_iff
audit_standard_axioms CommAlg.homologicalPower_generation_bound_iff
audit_standard_axioms CommAlg.homologicalPowerIdeal_eq_span_minimal
audit_standard_axioms CommAlg.homologicalPower_minimal_iff_rank_violation
audit_standard_axioms CommAlg.Polymatroid.powerShift_generator_endpoints
audit_standard_axioms CommAlg.Polymatroid.powerThreshold_eq_rationalCeiling
audit_standard_axioms CommAlg.Polymatroid.homological_homogenization
audit_standard_axioms CommAlg.Polymatroid.homological_homogenization_exists_rank
audit_standard_axioms CommAlg.Koszul.gradedTor_isInternal
audit_standard_axioms CommAlg.Koszul.derivedTor_nonzero_iff
audit_standard_axioms CommAlg.Koszul.finitePolynomialTorCoefficientIso
audit_standard_axioms CommAlg.Koszul.bettiNumber_pos_iff
audit_standard_axioms CommAlg.Koszul.finitePolynomialTor_nonzero_le_projectiveDimension

export_proof_dependencies ".lake/reports/audit/consequences_dependencies.json" [
  CommAlg.ProjectiveDimension.rankIdeal_projectiveDimension,
  CommAlg.ProjectiveDimension.polymatroidal_power_projectiveDimension,
  CommAlg.ProjectiveDimension.polymatroidal_power_projectiveDimension_eventual,
  CommAlg.homologicalPowerIdeal_generated_le,
  CommAlg.homologicalMultiIdeal_generated_in_box,
  CommAlg.homologicalPowerIdeal_eq_bot_of_above,
  CommAlg.homologicalShift_power_nonzero_iff,
  CommAlg.homologicalPower_minimal_degree_iff,
  CommAlg.homologicalPower_generation_bound_iff,
  CommAlg.homologicalPowerIdeal_eq_span_minimal,
  CommAlg.homologicalPower_minimal_iff_rank_violation,
  CommAlg.Polymatroid.powerShift_generator_endpoints,
  CommAlg.Polymatroid.powerThreshold_eq_rationalCeiling,
  CommAlg.Polymatroid.homological_homogenization,
  CommAlg.Polymatroid.homological_homogenization_exists_rank,
  CommAlg.Koszul.gradedTor_isInternal,
  CommAlg.Koszul.derivedTor_nonzero_iff,
  CommAlg.Koszul.finitePolynomialTorCoefficientIso,
  CommAlg.Koszul.bettiNumber_pos_iff,
  CommAlg.Koszul.finitePolynomialTor_nonzero_le_projectiveDimension
]

end CheckedSource118

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "119: CommAlg.Audit\n"

/-! ## Source: CommAlg.Audit -/
section CheckedSource119

/-! All principal theorems are guarded against unapproved transitive axioms. -/

end CheckedSource119

run_cmd Lean.Elab.Command.liftIO <| PalomarAudit.writeFile ".lake/reports/audit/homological/compile_progress.txt" "120: FourPapers.Homological.Audit\n"

/-! ## Source: FourPapers.Homological.Audit -/
section CheckedSource120

set_option autoImplicit false

/-! The public paper-numbered results and their semantic bridges are checked
against precisely Lean's standard logical axioms. -/

set_option maxHeartbeats 0
set_option maxRecDepth 10000

audit_standard_axioms FourPapers.Homological.theorem_1_1
audit_standard_axioms FourPapers.Homological.theorem_1_1_twisted
audit_standard_axioms FourPapers.Homological.theorem_1_1_generation
audit_standard_axioms FourPapers.Homological.theorem_1_2
audit_standard_axioms FourPapers.Homological.theorem_1_2_canonical
audit_standard_axioms FourPapers.Homological.corollary_4_1
audit_standard_axioms FourPapers.Homological.corollary_4_1_generation
audit_standard_axioms FourPapers.Homological.proposition_4_2
audit_standard_axioms FourPapers.Homological.corollary_4_3
audit_standard_axioms FourPapers.Homological.corollary_4_3_eventual
audit_standard_axioms FourPapers.Homological.theorem_4_4_zero
audit_standard_axioms FourPapers.Homological.theorem_4_4
audit_standard_axioms FourPapers.Homological.theorem_4_4_threshold_formula
audit_standard_axioms FourPapers.Homological.theorem_5_1
audit_standard_axioms FourPapers.Homological.theorem_5_1_rank
audit_standard_axioms FourPapers.Homological.theorem_5_1_field_independent
audit_standard_axioms FourPapers.Homological.theorem_6_1
audit_standard_axioms FourPapers.Homological.corollary_6_2

audit_standard_axioms CommAlg.Koszul.finitePolynomialResolution
audit_standard_axioms CommAlg.Koszul.finitePolynomialTorIso
audit_standard_axioms CommAlg.Koszul.finitePolynomialTorCoefficientIso
audit_standard_axioms CommAlg.Koszul.coefficientTorIso
audit_standard_axioms CommAlg.Koszul.homogeneousFacesIso
audit_standard_axioms CommAlg.Koszul.gradedTor_isInternal
audit_standard_axioms CommAlg.Koszul.bettiNumber_pos_iff
audit_standard_axioms CommAlg.Matroid.independence_nonzeroHomology_iff
audit_standard_axioms CommAlg.Polymatroid.rankBases_canonical
audit_standard_axioms CommAlg.Polymatroid.rank_base_minkowski
audit_standard_axioms CommAlg.Polymatroid.powerThreshold_eq_rationalCeiling
audit_standard_axioms CommAlg.Weight.integrallyClosed_of_weight_bounds

export_proof_dependencies ".lake/reports/audit/homological/principal_dependencies.json" [
  FourPapers.Homological.theorem_1_1,
  FourPapers.Homological.theorem_1_1_twisted,
  FourPapers.Homological.theorem_1_1_generation,
  FourPapers.Homological.theorem_1_2,
  FourPapers.Homological.theorem_1_2_canonical,
  FourPapers.Homological.corollary_4_1,
  FourPapers.Homological.corollary_4_1_generation,
  FourPapers.Homological.proposition_4_2,
  FourPapers.Homological.corollary_4_3,
  FourPapers.Homological.corollary_4_3_eventual,
  FourPapers.Homological.theorem_4_4_zero,
  FourPapers.Homological.theorem_4_4,
  FourPapers.Homological.theorem_4_4_threshold_formula,
  FourPapers.Homological.theorem_5_1,
  FourPapers.Homological.theorem_5_1_rank,
  FourPapers.Homological.theorem_5_1_field_independent,
  FourPapers.Homological.theorem_6_1,
  FourPapers.Homological.corollary_6_2,
  CommAlg.Polymatroid.homologicalShiftIdeal_partitionFormula,
  CommAlg.Polymatroid.homologicalShiftIdeal_canonicalRank,
  CommAlg.Polymatroid.gradedBettiNonzero_rankBases_iff,
  CommAlg.Polymatroid.homologicalShift_powers,
  CommAlg.Polymatroid.homologicalShift_twistedPowers,
  CommAlg.homologicalPowerIdeal_generated_le,
  CommAlg.Polymatroid.homologicalShift_severalColors,
  CommAlg.homologicalMultiIdeal_generated_in_box,
  CommAlg.Polymatroid.squarefreeVeronese_shift_below,
  CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold,
  CommAlg.Polymatroid.squarefreeVeronese_shift_at_threshold_ne_bot,
  CommAlg.ProjectiveDimension.rankIdeal_power_projectiveDimension,
  CommAlg.ProjectiveDimension.rankIdeal_power_projectiveDimension_eventual,
  CommAlg.homologicalPowerIdeal_eq_bot_of_above,
  CommAlg.homologicalShift_power_nonzero_iff,
  CommAlg.homologicalPower_minimal_degree_iff,
  CommAlg.homologicalPower_generation_bound_iff,
  CommAlg.homologicalPowerIdeal_eq_span_minimal,
  CommAlg.homologicalPower_minimal_iff_rank_violation,
  CommAlg.Polymatroid.powerShift_generator_endpoints,
  CommAlg.Polymatroid.powerThreshold_eq_rationalCeiling,
  CommAlg.Polymatroid.homological_homogenization,
  CommAlg.Polymatroid.homogenizedHomologicalIdeal_eq_rankIdeal,
  CommAlg.Polymatroid.homogenizedShiftRank_active_original,
  CommAlg.Polymatroid.homogenizedShiftRank_with_new_variable,
  CommAlg.Polymatroid.gradedBettiNonzero_rankBases_field_independent,
  CommAlg.homologicalPowerIdeal_integrallyClosed,
  CommAlg.homologicalMultiIdeal_integrallyClosed,
  CommAlg.Koszul.finitePolynomialResolution,
  CommAlg.Koszul.finitePolynomialTorIso,
  CommAlg.Koszul.finitePolynomialTorCoefficientIso,
  CommAlg.Koszul.coefficientTorIso,
  CommAlg.Koszul.homogeneousFacesIso,
  CommAlg.Koszul.gradedTor_isInternal,
  CommAlg.Koszul.bettiNumber_pos_iff,
  CommAlg.Matroid.independence_nonzeroHomology_iff,
  CommAlg.Polymatroid.rankBases_canonical,
  CommAlg.Polymatroid.rank_base_minkowski,
  CommAlg.Weight.integrallyClosed_of_weight_bounds
]

end CheckedSource120
