/- Intrinsic binary matroid cycles.

The predicate below refers only to ordinary Mathlib circuits.  It is a finite
iterated disjoint union of circuits, including the empty union.  We prove that
it is exactly the zero-sum support of a binary representation, and consequently
that binary coefficient cycles do not depend on the chosen representation.
-/
module
public import Recovery.Unimodular.ProductVectorMatroid
public import Recovery.Unimodular.PriorExtensions.SignedSumsSupport
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace Unimodular.BinaryMatroidCycles

open Unimodular.SignedSums.Binary

variable {E V W : Type*} [DecidableEq E]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- An intrinsic cycle of a finite binary matroid: a finite disjoint union of
ordinary matroid circuits.  The definition itself makes no reference to a
matrix, vector representation, coefficient kernel, or proposed sum operation. -/
inductive DisjointCircuitUnion (M : Matroid E) : Finset E → Prop
  | empty : DisjointCircuitUnion M ∅
  | union (C S : Finset E) (hC : M.IsCircuit (C : Set E))
      (hdis : Disjoint C S) (hS : DisjointCircuitUnion M S) :
      DisjointCircuitUnion M (C ∪ S)

/-- In characteristic two the unique nonzero circuit coefficients are all one.
This holds for arbitrary finite circuits, including loops and parallel pairs. -/
theorem circuit_sum_eq_zero (U : E → V) {C : Finset E}
    (hC : (VectorMatroid.ofFamily (K := F) U).IsCircuit (C : Set E)) :
    ∑ e ∈ C, U e = 0 := by
  classical
  have hdep : ¬ LinearIndepOn F U (C : Set E) := by
    simpa only [VectorMatroid.ofFamily_indep] using hC.not_indep
  obtain ⟨f, hf, i, hi, hfi⟩ := not_linearIndepOn_finset_iff.mp hdep
  let T := C.filter (fun e => f e ≠ 0)
  have hTCsub : T ⊆ C := Finset.filter_subset _ _
  have hsumT : ∑ e ∈ T, f e • U e = 0 := by
    calc
      ∑ e ∈ T, f e • U e = ∑ e ∈ C, f e • U e := by
        apply Finset.sum_subset hTCsub
        intro e he heT
        have hfe : f e = 0 := by
          by_contra hne
          exact heT (Finset.mem_filter.mpr ⟨he, hne⟩)
        simp [hfe]
      _ = 0 := hf
  have hTdep : ¬ (VectorMatroid.ofFamily (K := F) U).Indep (T : Set E) := by
    intro hT
    have hli := (VectorMatroid.ofFamily_indep U (T : Set E)).mp hT
    exact hfi ((linearIndepOn_finset_iff.mp hli) f hsumT i
      (Finset.mem_filter.mpr ⟨hi, hfi⟩))
  have hTC : (T : Set E) = (C : Set E) :=
    hC.eq_of_not_indep_subset hTdep (Finset.coe_subset.mpr hTCsub)
  have hone : ∀ e ∈ C, f e = 1 := by
    intro e he
    have heT : e ∈ T := by
      change e ∈ (T : Set E)
      rw [hTC]
      exact he
    have hne := (Finset.mem_filter.mp heT).2
    exact (value_zero_or_one (f e)).resolve_left hne
  calc
    ∑ e ∈ C, U e = ∑ e ∈ C, f e • U e := by
      apply Finset.sum_congr rfl
      intro e he
      simp [hone e he]
    _ = 0 := hf

/-- Every finite zero-sum set decomposes into disjoint circuits, and every
such disjoint union sums to zero.  No rank or cardinality restriction occurs. -/
theorem sum_eq_zero_iff_disjointCircuitUnion (U : E → V) (S : Finset E) :
    (∑ e ∈ S, U e = 0) ↔
      DisjointCircuitUnion (VectorMatroid.ofFamily (K := F) U) S := by
  classical
  constructor
  · refine Finset.strongInductionOn S ?_
    intro S ih hs
    by_cases hS : S = ∅
    · subst S
      exact DisjointCircuitUnion.empty
    have hdep : ¬ (VectorMatroid.ofFamily (K := F) U).Indep (S : Set E) := by
      intro hI
      have hli := (VectorMatroid.ofFamily_indep U (S : Set E)).mp hI
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hz := (linearIndepOn_finset_iff.mp hli) (fun _ => (1 : F))
        (by simpa using hs) e he
      exact one_ne_zero hz
    have hDep : (VectorMatroid.ofFamily (K := F) U).Dep (S : Set E) :=
      ⟨hdep, by simp⟩
    obtain ⟨C, hCS, hC⟩ := hDep.exists_isCircuit_subset
    have hCfin : C.Finite := S.finite_toSet.subset hCS
    let c := hCfin.toFinset
    have hcset : (c : Set E) = C := hCfin.coe_toFinset
    have hcS : c ⊆ S := by
      rw [← Finset.coe_subset, hcset]
      exact hCS
    have hc : (VectorMatroid.ofFamily (K := F) U).IsCircuit (c : Set E) := by
      rwa [hcset]
    have hcne : c.Nonempty := by
      rw [← Finset.coe_nonempty, hcset]
      exact hC.nonempty
    have hdis : Disjoint c (S \ c) := by
      apply Finset.disjoint_left.mpr
      intro e hec hed
      exact (Finset.mem_sdiff.mp hed).2 hec
    have hsumc := circuit_sum_eq_zero U hc
    have hsumd : ∑ e ∈ S \ c, U e = 0 := by
      have heq : (∑ e ∈ c, U e) + (∑ e ∈ S \ c, U e) = ∑ e ∈ S, U e := by
        rw [← Finset.sum_union hdis, Finset.union_sdiff_of_subset hcS]
      simpa [hsumc, hs] using heq
    have hd := ih (S \ c) (Finset.sdiff_ssubset hcS hcne) hsumd
    simpa only [Finset.union_sdiff_of_subset hcS] using
      DisjointCircuitUnion.union c (S \ c) hc hdis hd
  · intro h
    induction h with
    | empty => simp
    | union C S hC hdis hS ih =>
      rw [Finset.sum_union hdis, circuit_sum_eq_zero U hC, ih, zero_add]

/-- The coefficient-cycle predicate used in the signed-sum construction has
the ordinary representation-independent matroid meaning. -/
theorem cycle_iff_disjointCircuitUnion [Fintype E] (U : E → V) (x : E → F) :
    Cycle U x ↔
      DisjointCircuitUnion (VectorMatroid.ofFamily (K := F) U) (support x) := by
  rw [cycle_iff_support_sum, sum_eq_zero_iff_disjointCircuitUnion]

/-- Equality of the ordinary represented matroids suffices to identify every
binary coefficient cycle.  No chosen basis or isomorphism of ambient spaces
is assumed. -/
theorem cycle_iff_of_matroid_eq [Fintype E] (U : E → V) (Z : E → W)
    (h : VectorMatroid.ofFamily (K := F) U = VectorMatroid.ofFamily (K := F) Z)
    (x : E → F) : Cycle U x ↔ Cycle Z x := by
  rw [cycle_iff_disjointCircuitUnion, cycle_iff_disjointCircuitUnion, h]

/-- The same invariance holds directly for finite subsets of an arbitrary
label type, without any finiteness assumption on that type. -/
theorem sum_eq_zero_iff_of_matroid_eq (U : E → V) (Z : E → W)
    (h : VectorMatroid.ofFamily (K := F) U = VectorMatroid.ofFamily (K := F) Z)
    (S : Finset E) : (∑ e ∈ S, U e = 0) ↔ (∑ e ∈ S, Z e = 0) := by
  rw [sum_eq_zero_iff_disjointCircuitUnion, sum_eq_zero_iff_disjointCircuitUnion, h]

end Unimodular.BinaryMatroidCycles

#print axioms Unimodular.BinaryMatroidCycles.circuit_sum_eq_zero
#print axioms Unimodular.BinaryMatroidCycles.sum_eq_zero_iff_disjointCircuitUnion
#print axioms Unimodular.BinaryMatroidCycles.cycle_iff_disjointCircuitUnion
#print axioms Unimodular.BinaryMatroidCycles.cycle_iff_of_matroid_eq
#print axioms Unimodular.BinaryMatroidCycles.sum_eq_zero_iff_of_matroid_eq
#check Unimodular.BinaryMatroidCycles.sum_eq_zero_iff_of_matroid_eq
