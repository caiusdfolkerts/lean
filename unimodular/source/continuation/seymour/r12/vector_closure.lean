module

public import Recovery.Unimodular.ProductVectorMatroid
public import Mathlib.Combinatorics.Matroid.Loop

@[expose] public section

/-!
# Closure of an ordinary represented matroid

This complete proof is transported from the recovered
`PriorExtensions/SignedSumsHypotheses.lean`, avoiding unrelated toric geometry
imports. Its dependencies are the same ordinary vector-matroid basis facts.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Unimodular.SeymourCovectors

/-- Closure in the ordinary vector matroid is exactly membership in the
linear span of the indicated original vectors, for arbitrary ground sets. -/
theorem ofFamily_mem_closure_iff {K E V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : E → V) (S : Set E) (e : E) :
    e ∈ (VectorMatroid.ofFamily (K := K) v).closure S ↔
      v e ∈ Submodule.span K (v '' S) := by
  let M := VectorMatroid.ofFamily (K := K) v
  obtain ⟨B, hB⟩ := M.exists_isBasis S (by simp [M])
  have hspan := VectorMatroid.isBasis_span_eq v hB
  rw [← hB.closure_eq_closure, ← hspan]
  have hli : LinearIndepOn K v B := (VectorMatroid.ofFamily_indep v B).mp hB.indep
  by_cases he : e ∈ B
  · exact iff_of_true (M.subset_closure B (by simp [M]) he)
      (Submodule.subset_span ⟨e, he, rfl⟩)
  · rw [hB.indep.mem_closure_iff_of_notMem he]
    simp only [Matroid.dep_iff, M, VectorMatroid.ofFamily_ground, Set.subset_univ,
      and_true, VectorMatroid.ofFamily_indep, linearIndepOn_insert he, hli,
      true_and, not_not]


/-- Equal nonzero represented vectors give an actual two-element circuit. -/
theorem pair_isCircuit_of_eq
    {K E V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : E → V) {e f : E} (hef : e ≠ f) (hf : v f ≠ 0) (heq : v e = v f) :
    (VectorMatroid.ofFamily (K := K) v).IsCircuit {e, f} := by
  have he : (VectorMatroid.ofFamily (K := K) v).IsNonloop e := by
    rw [← Matroid.not_isLoop_iff (by simp), VectorMatroid.ofFamily_isLoop_iff, heq]
    exact hf
  apply (he.closure_eq_closure_iff_isCircuit_of_ne hef).mp
  ext x
  rw [ofFamily_mem_closure_iff, ofFamily_mem_closure_iff,
    Set.image_singleton, Set.image_singleton, heq]

/-- A vector spanned by other labels lies on an actual circuit through its
label. The conclusion retains the complete ordinary circuit predicate. -/
theorem exists_circuit_of_span
    {K E V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : E → V) {S : Set E} {e : E} (heS : e ∉ S)
    (hspan : v e ∈ Submodule.span K (v '' S)) :
    ∃ T, (VectorMatroid.ofFamily (K := K) v).IsCircuit T ∧ e ∈ T ∧ T \ {e} ⊆ S := by
  have hcl := (ofFamily_mem_closure_iff v S e).mpr hspan
  obtain ⟨T, hTsub, hT, heT⟩ := Matroid.exists_isCircuit_of_mem_closure hcl heS
  refine ⟨T, hT, heT, ?_⟩
  intro x hx
  exact (hTsub hx.1).resolve_left hx.2

end Unimodular.SeymourCovectors
