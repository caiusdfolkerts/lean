module
public import graph_foundation.part014
public import shared_results.part020_integer_filtered_homology_pieces

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.HomogeneousWeightFiltration -/
section

/-! # From the paper's componentwise hypotheses to the global filtration

Every element has finitely many homogeneous components. Therefore
exhaustiveness and separatedness on the actual homogeneous pieces imply
the global properties used in the Rees-quotient construction. This is
proved rather than added as a stronger hypothesis on the algebra.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace FourPapers.IntegerFiltered

open Classical DirectSum
open scoped BigOperators

variable {K A Γ : Type*} [CommRing K] [Ring A] [Algebra K A] [DecidableEq Γ]
  (P : Γ → Submodule K A) [DirectSum.Decomposition P]
  (level : ℤ → Submodule K A) (mono : Monotone level)

include mono in
theorem exhaustive_of_homogeneous_components
    (hex : ∀ i x,x∈P i→∃ n,x∈level n) : ∀ x : A,∃ n,x∈level n := by
  intro x
  choose n hn using fun i => hex i (DirectSum.decompose P x i).val
    (DirectSum.decompose P x i).property
  let s := (DirectSum.decompose P x).support
  let N : ℤ := ∑ i∈s,max 0 (n i)
  refine ⟨N,?_⟩
  rw [← DirectSum.sum_support_decompose P x]
  apply Submodule.sum_mem
  intro i hi
  apply mono (show n i≤N from ?_) (hn i)
  exact (le_max_right 0 (n i)).trans
    (Finset.single_le_sum (fun j _ => le_max_left 0 (n j)) hi)

theorem separated_of_homogeneous_components
    (hhom : ∀ n,SetLike.IsHomogeneous P (level n))
    (hsep : ∀ i x,x∈P i→(∀ n,x∈level n)→x=0) :
    ∀ x : A,(∀ n,x∈level n)→x=0 := by
  intro x hx
  rw [← DirectSum.sum_support_decompose P x]
  apply Finset.sum_eq_zero
  intro i _
  exact hsep i (DirectSum.decompose P x i).val
    (DirectSum.decompose P x i).property (fun n => hhom n i (hx n))

/-- Construct the actual integer weight filtration from precisely the
componentwise exhaustion and separation appearing in Proposition 3.1. -/
def multiplicativeFiltrationOfComponents
    (hhom : ∀ n,SetLike.IsHomogeneous P (level n))
    (hex : ∀ i x,x∈P i→∃ n,x∈level n)
    (hsep : ∀ i x,x∈P i→(∀ n,x∈level n)→x=0)
    (h1 : (1 : A)∈level 0)
    (hmul : ∀ i j,∀ x∈level i,∀ y∈level j,x*y∈level (i+j)) :
    MultiplicativeFiltration K A where
  level := level
  mono := mono
  exhaustive := exhaustive_of_homogeneous_components P level mono hex
  separated := separated_of_homogeneous_components P level hhom hsep
  one_mem := h1
  mul_mem := hmul

end FourPapers.IntegerFiltered

end
end
end


end
