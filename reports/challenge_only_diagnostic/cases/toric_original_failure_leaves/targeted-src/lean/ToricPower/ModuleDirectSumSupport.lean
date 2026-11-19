module

public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Removing only proved-zero summands from an unrestricted direct sum

Restriction to a predicate is a linear equivalence when every omitted
summand is already proved to be zero. The retained index set need not be
finite. The comparison is the literal restriction of coefficients.
-/

@[expose] public noncomputable section

open scoped Classical

namespace ToricPower

universe u v w

variable (R : Type u) [Semiring R] {I : Type v} (M : I → Type w)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  (p : I → Prop) (outside : ∀ i, ¬ p i → Subsingleton (M i))

include outside in
/-- Restriction is injective because every omitted coefficient is
already the unique element of its own zero module. -/
theorem directSumSubtype_injective :
    Function.Injective (DFinsupp.subtypeDomainLinearMap R M p) := by
  intro x y equal
  ext i
  by_cases present : p i
  · exact congrArg (fun z => z (⟨i,present⟩ : Subtype p)) equal
  · letI := outside i present
    exact Subsingleton.elim _ _

theorem directSumSubtype_single (i : Subtype p) (x : M i.val) :
    DFinsupp.subtypeDomainLinearMap R M p (DFinsupp.single i.val x) =
      DFinsupp.single i x := by
  ext j
  by_cases equal : j = i
  · subst j
    simp only [DFinsupp.subtypeDomainLinearMap_apply, DFinsupp.subtypeDomain_apply,
      DFinsupp.single_eq_same]
  · have distinct : j.val ≠ i.val := fun h => equal (Subtype.ext h)
    simp only [DFinsupp.subtypeDomainLinearMap_apply, DFinsupp.subtypeDomain_apply,
      DFinsupp.single_eq_of_ne distinct, DFinsupp.single_eq_of_ne equal]

/-- Every finite retained coefficient family lifts by the same literal
single-coordinate insertions, without a finite bound on its index set. -/
theorem directSumSubtype_surjective :
    Function.Surjective (DFinsupp.subtypeDomainLinearMap R M p) := by
  intro x
  induction x using DFinsupp.induction with
  | h0 => exact ⟨0, map_zero _⟩
  | ha i a x hi ha ih =>
      obtain ⟨y, rfl⟩ := ih
      refine ⟨DFinsupp.single i.val a + y, ?_⟩
      rw [map_add, directSumSubtype_single]

/-- An actual linear equivalence deleting exactly the proved-zero
summands and retaining every other coefficient unchanged. -/
def directSumSubtypeEquiv : (Π₀ i, M i) ≃ₗ[R] Π₀ i : Subtype p, M i.val :=
  LinearEquiv.ofBijective (DFinsupp.subtypeDomainLinearMap R M p)
    ⟨directSumSubtype_injective R M p outside, directSumSubtype_surjective R M p⟩

@[simp]
theorem directSumSubtypeEquiv_apply (x : Π₀ i, M i) (j : Subtype p) :
    directSumSubtypeEquiv R M p outside x j = x j.val := rfl

end ToricPower

end
