module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Int.Order.Basic
public import Lean.Elab.Tactic.Omega

/-!
# The finite negativity-pattern test

Section 5 replaces tests over every lattice character by finitely many ray
subsets. The integer inequalities below characterize exactly which subsets
occur. This result uses the full character type, with no bound on its values.
-/

@[expose] public noncomputable section

open scoped Classical

namespace ToricPower.FiniteNegativePatterns

variable {Ray Character : Type*} [Fintype Ray]

def negativeSet (value : Ray → ℤ) : Finset Ray :=
  Finset.univ.filter (fun ray => value ray < 0)

@[simp] theorem mem_negativeSet (value : Ray → ℤ) (ray : Ray) :
    ray ∈ negativeSet value ↔ value ray < 0 := by
  simp only [negativeSet, Finset.mem_filter, Finset.mem_univ, true_and]

def latticeFeasible (value : Character → Ray → ℤ) (negative : Finset Ray) : Prop :=
  ∃ character, ∀ ray,
    (ray ∈ negative → value character ray ≤ -1) ∧
    (ray ∉ negative → 0 ≤ value character ray)

theorem latticeFeasible_iff (value : Character → Ray → ℤ) (negative : Finset Ray) :
    latticeFeasible value negative ↔
      ∃ character, negativeSet (value character) = negative := by
  constructor
  · rintro ⟨character, bounds⟩
    refine ⟨character, ?_⟩
    ext ray
    rw [mem_negativeSet]
    constructor
    · intro negativeValue
      by_contra absent
      have nonnegativeValue := (bounds ray).2 absent
      omega
    · intro present
      have negativeValue := (bounds ray).1 present
      omega
  · rintro ⟨character, rfl⟩
    refine ⟨character, fun ray => ?_⟩
    simp only [mem_negativeSet]
    omega

theorem exists_character_iff_finite_pattern (value : Character → Ray → ℤ)
    (test : Finset Ray → Prop) :
    (∃ character, test (negativeSet (value character))) ↔
      ∃ negative ∈ (Finset.univ : Finset Ray).powerset,
        test negative ∧ latticeFeasible value negative := by
  constructor
  · rintro ⟨character, passed⟩
    exact ⟨negativeSet (value character), Finset.mem_powerset.mpr (Finset.subset_univ _),
      passed, (latticeFeasible_iff value _).mpr ⟨character, rfl⟩⟩
  · rintro ⟨negative, _, passed, feasible⟩
    obtain ⟨character, identity⟩ := (latticeFeasible_iff value negative).mp feasible
    exact ⟨character, identity.symm ▸ passed⟩

end ToricPower.FiniteNegativePatterns
