module

public import PaperVerification.FermionNewtonNumerators

/-!
# Divisibility detected by identifying two coordinates

The hyperplane tests below concern the actual polynomial numerator, not a
formal residue symbol. They reduce tangency and cancellation of opposite
simple poles to ordinary polynomial equalities after identifying the two
coordinates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

def identifyCoordinates (i j : Fin n) : P (F := F) (n := n) →ₐ[F] (P (F := F) (n := n)) :=
  aeval fun k ↦ if k = i then X j else X k

@[simp] theorem identifyCoordinates_X (i j k : Fin n) :
    identifyCoordinates (F := F) i j (X k) = if k = i then X j else X k := by
  simp only [identifyCoordinates, aeval_X]

theorem identifyCoordinates_eq_comp (i j : Fin n) (hij : i ≠ j) :
    identifyCoordinates (F := F) i j =
      (coordinateRestriction i).comp (coordinateShear i j hij).symm.toAlgHom := by
  ext k
  by_cases hk : k = i
  · subst k
    simp [identifyCoordinates, coordinateRestriction, coordinateShear, hij, Ne.symm hij]
  · simp [identifyCoordinates, coordinateRestriction, coordinateShear, hk]

theorem identifyCoordinates_eq_zero_iff (i j : Fin n) (hij : i ≠ j) (p : P (F := F) (n := n)) :
    identifyCoordinates i j p = 0 ↔ (X i - X j) ∣ p := by
  rw [identifyCoordinates_eq_comp i j hij]
  change coordinateRestriction i ((coordinateShear i j hij).symm p) = 0 ↔ _
  rw [coordinateRestriction_eq_zero_iff]
  constructor
  · intro hp
    have h := map_dvd (coordinateShear (F := F) i j hij) hp
    simpa only [coordinateShear_X_self, AlgEquiv.apply_symm_apply] using h
  · intro hp
    rw [← coordinateShear_X_self i j hij] at hp
    have h := map_dvd (coordinateShear (F := F) i j hij).symm hp
    simpa only [AlgEquiv.symm_apply_apply] using h

theorem identifyCoordinates_self_sub (i j : Fin n) (hij : i ≠ j) :
    identifyCoordinates (F := F) i j (X i - X j) = 0 := by
  simp only [map_sub, identifyCoordinates_X, if_pos rfl, if_true, if_neg (Ne.symm hij), sub_self]

theorem identifyCoordinates_star_ne_zero
    (a b k j : Fin n) (hab : a ≠ b) (hkj : k ≠ j)
    (hnotpair : ¬ (k = a ∧ j = b) ∧ ¬ (k = b ∧ j = a)) :
    identifyCoordinates (F := F) a b (X k - X j) ≠ 0 := by
  rw [map_sub, identifyCoordinates_X, identifyCoordinates_X]
  intro hz
  have he : (if k = a then b else k) = (if j = a then b else j) := by
    apply MvPolynomial.X_injective (R := F)
    simpa only [apply_ite] using sub_eq_zero.mp hz
  by_cases hka : k = a
  · by_cases hja : j = a
    · exact hkj (hka.trans hja.symm)
    · simp only [hka, hja, if_true, if_false] at he
      exact hnotpair.1 ⟨hka, he.symm⟩
  · by_cases hja : j = a
    · simp only [hka, hja, if_false, if_true] at he
      exact hnotpair.2 ⟨he, hja⟩
    · simp only [hka, hja, if_false] at he
      exact hkj he

section AlgebraicTests

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

/-- If a denominator does not vanish on a hyperplane, a common numerator
vanishes there whenever the common denominator does. -/
theorem numerator_vanishes_of_regular_denominator
    (φ : R →+* S) (Q N D A : R)
    (hA : D * A = Q * N) (hQ : φ Q = 0) (hD : φ D ≠ 0) : φ A = 0 := by
  have h := congrArg φ hA
  rw [map_mul, map_mul, hQ, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hD

/-- Equal evaluations of numerator and denominator give equal evaluations
of the cleared rational functions, without requiring the common denominator
itself to survive restriction. -/
theorem numerator_evaluations_eq_of_fraction_data
    (φ : R →+* S) (Q N₁ N₂ D₁ D₂ A₁ A₂ : R)
    (h₁ : D₁ * A₁ = Q * N₁) (h₂ : D₂ * A₂ = Q * N₂)
    (hD : φ D₁ ≠ 0) (hDeq : φ D₁ = φ D₂) (hNeq : φ N₁ = φ N₂) :
    φ A₁ = φ A₂ := by
  apply mul_left_cancel₀ hD
  have h₁' := congrArg φ h₁
  have h₂' := congrArg φ h₂
  simp only [map_mul] at h₁' h₂'
  rw [h₁', hDeq, h₂', hNeq]

/-- A single common factor is canceled in the polynomial ring before
restriction. This is the exact algebraic step behind a simple-pole residue. -/
theorem cancel_common_pole
    (p Q N D A : R) (hp : p ≠ 0)
    (h : (p * D) * A = (p * Q) * N) : D * A = Q * N := by
  apply mul_left_cancel₀ hp
  simpa only [mul_assoc] using h

/-- Opposite simple-pole denominators and matching weighted numerators
force the weighted numerator sum to vanish on the hyperplane. -/
theorem weighted_opposite_poles_cancel
    (φ : R →+* S) (p Q N₁ N₂ D₁ D₂ A₁ A₂ u v : R)
    (hp : p ≠ 0)
    (h₁ : (p * D₁) * A₁ = (p * Q) * N₁)
    (h₂ : ((-p) * D₂) * A₂ = (p * Q) * N₂)
    (hD : φ D₁ ≠ 0) (hDeq : φ D₁ = φ D₂)
    (hN : φ u * φ N₁ = φ v * φ N₂) :
    φ (u * A₁ + v * A₂) = 0 := by
  have h₁' := cancel_common_pole p Q N₁ D₁ A₁ hp h₁
  have h₂' : D₂ * A₂ = -(Q * N₂) := by
    apply mul_left_cancel₀ hp
    have he : p * (D₂ * A₂) = -(p * (Q * N₂)) := by
      have hneg := congrArg Neg.neg h₂
      simpa only [neg_mul, mul_assoc, neg_neg] using hneg
    simpa only [mul_neg] using he
  apply (mul_eq_zero.mp (show φ D₁ * φ (u * A₁ + v * A₂) = 0 from ?_)).resolve_left hD
  have h₁m := congrArg φ h₁'
  have h₂m := congrArg φ h₂'
  simp only [map_mul, map_neg] at h₁m h₂m
  rw [map_add, map_mul, map_mul, mul_add]
  calc
    φ D₁ * (φ u * φ A₁) + φ D₁ * (φ v * φ A₂) =
        φ u * (φ D₁ * φ A₁) + φ v * (φ D₂ * φ A₂) := by rw [← hDeq]; ring
    _ = φ Q * (φ u * φ N₁ - φ v * φ N₂) := by rw [h₁m, h₂m]; ring
    _ = 0 := by rw [hN, sub_self, mul_zero]

end AlgebraicTests

end PaperVerification.Fermion.Newton
