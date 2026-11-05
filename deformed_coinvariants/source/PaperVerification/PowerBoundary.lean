module

public import PaperVerification.PowerFullSupport
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The coordinate boundary of a power-tail quotient

The `i`th layer extracts the product of coordinates strictly greater than `i`
and deletes coordinate `i`. Its actual operator coefficients acquire precisely
the Euler shifts in equation (2.4). The omitted coordinate term is displayed
explicitly; it is divisible by the next full product in the boundary filtration.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerOperators

variable {K : Type*} [Field K] {n : ℕ}
local notation "P" => MvPolynomial (Fin n) K
local notation "P'" => MvPolynomial (Fin (n+1)) K

def boundaryIndices (i : Fin (n+1)) : Finset (Fin (n+1)) :=
  Finset.univ.filter fun j => i < j

def boundaryExponent (i : Fin (n+1)) : Fin (n+1) →₀ ℕ :=
  Finsupp.indicator (boundaryIndices i) (fun _ _ => 1)

def boundaryFactor (i : Fin (n+1)) : P' :=
  ∏ j ∈ boundaryIndices i, X j

theorem boundaryFactor_eq_monomial (i : Fin (n+1)) :
    boundaryFactor (K := K) i = monomial (boundaryExponent i) 1 := by
  simpa only [boundaryFactor, boundaryExponent, pow_one] using
    (prod_X_pow (R := K) (fun _ : Fin (n+1) => 1) (boundaryIndices i))

@[simp] theorem boundaryExponent_apply (i j : Fin (n+1)) :
    boundaryExponent i j = if i < j then 1 else 0 := by
  classical
  simp [boundaryExponent, boundaryIndices, Finsupp.indicator_apply]

theorem euler_boundaryFactor (i j : Fin (n+1)) :
    euler j (boundaryFactor (K := K) i) =
      if i < j then boundaryFactor i else 0 := by
  rw [euler_apply, boundaryFactor_eq_monomial, X_mul_pderiv_monomial,
    boundaryExponent_apply]
  split <;> simp_all only [one_smul, zero_smul, boundaryFactor_eq_monomial]

/-- Renaming into coordinates other than `i` gives polynomials independent of `i`. -/
theorem pderiv_rename_omitted {ι τ : Type*} (f : ι → τ) (i : τ)
    (hi : ∀ j, f j ≠ i) (p : MvPolynomial ι K) :
    pderiv i (rename f p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp =>
    simp only [map_mul, rename_X, pderiv_mul, hp, zero_mul,
      pderiv_X_of_ne (hi j), mul_zero, add_zero]

theorem euler_rename_emb {ι τ : Type*} (f : ι ↪ τ) (j : ι)
    (p : MvPolynomial ι K) :
    euler (f j) (rename f p) = rename f (euler j p) := by
  rw [euler_apply, pderiv_rename f.injective, euler_apply, map_mul, rename_X]

def boundaryLift (i : Fin (n+1)) : P →ₗ[K] P' :=
  (LinearMap.mulLeft K (boundaryFactor i)).comp (rename i.succAbove).toLinearMap

@[simp] theorem boundaryLift_apply (i : Fin (n+1)) (p : P) :
    boundaryLift i p = boundaryFactor i * rename i.succAbove p := rfl

def boundaryShift (i : Fin (n+1)) (j : Fin n) : ℕ :=
  if i < i.succAbove j then 1 else 0

def boundaryCoefficients (c : Fin (n+1) → K) (lam : K) (i : Fin (n+1)) : Fin n → K :=
  fun j => c (i.succAbove j) + lam * (boundaryShift i j : K)

theorem boundary_nonresonant (c : Fin (n+1) → K) (lam : K)
    (m : ℕ) (hnr : Nonresonant c lam m) (i : Fin (n+1)) :
    Nonresonant (boundaryCoefficients c lam i) lam m := by
  exact (hnr.comap i.succAboveEmb).shift (boundaryShift i)

theorem euler_boundaryLift_omitted (i : Fin (n+1)) (p : P) :
    euler i (boundaryLift i p) = 0 := by
  rw [boundaryLift_apply, euler_mul, euler_boundaryFactor]
  simp only [lt_self_iff_false, ite_false, zero_mul, zero_add, euler_apply,
    pderiv_rename_omitted i.succAbove i (fun j => Fin.succAbove_ne i j), mul_zero]

theorem boundary_component (c : Fin (n+1) → K) (lam : K)
    (i : Fin (n+1)) (j : Fin n) (k : ℕ) (p : P) :
    component (c (i.succAbove j)) lam (i.succAbove j) k (boundaryLift i p) =
      boundaryLift i (component (boundaryCoefficients c lam i j) lam j k p) := by
  simp only [component_apply, boundaryLift_apply, euler_mul, euler_boundaryFactor]
  have he : euler (i.succAbove j) (rename i.succAbove p) =
      rename i.succAbove (euler j p) := by
    rw [euler_apply, pderiv_rename Fin.succAbove_right_injective,
      euler_apply, map_mul, rename_X]
  rw [he]
  by_cases hij : i < i.succAbove j
  · simp only [hij, ite_true, boundaryCoefficients, boundaryShift, Nat.cast_one,
      mul_one, map_mul, map_add, map_pow, rename_X, map_smul,
      Algebra.smul_def, MvPolynomial.algebraMap_eq, map_add, map_mul, rename_C]
    ring
  · simp only [hij, ite_false, boundaryCoefficients, boundaryShift, Nat.cast_zero,
      mul_zero, add_zero, zero_mul, zero_add, map_mul, map_add, map_pow,
      rename_X, map_smul, Algebra.smul_def, MvPolynomial.algebraMap_eq,
      map_add, map_mul, rename_C]
    ring

/-- The exact boundary-layer identity, before taking any quotient. -/
theorem reversed_boundaryLift (c : Fin (n+1) → K) (lam : K)
    (i : Fin (n+1)) (k : ℕ) (p : P) :
    reversed c lam k (boundaryLift i p) =
      (c i + lam * (k : K)) • (X i ^ k * boundaryLift i p) +
        boundaryLift i (reversed (boundaryCoefficients c lam i) lam k p) := by
  rw [reversed_apply, Fin.sum_univ_succAbove _ i]
  simp_rw [boundary_component]
  rw [← map_sum, ← reversed_apply, component_apply, euler_boundaryLift_omitted,
    smul_zero, add_zero, mul_smul_comm]

/-- Every polynomial splits into a multiple of the omitted coordinate and
the literal renamed polynomial ring on the remaining coordinates. -/
theorem exists_coordinate_split (i : Fin (n+1)) (p : P') :
    ∃ (q : P') (r : P), p = X i * q + rename i.succAbove r := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp⟩
  | add p q hp hq =>
    obtain ⟨u, v, rfl⟩ := hp
    obtain ⟨u', v', rfl⟩ := hq
    exact ⟨u+u', v+v', by simp only [map_add]; ring⟩
  | mul_X p j hp =>
    by_cases hji : j = i
    · subst j
      exact ⟨p, 0, by simp [mul_comm]⟩
    · obtain ⟨l, rfl⟩ := (Fin.exists_succAbove_eq hji)
      obtain ⟨u, v, rfl⟩ := hp
      exact ⟨u * X (i.succAbove l), v * X l, by
        simp only [map_mul, rename_X]
        ring⟩

end PaperVerification.PowerOperators
