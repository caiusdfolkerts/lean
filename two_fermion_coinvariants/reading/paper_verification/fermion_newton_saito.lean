module

public import PaperVerification.FermionNewtonDeletion
public import PaperVerification.FermionNewtonCramer

/-!
# The determinant criterion for the actual Newton numerator module

All local divisibilities in the Cramer argument are proved here: coordinate
orders contribute their prescribed powers, positive edges contribute one
factor, and negative edges contribute `n-1` factors. Their defining equations
are pairwise relatively prime. Thus the paper's determinant formula, once
established for its explicit columns, constructs a basis of the full module.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open MvPolynomial
open scoped BigOperators Matrix

variable {F : Type*} [Field F] {n : ℕ}

abbrev Hyperplane (n : ℕ) := Fin n ⊕ Edge n

def hyperplaneLinear : Hyperplane n → P (F := F) (n := n)
  | .inl i => X i
  | .inr e => edgeLinear e

def numeratorMultiplicity (δ : Fin n → ℕ) (σ : Fin n → ℤ) : Hyperplane n → ℕ
  | .inl i => δ i
  | .inr e => if σ e.1.1 = 1 then 1 else if σ e.1.1 = -1 then n - 1 else 0

/-- The exact expected numerator determinant divisor. -/
def numeratorDetFactor (δ : Fin n → ℕ) (σ : Fin n → ℤ) : P (F := F) (n := n) :=
  ∏ h : Hyperplane n, hyperplaneLinear h ^ numeratorMultiplicity δ σ h

 theorem hyperplaneLinear_pairwise_relPrime :
    Pairwise (fun a b : Hyperplane n ↦ IsRelPrime (hyperplaneLinear (F := F) a) (hyperplaneLinear b)) := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          apply (MvPolynomial.prime_X (R := F) (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr
          simp only [hyperplaneLinear, MvPolynomial.X_dvd_X]
          exact fun hij ↦ hab (congrArg Sum.inl hij)
      | inr e => exact (edgeLinear_relPrime_X e i).symm
  | inr e =>
      cases b with
      | inl i => exact edgeLinear_relPrime_X e i
      | inr f => exact edgeLinear_pairwise_relPrime (fun hef => hab (congrArg Sum.inr hef))

 theorem numeratorDetFactor_ne_zero (δ : Fin n → ℕ) (σ : Fin n → ℤ) :
    numeratorDetFactor (F := F) δ σ ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro h hh
  apply pow_ne_zero
  cases h with
  | inl i => exact MvPolynomial.X_ne_zero i
  | inr e => exact (edgeLinear_prime e).ne_zero

/-- Every local factor has exactly the divisibility required by the paper's
common-numerator representation. -/
theorem hyperplane_power_dvd_numerator_det (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) (P (F := F) (n := n)))
    (hβ : ∀ i, β i ≠ 0) (hA : ∀ j, (fun i ↦ A i j) ∈ numeratorModule β δ σ)
    (h : Hyperplane n) :
    hyperplaneLinear h ^ numeratorMultiplicity δ σ h ∣ A.det := by
  cases h with
  | inl i =>
      exact row_divisor_dvd_det A i (X i ^ δ i) (fun j ↦ (hA j).1 i)
  | inr e =>
      by_cases hp : σ e.1.1 = 1
      · simp only [hyperplaneLinear, numeratorMultiplicity, if_pos hp, pow_one]
        exact tangent_factor_dvd_det A e.1.1 e.1.2 (ne_of_lt e.2) (edgeLinear e)
          (fun j ↦ (hA j).2.1 e hp)
      · by_cases hn : σ e.1.1 = -1
        · simp only [hyperplaneLinear, numeratorMultiplicity, if_neg hp, if_pos hn]
          have hv : IsUnit (C (β e.1.2) : P (F := F) (n := n)) :=
            (isUnit_iff_ne_zero.mpr (hβ e.1.2)).map MvPolynomial.C
          simpa only [Fintype.card_fin] using
            normal_factor_pow_dvd_det A e.1.1 e.1.2 (ne_of_lt e.2) (edgeLinear e)
              (C (β e.1.1)) (C (β e.1.2)) hv
              (fun j ↦ ((hA j).2.2 e hn).1)
              (fun i hi hj k ↦ ((hA k).2.2 e hn).2 i hi hj)
        · simp [hyperplaneLinear, numeratorMultiplicity, hp, hn]

/-- The common product divides the determinant of any columns in the actual
Newton module, including every replaced-column determinant in Cramer's rule. -/
theorem numeratorDetFactor_dvd_det (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) (P (F := F) (n := n)))
    (hβ : ∀ i, β i ≠ 0) (hA : ∀ j, (fun i ↦ A i j) ∈ numeratorModule β δ σ) :
    numeratorDetFactor δ σ ∣ A.det := by
  apply Fintype.prod_dvd_of_isRelPrime
  · intro h k hhk
    exact (hyperplaneLinear_pairwise_relPrime hhk).pow
  · exact hyperplane_power_dvd_numerator_det β δ σ A hβ hA

/-- An exact determinant factor, up to a unit, proves that the supplied literal
columns are a basis of the entire numerator module. There is no free-module
assumption on that module. -/
def numeratorBasisOfDeterminant (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) (P (F := F) (n := n)))
    (hβ : ∀ i, β i ≠ 0) (hA : ∀ j, (fun i ↦ A i j) ∈ numeratorModule β δ σ)
    (u : P (F := F) (n := n)) (hu : IsUnit u) (hdet : A.det = u * numeratorDetFactor δ σ) :
    Module.Basis (Fin n) (P (F := F) (n := n)) (numeratorModule β δ σ) :=
  basisOfColumnDeterminants (numeratorModule β δ σ) A hA
    (by rw [hdet]; exact mul_ne_zero hu.ne_zero (numeratorDetFactor_ne_zero δ σ))
    (by
      intro v hv j
      rw [hdet]
      apply hu.mul_left_dvd.mpr
      apply numeratorDetFactor_dvd_det β δ σ _ hβ
      intro k
      by_cases hkj : k = j
      · subst k
        simpa only [Matrix.updateCol_self] using hv
      · simpa only [Matrix.updateCol_ne hkj] using hA k)

@[simp] theorem numeratorBasisOfDeterminant_apply (β : Fin n → F) (δ : Fin n → ℕ)
    (σ : Fin n → ℤ) (A : Matrix (Fin n) (Fin n) (P (F := F) (n := n)))
    (hβ : ∀ i, β i ≠ 0) (hA : ∀ j, (fun i ↦ A i j) ∈ numeratorModule β δ σ)
    (u : P (F := F) (n := n)) (hu : IsUnit u) (hdet : A.det = u * numeratorDetFactor δ σ)
    (j : Fin n) :
    ((numeratorBasisOfDeterminant β δ σ A hβ hA u hu hdet j : numeratorModule β δ σ) :
      Fin n → P (F := F) (n := n)) = fun i ↦ A i j :=
  basisOfColumnDeterminants_apply _ _ _ _ _ j

end PaperVerification.Fermion.Newton
