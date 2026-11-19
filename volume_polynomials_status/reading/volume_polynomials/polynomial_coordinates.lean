module
public import VolumePolynomials.Definitions

@[expose] public section

/-!
# Exact correspondence with homogeneous multivariate polynomials

The finite coordinate convention retains every exponent of total degree `d`.
The mutually inverse coefficient maps below justify this point formally.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace VolumePolynomials

def multiIndexOfDegree {n d : ℕ} (e : Fin n →₀ ℕ) (he : e.degree = d) : MultiIndex n d := by
  have hle : ∀ i, e i ≤ d := by
    intro i
    rw [← he, Finsupp.degree_eq_sum]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)
  exact ⟨fun i => ⟨e i, Nat.lt_succ_of_le (hle i)⟩, by
    simpa only [← Finsupp.degree_eq_sum] using he⟩

@[simp] theorem exponent_multiIndexOfDegree {n d : ℕ} (e : Fin n →₀ ℕ)
    (he : e.degree = d) : exponent (multiIndexOfDegree e he) = e := by
  ext i
  rfl

def coefficientsOfPolynomial {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) : Coefficients n d :=
  fun α => p.coeff (exponent α)

@[simp] theorem coefficientsOfPolynomial_coefficientPolynomial {n d : ℕ}
    (c : Coefficients n d) : coefficientsOfPolynomial (coefficientPolynomial c) = c := by
  funext α
  exact coefficientPolynomial_coeff c α

theorem coefficientPolynomial_coefficientsOfPolynomial {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d) :
    coefficientPolynomial (coefficientsOfPolynomial (d := d) p) = p := by
  classical
  apply MvPolynomial.ext
  intro e
  by_cases he : e.degree = d
  · rw [← exponent_multiIndexOfDegree e he, coefficientPolynomial_coeff]
    rfl
  · have hzero : p.coeff e = 0 := by
      by_contra h
      apply he
      rw [Finsupp.degree_eq_weight_one]
      exact hp h
    have hne : ∀ α : MultiIndex n d, exponent α ≠ e := by
      intro α h
      apply he
      rw [← h]
      exact degree_exponent α
    simp [coefficientPolynomial, MvPolynomial.coeff_monomial, hne, hzero]

/-- All homogeneous degree-`d` polynomials, and only those, are represented by the
finite coefficient vectors used by the geometric realization relation. -/
theorem exists_coefficientPolynomial_iff {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    (∃ c : Coefficients n d, coefficientPolynomial c = p) ↔ p.IsHomogeneous d := by
  constructor
  · rintro ⟨c, rfl⟩
    exact coefficientPolynomial_homogeneous c
  · intro hp
    exact ⟨coefficientsOfPolynomial p, coefficientPolynomial_coefficientsOfPolynomial p hp⟩

theorem realizes_of_homogeneous_polynomial {n d : ℕ} (K : Fin n → Body d)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d)
    (hvol : ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) → MvPolynomial.eval t p = volumeFunction K t) :
    Realizes K (coefficientsOfPolynomial (d := d) p) := by
  intro t ht
  rw [evaluate_eq_polynomial_eval, coefficientPolynomial_coefficientsOfPolynomial p hp]
  exact hvol t ht

end VolumePolynomials
