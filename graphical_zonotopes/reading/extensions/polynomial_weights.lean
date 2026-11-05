module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Extremal weights of polynomial support

The coefficient ring of `gradeLift` retains every original monomial. Distinct
monomials of the same weight therefore cannot cancel merely because their
weights agree. Ordinary univariate degree and trailing degree then prove
additivity of the largest and smallest support weights over an integral domain.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GraphicalZonotopes.PolynomialWeights

variable {σ R : Type*} [CommSemiring R]

/-- The nonnegative integer weight of an exponent vector. -/
def weight (w : σ → ℕ) (d : σ →₀ ℕ) : ℕ :=
  d.sum fun i k => w i * k

/-- Adjoin a variable recording weight, while retaining the original monomial
in the coefficient ring. -/
def gradeLift (w : σ → ℕ) :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i)

@[simp]
theorem gradeLift_monomial (w : σ → ℕ) (d : σ →₀ ℕ) (a : R) :
    gradeLift w (MvPolynomial.monomial d a) =
      Polynomial.monomial (weight w d) (MvPolynomial.monomial d a) := by
  classical
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.monomial d a) = _
  rw [MvPolynomial.eval₂Hom_monomial]
  calc
    (Polynomial.C.comp MvPolynomial.C) a *
        d.prod (fun i k => (Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ w i) ^ k) =
      Polynomial.C (MvPolynomial.C a) *
        (Polynomial.C (d.prod fun i k => (MvPolynomial.X i : MvPolynomial σ R) ^ k) *
          Polynomial.X ^ weight w d) := by
            simp only [RingHom.comp_apply, Finsupp.prod, Finsupp.sum, weight,
              mul_pow, ← map_pow, Finset.prod_mul_distrib, ← map_prod,
              ← pow_mul, Finset.prod_pow_eq_pow_sum]
    _ = Polynomial.C (MvPolynomial.monomial d a) * Polynomial.X ^ weight w d := by
      simp only [MvPolynomial.monomial_eq, map_mul, mul_assoc]
    _ = _ := Polynomial.C_mul_X_pow_eq_monomial

/-- Expansion of the lift into its original monomials. -/
theorem gradeLift_eq_sum (w : σ → ℕ) (p : MvPolynomial σ R) :
    gradeLift w p = ∑ d ∈ p.support,
      Polynomial.monomial (weight w d) (MvPolynomial.monomial d (p.coeff d)) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum]
  exact Finset.sum_congr rfl fun d _ => gradeLift_monomial w d (p.coeff d)

/-- Taking first the weight coefficient and then the original monomial
coefficient recovers the original coefficient exactly. -/
theorem coeff_gradeLift (w : σ → ℕ) (p : MvPolynomial σ R)
    (k : ℕ) (e : σ →₀ ℕ) :
    ((gradeLift w p).coeff k).coeff e =
      if weight w e = k then p.coeff e else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
      rw [gradeLift_monomial, Polynomial.coeff_monomial]
      by_cases hde : d = e
      · subst d
        by_cases hw : weight w e = k <;> simp [hw]
      · have hzero : (MvPolynomial.monomial d a).coeff e = 0 := by
          simp [hde]
        by_cases hw : weight w d = k <;> simp [hw, hzero]
  | add p q hp hq =>
      simp only [map_add, Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
      split_ifs <;> simp

/-- The lift records exactly the weights occurring in the original support. -/
theorem support_gradeLift (w : σ → ℕ) (p : MvPolynomial σ R) :
    (gradeLift w p).support = p.support.image (weight w) := by
  classical
  ext k
  rw [Polynomial.mem_support_iff, Finset.mem_image]
  constructor
  · intro hk
    obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hk
    rw [coeff_gradeLift] at hd
    split_ifs at hd with hwd
    · exact ⟨d, MvPolynomial.mem_support_iff.mpr hd, hwd⟩
    · exact False.elim (hd rfl)
  · rintro ⟨d, hd, hwd⟩ hzero
    have hcoeff := congrArg (fun q : MvPolynomial σ R => q.coeff d) hzero
    rw [coeff_gradeLift, hwd, if_pos rfl, MvPolynomial.coeff_zero] at hcoeff
    exact MvPolynomial.mem_support_iff.mp hd hcoeff

@[simp]
theorem gradeLift_eq_zero_iff (w : σ → ℕ) (p : MvPolynomial σ R) :
    gradeLift w p = 0 ↔ p = 0 := by
  constructor
  · intro h
    apply MvPolynomial.ext
    intro d
    have hc := congrArg
      (fun q : Polynomial (MvPolynomial σ R) => (q.coeff (weight w d)).coeff d) h
    simpa [coeff_gradeLift] using hc
  · rintro rfl
    exact map_zero _

theorem gradeLift_ne_zero (w : σ → ℕ) {p : MvPolynomial σ R} (hp : p ≠ 0) :
    gradeLift w p ≠ 0 :=
  (gradeLift_eq_zero_iff w p).not.mpr hp

/-- Smallest support weight, with value zero on the zero polynomial. -/
def minWeight (w : σ → ℕ) (p : MvPolynomial σ R) : ℕ :=
  (gradeLift w p).natTrailingDegree

/-- Largest support weight, with value zero on the zero polynomial. -/
def maxWeight (w : σ → ℕ) (p : MvPolynomial σ R) : ℕ :=
  (gradeLift w p).natDegree

theorem minWeight_le_of_mem_support (w : σ → ℕ) {p : MvPolynomial σ R}
    {d : σ →₀ ℕ} (hd : d ∈ p.support) : minWeight w p ≤ weight w d := by
  classical
  apply Polynomial.natTrailingDegree_le_of_mem_supp
  rw [support_gradeLift]
  exact Finset.mem_image_of_mem _ hd

theorem weight_le_maxWeight_of_mem_support (w : σ → ℕ) {p : MvPolynomial σ R}
    {d : σ →₀ ℕ} (hd : d ∈ p.support) : weight w d ≤ maxWeight w p := by
  classical
  apply Polynomial.le_natDegree_of_mem_supp
  rw [support_gradeLift]
  exact Finset.mem_image_of_mem _ hd

theorem exists_weight_eq_minWeight (w : σ → ℕ) {p : MvPolynomial σ R}
    (hp : p ≠ 0) : ∃ d ∈ p.support, weight w d = minWeight w p := by
  classical
  have h := Polynomial.natTrailingDegree_mem_support_of_nonzero (gradeLift_ne_zero w hp)
  rw [support_gradeLift] at h
  exact Finset.mem_image.mp h

theorem exists_weight_eq_maxWeight (w : σ → ℕ) {p : MvPolynomial σ R}
    (hp : p ≠ 0) : ∃ d ∈ p.support, weight w d = maxWeight w p := by
  classical
  have h := Polynomial.natDegree_mem_support_of_nonzero (gradeLift_ne_zero w hp)
  rw [support_gradeLift] at h
  exact Finset.mem_image.mp h

theorem minWeight_le_maxWeight (w : σ → ℕ) (p : MvPolynomial σ R) :
    minWeight w p ≤ maxWeight w p :=
  Polynomial.natTrailingDegree_le_natDegree _

theorem le_minWeight_iff (w : σ → ℕ) {p : MvPolynomial σ R}
    (hp : p ≠ 0) (k : ℕ) :
    k ≤ minWeight w p ↔ ∀ d ∈ p.support, k ≤ weight w d := by
  constructor
  · intro hk d hd
    exact hk.trans (minWeight_le_of_mem_support w hd)
  · intro h
    obtain ⟨d, hd, hwd⟩ := exists_weight_eq_minWeight w hp
    exact hwd ▸ h d hd

theorem maxWeight_le_iff (w : σ → ℕ) {p : MvPolynomial σ R}
    (hp : p ≠ 0) (k : ℕ) :
    maxWeight w p ≤ k ↔ ∀ d ∈ p.support, weight w d ≤ k := by
  constructor
  · intro hk d hd
    exact (weight_le_maxWeight_of_mem_support w hd).trans hk
  · intro h
    obtain ⟨d, hd, hwd⟩ := exists_weight_eq_maxWeight w hp
    exact hwd ▸ h d hd

section Domain

variable [NoZeroDivisors R]

/-- Lowest weights add: cancellation cannot remove the product of the
lowest nonzero homogeneous components. -/
theorem minWeight_mul (w : σ → ℕ) {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    minWeight w (p * q) = minWeight w p + minWeight w q := by
  unfold minWeight
  rw [map_mul]
  exact Polynomial.natTrailingDegree_mul (gradeLift_ne_zero w hp) (gradeLift_ne_zero w hq)

/-- Highest weights add over a domain as well. -/
theorem maxWeight_mul (w : σ → ℕ) {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    maxWeight w (p * q) = maxWeight w p + maxWeight w q := by
  unfold maxWeight
  rw [map_mul]
  exact Polynomial.natDegree_mul (gradeLift_ne_zero w hp) (gradeLift_ne_zero w hq)

end Domain

section FiniteVariables

variable [Fintype σ]

theorem weight_eq_sum (w : σ → ℕ) (d : σ →₀ ℕ) :
    weight w d = ∑ i, w i * d i := by
  classical
  exact d.sum_fintype (fun i k => w i * k) (fun _ => mul_zero _)

theorem weight_indicator [DecidableEq σ] (S : Finset σ) (d : σ →₀ ℕ) :
    weight (fun i => if i ∈ S then 1 else 0) d = ∑ i ∈ S, d i := by
  classical
  rw [weight_eq_sum]
  simp [ite_mul, Finset.sum_ite_mem]

theorem weight_one (d : σ →₀ ℕ) : weight (fun _ : σ => 1) d = ∑ i, d i := by
  rw [weight_eq_sum]
  simp

theorem weight_add (w : σ → ℕ) (d e : σ →₀ ℕ) :
    weight w (d + e) = weight w d + weight w e := by
  simp only [weight_eq_sum, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

end FiniteVariables

end GraphicalZonotopes.PolynomialWeights
