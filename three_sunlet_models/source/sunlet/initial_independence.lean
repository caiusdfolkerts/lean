module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Finset.Max

/-! Algebraic independence from independent leading exponents, over every field.
The exponent calculation takes place over ℚ; the coefficient field has no
characteristic restriction. -/

@[expose] public section
noncomputable section
open scoped BigOperators MonomialOrder
open MvPolynomial

namespace Sunlet.InitialIndependence

variable {K ι σ : Type*} [Field K] [Fintype ι]

def exponentCombination (D : ι → σ →₀ ℕ) (d : ι →₀ ℕ) : σ →₀ ℕ :=
  ∑ i, d i • D i

lemma degree_aeval_monomial (m : MonomialOrder σ) (f : ι → MvPolynomial σ K)
    (hf : ∀ i, f i ≠ 0) (d : ι →₀ ℕ) {c : K} (hc : c ≠ 0) :
    m.degree (aeval f (monomial d c)) = exponentCombination (fun i => m.degree (f i)) d := by
  classical
  rw [aeval_monomial]
  have hprod : d.prod (fun i k => f i ^ k) = ∏ i, f i ^ d i := by
    exact Finsupp.prod_fintype _ _ (by intro i; simp)
  rw [hprod]
  change m.degree (C c * ∏ i, f i ^ d i) = _
  rw [m.degree_mul (by simpa using hc) (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hf i))),
    m.degree_C, zero_add]
  rw [m.degree_prod (fun i _ => pow_ne_zero _ (hf i))]
  simp only [m.degree_pow, exponentCombination]

lemma aeval_monomial_ne_zero (f : ι → MvPolynomial σ K)
    (hf : ∀ i, f i ≠ 0) (d : ι →₀ ℕ) {c : K} (hc : c ≠ 0) :
    aeval f (monomial d c) ≠ 0 := by
  classical
  rw [aeval_monomial]
  apply mul_ne_zero
  · change C c ≠ 0
    simpa using hc
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (hf i)

/-- Distinct exponent sums prevent every possible polynomial relation. -/
theorem algebraicIndependent_of_injective_exponentCombination
    (m : MonomialOrder σ) (f : ι → MvPolynomial σ K)
    (hf : ∀ i, f i ≠ 0)
    (hinj : Function.Injective (exponentCombination (fun i => m.degree (f i)))) :
    AlgebraicIndependent K f := by
  classical
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hpn
  let T : (ι →₀ ℕ) → MvPolynomial σ K := fun d => aeval f (monomial d (p.coeff d))
  have hT (d : ι →₀ ℕ) (hd : d ∈ p.support) : T d ≠ 0 :=
    aeval_monomial_ne_zero f hf d (mem_support_iff.mp hd)
  have hdegree (d : ι →₀ ℕ) (hd : d ∈ p.support) :
      m.degree (T d) = exponentCombination (fun i => m.degree (f i)) d :=
    degree_aeval_monomial m f hf d (mem_support_iff.mp hd)
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image p.support
    (fun e => m.toSyn (m.degree (T e))) (support_nonempty.mpr hpn)
  have hcoeff : (aeval f p).coeff (m.degree (T d)) = (T d).coeff (m.degree (T d)) := by
    conv_lhs => rw [p.as_sum, map_sum, coeff_sum]
    change (∑ e ∈ p.support, (T e).coeff (m.degree (T d))) = _
    apply Finset.sum_eq_single d
    · intro e he hne
      apply m.coeff_eq_zero_of_lt
      apply lt_of_le_of_ne (hmax e he)
      intro heq
      have heq' := m.toSyn.injective heq
      rw [hdegree e he, hdegree d hd] at heq'
      exact hne (hinj heq')
    · exact fun h => (h hd).elim
  have hnonzero : (T d).coeff (m.degree (T d)) ≠ 0 :=
    m.leadingCoeff_ne_zero_iff.mpr (hT d hd)
  apply hnonzero
  simpa [hp] using hcoeff.symm

end Sunlet.InitialIndependence
