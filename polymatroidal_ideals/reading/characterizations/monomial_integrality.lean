import Characterizations.ClearDenominators
import Characterizations.IntegralBridge

/-! # Integral equations for every lattice point of a monomial Newton polytope -/

noncomputable section
namespace Characterizations
universe u
open CommAlg.Polymatroid Finset MvPolynomial
open scoped BigOperators
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (k : Type*) [CommRing k]

theorem monomial_power_mem_of_convexHull (B : Family V) (a : Exponent V)
    (ha : realExponent a ∈ convexHull ℝ (realExponent '' (B : Set (Exponent V)))) :
    ∃ N : ℕ, 0 < N ∧ (monomial a (1 : k)) ^ N ∈ (monomialIdeal k B) ^ N := by
  classical
  obtain ⟨N, hN, J, hJ, p, m, hp, hsum, he⟩ := scaled_sum_of_mem_convexHull B a ha
  letI : Fintype J := hJ
  refine ⟨N, hN, ?_⟩
  have hprod : (∏ j, (monomial (p j) (1 : k)) ^ m j) ∈
      ∏ j, (monomialIdeal k B) ^ m j := by
    apply Ideal.prod_mem_prod
    intro j _
    apply Ideal.pow_mem_pow
    exact Ideal.subset_span (Set.mem_image_of_mem _ (hp j))
  have hpow : (∏ j, (monomialIdeal k B) ^ m j) = (monomialIdeal k B) ^ N := by
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  rw [hpow] at hprod
  have hmon : (monomial a (1 : k)) ^ N = ∏ j, (monomial (p j) (1 : k)) ^ m j := by
    simp only [MvPolynomial.monomial_pow, one_pow]
    rw [he]
    simpa using (MvPolynomial.monomial_sum_one (s := Finset.univ)
      (f := fun j => m j • p j) (R := k))
  rw [hmon]
  exact hprod

theorem monomial_integral_of_convexHull [Nontrivial k] (B : Family V) (a : Exponent V)
    (ha : realExponent a ∈ convexHull ℝ (realExponent '' (B : Set (Exponent V)))) :
    CommAlg.IntegralOverIdeal (monomialIdeal k B) (monomial a (1 : k)) := by
  obtain ⟨N, hN, h⟩ := monomial_power_mem_of_convexHull k B a ha
  exact integralOverIdeal_of_pow_mem hN h

end Characterizations
