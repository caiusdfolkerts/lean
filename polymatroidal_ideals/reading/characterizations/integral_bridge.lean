import CommAlg.IntegralClosure.Ideal
import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.Algebra.Polynomial.RingDivision

/-! # From actual Rees-algebra integrality to ideal integrality

This supplies addition and multiplication closure for the monomials proved
integral by a power-membership witness. The final conclusion is the ordinary
monic ideal-integrality equation, not a substitute definition.
-/

noncomputable section
namespace Characterizations
open Polynomial CommAlg
open scoped BigOperators
variable {R : Type*} [CommRing R]

def reesIntegralIdeal (I : Ideal R) : Ideal R where
  carrier := {x | IsIntegral (reesAlgebra I) (C x * X : R[X])}
  zero_mem' := by simpa using (isIntegral_zero : IsIntegral (reesAlgebra I) (0 : R[X]))
  add_mem' hx hy := by simpa [map_add, add_mul] using hx.add hy
  smul_mem' r x hx := by
    have hr : IsIntegral (reesAlgebra I) (C r : R[X]) := by
      exact isIntegral_algebraMap (R := reesAlgebra I) (A := R[X])
        (x := algebraMap R (reesAlgebra I) r)
    simpa [smul_eq_mul, map_mul, mul_assoc] using hr.mul hx

theorem mem_reesIntegralIdeal_of_pow_mem {I : Ideal R} {x : R} {n : ℕ}
    (hn : 0 < n) (hx : x ^ n ∈ I ^ n) : x ∈ reesIntegralIdeal I := by
  have hmem : (C x * X : R[X]) ^ n ∈ reesAlgebra I := by
    simpa [← Polynomial.C_mul_X_pow_eq_monomial, mul_pow] using
      (reesAlgebra.monomial_mem.mpr hx : Polynomial.monomial n (x ^ n) ∈ reesAlgebra I)
  have hi : IsIntegral (reesAlgebra I) ((C x * X : R[X]) ^ n) :=
    isIntegral_algebraMap (R := reesAlgebra I) (A := R[X]) (x := ⟨_, hmem⟩)
  exact IsIntegral.of_pow hn hi

theorem adjoin_C_mul_X_eq_rees (I : Ideal R) :
    Algebra.adjoin R {C r * X | r ∈ I} = reesAlgebra I := by
  rw [← adjoin_monomial_eq_reesAlgebra I]
  congr 1
  ext p
  simp only [Submodule.mem_map, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, by simp [← Polynomial.C_mul_X_pow_eq_monomial]⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, by simp [← Polynomial.C_mul_X_pow_eq_monomial]⟩

theorem integralOverIdeal_of_mem_reesIntegralIdeal [Nontrivial R] {I : Ideal R} {x : R}
    (hx : x ∈ reesIntegralIdeal I) : IntegralOverIdeal I x := by
  have hi : IsIntegral (Algebra.adjoin R {C r * X | r ∈ I}) (C x * X : R[X]) := by
    rw [adjoin_C_mul_X_eq_rees]
    exact hx
  have hAlg : Polynomial.algebra R R = Algebra.id R[X] := by
    apply Algebra.algebra_ext
    intro p
    simp [Polynomial.algebra]
  have ht := Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral
    (R := R) (S := R) (I := I) (x := x)
  rw [hAlg] at ht
  obtain ⟨p, hp, he, hc⟩ := ht hi
  refine ⟨p.natDegree, Polynomial.natDegree_pos_of_monic_of_aeval_eq_zero hp he,
    fun i => p.coeff i, fun i _ => hc i, ?_⟩
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ] at he
  simpa only [smul_eq_mul, hp.coeff_natDegree, one_mul, add_comm] using he

theorem integralOverIdeal_of_pow_mem [Nontrivial R] {I : Ideal R} {x : R} {n : ℕ}
    (hn : 0 < n) (hx : x ^ n ∈ I ^ n) : IntegralOverIdeal I x :=
  integralOverIdeal_of_mem_reesIntegralIdeal (mem_reesIntegralIdeal_of_pow_mem hn hx)

/-- Ideal-span induction transfers finitely many monomial power witnesses to
every polynomial in the generated ideal, with a genuine integral equation. -/
theorem integralOverIdeal_of_span_generators [Nontrivial R] {I : Ideal R} (S : Set R)
    (hS : ∀ x ∈ S, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ I ^ n)
    {x : R} (hx : x ∈ Ideal.span S) : IntegralOverIdeal I x := by
  apply integralOverIdeal_of_mem_reesIntegralIdeal
  apply (Ideal.span_le.mpr (fun y hy => ?_) : Ideal.span S ≤ reesIntegralIdeal I) hx
  obtain ⟨n, hn, hp⟩ := hS y hy
  exact mem_reesIntegralIdeal_of_pow_mem hn hp

end Characterizations
