module
public import ideal_integrality_foundation
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Ideal integral dependence and the actual Rees algebra

The monic ideal-equation definition is equivalent to ordinary ring
integrality of `xT` over Mathlib's `reesAlgebra I`.  Taking the coefficient of
`T^n` in an arbitrary monic equation proves the converse without assuming its
coefficients are homogeneous.  This equivalence proves that the elements
integral over an ideal form an actual ideal, over every commutative ring.

This is the ideal integral-closure operation used throughout the
subsequent proof of Corollary 7.2.
-/

noncomputable section

namespace CommAlg

open Polynomial
open scoped BigOperators

universe u
variable {R : Type u} [CommRing R]

/-- Homogenize the coefficient in `I^(n-i)` to degree `n-i` in the actual
Rees algebra.  The resulting monic equation annihilates `xT`. -/
theorem IntegralOverIdeal.isIntegral_rees {I : Ideal R} {x : R}
    (hx : IntegralOverIdeal I x) :
    IsIntegral (reesAlgebra I) (Polynomial.monomial 1 x) := by
  classical
  obtain ⟨n, hn, c, hc, heq⟩ := hx
  let b : Fin n → reesAlgebra I := fun i =>
    ⟨Polynomial.monomial (n - i.val) (c i.val),
      reesAlgebra.monomial_mem.mpr (hc i.val i.isLt)⟩
  let p : Polynomial (reesAlgebra I) :=
    X ^ n + ∑ i : Fin n, C (b i) * X ^ i.val
  have hp : p.Monic := by
    exact monic_X_pow_add (degree_sum_fin_lt b)
  refine ⟨p, hp, ?_⟩
  change aeval (Polynomial.monomial 1 x) p = 0
  have hb (i : Fin n) :
      (b i).val * Polynomial.monomial i.val (x ^ i.val) =
        Polynomial.monomial n (c i.val * x ^ i.val) := by
    dsimp only [b]
    rw [Polynomial.monomial_mul_monomial, Nat.sub_add_cancel i.isLt.le]
  have hpEval : aeval (Polynomial.monomial 1 x) p =
      Polynomial.monomial n (x ^ n + ∑ i : Fin n, c i.val * x ^ i.val) := by
    dsimp only [p]
    simp only [map_add, map_pow, map_sum, map_mul, Polynomial.aeval_X,
      Polynomial.aeval_C]
    change Polynomial.monomial 1 x ^ n +
      ∑ i : Fin n, (b i).val * Polynomial.monomial 1 x ^ i.val = _
    simp only [Polynomial.monomial_pow, one_mul]
    simp_rw [hb]
  rw [hpEval, Fin.sum_univ_eq_sum_range (fun i => c i * x ^ i) n, heq, map_zero]

/-- Extract degree `n` from a monic equation over the Rees algebra.
No homogeneous-coefficient hypothesis is imposed on that equation. -/
theorem integralOverIdeal_of_isIntegral_rees {I : Ideal R} {x : R}
    (hx : IsIntegral (reesAlgebra I) (Polynomial.monomial 1 x)) :
    IntegralOverIdeal I x := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · letI := hR
    apply integralOverIdeal_of_mem
    rw [Subsingleton.elim x 0]
    exact I.zero_mem
  · letI := hR
    obtain ⟨p, hp, hpz⟩ := hx
    have hpne : p ≠ 1 := by
      intro he
      rw [he, Polynomial.eval₂_one] at hpz
      exact one_ne_zero hpz
    let n := p.natDegree
    have hn : 0 < n := hp.natDegree_pos.mpr hpne
    let c : ℕ → R := fun i => ((p.coeff i : reesAlgebra I) : Polynomial R).coeff (n - i)
    refine ⟨n, hn, c, ?_, ?_⟩
    · intro i hi
      exact (p.coeff i).property (n - i)
    · have hEval : aeval (Polynomial.monomial 1 x) p = 0 := hpz
      rw [hp.as_sum] at hEval
      simp only [map_add, map_pow, map_sum, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C] at hEval
      change Polynomial.monomial 1 x ^ n +
        ∑ i ∈ Finset.range n,
          ((p.coeff i : reesAlgebra I) : Polynomial R) * Polynomial.monomial 1 x ^ i = 0
        at hEval
      simp only [Polynomial.monomial_pow, one_mul] at hEval
      have hs :
          (∑ i ∈ Finset.range n,
            ((p.coeff i : reesAlgebra I) : Polynomial R) *
              Polynomial.monomial i (x ^ i)).coeff n =
            ∑ i ∈ Finset.range n, c i * x ^ i := by
        rw [Polynomial.finsetSum_coeff]
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i ≤ n := (Finset.mem_range.mp hi).le
        simpa only [c, Nat.sub_add_cancel hin] using
          Polynomial.coeff_mul_monomial
            ((p.coeff i : reesAlgebra I) : Polynomial R) i (n - i) (x ^ i)
      have hcoeff := congrArg (fun q : Polynomial R => q.coeff n) hEval
      simpa only [Polynomial.coeff_add, Polynomial.coeff_monomial_same,
        hs, Polynomial.coeff_zero] using hcoeff

/-- Ordinary ideal integral dependence agrees exactly with integrality of
the degree-one element over the actual Rees algebra. -/
theorem integralOverIdeal_iff_isIntegral_rees (I : Ideal R) (x : R) :
    IntegralOverIdeal I x ↔
      IsIntegral (reesAlgebra I) (Polynomial.monomial 1 x) :=
  ⟨IntegralOverIdeal.isIntegral_rees, integralOverIdeal_of_isIntegral_rees⟩

theorem IntegralOverIdeal.add {I : Ideal R} {x y : R}
    (hx : IntegralOverIdeal I x) (hy : IntegralOverIdeal I y) :
    IntegralOverIdeal I (x + y) := by
  apply integralOverIdeal_of_isIntegral_rees
  simpa only [map_add] using hx.isIntegral_rees.add hy.isIntegral_rees

theorem IntegralOverIdeal.mul_left {I : Ideal R} {x : R}
    (hx : IntegralOverIdeal I x) (r : R) : IntegralOverIdeal I (r * x) := by
  apply integralOverIdeal_of_isIntegral_rees
  let cr : reesAlgebra I := ⟨Polynomial.C r, (reesAlgebra I).algebraMap_mem r⟩
  have hr : IsIntegral (reesAlgebra I) (Polynomial.C r) :=
    isIntegral_algebraMap (x := cr)
  simpa only [Polynomial.C_mul_monomial] using hr.mul hx.isIntegral_rees

/-- Integral dependence is monotone in the ideal, directly from the
coefficient-power requirements in its defining equation. -/
theorem IntegralOverIdeal.mono {I J : Ideal R} (hIJ : I ≤ J) {x : R}
    (hx : IntegralOverIdeal I x) : IntegralOverIdeal J x := by
  obtain ⟨n, hn, c, hc, heq⟩ := hx
  have hpow : ∀ a : ℕ, I ^ a ≤ J ^ a := by
    intro a
    induction a with
    | zero => exact le_rfl
    | succ a ih => simpa only [pow_succ] using Ideal.mul_mono ih hIJ
  exact ⟨n, hn, c, fun i hi => hpow (n - i) (hc i hi), heq⟩

/-- The actual ideal of elements integral over `I`, with closure under
addition and scalar multiplication proved through the Rees equivalence. -/
def idealIntegralClosure (I : Ideal R) : Ideal R where
  carrier := {x | IntegralOverIdeal I x}
  zero_mem' := integralOverIdeal_of_mem I.zero_mem
  add_mem' hx hy := hx.add hy
  smul_mem' r x hx := by
    change IntegralOverIdeal I (r * x)
    exact hx.mul_left r

@[simp] theorem mem_idealIntegralClosure (I : Ideal R) (x : R) :
    x ∈ idealIntegralClosure I ↔ IntegralOverIdeal I x := Iff.rfl

theorem le_idealIntegralClosure (I : Ideal R) : I ≤ idealIntegralClosure I :=
  fun _ hx => integralOverIdeal_of_mem hx

theorem idealIntegralClosure_mono {I J : Ideal R} (hIJ : I ≤ J) :
    idealIntegralClosure I ≤ idealIntegralClosure J :=
  fun _ hx => hx.mono hIJ

theorem idealIntegralClosure_le_of_integrallyClosed {I J : Ideal R}
    (hIJ : I ≤ J) (hJ : IsIntegrallyClosedIdeal J) : idealIntegralClosure I ≤ J :=
  fun x hx => hJ x (hx.mono hIJ)

theorem integrallyClosedIdeal_iff_integralClosure_eq (I : Ideal R) :
    IsIntegrallyClosedIdeal I ↔ idealIntegralClosure I = I := by
  constructor
  · intro hI
    exact le_antisymm (fun x hx => hI x hx) (le_idealIntegralClosure I)
  · intro hI x hx
    rw [← hI]
    exact hx

end CommAlg
end
