module

public import PaperVerification.AlternatingFormsNormalizedBand
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Algebraic independence from distinct weighted leading monomials

The criterion uses the actual multiplication and evaluation maps. It applies
to integer weights, with no term-order assumption: the support of each
individual polynomial is finite, and its displayed top term is unique.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial

namespace PaperVerification.AlternatingForms

variable {K σ ι : Type*} [Field K]

theorem IsWeightMonic.weight_le {w : σ → ℤ} {p : MvPolynomial σ K} {a b : σ →₀ ℕ}
    (hp : IsWeightMonic w p a) (hb : p.coeff b ≠ 0) :
    Finsupp.weight w b ≤ Finsupp.weight w a := by
  by_contra h
  have hlt := lt_of_not_ge h
  exact hb (hp.2 b (fun he => hlt.ne (congrArg (Finsupp.weight w) he).symm) hlt.le)

theorem IsWeightMonic.eq_of_weight_ge {w : σ → ℤ} {p : MvPolynomial σ K} {a b : σ →₀ ℕ}
    (hp : IsWeightMonic w p a) (hb : p.coeff b ≠ 0)
    (hw : Finsupp.weight w a ≤ Finsupp.weight w b) : b=a := by
  by_contra he
  exact hb (hp.2 b he hw)

theorem IsWeightMonic.mul {w : σ → ℤ} {p q : MvPolynomial σ K} {a b : σ →₀ ℕ}
    (hp : IsWeightMonic w p a) (hq : IsWeightMonic w q b) :
    IsWeightMonic w (p*q) (a+b) := by
  classical
  have hterm {z : σ →₀ ℕ} (x : (σ →₀ ℕ) × (σ →₀ ℕ))
      (hx : x.1+x.2=z) (hc : p.coeff x.1 * q.coeff x.2 ≠ 0)
      (hw : Finsupp.weight w (a+b) ≤ Finsupp.weight w z) : x=(a,b) := by
    have hp0 := (mul_ne_zero_iff.mp hc).1
    have hq0 := (mul_ne_zero_iff.mp hc).2
    have hpw := hp.weight_le hp0
    have hqw := hq.weight_le hq0
    have hsum := congrArg (Finsupp.weight w) hx
    simp only [map_add] at hsum hw
    have hpa : x.1=a := hp.eq_of_weight_ge hp0 (by linarith)
    have hqb : x.2=b := hq.eq_of_weight_ge hq0 (by linarith)
    exact Prod.ext hpa hqb
  constructor
  · rw [MvPolynomial.coeff_mul,Finset.sum_eq_single (a,b)]
    · rw [hp.1,hq.1,mul_one]
    · intro x hx hne
      by_contra hc
      exact hne (hterm x (Finset.mem_antidiagonal.mp hx) hc le_rfl)
    · intro hab
      exact (hab (Finset.mem_antidiagonal.mpr rfl)).elim
  · intro z hza hw
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    by_contra hc
    have he := hterm x (Finset.mem_antidiagonal.mp hx) hc hw
    have hz := Finset.mem_antidiagonal.mp hx
    rw [he] at hz
    exact hza hz.symm

theorem isWeightMonic_one (w : σ → ℤ) : IsWeightMonic w (1 : MvPolynomial σ K) 0 := by
  classical
  constructor
  · simp
  · intro b hb hw
    simp [MvPolynomial.coeff_one,hb,Ne.symm hb]

theorem IsWeightMonic.pow {w : σ → ℤ} {p : MvPolynomial σ K} {a : σ →₀ ℕ}
    (hp : IsWeightMonic w p a) (n : ℕ) : IsWeightMonic w (p^n) (n • a) := by
  induction n with
  | zero => simpa only [pow_zero,zero_smul] using isWeightMonic_one (K := K) w
  | succ n ih =>
    simpa only [pow_succ,succ_nsmul] using ih.mul hp

theorem isWeightMonic_prod {w : σ → ℤ} (S : Finset ι)
    (p : ι → MvPolynomial σ K) (a : ι → σ →₀ ℕ)
    (hp : ∀ i ∈ S, IsWeightMonic w (p i) (a i)) :
    IsWeightMonic w (∏ i ∈ S, p i) (∑ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.sum_empty] using isWeightMonic_one (K := K) w
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul
      (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))

theorem algebraicIndependent_of_weightMonic
    (w : σ → ℤ) (p : ι → MvPolynomial σ K) (a : ι → σ →₀ ℕ)
    (hp : ∀ i, IsWeightMonic w (p i) (a i))
    (ha : Function.Injective (Finsupp.linearCombination ℕ a)) :
    AlgebraicIndependent K p := by
  classical
  change Function.Injective (aeval (R := K) p)
  apply LinearMap.injective_of_linearIndependent (f := (aeval (R := K) p).toLinearMap)
    (MvPolynomial.basisMonomials ι K).span_eq
  have hmon (d : ι →₀ ℕ) :
      IsWeightMonic w (aeval (R := K) p (monomial d 1)) (Finsupp.linearCombination ℕ a d) := by
    rw [aeval_monomial,map_one,one_mul]
    exact isWeightMonic_prod d.support (fun i => p i ^ d i) (fun i => d i • a i)
      (fun i hi => (hp i).pow (d i))
  rw [MvPolynomial.coe_basisMonomials]
  change LinearIndependent K (fun d : ι →₀ ℕ => aeval (R := K) p (monomial d 1))
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro S
  exact linearIndependent_of_weightMonic (K := K) w
    (fun d : S => aeval (R := K) p (monomial d.val 1))
    (fun d : S => Finsupp.linearCombination ℕ a d.val)
    (ha.comp Subtype.val_injective) (fun d => hmon d.val)

end PaperVerification.AlternatingForms
