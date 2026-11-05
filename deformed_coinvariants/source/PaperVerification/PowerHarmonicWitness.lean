module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The exact harmonic polynomial at every exceptional parameter

The computation uses polynomial differentiation identities in every order,
including orders at and above the degree. It therefore needs no division by
falling factorials and no omitted boundary case.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

namespace PaperVerification.PowerHarmonicWitness

variable {K ι : Type*} [CommRing K]
local instance : DecidableEq ι := Classical.decEq ι
local notation "P" => MvPolynomial ι K

theorem pderiv_aeval_of_linear (i : ι) (S : P) (hS : pderiv i S = 1)
    (p : Polynomial K) :
    pderiv i (Polynomial.aeval S p) = Polynomial.aeval S p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial q a =>
    simp only [Polynomial.aeval_monomial, Polynomial.derivative_monomial,
      MvPolynomial.algebraMap_eq, pderiv_mul, pderiv_C, zero_mul, zero_add,
      pderiv_pow, hS, mul_one, map_mul, map_natCast]
    ring

theorem pderiv_iterate_aeval_mul_linear
    (i : ι) (S L : P) (δ : K)
    (hS : pderiv i S = 1) (hL : pderiv i L = C δ)
    (p : Polynomial K) (k : ℕ) :
    (pderiv i)^[k+1] (Polynomial.aeval S p * L) =
      Polynomial.aeval S (Polynomial.derivative^[k+1] p) * L +
        C ((k+1 : ℕ) : K) * C δ *
          Polynomial.aeval S (Polynomial.derivative^[k] p) := by
  induction k with
  | zero =>
    simp only [Nat.zero_add, Function.iterate_one, Function.iterate_zero,
      id_eq, Nat.cast_one, C_1, one_mul, pderiv_mul,
      pderiv_aeval_of_linear i S hS, hL]
    ring
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [map_add, pderiv_mul, pderiv_C, zero_mul, zero_add,
      pderiv_aeval_of_linear i S hS, hL]
    simp only [Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one,
      map_add, C_1]
    ring

/-- Euler's identity after any number of derivatives, including vanishing
derivatives above the degree. -/
theorem polynomial_iterated_euler (q k : ℕ) :
    Polynomial.X * Polynomial.derivative^[k+1] (Polynomial.X^q : Polynomial K) +
        (k : Polynomial K) * Polynomial.derivative^[k] (Polynomial.X^q) =
      (q : Polynomial K) * Polynomial.derivative^[k] (Polynomial.X^q) := by
  induction k with
  | zero =>
    simp only [Nat.zero_add, Function.iterate_one, Function.iterate_zero,
      id_eq, Nat.cast_zero, zero_mul, add_zero, Polynomial.derivative_X_pow,
      Polynomial.C_eq_natCast]
    cases q with
    | zero => simp
    | succ q => simp only [Nat.succ_sub_one, pow_succ]; ring
  | succ k ih =>
    have hd := congrArg Polynomial.derivative ih
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_X, Polynomial.derivative_natCast, one_mul,
      zero_mul, zero_add, ← Function.iterate_succ_apply'] at hd
    convert hd using 1 <;> push_cast <;> ring

variable [Fintype ι]

def sumVariables : P := ∑ i : ι, X i

@[simp] theorem pderiv_sumVariables (i : ι) :
    pderiv i (sumVariables (K := K) (ι := ι)) = 1 := by
  simp [sumVariables, pderiv_X, eq_comm]

def linearDifferenceCoefficient (a b i : ι) : K :=
  (if i=a then 1 else 0) - (if i=b then 1 else 0)

theorem pderiv_linearDifference (a b i : ι) :
    pderiv i (X a-X b : P) = C (linearDifferenceCoefficient (K := K) a b i) := by
  classical
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    simp_all [linearDifferenceCoefficient, pderiv_X, Pi.single_apply, eq_comm]

theorem sum_linearDifferenceCoefficient (a b : ι) :
    (∑ i, linearDifferenceCoefficient (K := K) a b i) = 0 := by
  simp [linearDifferenceCoefficient, Finset.sum_sub_distrib]

theorem sum_X_mul_linearDifferenceCoefficient (a b : ι) :
    (∑ i, (X i : P) * C (linearDifferenceCoefficient (K := K) a b i)) = X a-X b := by
  simp [linearDifferenceCoefficient, map_sub, mul_sub, Finset.sum_sub_distrib]

def harmonicWitness (a b : ι) (q : ℕ) : P :=
  sumVariables^q * (X a-X b)

theorem harmonicWitness_ne_zero [Nontrivial K]
    (a b : ι) (hab : a ≠ b) (q : ℕ) :
    harmonicWitness (K := K) a b q ≠ 0 := by
  let v : ι → K := fun i => if i=a then 1 else 0
  have he : MvPolynomial.eval v (harmonicWitness (K := K) a b q) = 1 := by
    simp [harmonicWitness, sumVariables, v, Ne.symm hab]
  intro hz
  rw [hz, map_zero] at he
  exact zero_ne_one he

theorem harmonicWitness_homogeneous (a b : ι) (q : ℕ) :
    (harmonicWitness (K := K) a b q).IsHomogeneous (q+1) := by
  have hS : (sumVariables (K := K) (ι := ι)).IsHomogeneous 1 := by
    exact IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X K i)
  have hL : (X a-X b : P).IsHomogeneous 1 :=
    (isHomogeneous_X K a).sub (isHomogeneous_X K b)
  simpa only [harmonicWitness, Nat.one_mul, nsmul_eq_mul] using (hS.pow q).mul hL

/-- The genuine formal adjoint of the original scalar power operator. The
adjointness with the Fischer pairing is established separately. -/
def adjointOriginal (α : K) (k : ℕ) (p : P) : P :=
  (∑ i, (pderiv i)^[k] p) +
    C α * ∑ i, X i * (pderiv i)^[k+1] p

theorem adjointOriginal_harmonicWitness (α : K) (a b : ι) (q k : ℕ) :
    adjointOriginal α (k+1) (harmonicWitness a b q) =
      C ((Fintype.card ι : K) + α * (q+1 : ℕ)) *
        Polynomial.aeval (sumVariables : P)
          (Polynomial.derivative^[k+1] (Polynomial.X^q : Polynomial K)) * (X a-X b) := by
  let S : P := sumVariables
  let L : P := X a-X b
  let A : ℕ → P := fun j => Polynomial.aeval S
    (Polynomial.derivative^[j] (Polynomial.X^q : Polynomial K))
  have hderiv (i : ι) (j : ℕ) :
      (pderiv i)^[j+1] (harmonicWitness a b q) =
        A (j+1)*L + C ((j+1 : ℕ) : K) *
          C (linearDifferenceCoefficient (K := K) a b i) * A j := by
    simpa only [harmonicWitness, map_pow, Polynomial.aeval_X, A, S, L] using
      pderiv_iterate_aeval_mul_linear i S L
        (linearDifferenceCoefficient (K := K) a b i)
        (pderiv_sumVariables i) (pderiv_linearDifference a b i)
        (Polynomial.X^q) j
  have hsum : (∑ i, (pderiv i)^[k+1] (harmonicWitness a b q)) =
      C (Fintype.card ι : K) * A (k+1) * L := by
    simp_rw [hderiv]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul,
      ← Finset.mul_sum, ← map_sum, sum_linearDifferenceCoefficient,
      map_zero, mul_zero, zero_mul, add_zero, map_natCast]
    ring
  have hweighted : (∑ i, X i * (pderiv i)^[k+1+1] (harmonicWitness a b q)) =
      C ((q+1 : ℕ) : K) * A (k+1) * L := by
    simp_rw [hderiv, mul_add]
    rw [Finset.sum_add_distrib]
    have he := congrArg (Polynomial.aeval S) (polynomial_iterated_euler (K := K) q (k+1))
    simp only [map_add, map_mul, map_natCast, Polynomial.aeval_X] at he
    change S*A (k+1+1) + ((k+1 : ℕ) : P)*A (k+1) = (q : P)*A (k+1) at he
    have hterm : (∑ i, X i *
        (C ((k+1+1 : ℕ) : K) * C (linearDifferenceCoefficient (K := K) a b i) * A (k+1))) =
        C ((k+1+1 : ℕ) : K) * (X a-X b) * A (k+1) := by
      simp_rw [show ∀ i : ι, X i *
        (C ((k+1+1 : ℕ) : K) * C (linearDifferenceCoefficient (K := K) a b i) * A (k+1)) =
        C ((k+1+1 : ℕ) : K) * (X i * C (linearDifferenceCoefficient (K := K) a b i)) * A (k+1)
        from fun _ => by ring]
      rw [← Finset.sum_mul, ← Finset.mul_sum, sum_X_mul_linearDifferenceCoefficient]
    rw [hterm, ← Finset.sum_mul]
    change S*(A (k+1+1)*L) + C ((k+1+1 : ℕ) : K)*L*A (k+1) = _
    have he' := congrArg (fun p : P => p*L) he
    simp only [map_natCast]
    push_cast at he' ⊢
    linear_combination he'
  rw [adjointOriginal, hsum, hweighted]
  simp only [map_add, map_mul, map_natCast]
  ring

theorem harmonicWitness_all_adjoint_zero (α : K) (a b : ι) (q : ℕ)
    (hres : (Fintype.card ι : K) + α * (q+1 : ℕ) = 0) :
    ∀ k : ℕ, 0 < k → adjointOriginal α k (harmonicWitness a b q) = 0 := by
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [Nat.succ_eq_add_one, adjointOriginal_harmonicWitness, hres, map_zero, zero_mul, zero_mul]

end PaperVerification.PowerHarmonicWitness
