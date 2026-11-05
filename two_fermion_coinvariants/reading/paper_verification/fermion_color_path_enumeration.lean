module

public import PaperVerification.FermionMarkedPathCore
public import PaperVerification.FermionEulerianTransfer

/-!
# Literal four-mark paths and the permutation Eulerian polynomial

The height is measured after the compulsory initial up-step. The four weights
are exactly h+2, (h+1)u, (h+1)v, and huv. A down-step from height zero has
coefficient zero, so summing all words also handles inadmissible words.

The identification of these
weights with the actual quotient character belongs to the basis bridge.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators Polynomial

namespace PaperVerification.Fermion.ColorPaths

open Polynomial Endpoint

variable {R : Type*} [CommSemiring R]

def stepWeight (u v : R) (h : ℕ) : Mark → R
  | .unmarked => (h+2 : ℕ)
  | .theta => (h+1 : ℕ)*u
  | .xi => (h+1 : ℕ)*v
  | .double => (h : R)*u*v

def coefficient (u v : R) : {n : ℕ} → (Fin n → Mark) → R
  | 0,_ => 1
  | n+1,m => coefficient u v (Fin.init m)*
      stepWeight u v (Paths.pathHeight (Fin.init m)) (m (Fin.last n))

def heightPolynomial (n : ℕ) (u v : R) : R[X] :=
  ∑ m : Fin n → Mark,C (coefficient u v m)*X^Paths.pathHeight m

theorem transfer_monomial (u v a : R) (h : ℕ) :
    Eulerian.transfer u v (C a*X^h)=
      C (a*(h+2 : ℕ))*X^(h+1)+
      C (a*(h+1 : ℕ)*u)*X^h+
      C (a*(h+1 : ℕ)*v)*X^h+
      C (a*(h : R)*u*v)*X^(h-1) := by
  cases h with
  | zero => simp [Eulerian.transfer,map_ofNat] <;> ring
  | succ h =>
      rw [Eulerian.transfer,derivative_C_mul,derivative_X_pow_succ]
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
        map_mul,map_add,map_one,map_ofNat,pow_succ]
      ring

theorem local_mark_sum (u v a : R) (h : ℕ) :
    (∑ m : Mark,C (a*stepWeight u v h m)*X^Paths.advance h m)=
      Eulerian.transfer u v (C a*X^h) := by
  rw [Paths.sum_mark,transfer_monomial]
  simp only [stepWeight,Paths.advance,mul_assoc]

@[simp] theorem heightPolynomial_zero (u v : R) : heightPolynomial 0 u v=1 := by
  simp [heightPolynomial,coefficient,Paths.pathHeight]

theorem heightPolynomial_succ (n : ℕ) (u v : R) :
    heightPolynomial (n+1) u v=Eulerian.transfer u v (heightPolynomial n u v) := by
  rw [heightPolynomial]
  rw [←Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n+1) ↦ Mark))]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [Fin.snocEquiv_apply,Paths.pathHeight,coefficient,Fin.init_snoc,Fin.snoc_last]
  simp only [local_mark_sum]
  rw [←Eulerian.transfer_sum]
  rfl

theorem heightPolynomial_eq_iterate (n : ℕ) (u v : R) :
    heightPolynomial n u v=(Eulerian.transfer u v)^[n] 1 := by
  induction n with
  | zero => simp only [heightPolynomial_zero,Function.iterate_zero,Function.id_def]
  | succ n ih => rw [heightPolynomial_succ,ih,Function.iterate_succ_apply']

/-- The literal finite sum over all four-mark words equals the literal
permutation ascent/descent sum, for every commutative coefficient semiring. -/
theorem sum_coefficient_eq_eulerian (n : ℕ) (u v : R) :
    (∑ m : Fin n → Mark,coefficient u v m)=
      Eulerian.permutationPolynomial (n+1) (1+u) (1+v) := by
  have h := congrArg (Polynomial.eval 1) (heightPolynomial_eq_iterate n u v)
  rw [Eulerian.iterate_transfer_eval] at h
  simpa only [heightPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,one_pow,mul_one] using h

end PaperVerification.Fermion.ColorPaths
