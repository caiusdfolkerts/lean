module

public import PaperVerification.FermionPaths
public import PaperVerification.FermionMarkedPathCore
public import PaperVerification.FermionEndpointLength
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Enumeration of every four-color marked path

This is the literal finite sum over all mark choices, with each step carrying
its corresponding polynomial box length.  A double step at height zero has
weight zero.  The local two-color sum removes the choice of degree splitting.

The identification with the actual
quotient grading and its box index is recorded separately.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.Paths

open Polynomial Endpoint
open scoped BigOperators

def pathCoefficient {A : Type*} [CommSemiring A]
    (r u v : ℕ → ℕ) (s : ℕ) (t : A) : {n : ℕ} → (Fin n → Mark) → A
  | 0,_ => 1
  | n+1,m =>
      pathCoefficient r u v s t (Fin.init m) *
        (pairedBoxBound (r n) (u n) (v n) s (pathHeight (Fin.init m)) (m (Fin.last n)) : A) *
        t^markDegree (m (Fin.last n))

def allPathPolynomial {A : Type*} [CommSemiring A]
    (r u v : ℕ → ℕ) (s : ℕ) (t : A) (n : ℕ) : A[X] :=
  ∑ m : Fin n → Mark, C (pathCoefficient r u v s t m)*X^pathHeight m

theorem local_mark_sum {A : Type*} [CommSemiring A]
    (r u v s h : ℕ) (huv : u+v=r*s) (a t : A) :
    (∑ m : Mark, C (a*(pairedBoxBound r u v s h m : A)*t^markDegree m)*X^advance h m) =
      C (r : A)*transfer (s : A) t (C a*X^h) := by
  rw [sum_mark,transfer_monomial]
  simp only [pairedBoxBound,markDegree,advance,pow_zero,pow_one,mul_one]
  have huv' : (u : A)+(v : A)=(r : A)*(s : A) := by simpa only [Nat.cast_add,Nat.cast_mul] using congrArg (fun x : ℕ ↦ (x : A)) huv
  simp only [Nat.cast_mul,Nat.cast_add]
  simp only [map_mul,map_add,map_ofNat]
  calc
    _ = C a*C (r : A)*C ((s : A)+(h : A))*X^(h+1) +
        C a*((C (r : A)*C (h : A)+C (v : A))+
          (C (r : A)*C (h : A)+C (u : A)))*C t*X^h +
        C a*C (r : A)*C (h : A)*C (t^2)*X^(h-1) := by
          simp only [map_add]
          ring
    _ = _ := by
      have hc : C (u : A)+C (v : A)=C (r : A)*C (s : A) := by
        rw [← map_add,huv',map_mul]
      have hf : ((C (r : A)*C (h : A)+C (v : A))+
          (C (r : A)*C (h : A)+C (u : A))) =
          C (r : A)*(C (s : A)+2*C (h : A)) := by
        calc
          _ = C (r : A)*(2*C (h : A))+(C (u : A)+C (v : A)) := by ring
          _ = C (r : A)*(2*C (h : A))+C (r : A)*C (s : A) := by rw [hc]
          _ = _ := by ring
      rw [hf]
      simp only [map_add,map_mul,map_ofNat,pow_two]
      ring

theorem transfer_C_mul {A : Type*} [CommSemiring A] (s t a : A) (p : A[X]) :
    transfer s t (C a*p)=C a*transfer s t p := by
  rw [transfer,derivative_C_mul,transfer]
  ring

theorem transfer_sum {A J : Type*} [CommSemiring A] (s t : A)
    (S : Finset J) (p : J → A[X]) :
    transfer s t (∑ j ∈ S,p j)=∑ j ∈ S,transfer s t (p j) := by
  simp only [transfer,derivative_sum,Finset.mul_sum]
  rw [Finset.sum_add_distrib]

theorem allPathPolynomial_succ {A : Type*} [CommSemiring A]
    (r u v : ℕ → ℕ) (s : ℕ) (t : A) (n : ℕ) (huv : u n+v n=r n*s) :
    allPathPolynomial r u v s t (n+1) =
      C (r n : A)*transfer (s : A) t (allPathPolynomial r u v s t n) := by
  classical
  rw [allPathPolynomial]
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n+1) ↦ Mark))]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [Fin.snocEquiv_apply,pathHeight,pathCoefficient,Fin.init_snoc,Fin.snoc_last]
  simp only [local_mark_sum _ _ _ _ _ huv]
  rw [← Finset.mul_sum,← transfer_sum]
  rfl

/-- The complete finite sum of all weighted mark choices has the closed
height/exterior polynomial asserted by the path-transfer calculation. -/
theorem allPathPolynomial_closed {A : Type*} [CommSemiring A]
    (r u v : ℕ → ℕ) (s : ℕ) (t : A) (huv : ∀ i,u i+v i=r i*s) (n : ℕ) :
    allPathPolynomial r u v s t n =
      C ((∏ i ∈ Finset.range n,r i : ℕ) : A)*transferPolynomial s t n := by
  induction n with
  | zero => simp [allPathPolynomial,pathHeight,pathCoefficient,transferPolynomial]
  | succ n ih =>
      rw [allPathPolynomial_succ r u v s t n (huv n),ih,transfer_C_mul,
        transferPolynomial,Finset.prod_range_succ,Nat.cast_mul,map_mul]
      ring

theorem allPathPolynomial_eval_one {A : Type*} [CommSemiring A]
    (r u v : ℕ → ℕ) (s : ℕ) (t : A) (huv : ∀ i,u i+v i=r i*s) (n : ℕ) :
    ∑ m : Fin n → Mark, pathCoefficient r u v s t m =
      ((∏ i ∈ Finset.range n,r i : ℕ) : A)*(s.ascFactorial n : A)*(1+t)^n := by
  have h := congrArg (Polynomial.eval 1) (allPathPolynomial_closed r u v s t huv n)
  simpa [allPathPolynomial,Polynomial.eval_finsetSum,transferPolynomial_eval_one,Polynomial.eval_prod,mul_assoc] using h

end PaperVerification.Fermion.Paths
