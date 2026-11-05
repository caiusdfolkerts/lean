module

public import PaperVerification.ExternalEulerianEulerianPeak
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.Ring

/-!
# The actual permutation Eulerian polynomial and the two-color transfer

Eulerian numbers here count permutations with a given descent number, using
the pinned RealRooted proof of insertion recurrence. The polynomial in this
file is proved equal to the literal sum over permutations with ascent and
descent exponents. Its shifted differential recurrence is the transfer
operator in Section 8.3 of the fermion paper.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators Polynomial

namespace PaperVerification.Fermion.Eulerian

open Polynomial Equiv.Perm

variable {R : Type*} [CommSemiring R]

/-- The exact homogeneous permutation sum printed in Section 8.3. -/
def permutationPolynomial (n : ℕ) (a b : R) : R :=
  ∑ σ : Equiv.Perm (Fin n), a^σ.ascentCount*b^σ.descentCount

/-- Positive-size descent histogram; n corresponds to permutations of n+1 letters. -/
def histogramPolynomial (n : ℕ) (a b : R) : R :=
  ∑ k∈Finset.range (n+1), (eulerianNumber (n+1) k : R)*a^(n-k)*b^k

theorem descentCount_le (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) : σ.descentCount≤n := by
  have h := σ.descentCount_add_ascentCount
  simp only [Nat.add_sub_cancel] at h
  omega

theorem ascentCount_eq (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    σ.ascentCount=n-σ.descentCount := by
  have h := σ.descentCount_add_ascentCount
  simp only [Nat.add_sub_cancel] at h
  omega

theorem eulerianNumber_above (n k : ℕ) (hk : n<k) : eulerianNumber (n+1) k=0 := by
  rw [eulerianNumber,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro σ hσ he
  have h := descentCount_le n σ
  omega

/-- Histogram aggregation preserves the literal permutation statistic. -/
theorem histogram_eq_permutation (n : ℕ) (a b : R) :
    histogramPolynomial n a b=permutationPolynomial (n+1) a b := by
  have hmap : ∀ σ∈(Finset.univ : Finset (Equiv.Perm (Fin (n+1)))),
      σ.descentCount∈Finset.range (n+1) := by
    intro σ hσ
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (descentCount_le n σ))
  have h := Finset.sum_fiberwise_of_maps_to' hmap (fun k ↦ a^(n-k)*b^k)
  calc
    histogramPolynomial n a b=
        ∑ σ : Equiv.Perm (Fin (n+1)),a^(n-σ.descentCount)*b^σ.descentCount := by
      simpa only [histogramPolynomial,Finset.sum_const,nsmul_eq_mul,eulerianNumber,
        mul_assoc] using h
    _=permutationPolynomial (n+1) a b := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [ascentCount_eq]

/-- The two-color differential operator, before evaluation of the height variable. -/
def transfer (u v : R) (p : R[X]) : R[X] :=
  (X+C u)*(X+C v)*derivative p+(2*X+C u+C v)*p

theorem transfer_sum {J : Type*} (u v : R) (s : Finset J) (f : J → R[X]) :
    transfer u v (∑ j∈s,f j)=∑ j∈s,transfer u v (f j) := by
  simp only [transfer,derivative_sum,Finset.mul_sum,Finset.sum_add_distrib]

theorem transfer_shifted_monomial (u v c : R) (p q : ℕ) :
    transfer u v (C c*(X+C u)^p*(X+C v)^q)=
      C (c*(q+1))*(X+C u)^(p+1)*(X+C v)^q+
        C (c*(p+1))*(X+C u)^p*(X+C v)^(q+1) := by
  cases p <;> cases q <;>
    simp only [transfer,derivative_mul,derivative_C,derivative_pow_succ,
      derivative_X_add_C,derivative_X,zero_mul,zero_add,mul_zero,add_zero,mul_one,one_mul,
      pow_zero,derivative_one,Nat.cast_add,Nat.cast_one,Nat.cast_zero,
      Nat.cast_succ,map_mul,map_add,map_natCast,map_one,map_ofNat] <;>
    simp only [pow_succ] <;> ring

def shiftedPolynomial (n : ℕ) (u v : R) : R[X] :=
  histogramPolynomial n (X+C u) (X+C v)

@[simp] theorem shiftedPolynomial_zero (u v : R) : shiftedPolynomial 0 u v=1 := by
  simp [shiftedPolynomial,histogramPolynomial,eulerianNumber_succ_zero]

/-- The full insertion recurrence becomes exactly the color-transfer operator. -/
theorem shiftedPolynomial_succ (n : ℕ) (u v : R) :
    shiftedPolynomial (n+1) u v=transfer u v (shiftedPolynomial n u v) := by
  let a : R[X] := X+C u
  let b : R[X] := X+C v
  let U (k : ℕ) : R[X] :=
    C (((k+1)*eulerianNumber (n+1) k : ℕ) : R)*a^(n+1-k)*b^k
  let D (k : ℕ) : R[X] :=
    C (((n+1-k)*eulerianNumber (n+1) k : ℕ) : R)*a^(n-k)*b^(k+1)
  have hzero : U 0=a^(n+1) := by
    simp only [U,eulerianNumber_succ_zero,zero_add,one_mul,Nat.cast_one,map_one,
      Nat.sub_zero,pow_zero,mul_one]
  have hend : U (n+1)=0 := by
    dsimp only [U]
    rw [eulerianNumber_above n (n+1) (Nat.lt_succ_self n)]
    simp only [mul_zero,Nat.cast_zero,map_zero,zero_mul]
  have hsum : (∑ k∈Finset.range (n+1),U (k+1))+U 0=
      ∑ k∈Finset.range (n+1),U k := by
    rw [Finset.sum_range_succ,Finset.sum_range_succ' U,hend,add_zero]
  have hterm (k : ℕ) :
      C (eulerianNumber (n+2) (k+1) : R)*a^((n+1)-(k+1))*b^(k+1)=U (k+1)+D k := by
    rw [show n+2=(n+1)+1 by omega,eulerianNumber_succ_succ]
    simp only [U,D,Nat.add_sub_add_right,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
      Nat.cast_ofNat,map_add,map_mul,map_ofNat,map_one,map_natCast]
    ring
  have htransfer : transfer u v (shiftedPolynomial n u v)=
      (∑ k∈Finset.range (n+1),U k)+(∑ k∈Finset.range (n+1),D k) := by
    rw [shiftedPolynomial,histogramPolynomial,transfer_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hexp : n-k+1=n+1-k := by omega
    have hdeg : ((n-k : ℕ) : R)+1=((n+1-k : ℕ) : R) := by
      simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun d : ℕ ↦ (d : R)) hexp
    change transfer u v (C (eulerianNumber (n+1) k : R)*a^(n-k)*b^k)=_
    rw [transfer_shifted_monomial]
    simp only [U,D,hexp,hdeg,Nat.cast_add,Nat.cast_mul,Nat.cast_one,map_mul,map_add]
    ring
  rw [htransfer]
  change (∑ k∈Finset.range ((n+1)+1),
    C (eulerianNumber ((n+1)+1) k : R)*a^((n+1)-k)*b^k)=_
  rw [Finset.sum_range_succ']
  simp only [eulerianNumber_succ_zero,Nat.cast_one,map_one,one_mul,Nat.sub_zero,
    pow_zero,mul_one]
  change (∑ k∈Finset.range (n+1),
    C (eulerianNumber (n+2) (k+1) : R)*a^((n+1)-(k+1))*b^(k+1))+a^(n+1)=_
  simp_rw [hterm]
  rw [Finset.sum_add_distrib,←hzero]
  calc
    _=((∑ k∈Finset.range (n+1),U (k+1))+U 0)+∑ k∈Finset.range (n+1),D k := by
      ac_rfl
    _=_ := by rw [hsum]

/-- Evaluating the height variable gives the actual homogeneous permutation sum. -/
theorem shiftedPolynomial_eval (n : ℕ) (u v z : R) :
    (shiftedPolynomial n u v).eval z=permutationPolynomial (n+1) (z+u) (z+v) := by
  rw [shiftedPolynomial,histogramPolynomial]
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_natCast]
  exact histogram_eq_permutation n (z+u) (z+v)

/-- Iterating the exact two-color transfer n times is the Eulerian polynomial
for actual permutations of n+1 letters, with the intended affine substitution. -/
theorem iterate_transfer_eval (n : ℕ) (u v : R) :
    ((transfer u v)^[n] 1).eval 1=permutationPolynomial (n+1) (1+u) (1+v) := by
  have h : (transfer u v)^[n] 1=shiftedPolynomial n u v := by
    induction n with
    | zero => simp only [Function.iterate_zero,Function.id_def,shiftedPolynomial_zero]
    | succ n ih =>
        rw [Function.iterate_succ_apply',ih,←shiftedPolynomial_succ]
  rw [h,shiftedPolynomial_eval]

end PaperVerification.Fermion.Eulerian
