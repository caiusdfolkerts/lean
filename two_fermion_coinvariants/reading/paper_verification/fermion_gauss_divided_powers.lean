module

public import PaperVerification.FermionSl2
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Tactic.NoncommRing

/-!
# Finite divided powers of commuting square-zero operators

The Gauss calculation needs finite exterior exponentials over rings in which only
`n!` is invertible. An exponential construction requiring a rational algebra would
lose the paper's positive-characteristic cases. Here the elementary coefficients
of a finite product are defined recursively and identified with divided powers.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.Fermion

open scoped BigOperators

section Ring

variable {B : Type*} [Ring B]

/-- The coefficient of degree `k` in the ordered product of the factors `1+t*x`.
The recursive definition is valid even in a noncommutative ambient ring. -/
def elementaryOperator : List B → ℕ → B
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | x :: l, k + 1 => elementaryOperator l (k + 1) + x * elementaryOperator l k

@[simp] theorem elementaryOperator_zero (l : List B) : elementaryOperator l 0 = 1 := by
  cases l <;> rfl

 theorem elementaryOperator_eq_zero_of_length_lt (l : List B) (k : ℕ)
    (h : l.length < k) : elementaryOperator l k = 0 := by
  induction l generalizing k with
  | nil => cases k <;> simp_all [elementaryOperator]
  | cons x l ih =>
    cases k with
    | zero => simp at h
    | succ k =>
      simp only [elementaryOperator, ih (k + 1) (by simpa using Nat.lt_of_succ_lt h),
        ih k (by simpa using h), mul_zero, add_zero]

/-- A square-zero summand leaves only the first two binomial terms. -/
theorem add_pow_succ_of_square_zero (x y : B) (hx : x * x = 0)
    (hxy : Commute x y) (k : ℕ) :
    (x + y) ^ (k + 1) = y ^ (k + 1) + (k + 1) • (x * y ^ k) := by
  induction k with
  | zero => simp [add_comm]
  | succ k ih =>
    have hz : (x * y ^ k) * x = 0 := by
      rw [mul_assoc, ← (hxy.pow_right k).eq, ← mul_assoc, hx, zero_mul]
    have hyx : y ^ (k + 1) * x = x * y ^ (k + 1) := (hxy.pow_right (k + 1)).eq.symm
    calc
      (x + y) ^ (k + 1 + 1) =
          (y ^ (k + 1) + (k + 1) • (x * y ^ k)) * (x + y) := by
        rw [pow_succ, ih]
      _ = y ^ (k + 1 + 1) + x * y ^ (k + 1) +
          (k + 1) • (x * y ^ (k + 1)) := by
        rw [add_mul, mul_add, mul_add, hyx, smul_mul_assoc, smul_mul_assoc, hz,
          nsmul_zero, zero_add, mul_assoc, ← pow_succ, ← pow_succ]
        abel
      _ = y ^ (k + 1 + 1) + (k + 1 + 1) • (x * y ^ (k + 1)) := by
        simp only [add_nsmul,one_nsmul]
        abel

/-- Powers of a sum of commuting square-zero terms have precisely the factorial
multiplicity of the squarefree elementary coefficient. -/
theorem sum_pow_eq_factorial_smul_elementary (l : List B)
    (hsq : ∀ x ∈ l, x * x = 0)
    (hcomm : ∀ x ∈ l, ∀ y ∈ l, Commute x y) (k : ℕ) :
    l.sum ^ k = k.factorial • elementaryOperator l k := by
  induction l generalizing k with
  | nil => cases k <;> simp [elementaryOperator]
  | cons x l ih =>
    have hsql : ∀ y ∈ l, y * y = 0 := fun y hy ↦ hsq y (List.mem_cons_of_mem x hy)
    have hcl : ∀ y ∈ l, ∀ z ∈ l, Commute y z := by
      intro y hy z hz
      exact hcomm y (List.mem_cons_of_mem x hy) z (List.mem_cons_of_mem x hz)
    cases k with
    | zero => simp
    | succ k =>
      rw [List.sum_cons, add_pow_succ_of_square_zero x l.sum
        (hsq x (List.mem_cons_self))
        (Commute.list_sum_right x l (fun y hy ↦
          hcomm x (List.mem_cons_self) y (List.mem_cons_of_mem x hy))),
        ih hsql hcl (k + 1), ih hsql hcl k, elementaryOperator]
      simp only [Nat.factorial_succ, smul_add, mul_smul_comm, smul_smul]

/-- Summing all elementary coefficients recovers the literal ordered product. -/
theorem prod_one_add_eq_sum_elementary (l : List B) :
    (l.map (fun x ↦ 1 + x)).prod =
      ∑ k ∈ Finset.range (l.length + 1), elementaryOperator l k := by
  induction l with
  | nil => simp [elementaryOperator]
  | cons x l ih =>
    have hshift :
        (∑ k ∈ Finset.range (l.length + 1), elementaryOperator l (k + 1)) + 1 =
          (l.map (fun y ↦ 1 + y)).prod := by
      calc
        _ = ∑ k ∈ Finset.range (l.length + 1 + 1), elementaryOperator l k := by
          conv_rhs => rw [Finset.sum_range_succ']
          rw [elementaryOperator_zero]
        _ = (∑ k ∈ Finset.range (l.length + 1), elementaryOperator l k) +
            elementaryOperator l (l.length + 1) := Finset.sum_range_succ _ _
        _ = _ := by
          rw [elementaryOperator_eq_zero_of_length_lt l (l.length + 1) (by omega),
            add_zero, ← ih]
    symm
    calc
      _ = (∑ k ∈ Finset.range (l.length + 1), elementaryOperator l (k + 1)) +
          1 + x * (∑ k ∈ Finset.range (l.length + 1), elementaryOperator l k) := by
        rw [List.length_cons, Finset.sum_range_succ']
        simp only [elementaryOperator, Finset.sum_add_distrib, ← Finset.mul_sum]
        abel
      _ = (l.map (fun y ↦ 1 + y)).prod + x * (l.map (fun y ↦ 1 + y)).prod := by
        rw [hshift, ← ih]
      _ = _ := by simp only [List.map_cons, List.prod_cons, add_mul, one_mul]

end Ring

section Scalar

variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]

/-- Scaling every factor scales the elementary coefficient by its exact degree. -/
theorem elementaryOperator_smul (l : List B) (a : R) (k : ℕ) :
    elementaryOperator (l.map (fun x ↦ a • x)) k = a ^ k • elementaryOperator l k := by
  induction l generalizing k with
  | nil => cases k <;> simp [elementaryOperator]
  | cons x l ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.map_cons, elementaryOperator, ih, smul_mul_assoc,
        mul_smul_comm, smul_smul, pow_succ', smul_add,mul_comm]

/-- The finite ordered product, with its scalar parameter displayed explicitly. -/
theorem prod_one_add_smul_eq_sum (l : List B) (a : R) :
    (l.map (fun x ↦ 1 + a • x)).prod =
      ∑ k ∈ Finset.range (l.length + 1), a ^ k • elementaryOperator l k := by
  have h := prod_one_add_eq_sum_elementary (l.map (fun x ↦ a • x))
  simpa only [List.map_map, Function.comp_def, List.length_map,
    elementaryOperator_smul] using h

end Scalar

section Operators

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

/-- A vanishing power forces the corresponding elementary operator to vanish
on the vector, provided the relevant factorial is a unit. -/
theorem elementary_apply_eq_zero_of_sum_power_eq_zero
    (l : List (Module.End R W))
    (hsq : ∀ x ∈ l, x * x = 0)
    (hcomm : ∀ x ∈ l, ∀ y ∈ l, Commute x y)
    (k : ℕ) (hunit : IsUnit (k.factorial : R)) (w : W)
    (hz : (l.sum ^ k) w = 0) : elementaryOperator l k w = 0 := by
  have h := congrArg (fun f : Module.End R W ↦ f w)
    (sum_pow_eq_factorial_smul_elementary l hsq hcomm k)
  rw [hz, LinearMap.smul_apply] at h
  exact hunit.smul_eq_zero.mp (by simpa only [Nat.cast_smul_eq_nsmul] using h.symm)

/-- The finite exponential of a primitive annihilator fixes its vector. Only
the factorial bound from the paper is used; no rational-algebra assumption occurs. -/
theorem prod_one_add_apply_eq_self_of_sum_apply_eq_zero
    (l : List (Module.End R W))
    (hsq : ∀ x ∈ l, x * x = 0)
    (hcomm : ∀ x ∈ l, ∀ y ∈ l, Commute x y)
    (hfac : IsUnit (l.length.factorial : R)) (w : W) (hw : l.sum w = 0) :
    ((l.map (fun x ↦ 1 + x)).prod : Module.End R W) w = w := by
  rw [prod_one_add_eq_sum_elementary, LinearMap.sum_apply]
  have hzero (k : ℕ) (hk : k ∈ Finset.range (l.length + 1)) (hne : k ≠ 0) :
      elementaryOperator l k w = 0 := by
    apply elementary_apply_eq_zero_of_sum_power_eq_zero l hsq hcomm k
      (unit_factorialCast_of_le hfac (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) w
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [pow_succ, Module.End.mul_apply, hw, map_zero]
  rw [Finset.sum_eq_single 0 (fun k hk hne ↦ hzero k hk hne)]
  · simp
  · simp

end Operators

end PaperVerification.Fermion
