module

public import PaperVerification.FermionMomentRecurrence
public import Mathlib.Tactic.Ring

/-!
# Support of the ordinary weighted moment equations

This is the exact rational-residue argument used in Sections 2.2 and 7.2,
proved instead with a polynomial that separates one repeated parameter value
from all the others. Repeated values are allowed, and their weights are summed.
No characteristic bound is needed for this support statement.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion

open scoped BigOperators
open Polynomial

section ModuleCoefficients

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/-- Annihilating all powers annihilates every polynomial in the same scalar parameters. -/
theorem polynomial_moment_zero (x : Fin n → R) (v : Fin n → M)
    (h : ∀ k : ℕ, moment x v k = 0) (p : R[X]) :
    (∑ i, p.eval (x i) • v i) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, add_smul, Finset.sum_add_distrib, hp, hq, add_zero]
  | monomial k a =>
    simp only [eval_monomial, mul_smul, ← Finset.smul_sum]
    change a • moment x v k = 0
    rw [h, smul_zero]

/-- The first `n` power moments are equivalent to all polynomial currents.

This uses the monic characteristic polynomial of the actual list of `n`
parameters; neither distinct parameters nor invertible Vandermonde determinants
are required. -/
theorem polynomial_moment_zero_iff_first (x : Fin n → R) (v : Fin n → M) :
    (∀ p : R[X], (∑ i, p.eval (x i) • v i) = 0) ↔
      ∀ j : Fin n, moment x v j = 0 := by
  constructor
  · intro h j
    simpa only [eval_pow, eval_X, moment] using h (X ^ (j : ℕ))
  · intro h p
    exact polynomial_moment_zero x v ((all_moments_eq_zero_iff x v).mpr h) p

end ModuleCoefficients

section FieldSupport

variable {F : Type*} [Field F] {n : ℕ}

/-- The indices sharing one parameter value; multiplicities are deliberately retained. -/
def parameterFiber (x : Fin n → F) (a : F) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i ↦ x i = a)

/-- A polynomial vanishing at every parameter different from `a`, but not at `a`. -/
def separator (x : Fin n → F) (a : F) : F[X] := by
  classical
  exact ∏ i ∈ Finset.univ.filter (fun i ↦ x i ≠ a), (X - C (x i))

theorem separator_eval_ne_zero (x : Fin n → F) (a : F) :
    (separator x a).eval a ≠ 0 := by
  classical
  rw [separator, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (Ne.symm (Finset.mem_filter.mp hi).2)

theorem separator_eval_other (x : Fin n → F) (a : F) (i : Fin n) (hi : x i ≠ a) :
    (separator x a).eval (x i) = 0 := by
  classical
  rw [separator, eval_prod]
  apply Finset.prod_eq_zero (by simp [hi] : i ∈ Finset.univ.filter (fun i ↦ x i ≠ a))
  simp

/-- A common function vanishes at all moment parameters once the weighted moments vanish.

The weight hypothesis is only on the actual nonempty fibers. This is stronger
than needed in the paper, whose assumptions make every nonempty subset sum a unit.
-/
theorem common_function_zero_of_moments
    (x β : Fin n → F) (f : F → F)
    (hβ : ∀ a : F, (parameterFiber x a).Nonempty →
      (∑ i ∈ parameterFiber x a, β i) ≠ 0)
    (h : ∀ k : Fin n, moment x (fun i ↦ β i * f (x i)) k = 0) :
    ∀ i, f (x i) = 0 := by
  classical
  have hall : ∀ k : ℕ, moment x (fun i ↦ β i * f (x i)) k = 0 :=
    (all_moments_eq_zero_iff x (fun i ↦ β i * f (x i))).mpr h
  intro i
  let a := x i
  let p := separator x a
  have hp : p.eval a ≠ 0 := separator_eval_ne_zero x a
  have hnonempty : (parameterFiber x a).Nonempty := ⟨i, by simp [parameterFiber, a]⟩
  have hsumβ := hβ a hnonempty
  have hz := polynomial_moment_zero x (fun i ↦ β i * f (x i)) hall p
  have hrestrict :
      (∑ j ∈ parameterFiber x a, p.eval (x j) * (β j * f (x j))) =
        ∑ j, p.eval (x j) * (β j * f (x j)) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hja : x j ≠ a := by simpa [parameterFiber] using hj
    rw [separator_eval_other x a j hja]
    simp
  have hfactor :
      (∑ j ∈ parameterFiber x a, p.eval (x j) * (β j * f (x j))) =
        ((∑ j ∈ parameterFiber x a, β j) * p.eval a) * f a := by
    calc
      _ = ∑ j ∈ parameterFiber x a, β j * (p.eval a * f a) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hja : x j = a := (Finset.mem_filter.mp hj).2
        rw [hja]
        ring
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hzero : ((∑ j ∈ parameterFiber x a, β j) * p.eval a) * f a = 0 := by
    rw [← hfactor, hrestrict]
    simpa only [smul_eq_mul] using hz
  exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero hsumβ hp)

/-- Exact support of the common-polynomial ordinary equations, including repeated parameters. -/
theorem common_polynomial_moments_zero_iff (x β : Fin n → F) (G : F[X])
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → (∑ i ∈ U, β i) ≠ 0) :
    (∀ k : Fin n, moment x (fun i ↦ β i * G.eval (x i)) k = 0) ↔
      ∀ i, G.eval (x i) = 0 := by
  refine ⟨?_, ?_⟩
  · exact common_function_zero_of_moments x β (fun a ↦ G.eval a)
      (fun a ha ↦ hβ (parameterFiber x a) ha)
  · intro h k
    simp [moment, h]

/-- For a positive power, the only ordinary zero is the origin, in any field. -/
theorem power_moments_zero_iff (x β : Fin n → F) (s : ℕ) (hs : 0 < s)
    (hβ : ∀ U : Finset (Fin n), U.Nonempty → (∑ i ∈ U, β i) ≠ 0) :
    (∀ k : Fin n, moment x (fun i ↦ β i * x i ^ s) k = 0) ↔ x = 0 := by
  have h := common_polynomial_moments_zero_iff x β (X ^ s) hβ
  simpa [eval_pow, eval_X, pow_eq_zero_iff hs.ne', funext_iff] using h

end FieldSupport

end PaperVerification.Fermion
