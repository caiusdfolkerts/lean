import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Simultaneous full rank for polynomial matrices

A polynomial matrix with one injective specialization is injective on a
nonempty polynomial open set.  Finitely many such conditions can therefore be
met simultaneously, even when their witnesses differ.  The proof uses Gram
determinants, avoiding a choice of full-size minors.
-/

namespace Cubical

open Matrix

theorem exists_eval_ne_zero {σ : Type*} {p : MvPolynomial σ ℝ} (hp : p ≠ 0) :
    ∃ x : σ → ℝ, MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext
  intro x
  simpa using h x

theorem exists_simultaneous_eval_ne_zero {σ J : Type*} [Fintype J]
    (p : J → MvPolynomial σ ℝ) (hp : ∀ j, p j ≠ 0) :
    ∃ x : σ → ℝ, ∀ j, MvPolynomial.eval x (p j) ≠ 0 := by
  classical
  have hprod : (∏ j, p j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hp j)
  obtain ⟨x, hx⟩ := exists_eval_ne_zero hprod
  refine ⟨x, ?_⟩
  rw [map_prod] at hx
  exact fun j ↦ Finset.prod_ne_zero_iff.mp hx j (Finset.mem_univ j)

theorem gram_det_ne_zero_iff {R C : Type*} [Fintype R] [Fintype C]
    [DecidableEq C] (A : Matrix R C ℝ) :
    (Aᵀ * A).det ≠ 0 ↔ Function.Injective A.mulVec := by
  have hker := Matrix.ker_mulVecLin_transpose_mul_self A
  have hi : Function.Injective (Aᵀ * A).mulVec ↔ Function.Injective A.mulVec := by
    change Function.Injective (Aᵀ * A).mulVecLin ↔ Function.Injective A.mulVecLin
    rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot, hker]
  rw [← hi, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]

def evalMatrix {σ R C : Type*} (A : Matrix R C (MvPolynomial σ ℝ))
    (x : σ → ℝ) : Matrix R C ℝ := A.map (MvPolynomial.eval x)

theorem eval_gram_det {σ R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    (A : Matrix R C (MvPolynomial σ ℝ)) (x : σ → ℝ) :
    MvPolynomial.eval x (Aᵀ * A).det =
      ((evalMatrix A x)ᵀ * evalMatrix A x).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply, evalMatrix, Matrix.mul_apply, map_sum, map_mul]

/-- A finite family of polynomial matrices has a common injective
specialization if each matrix has some injective specialization. -/
theorem exists_simultaneous_injective_specialization
    {σ J : Type*} [Fintype J] {R C : J → Type*}
    [∀ j, Fintype (R j)] [∀ j, Fintype (C j)] [∀ j, DecidableEq (C j)]
    (A : ∀ j, Matrix (R j) (C j) (MvPolynomial σ ℝ))
    (hA : ∀ j, ∃ x : σ → ℝ, Function.Injective (evalMatrix (A j) x).mulVec) :
    ∃ x : σ → ℝ, ∀ j, Function.Injective (evalMatrix (A j) x).mulVec := by
  have hp : ∀ j, ((A j)ᵀ * A j).det ≠ 0 := by
    intro j hzero
    obtain ⟨x, hx⟩ := hA j
    have hne := (gram_det_ne_zero_iff (evalMatrix (A j) x)).mpr hx
    rw [← eval_gram_det, hzero, map_zero] at hne
    exact hne rfl
  obtain ⟨x, hx⟩ := exists_simultaneous_eval_ne_zero
    (fun j ↦ ((A j)ᵀ * A j).det) hp
  refine ⟨x, fun j ↦ (gram_det_ne_zero_iff _).mp ?_⟩
  rw [← eval_gram_det]
  exact hx j

/-- Two finite families may be combined without identifying their row or
column types. -/
theorem exists_simultaneous_injective_specialization_pair
    {σ J K : Type*} [Fintype J] [Fintype K]
    {R C : J → Type*} {S D : K → Type*}
    [∀ j, Fintype (R j)] [∀ j, Fintype (C j)] [∀ j, DecidableEq (C j)]
    [∀ k, Fintype (S k)] [∀ k, Fintype (D k)] [∀ k, DecidableEq (D k)]
    (A : ∀ j, Matrix (R j) (C j) (MvPolynomial σ ℝ))
    (B : ∀ k, Matrix (S k) (D k) (MvPolynomial σ ℝ))
    (hA : ∀ j, ∃ x : σ → ℝ, Function.Injective (evalMatrix (A j) x).mulVec)
    (hB : ∀ k, ∃ x : σ → ℝ, Function.Injective (evalMatrix (B k) x).mulVec) :
    ∃ x : σ → ℝ,
      (∀ j, Function.Injective (evalMatrix (A j) x).mulVec) ∧
      (∀ k, Function.Injective (evalMatrix (B k) x).mulVec) := by
  classical
  have hpa : ∀ j, ((A j)ᵀ * A j).det ≠ 0 := by
    intro j hz
    obtain ⟨x, hx⟩ := hA j
    have hn := (gram_det_ne_zero_iff (evalMatrix (A j) x)).mpr hx
    rw [← eval_gram_det, hz, map_zero] at hn
    exact hn rfl
  have hpb : ∀ k, ((B k)ᵀ * B k).det ≠ 0 := by
    intro k hz
    obtain ⟨x, hx⟩ := hB k
    have hn := (gram_det_ne_zero_iff (evalMatrix (B k) x)).mpr hx
    rw [← eval_gram_det, hz, map_zero] at hn
    exact hn rfl
  obtain ⟨x, hx⟩ := exists_eval_ne_zero
    (mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hpa j))
      (Finset.prod_ne_zero_iff.mpr (fun k _ ↦ hpb k)))
  rw [map_mul, mul_ne_zero_iff, map_prod, map_prod] at hx
  refine ⟨x, ?_, ?_⟩
  · intro j
    apply (gram_det_ne_zero_iff _).mp
    rw [← eval_gram_det]
    exact Finset.prod_ne_zero_iff.mp hx.1 j (Finset.mem_univ j)
  · intro k
    apply (gram_det_ne_zero_iff _).mp
    rw [← eval_gram_det]
    exact Finset.prod_ne_zero_iff.mp hx.2 k (Finset.mem_univ k)

end Cubical
