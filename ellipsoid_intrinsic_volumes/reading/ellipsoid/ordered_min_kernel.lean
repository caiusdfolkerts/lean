module

public import Ellipsoid.PositiveJacobians
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

noncomputable section

open Matrix Finset
open scoped BigOperators

namespace EllipsoidVerification

def minRatioKernel {m : ℕ} (p : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => min (p i) (p j) / max (p i) (p j)

def squaredNodesWithZero {m : ℕ} (p : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases 0 (fun i => p i ^ 2)

def squaredNodeIncrement {m : ℕ} (p : Fin m → ℝ) (i : Fin m) : ℝ :=
  squaredNodesWithZero p i.succ - squaredNodesWithZero p i.castSucc

theorem squaredNodeIncrement_pos {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hpos : ∀ i, 0 < p i) (i : Fin m) :
    0 < squaredNodeIncrement p i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change 0 < p 0 ^ 2 - 0
        simpa only [sub_zero] using sq_pos_of_pos (hpos 0)
      · have hlt := hp j.castSucc_lt_succ
        have h0 := hpos j.castSucc
        simp only [squaredNodeIncrement, squaredNodesWithZero, Fin.castSucc_succ,
          Fin.cases_succ]
        nlinarith

theorem sum_squaredNodeIncrement {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    ∑ j ∈ Finset.Iic i, squaredNodeIncrement p j = p i ^ 2 := by
  simpa [squaredNodeIncrement, squaredNodesWithZero] using
    Fin.sum_Iic_sub i (squaredNodesWithZero p)

def minRatioCholesky {m : ℕ} (p : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if j ≤ i then Real.sqrt (squaredNodeIncrement p j) / p i else 0

theorem minRatioCholesky_isLowerTriangular {m : ℕ} (p : Fin m → ℝ) :
    (minRatioCholesky p).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  simp [minRatioCholesky, not_le.mpr hij']

theorem det_minRatioCholesky_pos {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hpos : ∀ i, 0 < p i) :
    0 < (minRatioCholesky p).det := by
  rw [Matrix.det_of_isLowerTriangular _ (minRatioCholesky_isLowerTriangular p)]
  apply Finset.prod_pos
  intro i hi
  simp only [minRatioCholesky, le_refl, if_true]
  exact div_pos (Real.sqrt_pos.2 (squaredNodeIncrement_pos hp hpos i)) (hpos i)

theorem minRatioCholesky_mul_transpose {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hpos : ∀ i, 0 < p i) :
    minRatioCholesky p * (minRatioCholesky p)ᵀ = minRatioKernel p := by
  ext i j
  have hentry (k : Fin m) :
      minRatioCholesky p i k * minRatioCholesky p j k =
        if k ≤ min i j then squaredNodeIncrement p k / (p i * p j) else 0 := by
    by_cases hki : k ≤ i <;> by_cases hkj : k ≤ j
    · simp only [minRatioCholesky, hki, hkj, if_true,
        le_min_iff.mpr ⟨hki, hkj⟩]
      rw [div_mul_div_comm, Real.mul_self_sqrt (squaredNodeIncrement_pos hp hpos k).le]
    · simp [minRatioCholesky, hki, hkj, le_min_iff]
    · simp [minRatioCholesky, hki, hkj, le_min_iff]
    · simp [minRatioCholesky, hki, hkj, le_min_iff]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hentry]
  rw [← Finset.sum_filter]
  have hset : Finset.univ.filter (fun k : Fin m => k ≤ min i j) = Finset.Iic (min i j) := by
    ext k
    simp
  rw [hset, ← Finset.sum_div, sum_squaredNodeIncrement]
  rcases le_total i j with hij | hji
  · simp only [min_eq_left hij, minRatioKernel, min_eq_left (hp.monotone hij),
      max_eq_right (hp.monotone hij)]
    field_simp [(hpos i).ne', (hpos j).ne']
  · simp only [min_eq_right hji, minRatioKernel, min_eq_right (hp.monotone hji),
      max_eq_left (hp.monotone hji)]
    field_simp [(hpos i).ne', (hpos j).ne']

/-- The strict auxiliary kernel in Lemma 3.1, with no probabilistic
assumption and with all positive, pairwise ordered real parameters. -/
theorem minRatioKernel_posDef {m : ℕ} {p : Fin m → ℝ}
    (hp : StrictMono p) (hpos : ∀ i, 0 < p i) : (minRatioKernel p).PosDef := by
  rw [← minRatioCholesky_mul_transpose hp hpos]
  have hu : IsUnit (minRatioCholesky p) :=
    (minRatioCholesky p).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr (det_minRatioCholesky_pos hp hpos).ne')
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.mul_conjTranspose_self (minRatioCholesky p)
      (Matrix.vecMul_injective_iff_isUnit.mpr hu)

end EllipsoidVerification
