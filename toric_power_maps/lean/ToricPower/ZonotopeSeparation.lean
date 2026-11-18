module

public import ToricPower.Circuits
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient

@[expose] public section
noncomputable section

open Set Matrix
open scoped BigOperators Pointwise

namespace ToricPower

variable {n s : ℕ}

theorem linearForm_eq_sum_coefficients (L : (Fin s → ℝ) →ₗ[ℝ] ℝ)
    (x : Fin s → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  have hx : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem realZonotope_isCompact (A : Matrix (Fin s) (Fin n) ℤ) :
    IsCompact (realZonotope A) := by
  exact isCompact_Icc.image (realDivisorQuotient A).continuous_of_finiteDimensional

theorem realZonotope_convex (A : Matrix (Fin s) (Fin n) ℤ) :
    Convex ℝ (realZonotope A) := by
  exact (convex_Icc (-1 : Fin s → ℝ) 0).linear_image (realDivisorQuotient A)

/-- Separation in the genuine real cokernel gives a relation among the rows of A
which violates the support inequality of the cube. -/
theorem exists_real_relation_separating_zonotope
    (A : Matrix (Fin s) (Fin n) ℤ) (a : Fin s → ℤ)
    (ha : realDivisorClass A a ∉ realZonotope A) :
    ∃ h : Fin s → ℝ,
      (∀ j, ∑ i, (A i j : ℝ) * h i = 0) ∧
      (∑ i, max (-h i) 0) < ∑ i, h i * (a i : ℝ) := by
  let W := LinearMap.range (A.map (Int.castRingHom ℝ)).mulVecLin
  letI : IsClosed (W : Set (Fin s → ℝ)) := W.closed_of_finiteDimensional
  obtain ⟨f, u, hf, hfa⟩ := geometric_hahn_banach_closed_point
    (realZonotope_convex A) (realZonotope_isCompact A).isClosed ha
  let L : (Fin s → ℝ) →ₗ[ℝ] ℝ := f.toLinearMap.comp (realDivisorQuotient A)
  let h : Fin s → ℝ := fun i => L (Pi.single i 1)
  have hL (x : Fin s → ℝ) : L x = ∑ i, h i * x i :=
    linearForm_eq_sum_coefficients L x
  have hvanish (x : Fin n → ℝ) : L (realRayMap A x) = 0 := by
    have hz : realDivisorQuotient A (realRayMap A x) = 0 := by
      change (Submodule.Quotient.mk (realRayMap A x) :
        (Fin s → ℝ) ⧸ W) = 0
      apply (Submodule.Quotient.mk_eq_zero W).mpr
      exact LinearMap.mem_range_self (A.map (Int.castRingHom ℝ)).mulVecLin x
    change f (realDivisorQuotient A (realRayMap A x)) = 0
    rw [hz, map_zero]
  have hker (j : Fin n) : ∑ i, (A i j : ℝ) * h i = 0 := by
    have hcol : realRayMap A (Pi.single j 1) = fun i => (A i j : ℝ) := by
      ext i
      simp [realRayMap, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hz := hvanish (Pi.single j 1)
    rw [hcol, hL] at hz
    simpa only [mul_comm] using hz
  let y : Fin s → ℝ := fun i => if h i < 0 then -1 else 0
  have hy : y ∈ Set.Icc (-1 : Fin s → ℝ) 0 := by
    constructor <;> intro i <;> dsimp [y] <;> split_ifs <;> norm_num
  have hLy : L y = ∑ i, max (-h i) 0 := by
    rw [hL]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : h i < 0
    · simp only [y, if_pos hi, mul_neg, mul_one]
      exact (max_eq_left (by linarith)).symm
    · have hh : 0 ≤ h i := le_of_not_gt hi
      simp [y, hi, max_eq_right (neg_nonpos.mpr hh)]
  have hfy : f (realDivisorQuotient A y) < u :=
    hf _ ⟨y, hy, rfl⟩
  have hxy : L y < L (fun i => (a i : ℝ)) := lt_trans hfy hfa
  rw [hLy, hL] at hxy
  exact ⟨h, hker, hxy⟩

end ToricPower

