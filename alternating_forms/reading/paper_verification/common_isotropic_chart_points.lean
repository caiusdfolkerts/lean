module

public import PaperVerification.CommonIsotropicSubspace
public import PaperVerification.AlternatingFormsChartUniversal
public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Actual normalized chart points for every pair of alternating forms

The abstract common-isotropic vectors are converted into the original coefficient
and row-chart conventions. A nonzero maximal minor is sorted and inverted, giving
an actual pivot-normalized matrix over the coefficient field. The original
row-isotropy equations are preserved because each new row is a linear combination
of the old rows.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Module Matrix MvPolynomial
open LinearMap (BilinForm)
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {K : Type*} [Field K] {s n t m : ℕ}

/-- The alternating bilinear form with the literal strictly increasing coefficients. -/
def coefficientBilinear (f : StrictPairs n → K) : BilinForm K (Fin n → K) :=
  ∑ a : StrictPairs n, f a •
    ((LinearMap.mul K K).compl₁₂ (LinearMap.proj a.val.1) (LinearMap.proj a.val.2) -
      (LinearMap.mul K K).compl₁₂ (LinearMap.proj a.val.2) (LinearMap.proj a.val.1))

@[simp] theorem coefficientBilinear_apply (f : StrictPairs n → K) (v w : Fin n → K) :
    coefficientBilinear f v w =
      ∑ a : StrictPairs n, f a • (v a.val.1 * w a.val.2 - v a.val.2 * w a.val.1) := by
  simp [coefficientBilinear, LinearMap.sum_apply, LinearMap.smul_apply]

theorem coefficientBilinear_isAlt (f : StrictPairs n → K) :
    (coefficientBilinear f).IsAlt := by
  intro v
  simp [coefficientBilinear_apply, mul_comm]

@[simp] theorem coefficientBilinear_rows (f : StrictPairs n → K)
    (A : Matrix (Fin (t + 2)) (Fin n) K) (i j : Fin (t + 2)) :
    coefficientBilinear f (A i) (A j) = alternatingRowPair f A i j := by
  rw [coefficientBilinear_apply]
  rfl

/-- Linear independence produces a nonzero minor with the original increasing
Plücker index convention. -/
theorem exists_plucker_minor_ne_zero (A : Matrix (Fin s) (Fin n) K)
    (hA : LinearIndependent K A) :
    ∃ p : PluckerIndex s n, (A.submatrix id p.val).det ≠ 0 := by
  classical
  obtain ⟨e, he⟩ :=
    (Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero (A := A)).mp hA
  let p := sortedPluckerIndex e e.injective
  refine ⟨p, ?_⟩
  intro hz
  have hperm := Matrix.det_permute' (Tuple.sort (e : Fin s → Fin n)).symm
    (A.submatrix id p.val)
  have hm : (A.submatrix id p.val).submatrix id (Tuple.sort (e : Fin s → Fin n)).symm =
      A.submatrix id e := by
    ext i j
    simp only [Matrix.submatrix_apply, id_eq, p, sortedPluckerIndex,
      Function.comp_apply, Equiv.apply_symm_apply]
  rw [hm, hz, mul_zero] at hperm
  exact he hperm

/-- Row operations preserve total isotropy for the actual bilinear form. -/
theorem bilinear_zero_on_mul_rows (B : BilinForm K (Fin n → K))
    (A : Matrix (Fin s) (Fin n) K) (P : Matrix (Fin s) (Fin s) K)
    (hA : ∀ i j, B (A i) (A j) = 0) (i j : Fin s) :
    B ((P * A) i) ((P * A) j) = 0 := by
  have hrow (i : Fin s) : (P * A) i = ∑ k, P i k • A k := by
    funext l
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrow, hrow]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    hA, smul_zero, Finset.sum_const_zero]

/-- An independent isotropic row matrix gives a point of one of the literal
original affine charts. No genericity or rank condition on the forms is used. -/
theorem exists_isotropicChartPoint_of_rows
    (forms : Fin m → StrictPairs n → K) (A : Matrix (Fin (t + 2)) (Fin n) K)
    (hA : LinearIndependent K A)
    (hiso : ∀ l i j, alternatingRowPair (forms l) A i j = 0) :
    ∃ p : PluckerIndex (t + 2) n, Nonempty (IsotropicChartPoint p forms K) := by
  classical
  obtain ⟨p, hp⟩ := exists_plucker_minor_ne_zero A hA
  let M := A.submatrix id p.val
  refine ⟨p, ⟨{ matrix := M⁻¹ * A, pivot := ?_, isotropic := ?_ }⟩⟩
  · have h : (M⁻¹ * A).submatrix id p.val = M⁻¹ * M := by
      ext i j
      rfl
    rw [h]
    exact Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hp)
  · intro l i j
    rw [← coefficientBilinear_rows]
    exact bilinear_zero_on_mul_rows (coefficientBilinear (forms l)) A M⁻¹
      (fun i j ↦ (coefficientBilinear_rows (forms l) A i j).trans (hiso l i j)) i j

/-- For every pair, every allowed plane dimension occurs in an actual isotropic chart. -/
theorem exists_common_isotropic_chartPoint (h₂ : (2 : K) ≠ 0)
    (forms : Fin 2 → StrictPairs n → K) (hs : t + 2 ≤ (n + 1) / 2) :
    ∃ p : PluckerIndex (t + 2) n, Nonempty (IsotropicChartPoint p forms K) := by
  obtain ⟨A, hA, h₀, h₁⟩ := CommonIsotropicSubspace.exists_common_isotropic_vectors h₂
    (coefficientBilinear (forms 0)) (coefficientBilinear (forms 1))
    (coefficientBilinear_isAlt _) (coefficientBilinear_isAlt _) (t + 2)
    (by simpa using hs)
  apply exists_isotropicChartPoint_of_rows forms A hA
  intro l i j
  fin_cases l
  · exact (coefficientBilinear_rows (forms 0) A i j).symm.trans (h₀ i j)
  · exact (coefficientBilinear_rows (forms 1) A i j).symm.trans (h₁ i j)

end PaperVerification.AlternatingForms
