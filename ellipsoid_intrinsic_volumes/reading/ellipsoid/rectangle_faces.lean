module

public import Ellipsoid.RectangleIsolation
public import Mathlib.Analysis.Calculus.FDeriv.Pi

@[expose] public section

noncomputable section

open Matrix Set Filter
open scoped BigOperators Topology

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def faceLinear (s : Finset ι) : (s → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => if h : i ∈ s then ContinuousLinearMap.proj ⟨i, h⟩ else 0

def faceRestrict (s : Finset ι) : (ι → ℝ) →L[ℝ] (s → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.val

def faceInsert (a : ι → ℝ) (s : Finset ι) (y : s → ℝ) : ι → ℝ :=
  fun i => if h : i ∈ s then y ⟨i, h⟩ else a i

theorem faceInsert_eq_affine (a : ι → ℝ) (s : Finset ι) (y : s → ℝ) :
    faceInsert a s y = faceLinear s y + (fun i => if i ∈ s then 0 else a i) := by
  funext i
  simp [faceInsert, faceLinear]
  split_ifs <;> simp

@[fun_prop] theorem continuous_faceInsert (a : ι → ℝ) (s : Finset ι) :
    Continuous (faceInsert a s) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ s
  · simpa only [faceInsert, dif_pos hi] using
      (continuous_apply (⟨i, hi⟩ : s))
  · simpa only [faceInsert, dif_neg hi] using
      (continuous_const : Continuous (fun _ : s → ℝ => a i))

theorem hasFDerivAt_faceInsert (a : ι → ℝ) (s : Finset ι) (y : s → ℝ) :
    HasFDerivAt (faceInsert a s) (faceLinear s) y := by
  simpa only [← faceInsert_eq_affine] using (faceLinear s).hasFDerivAt.add_const
    (fun i => if i ∈ s then (0 : ℝ) else a i)

@[simp] theorem faceInsert_restrict_self (a : ι → ℝ) (s : Finset ι) :
    faceInsert a s (faceRestrict s a) = a := by
  funext i
  simp [faceInsert, faceRestrict]

@[simp] theorem faceRestrict_insert (a : ι → ℝ) (s : Finset ι) (y : s → ℝ) :
    faceRestrict s (faceInsert a s y) = y := by
  funext i
  simp [faceInsert, faceRestrict, i.property]

theorem faceInsert_mem_box {a b : ι → ℝ} (hab : a ≤ b) (s : Finset ι)
    {y : s → ℝ} (hy : y ∈ Icc (faceRestrict s a) (faceRestrict s b)) :
    faceInsert a s y ∈ Icc a b := by
  constructor <;> intro i <;> by_cases hi : i ∈ s
  · simpa [faceInsert, hi, faceRestrict] using hy.1 ⟨i, hi⟩
  · simp [faceInsert, hi]
  · simpa [faceInsert, hi, faceRestrict] using hy.2 ⟨i, hi⟩
  · simpa [faceInsert, hi] using hab i

set_option backward.isDefEq.respectTransparency false in
theorem faceDerivative_matrix (s : Finset ι) (A : Matrix ι ι ℝ) :
    (faceRestrict s).comp ((matrixDerivative A).comp (faceLinear s)) =
      matrixDerivative (A.submatrix (fun i : s => i.val) (fun i : s => i.val)) := by
  obtain ⟨B, rfl⟩ := (Matrix.of : (ι → ι → ℝ) ≃ Matrix ι ι ℝ).surjective A
  ext y i
  simp only [ContinuousLinearMap.comp_apply, faceRestrict, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply, matrixDerivative_apply, Matrix.mulVec, dotProduct,
    Matrix.submatrix_apply, Matrix.of_apply, faceLinear, dite_apply,
    ContinuousLinearMap.zero_apply, mul_dite, mul_zero]
  trans ∑ j : ι, if h : j ∈ s then B i.val j * y ⟨j, h⟩ else 0
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases h : j ∈ s
    · simp only [dif_pos h, ContinuousLinearMap.proj_apply]
    · simp only [dif_neg h, ContinuousLinearMap.zero_apply, mul_zero]
  · simpa only [Finset.univ_eq_attach] using
      (Finset.sum_attach_eq_sum_dite s (fun j : s => B i.val j.val * y j)).symm

def faceMap (F : (ι → ℝ) → (ι → ℝ)) (a : ι → ℝ) (s : Finset ι) (y : s → ℝ) : s → ℝ :=
  faceRestrict s (F (faceInsert a s y))

set_option backward.isDefEq.respectTransparency false in
theorem hasFDerivAt_faceMap {F : (ι → ℝ) → (ι → ℝ)} {a : ι → ℝ}
    (s : Finset ι) {y : s → ℝ} {A : Matrix ι ι ℝ}
    (hF : HasFDerivAt F (matrixDerivative A) (faceInsert a s y)) :
    HasFDerivAt (faceMap F a s)
      (matrixDerivative (A.submatrix (fun i : s => i.val) (fun i : s => i.val))) y := by
  change HasFDerivAt ((faceRestrict s) ∘ (F ∘ (faceInsert a s)))
    (matrixDerivative (A.submatrix (fun i : s => i.val) (fun i : s => i.val))) y
  exact ((faceRestrict s).hasFDerivAt.comp y
    (hF.comp y (hasFDerivAt_faceInsert a s y))).congr_fderiv
      (faceDerivative_matrix s A)

theorem continuousOn_faceMap {F : (ι → ℝ) → (ι → ℝ)} {a b : ι → ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Icc a b)) (s : Finset ι) :
    ContinuousOn (faceMap F a s) (Icc (faceRestrict s a) (faceRestrict s b)) := by
  exact (faceRestrict s).continuous.comp_continuousOn
    (hF.comp (continuous_faceInsert a s).continuousOn (fun y hy => faceInsert_mem_box hab s hy))

end EllipsoidVerification
