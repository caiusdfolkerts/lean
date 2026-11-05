import bier.padded_inverse_span
import Mathlib.LinearAlgebra.Matrix.Block

/-! # The coordinate computation behind the geometric Schur complement -/

noncomputable section

namespace Bier

open Classical Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem det_fintype_irrel {J : Type*} [DecidableEq J]
    (F F' : Fintype J) (A : Matrix J J ℝ) :
    @Matrix.det J _ F ℝ _ A = @Matrix.det J _ F' ℝ _ A := by
  have he : F = F' := Subsingleton.elim _ _
  cases he
  rfl

def replacementMatrix (X : Matrix ι ι ℝ) (S : Finset ι) : Matrix ι ι ℝ :=
  fun i j => if j ∈ S then X i j else (1 : Matrix ι ι ℝ) i j

set_option backward.isDefEq.respectTransparency false in
theorem replacementMatrix_det (X : Matrix ι ι ℝ) (S : Finset ι) :
    (replacementMatrix X S).det = (principalMatrix X S).det := by
  rw [Matrix.det_toBlock _ (fun j => j ∈ S)]
  have hF : Subtype.fintype (fun j => j ∈ S) = Finset.Subtype.fintype S := Subsingleton.elim _ _
  try simp only [hF]
  have h11 : Matrix.toBlock (replacementMatrix X S) (fun j => j ∈ S) (fun j => j ∈ S) =
      principalMatrix X S := by
    ext i j
    simp [Matrix.toBlock_apply, replacementMatrix, principalMatrix]
  have h12 : Matrix.toBlock (replacementMatrix X S) (fun j => j ∈ S) (fun j => j ∉ S) = 0 := by
    ext i j
    have hij : i.val ≠ j.val := fun he => j.property (he ▸ i.property)
    simp [Matrix.toBlock_apply, replacementMatrix, Matrix.one_apply, hij, j.property]
  have h22 : Matrix.toBlock (replacementMatrix X S) (fun j => j ∉ S) (fun j => j ∉ S) = 1 := by
    ext i j
    simp [Matrix.toBlock_apply, replacementMatrix, Matrix.one_apply, Subtype.ext_iff, j.property]
  rw [h11, h12, h22]
  have hb := Matrix.det_fromBlocks_zero₁₂ (principalMatrix X S)
    (Matrix.toBlock (replacementMatrix X S) (fun j => j ∉ S) (fun j => j ∈ S))
    (1 : Matrix {j // j ∉ S} {j // j ∉ S} ℝ)
  rw [Matrix.det_one, mul_one] at hb
  convert! hb using 1
  exact det_fintype_irrel _ _ _

theorem replacementMatrix_principal_isUnit (X : Matrix ι ι ℝ) (S : Finset ι)
    (h : IsUnit (replacementMatrix X S)) : IsUnit (principalMatrix X S).det := by
  rw [← replacementMatrix_det]
  exact (Matrix.isUnit_iff_isUnit_det _).mp h

theorem replacementMatrix_mulVec (X : Matrix ι ι ℝ) (S : Finset ι)
    (a : ι → ℝ) (i : ι) :
    (replacementMatrix X S *ᵥ a) i =
      (∑ j ∈ S, X i j * a j) + if i ∈ S then 0 else a i := by
  simp only [Matrix.mulVec, dotProduct, replacementMatrix, ite_mul]
  rw [Finset.sum_ite]
  simp [Matrix.one_apply, ite_mul, Finset.filter_mem_eq_inter, eq_comm]

theorem replacementMatrix_solution_restrict (X : Matrix ι ι ℝ) (S : Finset ι)
    (hS : IsUnit (principalMatrix X S).det) (a b : ι → ℝ)
    (h : replacementMatrix X S *ᵥ a = b) :
    (fun j : S => a j.val) = (principalMatrix X S)⁻¹ *ᵥ (fun j : S => b j.val) := by
  have he : principalMatrix X S *ᵥ (fun j : S => a j.val) = fun j : S => b j.val := by
    funext i
    have hi := congrFun h i.val
    rw [replacementMatrix_mulVec, if_pos i.property, add_zero] at hi
    rw [Finset.sum_subtype (p := fun j => j ∈ S) (F := inferInstance) S (fun _ => Iff.rfl)] at hi
    simpa only [Matrix.mulVec, dotProduct, principalMatrix, Matrix.submatrix_apply] using hi
  have hi := congrArg (fun b : S → ℝ => (principalMatrix X S)⁻¹ *ᵥ b) he
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hS, Matrix.one_mulVec] at hi
  exact hi

def schurValue (X : Matrix ι ι ℝ) (S : Finset ι) (a : ι) : ℝ :=
  X a a - ∑ i : S, ∑ j : S, X a i.val * (principalMatrix X S)⁻¹ i j * X j.val a

theorem replacementMatrix_solution_coordinate (X : Matrix ι ι ℝ) (S : Finset ι)
    (hS : IsUnit (principalMatrix X S).det) (a : ι) (ha : a ∉ S) (α : ι → ℝ)
    (h : replacementMatrix X S *ᵥ α = fun j => X j a) :
    α a = schurValue X S a := by
  have hrestrict := replacementMatrix_solution_restrict X S hS α (fun j => X j a) h
  have he := congrFun h a
  rw [replacementMatrix_mulVec, if_neg ha] at he
  rw [Finset.sum_subtype (p := fun j => j ∈ S) (F := inferInstance) S (fun _ => Iff.rfl)] at he
  have hsum : (∑ j : S, X a j.val * α j.val) =
      ∑ i : S, ∑ j : S, X a i.val * (principalMatrix X S)⁻¹ i j * X j.val a := by
    apply Finset.sum_congr rfl
    intro i _
    have hi := congrFun hrestrict i
    rw [hi]
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hsum] at he
  unfold schurValue
  linarith

end Bier
