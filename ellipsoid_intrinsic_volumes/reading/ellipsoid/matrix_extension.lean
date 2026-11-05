module

public import Ellipsoid.PositiveJacobians

@[expose] public section

noncomputable section

open Matrix
open scoped BigOperators

namespace EllipsoidVerification

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def principalSelector (s : Finset ι) : Matrix s ι ℝ :=
  fun i j => if i.val = j then 1 else 0

def extendPrincipal (s : Finset ι) (A : Matrix s s ℝ) : Matrix ι ι ℝ :=
  (principalSelector s)ᵀ * A * principalSelector s

theorem extendPrincipal_apply (s : Finset ι) (A : Matrix s s ℝ) (i j : ι) :
    extendPrincipal s A i j = if hi : i ∈ s then
      if hj : j ∈ s then A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := by
  unfold extendPrincipal
  simp only [Matrix.mul_apply, Matrix.transpose_apply, principalSelector,
    Finset.sum_mul, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · rw [dif_pos hi, dif_pos hj]
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · rw [Finset.sum_eq_single ⟨i, hi⟩]
        · simp
        · intro a ha hai
          have hai' : a.val ≠ i := fun h => hai (Subtype.ext h)
          simp [hai']
        · simp
      · intro b hb hbj
        have hbj' : b.val ≠ j := fun h => hbj (Subtype.ext h)
        simp [hbj']
      · simp
    · rw [dif_pos hi, dif_neg hj]
      apply Finset.sum_eq_zero
      intro b hb
      have hbj : b.val ≠ j := fun h => hj (h ▸ b.property)
      simp [hbj]
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro b hb
    split_ifs
    · apply Finset.sum_eq_zero
      intro a ha
      have hai : a.val ≠ i := fun h => hi (h ▸ a.property)
      simp [hai]
    · rfl

theorem extendPrincipal_posSemidef (s : Finset ι) {A : Matrix s s ℝ}
    (hA : A.PosSemidef) : (extendPrincipal s A).PosSemidef := by
  simpa only [extendPrincipal, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hA.conjTranspose_mul_mul_same (principalSelector s)

end EllipsoidVerification
