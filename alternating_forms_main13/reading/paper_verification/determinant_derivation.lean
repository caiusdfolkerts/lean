module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

/-!
# The Leibniz rule for the determinant

The proof expands the actual determinant and uses the ordinary Leibniz rule.
It does not assume differentiability or invertibility of the matrix.
-/

@[expose] public section

set_option autoImplicit false

namespace PaperVerification.DeterminantDerivation

open scoped BigOperators

variable {K A ι n : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem derivation_finset_prod [DecidableEq ι]
    (D : Derivation K A A) (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) =
      ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hself : (insert a s).erase a = s := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hja, h | h⟩
        · exact (hja h).elim
        · exact h
      · intro hj
        exact ⟨ne_of_mem_of_not_mem hj ha, Or.inr hj⟩
    have hother (i : ι) (hi : i ∈ s) :
        (insert a s).erase i = insert a (s.erase i) := by
      have hai : a ≠ i := (ne_of_mem_of_not_mem hi ha).symm
      ext j
      simp only [Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hji, hja | hj⟩
        · exact Or.inl hja
        · exact Or.inr ⟨hji, hj⟩
      · rintro (rfl | ⟨hji, hj⟩)
        · exact ⟨hai, Or.inl rfl⟩
        · exact ⟨hji, Or.inr hj⟩
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha, hself]
    simp only [smul_eq_mul]
    rw [Finset.mul_sum, add_comm]
    congr 1
    · exact mul_comm _ _
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hother i hi, Finset.prod_insert]
      · ring
      · exact fun h => ha (Finset.mem_of_mem_erase h)

variable [Fintype n] [DecidableEq n]

theorem determinant_row_expansion (M : Matrix n n A) :
    M.det = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : A) *
      ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose M, Matrix.det_apply']
  rfl

/-- Jacobi's row formula, over every commutative algebra, with no inverse. -/
theorem derivation_det_rows (D : Derivation K A A) (M : Matrix n n A) :
    D M.det =
      ∑ i, (M.updateRow i (fun j => D (M i j))).det := by
  classical
  calc
    D M.det =
        ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : A) *
          ∑ i, D (M i (σ i)) * ∏ j ∈ Finset.univ.erase i, M j (σ j) := by
      rw [determinant_row_expansion, map_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [D.leibniz, D.map_intCast, smul_zero, add_zero,
        derivation_finset_prod]
      rfl
    _ = ∑ i, ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : A) *
          (D (M i (σ i)) * ∏ j ∈ Finset.univ.erase i, M j (σ j)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i, (M.updateRow i (fun j => D (M i j))).det := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [determinant_row_expansion]
      apply Finset.sum_congr rfl
      intro σ hσ
      congr 1
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => (M.updateRow i (fun k => D (M i k))) j (σ j))
        (Finset.mem_univ i)]
      rw [Matrix.updateRow_self]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [Matrix.updateRow_ne (Finset.mem_erase.mp hj).1]

end PaperVerification.DeterminantDerivation

