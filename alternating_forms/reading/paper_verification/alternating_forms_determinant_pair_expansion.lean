module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.Ring

/-!
# Pairing determinant permutations without dividing by two

Pair a permutation with its right composition by the transposition of the
first two columns.  The representative whose first two row indices are
increasing contributes one alternating row-pair expression.  This is a
literal determinant identity over every commutative ring, including
characteristic two.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.AlternatingForms

variable {R : Type*} [CommRing R] {t : ℕ}

def firstPairSwapPermutation (σ : Equiv.Perm (Fin (t+2))) :
    Equiv.Perm (Fin (t+2)) := σ * Equiv.swap 0 (Fin.succ 0)

@[simp] theorem firstPairSwapPermutation_zero (σ : Equiv.Perm (Fin (t+2))) :
    firstPairSwapPermutation σ 0 = σ (Fin.succ 0) := by
  simp only [firstPairSwapPermutation, Equiv.Perm.mul_apply, Equiv.swap_apply_left]

@[simp] theorem firstPairSwapPermutation_one (σ : Equiv.Perm (Fin (t+2))) :
    firstPairSwapPermutation σ (Fin.succ 0) = σ 0 := by
  simp only [firstPairSwapPermutation, Equiv.Perm.mul_apply, Equiv.swap_apply_right]

@[simp] theorem firstPairSwapPermutation_tail (σ : Equiv.Perm (Fin (t+2)))
    (i : Fin t) : firstPairSwapPermutation σ i.succ.succ = σ i.succ.succ := by
  have hzero : i.succ.succ ≠ (0 : Fin (t+2)) := Fin.succ_ne_zero _
  have hone : i.succ.succ ≠ (Fin.succ 0 : Fin (t+2)) := by
    intro h
    exact Fin.succ_ne_zero i (Fin.succ_injective _ h)
  simp only [firstPairSwapPermutation, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hzero hone]

@[simp] theorem firstPairSwapPermutation_twice (σ : Equiv.Perm (Fin (t+2))) :
    firstPairSwapPermutation (firstPairSwapPermutation σ)=σ := by
  apply Equiv.ext
  intro i
  simp only [firstPairSwapPermutation, Equiv.Perm.mul_apply, Equiv.swap_apply_self]

theorem firstPairSwapPermutation_sign (σ : Equiv.Perm (Fin (t+2))) :
    Equiv.Perm.sign (firstPairSwapPermutation σ) = -Equiv.Perm.sign σ := by
  have hne : (0 : Fin (t+2)) ≠ Fin.succ 0 := (Fin.succ_ne_zero 0).symm
  rw [firstPairSwapPermutation, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
  simp only [mul_neg, mul_one]

/-- The exact two-column Laplace expansion with one representative from
each transposition pair. No cancellation of the scalar 2 is used. -/
theorem determinant_pair_expansion (M : Matrix (Fin (t+2)) (Fin (t+2)) R) :
    M.det =
      ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin (t+2)) =>
          σ 0 < σ (Fin.succ 0)),
        Equiv.Perm.sign σ •
          ((M (σ 0) 0 * M (σ (Fin.succ 0)) (Fin.succ 0) -
              M (σ 0) (Fin.succ 0) * M (σ (Fin.succ 0)) 0) *
            ∏ i : Fin t, M (σ i.succ.succ) i.succ.succ) := by
  classical
  let H : Equiv.Perm (Fin (t+2)) → Prop := fun σ => σ 0 < σ (Fin.succ 0)
  let term : Equiv.Perm (Fin (t+2)) → R :=
    fun σ => Equiv.Perm.sign σ • ∏ i, M (σ i) i
  have hreverse :
      (∑ σ ∈ Finset.univ.filter (fun σ => ¬H σ), term σ) =
        ∑ σ ∈ Finset.univ.filter H, term (firstPairSwapPermutation σ) := by
    symm
    apply Finset.sum_bij (fun σ _ => firstPairSwapPermutation σ)
    · intro σ hσ
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hσ' := (Finset.mem_filter.mp hσ).2
      change ¬ firstPairSwapPermutation σ 0 <
        firstPairSwapPermutation σ (Fin.succ 0)
      rw [firstPairSwapPermutation_zero, firstPairSwapPermutation_one]
      exact not_lt_of_ge (le_of_lt hσ')
    · intro σ hσ τ hτ h
      have hh := congrArg firstPairSwapPermutation h
      simpa only [firstPairSwapPermutation_twice] using hh
    · intro σ hσ
      refine ⟨firstPairSwapPermutation σ, ?_, firstPairSwapPermutation_twice σ⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hσ' := (Finset.mem_filter.mp hσ).2
      have hne : σ 0 ≠ σ (Fin.succ 0) :=
        σ.injective.ne (Fin.succ_ne_zero 0).symm
      change firstPairSwapPermutation σ 0 < firstPairSwapPermutation σ (Fin.succ 0)
      rw [firstPairSwapPermutation_zero, firstPairSwapPermutation_one]
      exact lt_of_le_of_ne (le_of_not_gt hσ') hne.symm
    · intro σ hσ
      rfl
  have hterm (σ : Equiv.Perm (Fin (t+2))) :
      term σ + term (firstPairSwapPermutation σ) =
        Equiv.Perm.sign σ •
          ((M (σ 0) 0 * M (σ (Fin.succ 0)) (Fin.succ 0) -
              M (σ 0) (Fin.succ 0) * M (σ (Fin.succ 0)) 0) *
            ∏ i : Fin t, M (σ i.succ.succ) i.succ.succ) := by
    simp only [term, Fin.prod_univ_succ, firstPairSwapPermutation_zero,
      firstPairSwapPermutation_one, firstPairSwapPermutation_tail,
      firstPairSwapPermutation_sign, Units.smul_def, Units.val_neg, neg_smul]
    rw [← sub_eq_add_neg, ← smul_sub]
    congr 1
    ring
  rw [Matrix.det_apply]
  change (∑ σ, term σ) = _
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ H term,
    hreverse, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun σ hσ => hterm σ)

end PaperVerification.AlternatingForms
