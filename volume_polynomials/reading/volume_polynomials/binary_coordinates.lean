module

public import VolumePolynomials.BinaryPolynomial
public import VolumePolynomials.BinarySequences
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

set_option autoImplicit false
noncomputable section

/-! Exact equivalence between the full homogeneous coefficient vector and
the binomial normalization in Appendix A. Every degree-`d` monomial occurs
once; no coordinate is discarded. -/

open Set MeasureTheory
open scoped Pointwise BigOperators

namespace VolumePolynomials

def binaryIndex (d : ℕ) (i : Fin (d + 1)) : MultiIndex 2 d :=
  ⟨![⟨d - i.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩, i], by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)⟩

def binaryIndexEquiv (d : ℕ) : Fin (d + 1) ≃ MultiIndex 2 d where
  toFun := binaryIndex d
  invFun a := a.1 1
  left_inv i := rfl
  right_inv a := by
    first
    | apply Subtype.ext
      funext j
      fin_cases j
      · apply Fin.ext
        have h := a.2
        simp only [Fin.sum_univ_two] at h
        change d - (a.1 1).val = (a.1 0).val
        omega
      · rfl

def binaryNormalizedSequence {d : ℕ} (c : Coefficients 2 d) (i : ℕ) : ℝ :=
  if hi : i ≤ d then c (binaryIndex d ⟨i, Nat.lt_succ_of_le hi⟩) / (d.choose i : ℝ) else 0

theorem binaryNormalizedSequence_apply {d : ℕ} (c : Coefficients 2 d) (i : Fin (d + 1)) :
    binaryNormalizedSequence c i.val = c (binaryIndex d i) / (d.choose i.val : ℝ) := by
  first
  | simp only [binaryNormalizedSequence, dif_pos (Nat.le_of_lt_succ i.isLt)]

theorem choose_mul_binaryNormalizedSequence {d : ℕ} (c : Coefficients 2 d)
    (i : Fin (d + 1)) :
    (d.choose i.val : ℝ) * binaryNormalizedSequence c i.val = c (binaryIndex d i) := by
  first
  | rw [binaryNormalizedSequence_apply]
    apply mul_div_cancel₀
    exact_mod_cast (Nat.choose_pos (Nat.le_of_lt_succ i.isLt)).ne'

theorem evaluate_binary {d : ℕ} (c : Coefficients 2 d) (t : Fin 2 → ℝ) :
    evaluate c t = BinarySimplex.value d (binaryNormalizedSequence c) (t 0) (t 1) := by
  first
  | unfold evaluate BinarySimplex.value
    have heq := Fintype.sum_equiv (binaryIndexEquiv d)
      (fun i => c (binaryIndex d i) * ∏ j : Fin 2, t j ^ ((binaryIndex d i).1 j : ℕ))
      (fun a => c a * ∏ j : Fin 2, t j ^ (a.1 j : ℕ)) (fun _ => rfl)
    rw [← heq, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [← choose_mul_binaryNormalizedSequence c i]
    simp only [binaryIndex, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem realizes_binary_iff {d : ℕ} (c : Coefficients 2 d) (K : Fin 2 → Body d) :
    Realizes K c ↔ BinarySimplex.Realizes d (binaryNormalizedSequence c) (K 0) (K 1) := by
  first
  | constructor
    · intro h t s ht hs
      have hw : ∀ i : Fin 2, 0 ≤ (![t, s] : Fin 2 → ℝ) i := by
        first
        | intro i
          fin_cases i <;> assumption
      have he := h ![t, s] hw
      rw [evaluate_binary] at he
      simpa only [volumeFunction, weightedSum, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one] using he.symm
    · intro h t ht
      rw [evaluate_binary]
      simpa only [volumeFunction, weightedSum, Fin.sum_univ_two] using
        (h (t 0) (t 1) (ht 0) (ht 1)).symm

theorem binary_volumeLocus_iff {d : ℕ} (c : Coefficients 2 d) :
    c ∈ VolumeLocus 2 d ↔
      ∃ A B : Body d, BinarySimplex.Realizes d (binaryNormalizedSequence c) A B := by
  first
  | constructor
    · rintro ⟨K, hK⟩
      exact ⟨K 0, K 1, (realizes_binary_iff c K).mp hK⟩
    · rintro ⟨A, B, h⟩
      exact ⟨![A, B], (realizes_binary_iff c ![A, B]).mpr h⟩

end VolumePolynomials
