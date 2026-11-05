module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

/-!
# The all-one Newton expansion induction

The three actual suffix recurrences prove both parts of the paper's
auxiliary assertion. In particular, vanishing above the required height is
an algebraic consequence of those recurrences; it does not require assuming
polynomial Cramer coefficients before the determinant is known nonzero.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PaperVerification.Fermion.Newton

open scoped BigOperators

variable {L : Type*} [CommRing L] {n : ℕ}

/-- The exact auxiliary assertion used in the all-one determinant induction. -/
def PowerExpansionPattern (height : Fin n → ℤ) (A : ℕ → Fin n → L) : Prop :=
  (∀ d : ℕ, 1 ≤ d → ∀ i, (d : ℤ) < height i → A d i = 0) ∧
  (∀ d : ℕ, 1 ≤ d → ∀ i, height i = (d : ℤ) →
    A d i = if ∀ j, j < i → height j ≠ (d : ℤ) then 1 else 0)

theorem firstHeight_succ_iff
    (height : Fin (n + 1) → ℤ) (suffixHeight : Fin n → ℤ) (σ : ℤ)
    (hzero : height 0 = 1) (hsucc : ∀ i, height i.succ = suffixHeight i + σ)
    (d e : ℕ) (hd : 2 ≤ d) (he : (e : ℤ) + σ = d) (i : Fin n) :
    (∀ j, j < i.succ → height j ≠ (d : ℤ)) ↔
      ∀ j, j < i → suffixHeight j ≠ (e : ℤ) := by
  constructor
  · intro h j hj hjh
    apply h j.succ (by simpa using hj)
    rw [hsucc, hjh, he]
  · intro h j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · intro hj heq
      rw [hzero] at heq
      omega
    · intro hk heq
      apply h k (by simpa using hk)
      rw [hsucc] at heq
      omega

/-- The recurrence data are the three block-elimination identities for the
literal Newton matrix. No freeness, degree, or determinant conclusion is
included among these hypotheses. -/
theorem powerExpansionPattern_of_suffix_recurrences
    (height : Fin (n + 1) → ℤ) (suffixHeight : Fin n → ℤ)
    (A : ℕ → Fin (n + 1) → L) (B : ℕ → Fin n → L) (z : L) (σ : ℤ)
    (hσ : σ = -1 ∨ σ = 0 ∨ σ = 1)
    (hzero : height 0 = 1)
    (hsucc : ∀ i, height i.succ = suffixHeight i + σ)
    (hB : PowerExpansionPattern suffixHeight B)
    (hfirst : ∀ i, A 1 i = if i = 0 then 1 else 0)
    (hflat : σ = 0 → ∀ d, 2 ≤ d → ∀ i,
      A d i.succ = B d i - z ^ (d - 1) * B 1 i)
    (hup : σ = 1 → ∀ d, 2 ≤ d → ∀ i,
      A d i.succ = ∑ a ∈ Finset.range (d - 1), z ^ (d - 2 - a) * B (a + 1) i)
    (hdown : σ = -1 → ∀ d, 2 ≤ d → ∀ i,
      A d i.succ = B (d + 1) i - z * B d i - A d 0 * B 2 i + z * A d 0 * B 1 i) :
    PowerExpansionPattern height A := by
  constructor
  · intro d hd i hi
    by_cases hd1 : d = 1
    · subst d
      have hi0 : i ≠ 0 := by
        intro he
        subst i
        rw [hzero] at hi
        omega
      rw [hfirst, if_neg hi0]
    · have hd2 : 2 ≤ d := by omega
      revert hi
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · intro hi
        rw [hzero] at hi
        omega
      · intro hi
        have hh := hsucc i
        rcases hσ with hσ | hσ | hσ
        · rw [hdown hσ d hd2 i,
            hB.1 (d + 1) (by omega) i (by omega),
            hB.1 d hd i (by omega), hB.1 2 (by omega) i (by omega),
            hB.1 1 (by omega) i (by omega)]
          ring
        · rw [hflat hσ d hd2 i,
            hB.1 d hd i (by omega), hB.1 1 (by omega) i (by omega)]
          ring
        · rw [hup hσ d hd2 i]
          apply Finset.sum_eq_zero
          intro a ha
          have ha' : a < d - 1 := Finset.mem_range.mp ha
          rw [hB.1 (a + 1) (by omega) i (by omega), mul_zero]
  · intro d hd i hi
    by_cases hd1 : d = 1
    · subst d
      rw [hfirst]
      by_cases hi0 : i = 0
      · subst i
        simp
      · have hn : ¬ ∀ j, j < i → height j ≠ (1 : ℤ) := by
          intro hf
          exact hf 0 (Fin.pos_iff_ne_zero.mpr hi0) hzero
        simp only [Int.natCast_one,if_neg hi0,if_neg hn]
    · have hd2 : 2 ≤ d := by omega
      revert hi
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · intro hi
        rw [hzero] at hi
        omega
      · intro hi
        have hh := hsucc i
        rcases hσ with hσ | hσ | hσ
        · have hsi : suffixHeight i = ((d + 1 : ℕ) : ℤ) := by omega
          rw [hdown hσ d hd2 i,
            hB.1 d hd i (by omega), hB.1 2 (by omega) i (by omega),
            hB.1 1 (by omega) i (by omega),
            hB.2 (d + 1) (by omega) i hsi]
          have hfirst' := firstHeight_succ_iff height suffixHeight σ hzero hsucc
            d (d + 1) hd2 (by omega) i
          simp only [hfirst',mul_zero,sub_zero,add_zero]
        · have hsi : suffixHeight i = (d : ℤ) := by omega
          rw [hflat hσ d hd2 i, hB.1 1 (by omega) i (by omega),
            hB.2 d hd i hsi]
          have hfirst' := firstHeight_succ_iff height suffixHeight σ hzero hsucc
            d d hd2 (by omega) i
          simp only [hfirst',mul_zero,sub_zero,add_zero]
        · have hsi : suffixHeight i = ((d - 1 : ℕ) : ℤ) := by omega
          rw [hup hσ d hd2 i, Finset.sum_eq_single (d - 2)]
          · have ha : (d - 2) + 1 = d - 1 := by omega
            rw [Nat.sub_self, pow_zero, one_mul, ha, hB.2 (d - 1) (by omega) i hsi]
            have hfirst' := firstHeight_succ_iff height suffixHeight σ hzero hsucc
              d (d - 1) hd2 (by omega) i
            simp only [hfirst']
          · intro a ha hane
            have ha' : a < d - 1 := Finset.mem_range.mp ha
            rw [hB.1 (a + 1) (by omega) i (by omega), mul_zero]
          · intro hnot
            exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

end PaperVerification.Fermion.Newton
