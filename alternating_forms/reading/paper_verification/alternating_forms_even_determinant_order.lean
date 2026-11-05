module

public import PaperVerification.AlternatingFormsEvenDeterminants
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The unique least exponent in an odd-subset determinant

The row order is the literal alternating constant/variable order. Under
b_i=t^i and c_i=t^(m-1-i), its slopes are r,r-1,...,-r.
Strict rearrangement gives a unique least permutation, uniformly in r.
No experimentally checked determinant or finite size bound is used.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.EvenDeterminants

open scoped BigOperators

/-- Interleave the two actual row families. -/
def rowPosition (r : ℕ) : OddRows r → Fin (2 * r + 1)
  | Sum.inl i => ⟨2 * i.val, by omega⟩
  | Sum.inr i => ⟨2 * i.val + 1, by omega⟩

theorem rowPosition_injective (r : ℕ) : Function.Injective (rowPosition r) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      apply congrArg Sum.inl
      apply Fin.ext
      have hv := congrArg Fin.val hij
      dsimp [rowPosition] at hv
      omega
    | inr j =>
      have hv := congrArg Fin.val hij
      dsimp [rowPosition] at hv
      omega
  | inr i =>
    cases j with
    | inl j =>
      have hv := congrArg Fin.val hij
      dsimp [rowPosition] at hv
      omega
    | inr j =>
      apply congrArg Sum.inr
      apply Fin.ext
      have hv := congrArg Fin.val hij
      dsimp [rowPosition] at hv
      omega

theorem rowPosition_surjective (r : ℕ) : Function.Surjective (rowPosition r) := by
  intro j
  by_cases he : j.val % 2 = 0
  · refine ⟨Sum.inl ⟨j.val / 2, by have := j.isLt; omega⟩, ?_⟩
    apply Fin.ext
    dsimp [rowPosition]
    omega
  · refine ⟨Sum.inr ⟨j.val / 2, by have := j.isLt; omega⟩, ?_⟩
    apply Fin.ext
    dsimp [rowPosition]
    omega

def rowPositionEquiv (r : ℕ) : OddRows r ≃ Fin (2 * r + 1) :=
  Equiv.ofBijective (rowPosition r)
    ⟨rowPosition_injective r, rowPosition_surjective r⟩

@[simp] theorem rowPositionEquiv_apply (r : ℕ) (i : OddRows r) :
    rowPositionEquiv r i = rowPosition r i := rfl

/-- The integer part of the assignment cost that depends on the permutation. -/
def assignmentCost {n : ℕ} (r : ℤ) (v : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) : ℤ :=
  ∑ i, (r - (i.val : ℤ)) * v (σ i)

theorem assignment_antivary {n : ℕ} (r : ℤ) (v : Fin n → ℤ) (hv : StrictMono v) :
    Antivary (fun i : Fin n => r - (i.val : ℤ)) v := by
  intro i j hij
  have hlt : i < j := hv.lt_iff_lt.mp hij
  have hval : (i.val : ℤ) ≤ j.val := by exact_mod_cast hlt.le
  exact sub_le_sub_left hval r

theorem assignmentCost_minimal {n : ℕ} (r : ℤ) (v : Fin n → ℤ)
    (hv : StrictMono v) (σ : Equiv.Perm (Fin n)) :
    assignmentCost r v 1 ≤ assignmentCost r v σ := by
  simpa only [assignmentCost, Equiv.Perm.one_apply] using
    (assignment_antivary r v hv).sum_mul_le_sum_mul_comp_perm (σ := σ)

/-- Equality in this strict rearrangement forces the actual permutation to be identity. -/
theorem assignmentCost_eq_minimal_iff {n : ℕ} (r : ℤ) (v : Fin n → ℤ)
    (hv : StrictMono v) (σ : Equiv.Perm (Fin n)) :
    assignmentCost r v σ = assignmentCost r v 1 ↔ σ = 1 := by
  constructor
  · intro heq
    have hanti : Antivary (fun i : Fin n => r - (i.val : ℤ)) (v ∘ σ) :=
      (assignment_antivary r v hv).sum_mul_eq_sum_mul_comp_perm_iff.mp
        (by simpa only [assignmentCost, Equiv.Perm.one_apply] using heq)
    have hmono : StrictMono σ := by
      intro i j hij
      by_contra hnot
      have hle : σ j ≤ σ i := le_of_not_gt hnot
      have hne : σ j ≠ σ i := σ.injective.ne (ne_of_lt hij).symm
      have hlt : σ j < σ i := lt_of_le_of_ne hle hne
      have hbad := hanti (hv hlt)
      change r - (i.val : ℤ) ≤ r - (j.val : ℤ) at hbad
      have hij' : i.val < j.val := hij
      omega
    apply Equiv.ext
    intro i
    exact congrFun hmono.eq_id i
  · rintro rfl
    rfl

theorem assignmentCost_strict {n : ℕ} (r : ℤ) (v : Fin n → ℤ)
    (hv : StrictMono v) (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
    assignmentCost r v 1 < assignmentCost r v σ :=
  lt_of_le_of_ne (assignmentCost_minimal r v hv σ)
    (fun h => hσ ((assignmentCost_eq_minimal_iff r v hv σ).mp h.symm))

/-- The nonnegative t-exponent of each actual matrix entry. -/
def entryExponent (m r : ℕ) : OddRows r → Fin m → ℕ
  | Sum.inl i, j => (r - i.val) * j.val + i.val * (m - 1 - j.val)
  | Sum.inr i, j => (r - 1 - i.val) * j.val + i.val * (m - 1 - j.val)

/-- The row-dependent constant in the exponent; it is independent of the column. -/
def rowExponentConstant (m r : ℕ) : OddRows r → ℤ
  | Sum.inl i => (i.val : ℤ) * ((m : ℤ) - 1)
  | Sum.inr i => (i.val : ℤ) * ((m : ℤ) - 1)

theorem entryExponent_cast (m r : ℕ) (i : OddRows r) (j : Fin m) :
    (entryExponent m r i j : ℤ) =
      ((r : ℤ) - (rowPosition r i).val) * j.val + rowExponentConstant m r i := by
  have hm : 1 ≤ m := by have := j.isLt; omega
  have hj : j.val ≤ m - 1 := by have := j.isLt; omega
  have hc : ((m - 1 - j.val : ℕ) : ℤ) = (m : ℤ) - 1 - j.val := by
    rw [Nat.cast_sub hj, Nat.cast_sub hm]
    norm_num
  cases i with
  | inl i =>
    have hi : i.val ≤ r := by have := i.isLt; omega
    have hr : ((r - i.val : ℕ) : ℤ) = (r : ℤ) - i.val := Nat.cast_sub hi
    simp only [entryExponent, rowPosition, rowExponentConstant, Nat.cast_add,
      Nat.cast_mul, hr, hc, Fin.val_mk]
    ring
  | inr i =>
    have hr₁ : 1 ≤ r := by have := i.isLt; omega
    have hi : i.val ≤ r - 1 := by have := i.isLt; omega
    have hr : ((r - 1 - i.val : ℕ) : ℤ) = (r : ℤ) - 1 - i.val := by
      rw [Nat.cast_sub hi, Nat.cast_sub hr₁]
      norm_num
    simp only [entryExponent, rowPosition, rowExponentConstant, Nat.cast_add,
      Nat.cast_mul, Nat.cast_one, hr, hc, Fin.val_mk]
    ring

def determinantTermExponent (m r : ℕ) (I : Fin (2 * r + 1) → Fin m)
    (σ : Equiv.Perm (OddRows r)) : ℕ :=
  ∑ i, entryExponent m r i (I (rowPosition r (σ i)))

theorem determinantTermExponent_cast (m r : ℕ) (I : Fin (2 * r + 1) → Fin m)
    (σ : Equiv.Perm (OddRows r)) :
    (determinantTermExponent m r I σ : ℤ) =
      (∑ i, rowExponentConstant m r i) +
        assignmentCost (r : ℤ) (fun j => (I j).val)
          (Equiv.permCongr (rowPositionEquiv r) σ) := by
  rw [determinantTermExponent, Nat.cast_sum]
  simp_rw [entryExponent_cast]
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  unfold assignmentCost
  apply Fintype.sum_equiv (rowPositionEquiv r) _ _
  intro i
  simp only [Equiv.permCongr_apply, rowPositionEquiv_apply]
  rw [show (rowPositionEquiv r).symm (rowPosition r i) = i from
    (rowPositionEquiv r).symm_apply_apply i]

theorem determinantTermExponent_unique_minimum (m r : ℕ)
    (I : Fin (2 * r + 1) → Fin m) (hI : StrictMono I)
    (σ : Equiv.Perm (OddRows r)) (hσ : σ ≠ 1) :
    determinantTermExponent m r I 1 < determinantTermExponent m r I σ := by
  have hone : Equiv.permCongr (rowPositionEquiv r) (1 : Equiv.Perm (OddRows r)) = 1 := by
    apply Equiv.ext
    intro i
    simp only [Equiv.permCongr_apply, Equiv.Perm.one_apply, Equiv.apply_symm_apply]
  have hv : StrictMono (fun j => ((I j).val : ℤ)) := by
    intro i j hij
    have hval : (I i).val < (I j).val := hI hij
    exact Int.ofNat_lt.mpr hval
  have hσ' : Equiv.permCongr (rowPositionEquiv r) σ ≠ 1 := by
    intro he
    apply hσ
    apply (Equiv.permCongr (rowPositionEquiv r)).injective
    rw [hone]
    exact he
  have hlt := assignmentCost_strict (r : ℤ) (fun j => ((I j).val : ℤ)) hv
    (Equiv.permCongr (rowPositionEquiv r) σ) hσ'
  have h₁ := determinantTermExponent_cast m r I 1
  have h₂ := determinantTermExponent_cast m r I σ
  rw [hone] at h₁
  omega

end PaperVerification.AlternatingForms.EvenDeterminants

