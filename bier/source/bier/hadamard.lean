import bier.sign_rank
import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Tactic.FinCases

/-!
# The explicit Paley–Walsh matrix

The twelve Paley labels are ordered as infinity, then the eleven field
elements.  All finite calculations below produce kernel-checked proofs.
The Walsh orthogonality theorem is proved for every finite coordinate set.
-/

namespace Bier

open scoped BigOperators Matrix Kronecker

def quadraticCharacter11 (a : ZMod 11) : ℤ :=
  if a = 0 then 0 else if ∃ x : ZMod 11, x * x = a then 1 else -1

/-- Index zero is infinity; index `i+1` is the field element `i`. -/
def paleyInt : Matrix (Fin 12) (Fin 12) ℤ := fun i j =>
  if i = 0 ∨ j = 0 then 1
  else if i = j then -1
  else quadraticCharacter11 ((j.val : ZMod 11) - (i.val : ZMod 11))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem paleyInt_sign : ∀ i j, paleyInt i j = 1 ∨ paleyInt i j = -1 := by
  unfold paleyInt
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem paleyInt_orthogonal :
    (paleyInt : Matrix (Fin 12) (Fin 12) ℤ) * Matrix.transpose paleyInt =
      (12 : ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ) := by
  decide

noncomputable def paley : Matrix (Fin 12) (Fin 12) ℝ := fun i j => paleyInt i j

theorem paley_sign : IsSignMatrix paley := by
  intro i j
  rcases paleyInt_sign i j with h | h
  · left; simp [paley, h]
  · right; simp [paley, h]

theorem paley_orthogonal : paley * paleyᵀ = (12 : ℝ) • 1 := by
  ext i j
  have h := congrFun (congrFun paleyInt_orthogonal i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply] at h ⊢
  simp only [paley]
  exact_mod_cast h

theorem paley_hadamard : paley.IsHadamard := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    rcases paley_sign i j with h | h <;> simp [h, Unitary.mem_iff]
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Fintype.card_fin,
      Nat.cast_ofNat] using
      paley_orthogonal
  · norm_num [isRegular_iff_ne_zero]

@[simp] theorem paley_first_column (i : Fin 12) : paley i 0 = 1 := by
  simp [paley, paleyInt]

def bitSign (x y : Fin 2) : ℝ := if x = 1 ∧ y = 1 then -1 else 1

theorem bitSign_sign (x y : Fin 2) : bitSign x y = 1 ∨ bitSign x y = -1 := by
  simp only [bitSign]
  split_ifs <;> simp

theorem bitSign_symm (x y : Fin 2) : bitSign x y = bitSign y x := by
  simp [bitSign, and_comm]

theorem bitSign_orthogonal (x z : Fin 2) :
    (∑ y : Fin 2, bitSign x y * bitSign z y) = if x = z then 2 else 0 := by
  fin_cases x <;> fin_cases z <;> norm_num [bitSign, Fin.sum_univ_two]

noncomputable def walsh (T : Type*) [Fintype T] :
    Matrix (T → Fin 2) (T → Fin 2) ℝ := fun x y => ∏ t, bitSign (x t) (y t)

theorem walsh_symm {T : Type*} [Fintype T] (x y : T → Fin 2) :
    walsh T x y = walsh T y x := by
  simp only [walsh, bitSign_symm]

theorem walsh_unitary {T : Type*} [Fintype T] (x y : T → Fin 2) :
    walsh T x y ∈ unitary ℝ := by
  apply (unitary ℝ).prod_mem
  intro t _
  rcases bitSign_sign (x t) (y t) with h | h <;> simp [h, Unitary.mem_iff]

theorem walsh_orthogonal {T : Type*} [Fintype T] [DecidableEq T]
    (x z : T → Fin 2) :
    (∑ y, walsh T x y * walsh T z y) =
      if x = z then (2 : ℝ) ^ Fintype.card T else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun t (b : Fin 2) => bitSign (x t) b * bitSign (z t) b)]
  simp only [bitSign_orthogonal]
  split_ifs with h
  · subst z
    simp
  · obtain ⟨t, ht⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)

theorem walsh_hadamard (T : Type*) [Fintype T] [DecidableEq T] :
    (walsh T).IsHadamard := by
  classical
  refine ⟨walsh_unitary, ?_, ?_⟩
  · ext x z
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.card_fun, Fintype.card_fin] using walsh_orthogonal x z
  · ext x z
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.card_fun, Fintype.card_fin, walsh_symm] using walsh_orthogonal x z

theorem walsh_sign (T : Type*) [Fintype T] [DecidableEq T] : IsSignMatrix (walsh T) := by
  intro x y
  have h := walsh_unitary x y
  simpa [Unitary.mem_iff, mul_self_eq_one_iff] using h.1

@[simp] theorem walsh_zero_column (T : Type*) [Fintype T] (x : T → Fin 2) :
    walsh T x (fun _ => 0) = 1 := by
  simp [walsh, bitSign]

abbrev ExplicitIndex := (Fin 12 × Fin 12) × (Fin 10 → Fin 2)

noncomputable def explicitHadamard : Matrix ExplicitIndex ExplicitIndex ℝ :=
  (paley ⊗ₖ paley) ⊗ₖ walsh (Fin 10)

theorem explicitHadamard_hadamard : explicitHadamard.IsHadamard :=
  (paley_hadamard.kronecker paley_hadamard).kronecker (walsh_hadamard (Fin 10))

theorem explicitIndex_card : Fintype.card ExplicitIndex = 147456 := by
  simp [ExplicitIndex, Fintype.card_fun]

theorem explicitHadamard_sign : IsSignMatrix explicitHadamard := by
  intro i j
  have h := explicitHadamard_hadamard.apply_mem i j
  simpa [Unitary.mem_iff, mul_self_eq_one_iff] using h.1

@[simp] theorem explicitHadamard_first_column (i : ExplicitIndex) :
    explicitHadamard i ((0, 0), fun _ => 0) = 1 := by
  simp [explicitHadamard, Matrix.kroneckerMap_apply]

end Bier
