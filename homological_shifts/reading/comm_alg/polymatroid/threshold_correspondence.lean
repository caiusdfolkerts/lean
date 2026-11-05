import CommAlg.Polymatroid.PartitionThreshold
import Mathlib.Data.Rat.Floor

/-! # Exact correspondence with the paper's signed rational ceilings

Natural subtraction in the implementation clamps the numerator at zero.
The first theorem verifies that this is exactly the nonnegative part of the
ordinary rational ceiling, even when the paper's signed numerator is negative.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

theorem signedCeiling_toNat_eq_ceilDiv (κ b δ : ℕ) (hδ : 0 < δ) :
    (Int.ceil (((κ : ℚ) - b) / δ)).toNat = (κ - b) ⌈/⌉ δ := by
  apply eq_of_forall_ge_iff
  intro s
  have hδQ : (0 : ℚ) < δ := by exact_mod_cast hδ
  calc
    (Int.ceil (((κ : ℚ) - b) / δ)).toNat ≤ s ↔
        ((κ : ℚ) - b) / δ ≤ s := by
      rw [Int.toNat_le, Int.ceil_le]
      simp only [Int.cast_natCast]
    _ ↔ (κ : ℚ) ≤ s * δ + b := by rw [div_le_iff₀ hδQ, sub_le_iff_le_add]
    _ ↔ κ ≤ s * δ + b := by norm_cast
    _ ↔ (κ - b) ⌈/⌉ δ ≤ s := by
      rw [ceilDiv_le_iff_le_mul hδ, Nat.mul_comm δ s]
      omega

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The implemented threshold is the paper's maximum over positive-defect
partitions of the nonnegative part of its displayed rational ceiling. -/
theorem powerThreshold_eq_rationalCeiling (ρ : RankFunction V) (i : ℕ) (A : Finset V) :
    powerThreshold ρ i A = Finset.univ.sup (fun P : Finpartition A =>
      if 0 < partitionDefect ρ P then
        (Int.ceil ((((eventualCorrection ρ i A : ℕ) : ℚ) - partitionSlack P) /
          (partitionDefect ρ P : ℚ))).toNat else 0) := by
  unfold powerThreshold affineThreshold
  apply Finset.sup_congr rfl
  intro P hP
  by_cases hd : partitionDefect ρ P = 0
  · simp [hd]
  · have hp : 0 < partitionDefect ρ P := by omega
    simp only [if_neg hd, if_pos hp]
    exact (signedCeiling_toNat_eq_ceilDiv _ _ _ hp).symm

end CommAlg.Polymatroid
