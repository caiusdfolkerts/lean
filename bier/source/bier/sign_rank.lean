import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

/-! # Sign matrices, actual realizations, and sign rank

The rank in this definition is Mathlib's dimension of the range of the
matrix's actual linear map.  A realization retains every strict sign.
-/

noncomputable section

namespace Bier

variable {R C : Type*} [Fintype R] [Fintype C]

def IsSignMatrix (H : Matrix R C ℝ) : Prop :=
  ∀ r c, H r c = 1 ∨ H r c = -1

def SignRealizes (H M : Matrix R C ℝ) : Prop :=
  ∀ r c, 0 < H r c * M r c

def signRank (H : Matrix R C ℝ) : ℕ :=
  sInf {n : ℕ | ∃ M : Matrix R C ℝ, SignRealizes H M ∧ M.rank = n}

theorem IsSignMatrix.realizes_self {H : Matrix R C ℝ} (hH : IsSignMatrix H) :
    SignRealizes H H := by
  intro r c
  rcases hH r c with h | h <;> rw [h] <;> norm_num

theorem signRank_le_rank {H M : Matrix R C ℝ} (hM : SignRealizes H M) :
    signRank H ≤ M.rank :=
  Nat.sInf_le ⟨M, hM, rfl⟩

theorem exists_rank_eq_signRank {H : Matrix R C ℝ} (hH : IsSignMatrix H) :
    ∃ M : Matrix R C ℝ, SignRealizes H M ∧ M.rank = signRank H := by
  exact Nat.sInf_mem (s := {n : ℕ | ∃ M : Matrix R C ℝ,
    SignRealizes H M ∧ M.rank = n}) ⟨H.rank, H, hH.realizes_self, rfl⟩

theorem signRank_le {H : Matrix R C ℝ} (hH : IsSignMatrix H) :
    signRank H ≤ H.rank := signRank_le_rank hH.realizes_self

theorem signRank_le_card_rows {H : Matrix R C ℝ} (hH : IsSignMatrix H) :
    signRank H ≤ Fintype.card R :=
  (signRank_le hH).trans (Matrix.rank_le_card_height H)

theorem signRank_le_card_cols {H : Matrix R C ℝ} (hH : IsSignMatrix H) :
    signRank H ≤ Fintype.card C :=
  (signRank_le hH).trans (Matrix.rank_le_card_width H)

theorem SignRealizes.entry_ne_zero {H M : Matrix R C ℝ}
    (hM : SignRealizes H M) (r : R) (c : C) : M r c ≠ 0 := by
  intro h
  have hp := hM r c
  simp [h] at hp

end Bier
