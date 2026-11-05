import CommAlg.Polymatroid.RankFunction

/-! # Rank interpolation under domination of marginal increments -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [DecidableEq V]

def shiftRankValue (g u : RankFunction V) (i : ℕ) (A : Finset V) : ℕ :=
  if A = ∅ then 0 else min (g A + i) (u A)

@[simp] theorem shiftRankValue_empty (g u : RankFunction V) (i : ℕ) :
    shiftRankValue g u i ∅ = 0 := by simp [shiftRankValue]

theorem shiftRankValue_le_u (g u : RankFunction V) (i : ℕ) (A : Finset V) :
    shiftRankValue g u i A ≤ u A := by
  unfold shiftRankValue
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_right _ _

theorem shiftRankValue_le_add (g u : RankFunction V) (i : ℕ) (A : Finset V) :
    shiftRankValue g u i A ≤ g A + i := by
  unfold shiftRankValue
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_left _ _

/-- Lemma 3.3, first interpolation, with exactly its marginal hypothesis. -/
def RankFunction.interpolate (g u : RankFunction V) (h : u.Dominates g)
    (i : ℕ) : RankFunction V where
  toFun := shiftRankValue g u i
  empty := shiftRankValue_empty g u i
  monotone := by
    intro A B hAB
    by_cases hA : A = ∅
    · simp [hA]
    have hB : B ≠ ∅ := by
      intro heq
      apply hA
      simpa [heq] using hAB
    simp only [shiftRankValue, if_neg hA, if_neg hB]
    exact min_le_min (Nat.add_le_add_right (g.monotone hAB) i) (u.monotone hAB)
  submodular := by
    intro A B
    by_cases hA : A = ∅
    · simp [hA]
    by_cases hB : B = ∅
    · simp [hB]
    have hUg := shiftRankValue_le_add g u i (A ∪ B)
    have hIg := shiftRankValue_le_add g u i (A ∩ B)
    have hUu := shiftRankValue_le_u g u i (A ∪ B)
    have hIu := shiftRankValue_le_u g u i (A ∩ B)
    have hg := g.submodular A B
    have hu := u.submodular A B
    have hm := RankFunction.mixed_submodular h A B
    have hm' := RankFunction.mixed_submodular h B A
    rw [Finset.union_comm B A, Finset.inter_comm B A] at hm'
    rcases le_total (g A + i) (u A) with ha | ha <;>
      rcases le_total (g B + i) (u B) with hb | hb
    · have hAv : shiftRankValue g u i A = g A + i := by
        simp [shiftRankValue, hA, min_eq_left ha]
      have hBv : shiftRankValue g u i B = g B + i := by
        simp [shiftRankValue, hB, min_eq_left hb]
      rw [hAv, hBv]
      omega
    · have hAv : shiftRankValue g u i A = g A + i := by
        simp [shiftRankValue, hA, min_eq_left ha]
      have hBv : shiftRankValue g u i B = u B := by
        simp [shiftRankValue, hB, min_eq_right hb]
      rw [hAv, hBv]
      omega
    · have hAv : shiftRankValue g u i A = u A := by
        simp [shiftRankValue, hA, min_eq_right ha]
      have hBv : shiftRankValue g u i B = g B + i := by
        simp [shiftRankValue, hB, min_eq_left hb]
      rw [hAv, hBv]
      omega
    · have hAv : shiftRankValue g u i A = u A := by
        simp [shiftRankValue, hA, min_eq_right ha]
      have hBv : shiftRankValue g u i B = u B := by
        simp [shiftRankValue, hB, min_eq_right hb]
      rw [hAv, hBv]
      omega

@[simp] theorem RankFunction.interpolate_apply (g u : RankFunction V)
    (h : u.Dominates g) (i : ℕ) (A : Finset V) :
    g.interpolate u h i A = shiftRankValue g u i A := rfl

end CommAlg.Polymatroid
