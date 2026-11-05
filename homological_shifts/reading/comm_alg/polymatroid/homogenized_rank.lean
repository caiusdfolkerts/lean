import CommAlg.Polymatroid.RankInterpolation
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finsupp.Option

/-! # Homogenization of ranks with ordered marginal increments

`none` denotes the additional coordinate `z`; `some j` denotes an original
coordinate.  Both branches of the rank formula are proved for every subset.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def rankGap (g u : RankFunction V) : ℕ := u univ - g univ

theorem RankFunction.gap_bound {g u : RankFunction V} (h : u.Dominates g)
    (A : Finset V) : u A ≤ rankGap g u + g A := by
  have hE := RankFunction.le_of_dominates h univ
  have hm := h A univ (subset_univ A)
  unfold rankGap
  omega

def homogenizedRankValue (g u : RankFunction V) (A : Finset (Option V)) : ℕ :=
  if none ∈ A then rankGap g u + g A.eraseNone else u A.eraseNone

/-- The second interpolation in Lemma 3.3, on the ground set extended by one
genuine new coordinate. -/
def RankFunction.homogenize (g u : RankFunction V) (h : u.Dominates g) :
    RankFunction (Option V) where
  toFun := homogenizedRankValue g u
  empty := by simp [homogenizedRankValue]
  monotone := by
    intro A B hAB
    have hm : A.eraseNone ⊆ B.eraseNone := Finset.eraseNone.monotone hAB
    by_cases hA : none ∈ A
    · have hB := hAB hA
      simp only [homogenizedRankValue, if_pos hA, if_pos hB]
      exact Nat.add_le_add_left (g.monotone hm) _
    · by_cases hB : none ∈ B
      · simp only [homogenizedRankValue, if_neg hA, if_pos hB]
        exact (RankFunction.gap_bound h A.eraseNone).trans
          (Nat.add_le_add_left (g.monotone hm) _)
      · simp only [homogenizedRankValue, if_neg hA, if_neg hB]
        exact u.monotone hm
  submodular := by
    intro A B
    have hg := g.submodular A.eraseNone B.eraseNone
    have hu := u.submodular A.eraseNone B.eraseNone
    have hm := RankFunction.mixed_submodular h A.eraseNone B.eraseNone
    have hm' := RankFunction.mixed_submodular h B.eraseNone A.eraseNone
    rw [Finset.union_comm B.eraseNone A.eraseNone,
      Finset.inter_comm B.eraseNone A.eraseNone] at hm'
    by_cases hA : none ∈ A <;> by_cases hB : none ∈ B <;>
      simp [homogenizedRankValue, hA, hB] <;> omega

@[simp] theorem RankFunction.homogenize_apply (g u : RankFunction V)
    (h : u.Dominates g) (A : Finset (Option V)) :
    g.homogenize u h A = homogenizedRankValue g u A := rfl

@[simp] theorem RankFunction.homogenize_some (g u : RankFunction V)
    (h : u.Dominates g) (A : Finset V) :
    g.homogenize u h (A.image some) = u A := by
  simp [homogenizedRankValue]

@[simp] theorem RankFunction.homogenize_insertNone (g u : RankFunction V)
    (h : u.Dominates g) (A : Finset V) :
    g.homogenize u h A.insertNone = rankGap g u + g A := by
  simp [homogenizedRankValue]

@[simp] theorem RankFunction.homogenize_singleton_none (g u : RankFunction V)
    (h : u.Dominates g) :
    g.homogenize u h {none} = rankGap g u := by
  simp [homogenizedRankValue]

@[simp] theorem RankFunction.homogenize_univ (g u : RankFunction V)
    (h : u.Dominates g) :
    g.homogenize u h univ = u univ := by
  have hg := RankFunction.le_of_dominates h univ
  have he : (univ : Finset (Option V)).eraseNone = univ := by ext x; simp
  simp [homogenizedRankValue, he, rankGap, Nat.sub_add_cancel hg]

end CommAlg.Polymatroid
