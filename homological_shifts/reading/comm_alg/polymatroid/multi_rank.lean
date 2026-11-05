import CommAlg.Polymatroid.IdealProducts

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]

def zeroRank : RankFunction V where
  toFun _ := 0
  empty := rfl
  monotone := fun _ _ _ => le_rfl
  submodular _ _ := le_rfl

def sumRanks (F : Finset J) (ρ : J → RankFunction V) : RankFunction V where
  toFun A := ∑ j ∈ F, ρ j A
  empty := by simp
  monotone := fun _ _ h => Finset.sum_le_sum (fun j _ => (ρ j).monotone h)
  submodular A B := by
    simpa only [← Finset.sum_add_distrib] using Finset.sum_le_sum (s := F)
      (fun j _ => (ρ j).submodular A B)

@[simp] theorem zeroRank_apply (A : Finset V) : zeroRank A = 0 := rfl

@[simp] theorem sumRanks_apply (F : Finset J) (ρ : J → RankFunction V) (A : Finset V) :
    sumRanks F ρ A = ∑ j ∈ F, ρ j A := rfl

@[simp] theorem sumRanks_empty (ρ : J → RankFunction V) : sumRanks ∅ ρ = zeroRank := by
  apply RankFunction.ext_fun
  intro A
  simp

theorem sumRanks_insert (F : Finset J) (ρ : J → RankFunction V) {j : J} (hj : j ∉ F) :
    sumRanks (insert j F) ρ = (ρ j).add (sumRanks F ρ) := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.add, hj]

theorem rankIdeal_zeroRank (k : Type*) [CommSemiring k] : rankIdeal k (zeroRank (V := V)) = ⊤ := by
  have hz : (zeroRank (V := V)).scale 0 = zeroRank := by
    apply RankFunction.ext_fun
    intro A
    rfl
  rw [← hz]
  exact rankIdeal_scale_zero k _

theorem rankIdeal_sumRanks (k : Type*) [CommSemiring k] (F : Finset J)
    (ρ : J → RankFunction V) : rankIdeal k (sumRanks F ρ) = ∏ j ∈ F, rankIdeal k (ρ j) := by
  induction F using Finset.induction_on with
  | empty => simp [rankIdeal_zeroRank]
  | @insert j F hj ih =>
    rw [sumRanks_insert F ρ hj, rankIdeal_add, ih, Finset.prod_insert hj]

def multiRank [Fintype J] (ρ : J → RankFunction V) (s : J →₀ ℕ) : RankFunction V :=
  sumRanks Finset.univ (fun j => (ρ j).scale (s j))

@[simp] theorem multiRank_apply [Fintype J] (ρ : J → RankFunction V) (s : J →₀ ℕ)
    (A : Finset V) : multiRank ρ s A = ∑ j, s j * ρ j A := rfl

@[simp] theorem multiRank_zero [Fintype J] (ρ : J → RankFunction V) : multiRank ρ 0 = zeroRank := by
  apply RankFunction.ext_fun
  intro A
  simp

theorem multiRank_add [Fintype J] (ρ : J → RankFunction V) (s t : J →₀ ℕ) :
    multiRank ρ (s + t) = (multiRank ρ s).add (multiRank ρ t) := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.add, Nat.add_mul, Finset.sum_add_distrib]

@[simp] theorem multiRank_single [Fintype J] (ρ : J → RankFunction V) (j : J) (n : ℕ) :
    multiRank ρ (Finsupp.single j n) = (ρ j).scale n := by
  apply RankFunction.ext_fun
  intro A
  simp [RankFunction.scale, Finsupp.single_apply]

/-- Exact equality of actual products of polynomial ideals, for every multidegree. -/
theorem rankIdeal_multiRank (k : Type*) [CommSemiring k] [Fintype J]
    (ρ : J → RankFunction V) (s : J →₀ ℕ) :
    rankIdeal k (multiRank ρ s) = ∏ j, (rankIdeal k (ρ j)) ^ (s j) := by
  rw [multiRank, rankIdeal_sumRanks]
  apply Finset.prod_congr rfl
  intro j hj
  exact rankIdeal_scale k (ρ j) (s j)

end CommAlg.Polymatroid
