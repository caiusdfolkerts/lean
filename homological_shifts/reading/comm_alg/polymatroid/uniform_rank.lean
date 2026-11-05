import CommAlg.Polymatroid.TrimBounds
import CommAlg.Polymatroid.RankBases
import CommAlg.Polymatroid.PartitionDefect

/-! # Uniform ranks and the singleton caps of homological ranks -/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def RankFunction.truncate (g : RankFunction V) (d : ℕ) : RankFunction V where
  toFun A := min (g A) d
  empty := by simp
  monotone := fun A B h => min_le_min_right d (g.monotone h)
  submodular A B := by
    have hg := g.submodular A B
    have hiA := g.monotone (inter_subset_left : A ∩ B ⊆ A)
    have hiB := g.monotone (inter_subset_right : A ∩ B ⊆ B)
    omega

def cardinalRank (V : Type*) [DecidableEq V] : RankFunction V where
  toFun A := A.card
  empty := card_empty
  monotone := fun _ _ h => card_le_card h
  submodular A B := (card_union_add_card_inter A B).le

def uniformRank (V : Type*) [DecidableEq V] (d : ℕ) : RankFunction V :=
  (cardinalRank V).truncate d

@[simp] theorem uniformRank_apply (d : ℕ) (A : Finset V) :
    uniformRank V d A = min A.card d := rfl

def uniformPowerRank (V : Type*) [DecidableEq V] (d s : ℕ) : RankFunction V :=
  RankFunction.scale s (uniformRank V d)

@[simp] theorem uniformPowerRank_apply (d s : ℕ) (A : Finset V) :
    uniformPowerRank V d s A = s * min A.card d := rfl

theorem uniformPowerRank_active {d s : ℕ} (hd : 1 ≤ d) (hs : 1 ≤ s) :
    (uniformPowerRank V d s).Active := by
  intro A hA
  have hc : 1 ≤ A.card := card_pos.mpr hA
  have hm : 1 ≤ min A.card d := le_min hc hd
  change 1 ≤ s * min A.card d
  nlinarith

theorem RankFunction.le_sum_singletons (g : RankFunction V) (A : Finset V) :
    g A ≤ ∑ j ∈ A, g {j} := by
  simpa [Finpartition.parts_bot] using g.le_sum_partition (⊥ : Finpartition A)

theorem homologicalRank_singleton (g : RankFunction V) (hg : g.Active)
    (i : ℕ) (j : V) : homologicalRank g hg i {j} = g {j} := by
  have hD := partitionRank_le_single g (singleton_nonempty j)
  have hg1 := hg {j} (singleton_nonempty j)
  have hLo : g {j} ≤ augmentedPartitionRank g {j} :=
    RankFunction.le_of_dominates (augmentedRank_dominates g hg) {j}
  have hEq : augmentedPartitionRank g {j} = g {j} := by
    unfold augmentedPartitionRank at hLo ⊢
    simp only [card_singleton] at *
    omega
  rw [homologicalRank_apply g hg i (singleton_nonempty j)]
  change min (g {j} + i) (augmentedPartitionRank g {j}) = _
  rw [hEq, min_eq_right (Nat.le_add_right _ _)]

theorem homologicalRank_le_sum_singletons (g : RankFunction V) (hg : g.Active)
    (i : ℕ) (A : Finset V) : homologicalRank g hg i A ≤ ∑ j ∈ A, g {j} := by
  simpa only [homologicalRank_singleton] using (homologicalRank g hg i).le_sum_singletons A

@[simp] theorem subsetSum_constExponent (n : ℕ) (A : Finset V) :
    subsetSum (constExponent n : Exponent V) A = A.card * n := by
  simp [subsetSum]

@[simp] theorem degree_constExponent (n : ℕ) :
    (constExponent n : Exponent V).degree = Fintype.card V * n := by
  simp [Finsupp.degree_eq_sum]

/-- The bases of a scaled uniform rank are exactly the bounded exponent
vectors of the required total degree. This identifies the squarefree
Veronese family at `s=1` and all its powers at arbitrary `s`. -/
theorem isRankBase_uniformPower_iff (d s : ℕ) (hd : d ≤ Fintype.card V)
    (a : Exponent V) :
    IsRankBase (uniformPowerRank V d s) a ↔ a.degree = s * d ∧ ∀ j, a j ≤ s := by
  have htop : uniformPowerRank V d s univ = s * d := by simp [min_eq_right hd]
  constructor
  · rintro ⟨hdeg, hbound⟩
    refine ⟨hdeg.trans htop, fun j => ?_⟩
    have h := hbound {j}
    simp only [subsetSum, sum_singleton, uniformPowerRank_apply, card_singleton] at h
    have hm : min 1 d ≤ 1 := min_le_left _ _
    nlinarith
  · rintro ⟨hdeg, hcap⟩
    refine ⟨hdeg.trans htop.symm, fun A => ?_⟩
    have hc : subsetSum a A ≤ A.card * s := by
      simpa [subsetSum] using (Finset.sum_le_sum (s := A) (fun j _ => hcap j))
    have ht : subsetSum a A ≤ s * d := by
      have h := subsetSum_mono a (subset_univ A)
      simpa only [subsetSum_univ, hdeg] using h
    change subsetSum a A ≤ s * min A.card d
    rcases le_total A.card d with h | h
    · rw [min_eq_left h, Nat.mul_comm]
      exact hc
    · rwa [min_eq_right h]

end CommAlg.Polymatroid
