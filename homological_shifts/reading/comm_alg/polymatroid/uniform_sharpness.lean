import CommAlg.Polymatroid.UniformRank

/-!
# Uniform-matroid sharpness in every positive homological degree

For a ground set of size `i + 1`, the rank-`i` uniform matroid gives the
squarefree Veronese example. Below the `i`th power its homological rank
cannot reach the required degree. At that power the only base exponent is
the constant vector `i`.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem uniform_homologicalRank_cap (i s : ℕ) (hi : 1 ≤ i) (hs : 1 ≤ s)
    (A : Finset V) :
    homologicalRank (uniformPowerRank V i s) (uniformPowerRank_active hi hs) i A ≤
      A.card * s := by
  have h := homologicalRank_le_sum_singletons (uniformPowerRank V i s)
    (uniformPowerRank_active hi hs) i A
  simpa only [uniformPowerRank_apply, card_singleton, min_eq_left hi,
    Nat.mul_one, sum_const_nat] using h

/-- The total rank is too small at every positive power below `i`. -/
theorem uniform_homologicalRank_lt {i s : ℕ} (hi : 1 ≤ i) (hs : 1 ≤ s)
    (hsi : s < i) (hcard : Fintype.card V = i + 1) :
    homologicalRank (uniformPowerRank V i s) (uniformPowerRank_active hi hs) i univ <
      uniformPowerRank V i s univ + i := by
  have h := uniform_homologicalRank_cap (V := V) i s hi hs univ
  simp only [card_univ, hcard, uniformPowerRank_apply,
    min_eq_right (Nat.le_succ i)] at h ⊢
  nlinarith

theorem uniform_threshold_supportPred_bound {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) {A : Finset V} (hA : A.Nonempty) :
    subsetSum (supportPred (constExponent i : Exponent V)) A ≤
      uniformPowerRank V i i A - 1 := by
  have hc : 1 ≤ A.card := card_pos.mpr hA
  have hcn : A.card ≤ i + 1 := by
    simpa only [hcard] using card_le_univ A
  have him : i - 1 + 1 = i := Nat.sub_add_cancel hi
  have hsum : subsetSum (supportPred (constExponent i : Exponent V)) A =
      A.card * (i - 1) := by
    simp [subsetSum]
  rw [hsum, uniformPowerRank_apply]
  rcases le_total A.card i with h | h
  · rw [min_eq_left h]
    have hp : 1 ≤ i * A.card := by nlinarith
    have hs := Nat.sub_add_cancel hp
    nlinarith
  · rw [min_eq_right h]
    have hp : 1 ≤ i * i := by nlinarith
    have hs := Nat.sub_add_cancel hp
    nlinarith

/-- The constant exponent satisfies every augmented partition inequality. -/
theorem uniform_threshold_augmented_feasible {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    ∀ A, subsetSum (constExponent i : Exponent V) A ≤
      augmentedPartitionRank (uniformPowerRank V i i) A :=
  (supportPred_nonempty_bounds_iff_augmented (uniformPowerRank V i i)
    (constExponent i)).mp (fun _ hA => uniform_threshold_supportPred_bound hi hcard hA)

theorem uniform_threshold_upperFeasible {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    UpperFeasible
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i)
      (constExponent i) := by
  intro A
  by_cases hA : A.Nonempty
  · rw [homologicalRank_apply _ _ _ hA]
    change subsetSum (constExponent i) A ≤
      min (uniformPowerRank V i i A + i) (augmentedPartitionRank _ A)
    refine le_min ?_ (uniform_threshold_augmented_feasible hi hcard A)
    rw [subsetSum_constExponent, uniformPowerRank_apply]
    have hc : A.card ≤ i + 1 := by simpa only [hcard] using card_le_univ A
    rcases le_total A.card i with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h]
      nlinarith
  · have he := not_nonempty_iff_eq_empty.mp hA
    simp [he, subsetSum]

/-- At the `i`th power the required total degree is attained. -/
theorem uniform_homologicalRank_top {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i univ =
      uniformPowerRank V i i univ + i := by
  have hLo := uniform_threshold_upperFeasible hi hcard univ
  have hHi := uniform_homologicalRank_cap (V := V) i i hi hi univ
  simp only [subsetSum_constExponent, card_univ, hcard] at hLo hHi
  simp only [uniformPowerRank_apply, card_univ, hcard,
    min_eq_right (Nat.le_succ i)]
  nlinarith

theorem uniform_threshold_isRankBase {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    IsRankBase
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i)
      (constExponent i) := by
  refine ⟨?_, uniform_threshold_upperFeasible hi hcard⟩
  rw [degree_constExponent, uniform_homologicalRank_top hi hcard]
  simp only [hcard, uniformPowerRank_apply, card_univ,
    min_eq_right (Nat.le_succ i)]
  nlinarith

/-- The exact unique base at the sharp threshold, with no restriction on the
positive homological degree. -/
theorem uniform_threshold_isRankBase_iff {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) (a : Exponent V) :
    IsRankBase
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i) a ↔
      a = constExponent i := by
  constructor
  · intro ha
    have hcap : a ≤ constExponent i := by
      intro j
      have h := ha.2 {j}
      rw [homologicalRank_singleton] at h
      simpa only [subsetSum, sum_singleton, uniformPowerRank_apply, card_singleton,
        min_eq_left hi, Nat.mul_one, constExponent_apply] using h
    apply eq_of_le_of_degree_eq hcap
    exact ha.1.trans (uniform_threshold_isRankBase hi hcard).1.symm
  · rintro rfl
    exact uniform_threshold_isRankBase hi hcard

theorem uniform_threshold_rankBases {i : ℕ} (hi : 1 ≤ i)
    (hcard : Fintype.card V = i + 1) :
    rankBases
      (homologicalRank (uniformPowerRank V i i) (uniformPowerRank_active hi hi) i) =
      {constExponent i} := by
  ext a
  rw [mem_rankBases, uniform_threshold_isRankBase_iff hi hcard, mem_singleton]

end CommAlg.Polymatroid
