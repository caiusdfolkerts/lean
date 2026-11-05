module
public import PaperVerification.LatticeDefs
public import PaperVerification.LatticeRounding
public import PaperVerification.LatticeCoordinates
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Ring.Int.Parity
@[expose] public section
/-! # Exact squared-distance formula and covering estimate for `D_n^+` -/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

/-- Squared nearest-integer distance before a parity correction. -/
def integerBaseCost (x : Fin n → ℝ) : ℝ := ∑ i, (foldedRadius x i) ^ 2

/-- Squared nearest-half-integer distance before a parity correction. -/
def halfBaseCost (x : Fin n → ℝ) : ℝ := ∑ i, (1 / 2 - foldedRadius x i) ^ 2

/-- The actual correction in the even integer coset. -/
def integerRepairCost (x : Fin n → ℝ) (M : ℝ) : ℝ :=
  integerBaseCost x + if Even (∑ i, roundedInt x i) then 0 else 1 - 2 * M

/-- The actual correction in the even half-integer coset. -/
def halfRepairCost (x : Fin n → ℝ) (m : ℝ) : ℝ :=
  halfBaseCost x + if Even (∑ i, halfRoundedInt x i) then 0 else 2 * m

theorem halfBaseCost_eq (x : Fin n → ℝ) :
    halfBaseCost x = integerBaseCost x - (∑ i, foldedRadius x i) + (n : ℝ) / 4 := by
  unfold halfBaseCost integerBaseCost
  calc
    _ = ∑ i, ((foldedRadius x i) ^ 2 - foldedRadius x i + 1 / 4) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring

theorem sqDist_roundedInt (x : Fin n → ℝ) :
    sqDist x (intVec (roundedInt x)) = integerBaseCost x := by
  simp [sqDist, intVec, integerBaseCost, foldedRadius, sq_abs]

theorem sqDist_halfRoundedInt (x : Fin n → ℝ) :
    sqDist x (fun i => (halfRoundedInt x i : ℝ) + 1 / 2) = halfBaseCost x := by
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrArg (fun t : ℝ => t ^ 2) (abs_sub_halfRoundedInt x i)
  simpa only [sq_abs] using h

theorem integerRepairCost_le_sqDist (x : Fin n → ℝ) (z : Fin n → ℤ) (M : ℝ)
    (hM : ∀ i, foldedRadius x i ≤ M) (hz : Even (∑ i, z i)) :
    integerRepairCost x M ≤ sqDist x (intVec z) := by
  have h := even_integer_sq_lower x (roundedInt x) z M
    (foldedRadius_le_half x) hM hz
  simpa only [integerRepairCost, integerBaseCost, sqDist, intVec, foldedRadius, sq_abs] using h

theorem halfRepairCost_le_sqDist (x : Fin n → ℝ) (z : Fin n → ℤ) (m : ℝ)
    (hm : ∀ i, m ≤ foldedRadius x i) (hz : Even (∑ i, z i)) :
    halfRepairCost x m ≤ sqDist x (fun i => (z i : ℝ) + 1 / 2) := by
  have hrepr (i : Fin n) :
      |(x i - 1 / 2) - (halfRoundedInt x i : ℝ)| = 1 / 2 - foldedRadius x i := by
    convert abs_sub_halfRoundedInt x i using 1 <;> congr 1 <;> ring
  have hq (i : Fin n) : |(x i - 1 / 2) - (halfRoundedInt x i : ℝ)| ≤ 1 / 2 := by
    rw [hrepr]
    linarith [foldedRadius_nonneg x i]
  have hM (i : Fin n) : |(x i - 1 / 2) - (halfRoundedInt x i : ℝ)| ≤ 1 / 2 - m := by
    rw [hrepr]
    linarith [hm i]
  have h := even_integer_sq_lower (fun i => x i - 1 / 2) (halfRoundedInt x) z
    (1 / 2 - m) hq hM hz
  have hs (i : Fin n) : ((x i - 1 / 2) - (halfRoundedInt x i : ℝ)) ^ 2 =
      (1 / 2 - foldedRadius x i) ^ 2 := by
    rw [← hrepr, sq_abs]
  have ht (i : Fin n) : ((x i - 1 / 2) - (z i : ℝ)) ^ 2 =
      (x i - ((z i : ℝ) + 1 / 2)) ^ 2 := by ring
  simp only [hs, ht] at h
  unfold halfRepairCost halfBaseCost sqDist
  by_cases he : Even (∑ i, halfRoundedInt x i) <;> simp only [he, if_true, if_false] at h ⊢ <;>
    linarith

theorem squaredDepth_le_integerRepairCost (x : Fin n → ℝ) (j : Fin n) :
    squaredDepth (dPlusSet n) x ≤ integerRepairCost x (foldedRadius x j) := by
  by_cases he : Even (∑ i, roundedInt x i)
  · calc
      _ ≤ sqDist x (intVec (roundedInt x)) :=
        squaredDepth_le (L := dPlusSet n) x ⟨roundedInt x, he, Or.inl rfl⟩
      _ = _ := by rw [sqDist_roundedInt]; simp [integerRepairCost, he]
  · obtain ⟨z, hz, hdist⟩ := exists_even_integer_bound x j
    calc
      _ ≤ sqDist x (intVec z) := squaredDepth_le (L := dPlusSet n) x ⟨z, hz, Or.inl rfl⟩
      _ ≤ _ := by simpa [sqDist, intVec, integerRepairCost, integerBaseCost, he, sub_eq_add_neg, add_assoc] using hdist

theorem squaredDepth_le_halfRepairCost (x : Fin n → ℝ) (j : Fin n) :
    squaredDepth (dPlusSet n) x ≤ halfRepairCost x (foldedRadius x j) := by
  by_cases he : Even (∑ i, halfRoundedInt x i)
  · calc
      _ ≤ sqDist x (fun i => (halfRoundedInt x i : ℝ) + 1 / 2) :=
        squaredDepth_le (L := dPlusSet n) x ⟨halfRoundedInt x, he, Or.inr rfl⟩
      _ = _ := by rw [sqDist_halfRoundedInt]; simp [halfRepairCost, he]
  · obtain ⟨z, hz, hdist⟩ := exists_even_half_integer_bound x j
    calc
      _ ≤ sqDist x (fun i => (z i : ℝ) + 1 / 2) := squaredDepth_le (L := dPlusSet n) x ⟨z, hz, Or.inr rfl⟩
      _ ≤ _ := by simpa [sqDist, halfRepairCost, halfBaseCost, he] using hdist

/-- Exact squared distance to the actual union of the two even coordinate cosets. -/
theorem squaredDepth_dPlus_eq (x : Fin n → ℝ) (lo hi : Fin n)
    (hlo : ∀ i, foldedRadius x lo ≤ foldedRadius x i)
    (hhi : ∀ i, foldedRadius x i ≤ foldedRadius x hi) :
    squaredDepth (dPlusSet n) x =
      min (integerRepairCost x (foldedRadius x hi)) (halfRepairCost x (foldedRadius x lo)) := by
  apply le_antisymm
  · exact le_min (squaredDepth_le_integerRepairCost x hi) (squaredDepth_le_halfRepairCost x lo)
  · apply le_csInf ((dPlusSet_nonempty n).image (fun z => sqDist x z))
    rintro r ⟨v, hv, rfl⟩
    rcases hv with ⟨z, hz, h | h⟩
    · rw [h]
      exact (min_le_left _ _).trans (integerRepairCost_le_sqDist x z _ hhi hz)
    · rw [h]
      exact (min_le_right _ _).trans (halfRepairCost_le_sqDist x z _ hlo hz)

/-- Both parity repairs are bounded by the sharp algebraic envelope. -/
theorem squaredDepth_le_roundingEnvelope (x : Fin n → ℝ) (lo hi : Fin n)
    (hlo : ∀ i, foldedRadius x lo ≤ foldedRadius x i)
    (hhi : ∀ i, foldedRadius x i ≤ foldedRadius x hi) :
    squaredDepth (dPlusSet n) x ≤ PaperVerification.Lattice.roundingEnvelope (n : ℝ)
      (foldedRadius x lo) (foldedRadius x hi) (∑ i, foldedRadius x i) := by
  have hs : integerBaseCost x ≤ (foldedRadius x lo + foldedRadius x hi) *
      (∑ i, foldedRadius x i) - (n : ℝ) * foldedRadius x lo * foldedRadius x hi := by
    simpa [integerBaseCost] using PaperVerification.Lattice.folded_square_sum_le
      Finset.univ (foldedRadius x) (foldedRadius x lo) (foldedRadius x hi)
      (fun i _ => hlo i) (fun i _ => hhi i)
  obtain ⟨zi, hzi, hdi⟩ := exists_even_integer_bound x hi
  obtain ⟨zh, hzh, hdh⟩ := exists_even_half_integer_bound x lo
  have hiDepth := (squaredDepth_le x (show intVec zi ∈ dPlusSet n from
    ⟨zi, hzi, Or.inl rfl⟩)).trans hdi
  have hhDepth := (squaredDepth_le x (show (fun i => (zh i : ℝ) + 1 / 2) ∈ dPlusSet n from
    ⟨zh, hzh, Or.inr rfl⟩)).trans hdh
  change squaredDepth (dPlusSet n) x ≤ integerBaseCost x + 1 - 2 * foldedRadius x hi at hiDepth
  change squaredDepth (dPlusSet n) x ≤ halfBaseCost x + 2 * foldedRadius x lo at hhDepth
  rw [halfBaseCost_eq] at hhDepth
  unfold PaperVerification.Lattice.roundingEnvelope
  exact le_min (by linarith) (by linarith)

/-- The covering-radius upper bound in Proposition 3.4, for all dimensions n>=8. -/
theorem squaredDepth_dPlus_le (hn : 8 ≤ n) (x : Fin n → ℝ) :
    squaredDepth (dPlusSet n) x ≤ (n : ℝ) / 8 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 8) hn
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ (foldedRadius x) hne
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ (foldedRadius x) hne
  have hlo' : ∀ i, foldedRadius x lo ≤ foldedRadius x i := fun i => hlo i (Finset.mem_univ _)
  have hhi' : ∀ i, foldedRadius x i ≤ foldedRadius x hi := fun i => hhi i (Finset.mem_univ _)
  exact (squaredDepth_le_roundingEnvelope x lo hi hlo' hhi').trans
    (PaperVerification.Lattice.roundingEnvelope_le (n : ℝ) _ _ _ (by exact_mod_cast hn)
      (foldedRadius_nonneg x lo) (hlo' hi) (foldedRadius_le_half x hi))

/-- Every lattice point is at least as far away as independent coordinate rounding. -/
theorem min_baseCost_le_squaredDepth (x : Fin n → ℝ) :
    min (integerBaseCost x) (halfBaseCost x) ≤ squaredDepth (dPlusSet n) x := by
  apply le_csInf ((dPlusSet_nonempty n).image (fun z => sqDist x z))
  rintro r ⟨v, hv, rfl⟩
  rcases hv with ⟨z, hz, h | h⟩
  · rw [h]
    have hi := integerRepairCost_le_sqDist x z (1 / 2) (foldedRadius_le_half x) hz
    simp only [integerRepairCost] at hi
    norm_num at hi
    exact (min_le_left _ _).trans hi
  · rw [h]
    have hi := halfRepairCost_le_sqDist x z 0 (foldedRadius_nonneg x) hz
    simp only [halfRepairCost, mul_zero, ite_self, add_zero] at hi
    exact (min_le_right _ _).trans hi

/-- The folded-coordinate formulation of exactly half integer and half half-integer
coordinates. A separate equivalence identifies these radii with the stated grid. -/
def BalancedHalfGrid (x : Fin n → ℝ) : Prop :=
  (∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2) ∧
    (∑ i, foldedRadius x i) = (n : ℝ) / 4

theorem integerBaseCost_of_balanced {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    integerBaseCost x = (n : ℝ) / 8 := by
  have hi (i : Fin n) : (foldedRadius x i) ^ 2 = foldedRadius x i / 2 := by
    rcases hx.1 i with h | h <;> rw [h] <;> norm_num
  unfold integerBaseCost
  simp only [hi]
  rw [← Finset.sum_div, hx.2]
  ring

theorem halfBaseCost_of_balanced {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    halfBaseCost x = (n : ℝ) / 8 := by
  rw [halfBaseCost_eq, integerBaseCost_of_balanced hx, hx.2]
  ring

/-- Every point in the full balanced half-grid attains the sharp radius. -/
theorem squaredDepth_dPlus_of_balanced (hn : 8 ≤ n) {x : Fin n → ℝ} (hx : BalancedHalfGrid x) :
    squaredDepth (dPlusSet n) x = (n : ℝ) / 8 := by
  apply le_antisymm (squaredDepth_dPlus_le hn x)
  have h := min_baseCost_le_squaredDepth x
  simpa only [integerBaseCost_of_balanced hx, halfBaseCost_of_balanced hx, min_self] using h


/-- The all-dimensional bound has no additional equality points when n>8. -/
theorem balanced_of_squaredDepth_eq (hn : 8 < n) {x : Fin n → ℝ}
    (hdepth : squaredDepth (dPlusSet n) x = (n : ℝ) / 8) : BalancedHalfGrid x := by
  have hn0 : 0 < n := lt_trans (by decide : 0 < 8) hn
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn0⟩, Finset.mem_univ _⟩
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ (foldedRadius x) hne
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ (foldedRadius x) hne
  have hlo' : ∀ i, foldedRadius x lo ≤ foldedRadius x i := fun i => hlo i (Finset.mem_univ _)
  have hhi' : ∀ i, foldedRadius x i ≤ foldedRadius x hi := fun i => hhi i (Finset.mem_univ _)
  have henv : PaperVerification.Lattice.roundingEnvelope (n : ℝ)
      (foldedRadius x lo) (foldedRadius x hi) (∑ i, foldedRadius x i) = (n : ℝ) / 8 := by
    apply le_antisymm
    · exact PaperVerification.Lattice.roundingEnvelope_le (n : ℝ) _ _ _
        (by exact_mod_cast hn.le) (foldedRadius_nonneg x lo) (hlo' hi) (foldedRadius_le_half x hi)
    · rw [← hdepth]
      exact squaredDepth_le_roundingEnvelope x lo hi hlo' hhi'
  obtain ⟨hm0, hMhalf, hT⟩ := (PaperVerification.Lattice.roundingEnvelope_eq_iff
    (n : ℝ) _ _ _ (by exact_mod_cast hn) (foldedRadius_nonneg x lo) (hlo' hi)
    (foldedRadius_le_half x hi)).mp henv
  have hhalf : halfBaseCost x = integerBaseCost x := by
    rw [halfBaseCost_eq, hT]
    ring
  have hQ : integerBaseCost x = (n : ℝ) / 8 := by
    have h := squaredDepth_dPlus_eq x lo hi hlo' hhi'
    simp [integerRepairCost, halfRepairCost, hm0, hMhalf, hhalf] at h
    linarith
  have hsum : (∑ i, foldedRadius x i * (1 / 2 - foldedRadius x i)) = 0 := by
    calc
      _ = (∑ i, foldedRadius x i) / 2 - integerBaseCost x := by
        unfold integerBaseCost
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hT, hQ]; ring
  refine ⟨?_, hT⟩
  intro i
  have hi : foldedRadius x i * (1 / 2 - foldedRadius x i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (foldedRadius_nonneg x j)
      (sub_nonneg.mpr (foldedRadius_le_half x j)))).mp hsum i (Finset.mem_univ _)
  rcases mul_eq_zero.mp hi with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- An explicit finite-set construction supplies a balanced half-grid point
in every even dimension. No bounded enumeration is used. -/
theorem exists_balancedHalfGrid (heven : Even n) : ∃ x : Fin n → ℝ, BalancedHalfGrid x := by
  classical
  have hcard : n / 2 ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using Nat.div_le_self n 2
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq hcard
  let x : Fin n → ℝ := fun i => if i ∈ s then 1 / 2 else 0
  have hround : round (1 / 2 : ℝ) = 1 := by norm_num [round_eq]
  have hr (i : Fin n) : foldedRadius x i = if i ∈ s then 1 / 2 else 0 := by
    by_cases hi : i ∈ s
    · norm_num [foldedRadius, roundedInt, x, hi, hround]
    · simp [foldedRadius, roundedInt, x, hi]
  refine ⟨x, ?_, ?_⟩
  · intro i
    rw [hr]
    by_cases hi : i ∈ s <;> simp [hi]
  · have hsum : (∑ i, foldedRadius x i) = (s.card : ℝ) / 2 := by
      simp only [hr]
      rw [Fintype.sum_ite_mem]
      simp <;> ring
    rw [hsum, hs]
    have he : 2 * (↑(n / 2) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.two_mul_div_two_of_even heven
    linarith

/-- The maximum squared distance in every even dimension n>=8 is exactly n/8. -/
theorem dPlus_squared_covering_radius (hn : 8 ≤ n) (heven : Even n) :
    (∀ x : Fin n → ℝ, squaredDepth (dPlusSet n) x ≤ (n : ℝ) / 8) ∧
      ∃ x : Fin n → ℝ, squaredDepth (dPlusSet n) x = (n : ℝ) / 8 := by
  refine ⟨squaredDepth_dPlus_le hn, ?_⟩
  obtain ⟨x, hx⟩ := exists_balancedHalfGrid heven
  exact ⟨x, squaredDepth_dPlus_of_balanced hn hx⟩

theorem isDeepHole_dPlus_iff_depth (hn : 8 ≤ n) (heven : Even n) (x : Fin n → ℝ) :
    IsDeepHole (dPlusSet n) x ↔ squaredDepth (dPlusSet n) x = (n : ℝ) / 8 := by
  obtain ⟨hupper, y, hy⟩ := dPlus_squared_covering_radius hn heven
  constructor
  · intro hx
    exact le_antisymm (hupper x) (hy ▸ hx y)
  · intro hx y
    rw [hx]
    exact hupper y

/-- Complete deep-hole classification in all even dimensions strictly above eight. -/
theorem isDeepHole_dPlus_iff_balanced (hn : 8 < n) (heven : Even n) (x : Fin n → ℝ) :
    IsDeepHole (dPlusSet n) x ↔ BalancedHalfGrid x := by
  rw [isDeepHole_dPlus_iff_depth hn.le heven]
  exact ⟨balanced_of_squaredDepth_eq hn, squaredDepth_dPlus_of_balanced hn.le⟩


/-- Exact distance when every folded coordinate has the same value. -/
theorem squaredDepth_dPlus_of_constant (x : Fin n → ℝ) (j : Fin n) (t : ℝ)
    (ht : ∀ i, foldedRadius x i = t) :
    squaredDepth (dPlusSet n) x =
      min ((n : ℝ) * t ^ 2 + if Even (∑ i, roundedInt x i) then 0 else 1 - 2 * t)
        ((n : ℝ) * (1 / 2 - t) ^ 2 + if Even (∑ i, halfRoundedInt x i) then 0 else 2 * t) := by
  have h := squaredDepth_dPlus_eq x j j (by simp [ht]) (by simp [ht])
  simpa [integerRepairCost, halfRepairCost, integerBaseCost, halfBaseCost, ht] using h

/-- At the full spread endpoints, attaining n/8 forces the balanced half-grid. -/
theorem balanced_of_endpoint_extrema (x : Fin n → ℝ) (lo hi : Fin n)
    (hlo : ∀ i, foldedRadius x lo ≤ foldedRadius x i)
    (hhi : ∀ i, foldedRadius x i ≤ foldedRadius x hi)
    (hm : foldedRadius x lo = 0) (hM : foldedRadius x hi = 1 / 2)
    (hd : squaredDepth (dPlusSet n) x = (n : ℝ) / 8) : BalancedHalfGrid x := by
  have he := squaredDepth_le_roundingEnvelope x lo hi hlo hhi
  rw [hd, hm, hM] at he
  unfold PaperVerification.Lattice.roundingEnvelope at he
  obtain ⟨ha, hb⟩ := le_min_iff.mp he
  have hT : (∑ i, foldedRadius x i) = (n : ℝ) / 4 := by linarith
  have hhalf : halfBaseCost x = integerBaseCost x := by
    rw [halfBaseCost_eq, hT]
    ring
  have hQ : integerBaseCost x = (n : ℝ) / 8 := by
    have h := squaredDepth_dPlus_eq x lo hi hlo hhi
    simp [integerRepairCost, halfRepairCost, hm, hM, hhalf] at h
    linarith
  have hsum : (∑ i, foldedRadius x i * (1 / 2 - foldedRadius x i)) = 0 := by
    calc
      _ = (∑ i, foldedRadius x i) / 2 - integerBaseCost x := by
        unfold integerBaseCost
        rw [Finset.sum_div, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hT, hQ]; ring
  refine ⟨?_, hT⟩
  intro i
  have hi : foldedRadius x i * (1 / 2 - foldedRadius x i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (foldedRadius_nonneg x j)
      (sub_nonneg.mpr (foldedRadius_le_half x j)))).mp hsum i (Finset.mem_univ _)
  exact (mul_eq_zero.mp hi).imp id (fun h => by linarith)

/-- The exceptional dimension-eight equality families, in canonical rounding
coordinates. The two endpoint families together give the integer/all-half hole
coset; the final family records both necessary quarter-grid parity conditions. -/
def E8FoldedHole (x : Fin 8 → ℝ) : Prop :=
  ((∀ i, foldedRadius x i = 0) ∧ ¬Even (∑ i, roundedInt x i)) ∨
  ((∀ i, foldedRadius x i = 1 / 2) ∧ ¬Even (∑ i, halfRoundedInt x i)) ∨
  BalancedHalfGrid x ∨
  ((∀ i, foldedRadius x i = 1 / 4) ∧ ¬Even (∑ i, roundedInt x i) ∧
    ¬Even (∑ i, halfRoundedInt x i))

/-- Complete equality analysis in dimension eight, including all extra families. -/
theorem squaredDepth_E8_eq_one_iff (x : Fin 8 → ℝ) :
    squaredDepth (dPlusSet 8) x = 1 ↔ E8FoldedHole x := by
  constructor
  · intro hd
    obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ (foldedRadius x)
      (show (Finset.univ : Finset (Fin 8)).Nonempty from ⟨0, Finset.mem_univ _⟩)
    obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ (foldedRadius x)
      (show (Finset.univ : Finset (Fin 8)).Nonempty from ⟨0, Finset.mem_univ _⟩)
    have hlo' : ∀ i, foldedRadius x lo ≤ foldedRadius x i := fun i => hlo i (Finset.mem_univ _)
    have hhi' : ∀ i, foldedRadius x i ≤ foldedRadius x hi := fun i => hhi i (Finset.mem_univ _)
    have hp : PaperVerification.Lattice.roundingPeak 8 (foldedRadius x lo) (foldedRadius x hi) = 1 := by
      apply le_antisymm
      · simpa using PaperVerification.Lattice.roundingPeak_le 8 _ _ (by norm_num)
          (foldedRadius_nonneg x lo) (hlo' hi) (foldedRadius_le_half x hi)
      · rw [← hd]
        exact (squaredDepth_le_roundingEnvelope x lo hi hlo' hhi').trans
          (PaperVerification.Lattice.roundingEnvelope_le_peak 8 _ _ _
            (foldedRadius_nonneg x lo) (hlo' hi) (foldedRadius_le_half x hi))
    rcases (PaperVerification.Lattice.roundingPeak_eight_eq_iff _ _
      (foldedRadius_nonneg x lo) (hlo' hi) (foldedRadius_le_half x hi)).mp hp with hflat | hends
    · let t := foldedRadius x lo
      have ht : ∀ i, foldedRadius x i = t := by
        intro i
        exact le_antisymm ((hhi' i).trans_eq hflat) (hlo' i)
      have hnonneg : 0 ≤ t := foldedRadius_nonneg x lo
      have hhalf : t ≤ 1 / 2 := foldedRadius_le_half x lo
      have hformula := squaredDepth_dPlus_of_constant x lo t ht
      rw [hd] at hformula
      by_cases hz : t = 0
      · apply Or.inl
        refine ⟨by simpa [hz] using ht, ?_⟩
        intro he
        norm_num [hz, he] at hformula
      · by_cases hh : t = 1 / 2
        · refine Or.inr (Or.inl ?_)
          refine ⟨by simpa [hh] using ht, ?_⟩
          intro he
          norm_num [hh, he] at hformula
        · have htpos : 0 < t := lt_of_le_of_ne hnonneg (Ne.symm hz)
          have htlt : t < 1 / 2 := lt_of_le_of_ne hhalf hh
          obtain ⟨zi, hzi, hdi⟩ := exists_even_integer_bound x lo
          obtain ⟨zh, hzh, hdh⟩ := exists_even_half_integer_bound x lo
          have hiDepth := (squaredDepth_le x (show intVec zi ∈ dPlusSet 8 from
            ⟨zi, hzi, Or.inl rfl⟩)).trans hdi
          have hhDepth := (squaredDepth_le x (show (fun i => (zh i : ℝ) + 1 / 2) ∈ dPlusSet 8 from
            ⟨zh, hzh, Or.inr rfl⟩)).trans hdh
          simp only [hd, ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_ofNat] at hiDepth hhDepth
          have hquarter : t = 1 / 4 := by
            apply le_antisymm
            · by_contra h
              have hp := mul_pos (by linarith : 0 < 4 * t - 1) (by linarith : 0 < 1 - 2 * t)
              nlinarith only [hhDepth, hp]
            · by_contra h
              have hp := mul_pos htpos (by linarith : 0 < 1 - 4 * t)
              nlinarith only [hiDepth, hp]
          refine Or.inr (Or.inr (Or.inr ?_))
          refine ⟨by simpa [hquarter] using ht, ?_, ?_⟩
          · intro he
            by_cases he' : Even (∑ i, halfRoundedInt x i) <;>
              norm_num [hquarter, he, he'] at hformula
          · intro he
            by_cases he' : Even (∑ i, roundedInt x i) <;>
              norm_num [hquarter, he, he'] at hformula
    · refine Or.inr (Or.inr (Or.inl ?_))
      exact balanced_of_endpoint_extrema x lo hi hlo' hhi' hends.1 hends.2 (by simpa using hd)
  · rintro (⟨ht, he⟩ | ⟨ht, he⟩ | hb | ⟨ht, he, he'⟩)
    · have h := squaredDepth_dPlus_of_constant x 0 0 ht
      norm_num [he] at h
      exact h
    · have h := squaredDepth_dPlus_of_constant x 0 (1 / 2) ht
      norm_num [he] at h
      exact h
    · simpa using squaredDepth_dPlus_of_balanced (by decide : 8 ≤ 8) hb
    · have h := squaredDepth_dPlus_of_constant x 0 (1 / 4) ht
      norm_num [he, he'] at h
      exact h

/-- The complete deep-hole classification for E8 in folded coordinates. -/
theorem isDeepHole_E8_iff (x : Fin 8 → ℝ) : IsDeepHole (dPlusSet 8) x ↔ E8FoldedHole x := by
  rw [isDeepHole_dPlus_iff_depth (by decide : 8 ≤ 8) (⟨4, by norm_num⟩ : Even 8)]
  norm_num
  exact squaredDepth_E8_eq_one_iff x


/-- Membership in the coordinate half-integer grid, with its usual meaning. -/
def HalfIntegerGrid (x : Fin n → ℝ) : Prop := ∀ i, ∃ k : ℤ, x i = (k : ℝ) / 2

/-- Count coordinates that are not integers. -/
def nonintegerCount (x : Fin n → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ¬∃ k : ℤ, x i = (k : ℝ)).card

/-- The exact set displayed in equation (10) of the manuscript. -/
def PaperHalfGrid (x : Fin n → ℝ) : Prop := HalfIntegerGrid x ∧ nonintegerCount x = n / 2

theorem halfIntegerCoordinate_iff (x : Fin n → ℝ) (i : Fin n) :
    (∃ k : ℤ, x i = (k : ℝ) / 2) ↔
      foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨z, he | ho⟩ := Int.even_or_odd' k
    · apply Or.inl
      apply (foldedRadius_eq_zero_iff x i).mpr
      refine ⟨z, ?_⟩
      rw [hk, he]
      push_cast
      ring
    · apply Or.inr
      apply (foldedRadius_eq_half_iff x i).mpr
      refine ⟨z, ?_⟩
      rw [hk, ho]
      push_cast
      ring
  · rintro (h | h)
    · obtain ⟨z, hz⟩ := (foldedRadius_eq_zero_iff x i).mp h
      refine ⟨2 * z, ?_⟩
      rw [hz]
      push_cast
      ring
    · obtain ⟨z, hz⟩ := (foldedRadius_eq_half_iff x i).mp h
      refine ⟨2 * z + 1, ?_⟩
      rw [hz]
      push_cast
      ring

theorem folded_sum_eq_nonintegerCount (x : Fin n → ℝ)
    (hx : ∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2) :
    (∑ i, foldedRadius x i) = (nonintegerCount x : ℝ) / 2 := by
  classical
  have hi (i : Fin n) : foldedRadius x i =
      if ¬∃ k : ℤ, x i = (k : ℝ) then 1 / 2 else 0 := by
    by_cases hz : ∃ k : ℤ, x i = (k : ℝ)
    · simp [hz, (foldedRadius_eq_zero_iff x i).mpr hz]
    · simp only [hz, not_false_eq_true, if_true]
      rcases hx i with h | h
      · exact False.elim (hz ((foldedRadius_eq_zero_iff x i).mp h))
      · exact h
  simp only [hi]
  rw [Finset.sum_ite]
  simp [nonintegerCount] <;> ring

/-- The folded characterization is faithfully equivalent to the paper's actual
half-grid and exact cardinality condition, throughout its stated even dimensions. -/
theorem balancedHalfGrid_iff_paperHalfGrid (heven : Even n) (x : Fin n → ℝ) :
    BalancedHalfGrid x ↔ PaperHalfGrid x := by
  constructor
  · intro hx
    refine ⟨fun i => (halfIntegerCoordinate_iff x i).mpr (hx.1 i), ?_⟩
    have hsum := folded_sum_eq_nonintegerCount x hx.1
    have he : 2 * nonintegerCount x = n := by
      have heR : 2 * (nonintegerCount x : ℝ) = (n : ℝ) := by linarith [hx.2]
      exact_mod_cast heR
    calc
      nonintegerCount x = (2 * nonintegerCount x) / 2 := by simp
      _ = n / 2 := by rw [he]
  · rintro ⟨hgrid, hcount⟩
    have hx : ∀ i, foldedRadius x i = 0 ∨ foldedRadius x i = 1 / 2 :=
      fun i => (halfIntegerCoordinate_iff x i).mp (hgrid i)
    refine ⟨hx, ?_⟩
    rw [folded_sum_eq_nonintegerCount x hx, hcount]
    have he : 2 * (↑(n / 2) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.two_mul_div_two_of_even heven
    linarith

/-- Proposition 3.4's complete n>8 equality locus with its original coordinate meaning. -/
theorem isDeepHole_dPlus_iff_paperHalfGrid (hn : 8 < n) (heven : Even n) (x : Fin n → ℝ) :
    IsDeepHole (dPlusSet n) x ↔ PaperHalfGrid x :=
  (isDeepHole_dPlus_iff_balanced hn heven x).trans (balancedHalfGrid_iff_paperHalfGrid heven x)

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.squaredDepth_dPlus_le
#print axioms PaperVerification.ColdSpots.squaredDepth_dPlus_of_balanced

#print axioms PaperVerification.ColdSpots.dPlus_squared_covering_radius
#print axioms PaperVerification.ColdSpots.isDeepHole_dPlus_iff_balanced

#print axioms PaperVerification.ColdSpots.isDeepHole_E8_iff

#print axioms PaperVerification.ColdSpots.isDeepHole_dPlus_iff_paperHalfGrid
