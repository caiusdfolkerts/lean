module
public import PaperVerification.LatticeGeometry
public import Mathlib.Algebra.Ring.Int.Parity
@[expose] public section
/-! # The literal coordinate families of the E8 deep holes

This module identifies the complete folded-coordinate result with the three
families printed in Proposition 3.4.  In particular, the quarter-grid family
retains both its odd integer-sum condition and its even number of minus signs.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

variable {n : ℕ}

def negativeSignCount (ε : Fin n → ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ε i = -1).card

/-- The exceptional quarter-coordinate family with its literal sign parity. -/
def E8QuarterFamily (x : Fin 8 → ℝ) : Prop :=
  ∃ m ε : Fin 8 → ℤ, Odd (∑ i, m i) ∧ (∀ i, ε i = 1 ∨ ε i = -1) ∧
    Even (negativeSignCount ε) ∧ ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4

/-- The first coordinate vector in the Euclidean realization of E8. -/
def e8FirstVector : Fin 8 → ℝ := fun i => if i = 0 then 1 else 0

/-- The literal translate `e₁ + E8`. -/
def E8FirstFamily (x : Fin 8 → ℝ) : Prop :=
  ∃ y ∈ dPlusSet 8, x = e8FirstVector + y

/-- An elementary intermediate description of the same odd coset. -/
def E8OddCoset (x : Fin 8 → ℝ) : Prop :=
  ∃ z : Fin 8 → ℤ, Odd (∑ i, z i) ∧
    (x = intVec z ∨ x = fun i => (z i : ℝ) + 1 / 2)

theorem roundedInt_intVec (z : Fin n → ℤ) : roundedInt (intVec z) = z := by
  funext i
  simp [roundedInt, intVec]

theorem halfRoundedInt_halfVec (z : Fin n → ℤ) :
    halfRoundedInt (fun i => (z i : ℝ) + 1 / 2) = z := by
  have hh : round (1 / 2 : ℝ) = 1 := by norm_num [round_eq]
  funext i
  have hround : roundedInt (fun i => (z i : ℝ) + 1 / 2) i = z i + 1 := by
    simp only [roundedInt, round_intCast_add, hh]
  have hneg : ¬(0 : ℝ) ≤ (z i : ℝ) + 1 / 2 - ((z i + 1 : ℤ) : ℝ) := by
    push_cast
    linarith
  simp only [halfRoundedInt, hround, if_neg hneg]
  ring

theorem e8OddCoset_iff_folded_endpoints (x : Fin 8 → ℝ) :
    E8OddCoset x ↔
      ((∀ i, foldedRadius x i = 0) ∧ ¬Even (∑ i, roundedInt x i)) ∨
      ((∀ i, foldedRadius x i = 1 / 2) ∧ ¬Even (∑ i, halfRoundedInt x i)) := by
  constructor
  · rintro ⟨z, hz, hx | hx⟩
    · subst x
      refine Or.inl ⟨?_, ?_⟩
      · intro i
        exact (foldedRadius_eq_zero_iff _ i).mpr ⟨z i, rfl⟩
      · rw [roundedInt_intVec]
        exact Int.not_even_iff_odd.mpr hz
    · subst x
      refine Or.inr ⟨?_, ?_⟩
      · intro i
        exact (foldedRadius_eq_half_iff _ i).mpr ⟨z i, rfl⟩
      · rw [halfRoundedInt_halfVec]
        exact Int.not_even_iff_odd.mpr hz
  · rintro (⟨hr, hp⟩ | ⟨hr, hp⟩)
    · refine ⟨roundedInt x, Int.not_even_iff_odd.mp hp, Or.inl ?_⟩
      funext i
      exact sub_eq_zero.mp (abs_eq_zero.mp (hr i))
    · refine ⟨halfRoundedInt x, Int.not_even_iff_odd.mp hp, Or.inr ?_⟩
      funext i
      have h := abs_sub_halfRoundedInt x i
      rw [hr i, sub_self] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp h)

theorem e8FirstFamily_iff_oddCoset (x : Fin 8 → ℝ) :
    E8FirstFamily x ↔ E8OddCoset x := by
  classical
  constructor
  · rintro ⟨y, ⟨z, hz, hy | hy⟩, hx⟩
    all_goals
      refine ⟨alterCoordinate z 0 1, ?_, ?_⟩
    · rw [sum_alterCoordinate]
      apply Int.not_even_iff_odd.mp
      simpa only [Int.even_add_one, not_not] using hz
    · left
      rw [hx, hy]
      funext i
      by_cases hi : i = 0 <;> simp [e8FirstVector, alterCoordinate, intVec, hi] <;> ring
    · rw [sum_alterCoordinate]
      apply Int.not_even_iff_odd.mp
      simpa only [Int.even_add_one, not_not] using hz
    · right
      rw [hx, hy]
      funext i
      by_cases hi : i = 0 <;> simp [e8FirstVector, alterCoordinate, intVec, hi] <;> ring
  · rintro ⟨z, hz, hx | hx⟩
    · refine ⟨intVec (alterCoordinate z 0 (-1)), ?_, ?_⟩
      · refine ⟨alterCoordinate z 0 (-1), ?_, Or.inl rfl⟩
        rw [sum_alterCoordinate]
        simpa only [sub_eq_add_neg] using Int.even_sub_one.mpr (Int.not_even_iff_odd.mpr hz)
      · rw [hx]
        funext i
        by_cases hi : i = 0 <;> simp [e8FirstVector, alterCoordinate, intVec, hi] <;> ring
    · refine ⟨(fun i => (alterCoordinate z 0 (-1) i : ℝ) + 1 / 2), ?_, ?_⟩
      · refine ⟨alterCoordinate z 0 (-1), ?_, Or.inr rfl⟩
        rw [sum_alterCoordinate]
        simpa only [sub_eq_add_neg] using Int.even_sub_one.mpr (Int.not_even_iff_odd.mpr hz)
      · rw [hx]
        funext i
        by_cases hi : i = 0 <;> simp [e8FirstVector, alterCoordinate, intVec, hi] <;> ring

theorem roundedInt_of_signed_quarters {x : Fin n → ℝ} {m ε : Fin n → ℤ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hx : ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4) : roundedInt x = m := by
  have hp : round (1 / 4 : ℝ) = 0 := round_eq_zero_iff.mpr (by norm_num)
  have hn : round (-1 / 4 : ℝ) = 0 := round_eq_zero_iff.mpr (by norm_num)
  funext i
  dsimp [roundedInt]
  rw [hx i, round_intCast_add]
  rcases hε i with he | he <;> norm_num [he, hp, hn]

theorem foldedRadius_of_signed_quarters {x : Fin n → ℝ} {m ε : Fin n → ℤ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hx : ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4) :
    ∀ i, foldedRadius x i = 1 / 4 := by
  intro i
  unfold foldedRadius
  rw [roundedInt_of_signed_quarters hε hx, hx i]
  rcases hε i with he | he <;> norm_num [he]

theorem halfRoundedInt_of_signed_quarters {x : Fin n → ℝ} {m ε : Fin n → ℤ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hx : ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4) :
    ∀ i, halfRoundedInt x i = m i - if ε i = -1 then 1 else 0 := by
  intro i
  unfold halfRoundedInt
  rw [roundedInt_of_signed_quarters hε hx, hx i]
  rcases hε i with he | he <;> norm_num [he, sub_eq_add_neg]

theorem sum_halfRoundedInt_of_signed_quarters {x : Fin n → ℝ} {m ε : Fin n → ℤ}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hx : ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4) :
    (∑ i, halfRoundedInt x i) = (∑ i, m i) - (negativeSignCount ε : ℤ) := by
  classical
  simp only [halfRoundedInt_of_signed_quarters hε hx, Finset.sum_sub_distrib]
  simp [negativeSignCount, Finset.sum_ite]

theorem e8QuarterFamily_iff_folded (x : Fin 8 → ℝ) :
    E8QuarterFamily x ↔ ((∀ i, foldedRadius x i = 1 / 4) ∧
      ¬Even (∑ i, roundedInt x i) ∧ ¬Even (∑ i, halfRoundedInt x i)) := by
  classical
  constructor
  · rintro ⟨m, ε, hm, hε, he, hx⟩
    refine ⟨foldedRadius_of_signed_quarters hε hx, ?_, ?_⟩
    · rw [roundedInt_of_signed_quarters hε hx]
      exact Int.not_even_iff_odd.mpr hm
    · rw [sum_halfRoundedInt_of_signed_quarters hε hx]
      apply Int.not_even_iff_odd.mpr
      exact Int.odd_sub.mpr ⟨fun _ => (Int.even_coe_nat _).mpr he, fun _ => hm⟩
  · rintro ⟨hr, hm, hh⟩
    let m := roundedInt x
    let ε : Fin 8 → ℤ := fun i => if 0 ≤ x i - (m i : ℝ) then 1 else -1
    have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
      intro i
      by_cases hi : 0 ≤ x i - (m i : ℝ)
      · exact Or.inl (if_pos hi)
      · exact Or.inr (if_neg hi)
    have hx : ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4 := by
      intro i
      have hi : |x i - (m i : ℝ)| = 1 / 4 := hr i
      by_cases hs : 0 ≤ x i - (m i : ℝ)
      · rw [abs_of_nonneg hs] at hi
        simp only [ε, if_pos hs, Int.cast_one]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hs)] at hi
        simp only [ε, if_neg hs, Int.cast_neg, Int.cast_one]
        linarith
    have hmo : Odd (∑ i, m i) := Int.not_even_iff_odd.mp hm
    have hho := Int.not_even_iff_odd.mp hh
    rw [sum_halfRoundedInt_of_signed_quarters hε hx] at hho
    have he : Even (negativeSignCount ε) :=
      (Int.even_coe_nat _).mp ((Int.odd_sub.mp hho).mp hmo)
    exact ⟨m, ε, hmo, hε, he, hx⟩

/-- The paper's three complete coordinate families, with no bounded enumeration. -/
def E8PaperHole (x : Fin 8 → ℝ) : Prop :=
  E8FirstFamily x ∨ PaperHalfGrid x ∨ E8QuarterFamily x

theorem e8FoldedHole_iff_paper (x : Fin 8 → ℝ) : E8FoldedHole x ↔ E8PaperHole x := by
  rw [E8PaperHole, e8FirstFamily_iff_oddCoset, e8OddCoset_iff_folded_endpoints,
    ← balancedHalfGrid_iff_paperHalfGrid (by decide : Even 8), e8QuarterFamily_iff_folded]
  unfold E8FoldedHole
  tauto

/-- Proposition 3.4 in its literal dimension-eight coordinate formulation. -/
theorem isDeepHole_E8_iff_paper (x : Fin 8 → ℝ) :
    IsDeepHole (dPlusSet 8) x ↔ E8PaperHole x :=
  (isDeepHole_E8_iff x).trans (e8FoldedHole_iff_paper x)

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.e8FoldedHole_iff_paper
#print axioms PaperVerification.ColdSpots.isDeepHole_E8_iff_paper
