module

public import Papers.GraphicalZonotopes.Mobius

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators

/-- A literal Boolean coordinate, viewed in the coefficient field. -/
def membershipBit {V : Type*} [DecidableEq V] (S : Finset V) (v : V) : ℝ :=
  if v ∈ S then 1 else 0

@[simp] theorem membershipBit_zero_or_one {V : Type*} [DecidableEq V]
    (S : Finset V) (v : V) : membershipBit S v = 0 ∨ membershipBit S v = 1 := by
  unfold membershipBit
  split <;> simp

/-- Zero extension beyond the endpoints is part of the definition, rather
than a convention left to an informal boundary argument. -/
def integerBit {n : ℕ} (S : Finset (Fin n)) (k : ℤ) : ℝ :=
  if ∃ v : Fin n, (v.val : ℤ) = k ∧ v ∈ S then 1 else 0

@[simp] theorem integerBit_cast {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    integerBit S (v.val : ℤ) = membershipBit S v := by
  have he : (∃ w : Fin n, (w.val : ℤ) = (v.val : ℤ) ∧ w ∈ S) ↔ v ∈ S := by
    constructor
    · rintro ⟨w, hw, hS⟩
      have h : w = v := Fin.ext (by exact_mod_cast hw)
      simpa [h] using hS
    · intro h
      exact ⟨v, rfl, h⟩
  unfold integerBit membershipBit
  simp only [he]

theorem integerBit_zero_or_one {n : ℕ} (S : Finset (Fin n)) (k : ℤ) :
    integerBit S k = 0 ∨ integerBit S k = 1 := by
  unfold integerBit
  split <;> simp

theorem integerBit_bounds_of_ne_zero {n : ℕ} {S : Finset (Fin n)} {k : ℤ}
    (h : integerBit S k ≠ 0) : 0 ≤ k ∧ k < n := by
  unfold integerBit at h
  split at h
  · rename_i hm
    obtain ⟨v, rfl, hv⟩ := hm
    exact ⟨by omega, by exact_mod_cast v.isLt⟩
  · exact False.elim (h rfl)

theorem integerBit_eq_zero_of_outside {n : ℕ} (S : Finset (Fin n)) (k : ℤ)
    (h : k < 0 ∨ (n : ℤ) ≤ k) : integerBit S k = 0 := by
  by_contra hn
  have hb := integerBit_bounds_of_ne_zero hn
  omega

/-- Ordered three-point monomials have precisely their three possible pair
rows. This is an identity for every conditioning set. -/
theorem delta_monomial_three {n : ℕ} {a b c u v : Fin n} {S : Finset (Fin n)}
    (hab : a < b) (hbc : b < c) (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (setMonomial {a,b,c}) u v S =
      (if u = a ∧ v = b then membershipBit S c else 0) +
      (if u = a ∧ v = c then membershipBit S b else 0) +
      (if u = b ∧ v = c then membershipBit S a else 0) := by
  rw [delta_setMonomial (ne_of_lt huv) hu hv]
  by_cases huC : u ∈ ({a,b,c} : Finset (Fin n))
  · by_cases hvC : v ∈ ({a,b,c} : Finset (Fin n))
    · simp only [mem_insert, mem_singleton] at huC hvC
      rcases huC with rfl | rfl | rfl <;> rcases hvC with rfl | rfl | rfl
      all_goals first | omega | simp_all [membershipBit, insert_subset_iff, Fin.ext_iff]
      all_goals try { split_ifs <;> simp_all <;> omega }
    · have hvab : v ≠ a ∧ v ≠ b ∧ v ≠ c := by simpa using hvC
      simp [huC, hvC, hvab.1, hvab.2.1, hvab.2.2]
  · have huab : u ≠ a ∧ u ≠ b ∧ u ≠ c := by simpa using huC
    simp [huC, huab.1, huab.2.1, huab.2.2]

/-- The analogous exact six-term identity for a four-point monomial. -/
theorem delta_monomial_four {n : ℕ} {a b c d u v : Fin n} {S : Finset (Fin n)}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (huv : u < v) (hu : u ∉ S) (hv : v ∉ S) :
    delta (setMonomial {a,b,c,d}) u v S =
      (if u = a ∧ v = b then membershipBit S c * membershipBit S d else 0) +
      (if u = a ∧ v = c then membershipBit S b * membershipBit S d else 0) +
      (if u = a ∧ v = d then membershipBit S b * membershipBit S c else 0) +
      (if u = b ∧ v = c then membershipBit S a * membershipBit S d else 0) +
      (if u = b ∧ v = d then membershipBit S a * membershipBit S c else 0) +
      (if u = c ∧ v = d then membershipBit S a * membershipBit S b else 0) := by
  rw [delta_setMonomial (ne_of_lt huv) hu hv]
  by_cases huC : u ∈ ({a,b,c,d} : Finset (Fin n))
  · by_cases hvC : v ∈ ({a,b,c,d} : Finset (Fin n))
    · simp only [mem_insert, mem_singleton] at huC hvC
      rcases huC with rfl | rfl | rfl | rfl <;>
        rcases hvC with rfl | rfl | rfl | rfl
      all_goals first | omega | simp_all [membershipBit, insert_subset_iff, Fin.ext_iff]
      all_goals try { split_ifs <;> simp_all <;> omega }
      all_goals split_ifs <;> simp_all <;> omega
    · have hvab : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d := by simpa using hvC
      simp [huC, hvC, hvab.1, hvab.2.1, hvab.2.2.1, hvab.2.2.2]
  · have huab : u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ d := by simpa using huC
    simp [huC, huab.1, huab.2.1, huab.2.2.1, huab.2.2.2]

/-- Collapse a translated Kronecker row. The support hypothesis is explicitly
proved from the zero-extended Boolean factors in each application. -/
theorem sum_at_integer (N : ℕ) (k : ℤ) (r : ℝ)
    (hr : r ≠ 0 → 0 ≤ k ∧ k < N) :
    (∑ j : Fin N, if (j.val : ℤ) = k then r else 0) = r := by
  by_cases hz : r = 0
  · simp [hz]
  · obtain ⟨hk0, hkN⟩ := hr hz
    let j : Fin N := ⟨k.toNat, by omega⟩
    have hj : (j.val : ℤ) = k := by dsimp [j]; omega
    rw [sum_eq_single j]
    · simp [hj]
    · intro l hl hlj
      have hne : (l.val : ℤ) ≠ k := by
        intro he
        apply hlj
        apply Fin.ext
        dsimp [j]
        omega
      simp [hne]
    · simp

/-- A useful version with a function evaluated at the start of the window. -/
theorem sum_pair_start (N : ℕ) (a b u v : ℤ) (F : ℤ → ℝ)
    (hsupport : v = u + (b-a) → F (u-a) ≠ 0 → 0 ≤ u-a ∧ u-a < N) :
    (∑ j : Fin N, if u = (j.val : ℤ)+a ∧ v = (j.val : ℤ)+b
      then F (j.val : ℤ) else 0) =
      if v = u + (b-a) then F (u-a) else 0 := by
  have hterm (j : Fin N) :
      (if u = (j.val : ℤ)+a ∧ v = (j.val : ℤ)+b then F (j.val : ℤ) else 0) =
      if v = u+(b-a) then (if (j.val : ℤ) = u-a then F (u-a) else 0) else 0 := by
    by_cases h : v = u+(b-a)
    · rw [if_pos h]
      by_cases hj : (j.val : ℤ) = u-a
      · have he : u = (j.val : ℤ)+a ∧ v = (j.val : ℤ)+b := by omega
        rw [if_pos he, if_pos hj, hj]
      · have he : ¬(u = (j.val : ℤ)+a ∧ v = (j.val : ℤ)+b) := by omega
        rw [if_neg he, if_neg hj]
    · have he : ¬(u = (j.val : ℤ)+a ∧ v = (j.val : ℤ)+b) := by omega
      rw [if_neg he, if_neg h]
  simp_rw [hterm]
  by_cases h : v = u+(b-a)
  · simp only [if_pos h]
    exact sum_at_integer N (u-a) (F (u-a)) (hsupport h)
  · simp [h]

/-- The path's three slack polynomials, checked for every Boolean assignment. -/
theorem path_boolean_slack_one {a b c d : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) :
    0 ≤ a*(1-b)+b*(1-c)+c*(1-d) ∧ a*(1-b)+b*(1-c)+c*(1-d) ≤ 2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> norm_num

theorem path_boolean_slack_two {a b c : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    0 ≤ b*(1-a)+c*(1-b) ∧ b*(1-a)+c*(1-b) ≤ 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> norm_num

theorem path_boolean_slack_three {a b : ℝ}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    0 ≤ b*(1-a) ∧ b*(1-a) ≤ 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

end GraphicalZonotopes
