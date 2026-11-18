module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum

/-!
# Exact sign patterns in a zero-sum hyperplane

This is a general finite-dimensional lemma. The six-coordinate counts below
count actual sign patterns, not fans. The geometric equivalence with all A3
facet subdivisions and the projectivity criterion are separate obligations.

UNVERIFIED DEVELOPMENT SOURCE until its exact pinned native check succeeds.
-/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace Unimodular.A3SignPatterns

variable {I : Type*} [Fintype I]

/-- The signs compatible with a zero-sum vector. -/
def Admissible (s : I → SignType) : Prop :=
  (∀ i, s i = 0) ∨ ((∃ i, s i = 1) ∧ ∃ i, s i = -1)

instance admissibleDecidable (s : I → SignType) : Decidable (Admissible s) :=
  inferInstanceAs (Decidable ((∀ i, s i = 0) ∨ ((∃ i, s i = 1) ∧ ∃ i, s i = -1)))

def positiveIndices (s : I → SignType) : Finset I :=
  Finset.univ.filter (fun i => s i = 1)

def negativeIndices (s : I → SignType) : Finset I :=
  Finset.univ.filter (fun i => s i = -1)

/-- An explicit integer-valued real witness: every positive entry is the
number of negative indices, and every negative entry is minus the number of
positive indices. This witness is valid whenever both signs occur. -/
def balancedWeight (s : I → SignType) (i : I) : ℝ :=
  (if s i = 1 then ((negativeIndices s).card : ℝ) else 0) -
  (if s i = -1 then ((positiveIndices s).card : ℝ) else 0)

theorem sum_balancedWeight (s : I → SignType) :
    (∑ i, balancedWeight s i) = 0 := by
  classical
  simp only [balancedWeight, Finset.sum_sub_distrib, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  exact sub_eq_zero.mpr (mul_comm _ _)

theorem balancedWeight_sign (s : I → SignType)
    (hp : ∃ i, s i = 1) (hn : ∃ i, s i = -1) :
    ∀ i, SignType.sign (balancedWeight s i) = s i := by
  classical
  have hpCard : 0 < (positiveIndices s).card := by
    rcases hp with ⟨i, hi⟩
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hnCard : 0 < (negativeIndices s).card := by
    rcases hn with ⟨i, hi⟩
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  intro i
  cases hsi : s i with
  | zero => simp [balancedWeight, hsi]
  | neg =>
    change SignType.sign (balancedWeight s i) = (-1 : SignType)
    apply sign_eq_neg_one_iff.mpr
    simpa [balancedWeight, hsi] using
      (neg_neg_of_pos (Nat.cast_pos.mpr hpCard) : -((positiveIndices s).card : ℝ) < 0)
  | pos =>
    change SignType.sign (balancedWeight s i) = (1 : SignType)
    apply sign_eq_one_iff.mpr
    simpa [balancedWeight, hsi] using
      (Nat.cast_pos.mpr hnCard : (0 : ℝ) < (negativeIndices s).card)

theorem exists_pos_and_neg_of_zero_sum {x : I → ℝ}
    (hsum : (∑ i, x i) = 0) (hnz : ∃ i, x i ≠ 0) :
    (∃ i, 0 < x i) ∧ ∃ i, x i < 0 := by
  classical
  constructor
  · by_contra h
    simp only [not_exists, not_lt] at h
    rcases hnz with ⟨i, hi⟩
    exact hi ((Finset.sum_eq_zero_iff_of_nonpos (fun j _ => h j)).mp
      hsum i (Finset.mem_univ i))
  · by_contra h
    simp only [not_exists, not_lt] at h
    rcases hnz with ⟨i, hi⟩
    exact hi ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h j)).mp
      hsum i (Finset.mem_univ i))

/-- Complete sign realizability, for every finite index type, including the
empty type. The existential witness satisfies the literal real zero-sum
identity and the ordinary Mathlib sign function. -/
theorem exists_zero_sum_with_sign_iff (s : I → SignType) :
    (∃ x : I → ℝ, (∑ i, x i) = 0 ∧ ∀ i, SignType.sign (x i) = s i) ↔
      Admissible s := by
  classical
  constructor
  · rintro ⟨x, hsum, hsign⟩
    by_cases hz : ∀ i, s i = 0
    · exact Or.inl hz
    · apply Or.inr
      rcases not_forall.mp hz with ⟨i, hi⟩
      have hxi : x i ≠ 0 := by
        intro h
        apply hi
        rw [← hsign i, h, sign_zero]
      obtain ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ := exists_pos_and_neg_of_zero_sum hsum ⟨i, hxi⟩
      exact ⟨⟨j, (hsign j).symm.trans (sign_pos hj)⟩,
        ⟨k, (hsign k).symm.trans (sign_neg hk)⟩⟩
  · rintro (hz | ⟨hp, hn⟩)
    · exact ⟨fun _ => 0, by simp, fun i => by rw [hz i]; exact sign_zero⟩
    · exact ⟨balancedWeight s, sum_balancedWeight s, balancedWeight_sign s hp hn⟩

/-- A change of sign in any fixed set of coordinates is a genuine bijection
of all sign patterns. It also preserves the property of having no zero entry. -/
def reorient (c : I → SignType) (hc : ∀ i, c i ≠ 0) :
    (I → SignType) ≃ (I → SignType) where
  toFun s i := c i * s i
  invFun s i := c i * s i
  left_inv s := by
    funext i
    have hi := hc i
    cases hci : c i <;> simp_all
  right_inv s := by
    funext i
    have hi := hc i
    cases hci : c i <;> simp_all

/-- The signs of a triangulation have no zero coordinate. -/
def NoZero (s : I → SignType) : Prop := ∀ i, s i ≠ 0

instance noZeroDecidable (s : I → SignType) : Decidable (NoZero s) :=
  inferInstanceAs (Decidable (∀ i, s i ≠ 0))

theorem noZero_reorient_iff (c : I → SignType) (hc : ∀ i, c i ≠ 0)
    (s : I → SignType) : NoZero (reorient c hc s) ↔ NoZero s := by
  change (∀ i, c i * s i ≠ 0) ↔ ∀ i, s i ≠ 0
  constructor
  · intro h i
    exact (mul_ne_zero_iff.mp (h i)).2
  · intro h i
    exact mul_ne_zero (hc i) (h i)

set_option maxRecDepth 100000 in
/-- All six-coordinate ternary patterns. This is a kernel computation of a
finite cardinality, not an empirical enumeration. -/
theorem six_pattern_count : Fintype.card (Fin 6 → SignType) = 729 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem six_admissible_pattern_count :
    Fintype.card {s : Fin 6 → SignType // Admissible s} = 603 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem six_noZero_pattern_count :
    Fintype.card {s : Fin 6 → SignType // NoZero s} = 64 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem six_admissible_noZero_pattern_count :
    Fintype.card {s : Fin 6 → SignType // Admissible s ∧ NoZero s} = 62 := by decide

#print axioms exists_zero_sum_with_sign_iff
#print axioms reorient
#print axioms noZero_reorient_iff
#print axioms six_pattern_count
#print axioms six_admissible_pattern_count
#print axioms six_noZero_pattern_count
#print axioms six_admissible_noZero_pattern_count

end Unimodular.A3SignPatterns

#check "UNIMODULAR_A3_SIGN_PATTERNS_EOF_V3"
