module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
/-!
# The all-dimensional rounding estimate

The inequalities here are the continuous optimization in equations (11)--(12)
of the lattice paper. They are valid for every real `n ≥ 8`, and consequently
for every dimension in the paper. No theta or lattice conclusion is declared
without the missing geometric and analytic dependencies.
-/

noncomputable section

namespace PaperVerification.Lattice

open scoped BigOperators

/-- The two affine parity-repair upper bounds after taking the secant estimate. -/
def roundingEnvelope (n m M T : ℝ) : ℝ :=
  min ((m + M) * T - n * m * M + 1 - 2 * M)
    ((m + M - 1) * T + n / 4 - n * m * M + 2 * m)

/-- Their common value, written in the factored form useful for equality. -/
def roundingPeak (n m M : ℝ) : ℝ :=
  n / 8 - (n / 4 - 2) * (m + M - 1 / 2) ^ 2 -
    (1 / 2 - (M - m)) * (n / 4 * (M - m) + n / 8 - 1)

/-- The envelope of the increasing and decreasing affine bounds is bounded
by their common value, without any restriction on the coordinate sum `T`. -/
theorem roundingEnvelope_le_peak (n m M T : ℝ)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1 / 2) :
    roundingEnvelope n m M T ≤ roundingPeak n m M := by
  have hs : 0 ≤ m + M := by linarith
  have hs1 : m + M ≤ 1 := by linarith
  rcases le_total T (n / 4 - 1 + 2 * (m + M)) with hT | hT
  · refine (min_le_left _ _).trans ?_
    unfold roundingPeak
    have hprod := mul_nonneg hs (sub_nonneg.mpr hT)
    linarith
  · refine (min_le_right _ _).trans ?_
    unfold roundingPeak
    have hprod := mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hT)
    linarith

/-- The sharp polynomial estimate, valid throughout the full dimension range. -/
theorem roundingPeak_le (n m M : ℝ) (hn : 8 ≤ n)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1 / 2) :
    roundingPeak n m M ≤ n / 8 := by
  have ha : 0 ≤ (n / 4 - 2) * (m + M - 1 / 2) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hb : 0 ≤ (1 / 2 - (M - m)) * (n / 4 * (M - m) + n / 8 - 1) := by
    apply mul_nonneg
    · linarith
    · have := mul_nonneg (by linarith : 0 ≤ n / 4) (sub_nonneg.mpr hmM)
      linarith
  unfold roundingPeak
  linarith

/-- Equation (12) implies the uniform `n/8` upper bound. -/
theorem roundingEnvelope_le (n m M T : ℝ) (hn : 8 ≤ n)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1 / 2) :
    roundingEnvelope n m M T ≤ n / 8 :=
  (roundingEnvelope_le_peak n m M T hm hmM hM).trans (roundingPeak_le n m M hn hm hmM hM)

/-- Above dimension eight, equality forces the two extreme folded coordinates
and the balanced total. This is the sharp equality statement for the envelope. -/
theorem roundingEnvelope_eq_iff (n m M T : ℝ) (hn : 8 < n)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1 / 2) :
    roundingEnvelope n m M T = n / 8 ↔ m = 0 ∧ M = 1 / 2 ∧ T = n / 4 := by
  constructor
  · intro heq
    have hpeak : roundingPeak n m M = n / 8 := le_antisymm
      (roundingPeak_le n m M hn.le hm hmM hM)
      (heq ▸ roundingEnvelope_le_peak n m M T hm hmM hM)
    have ha : 0 ≤ (n / 4 - 2) * (m + M - 1 / 2) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hp : 0 < n / 4 * (M - m) + n / 8 - 1 := by
      have := mul_nonneg (by linarith : 0 ≤ n / 4) (sub_nonneg.mpr hmM)
      linarith
    have hb : 0 ≤ (1 / 2 - (M - m)) * (n / 4 * (M - m) + n / 8 - 1) :=
      mul_nonneg (by linarith) hp.le
    have hz : (1 / 2 - (M - m)) * (n / 4 * (M - m) + n / 8 - 1) = 0 := by
      unfold roundingPeak at hpeak
      linarith
    have hδ : 1 / 2 - (M - m) = 0 :=
      (mul_eq_zero.mp hz).resolve_right (ne_of_gt hp)
    have hm0 : m = 0 := by linarith
    have hMhalf : M = 1 / 2 := by linarith
    refine ⟨hm0, hMhalf, ?_⟩
    unfold roundingEnvelope at heq
    have hleft := (le_min_iff.mp heq.ge).1
    have hright := (le_min_iff.mp heq.ge).2
    rw [hm0, hMhalf] at hleft hright
    linarith
  · rintro ⟨rfl, rfl, rfl⟩
    unfold roundingEnvelope
    ring_nf
    simp


/-- Dimension eight has exactly two extremal spread values. -/
theorem roundingPeak_eight_eq_iff (m M : ℝ)
    (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1 / 2) :
    roundingPeak 8 m M = 1 ↔ M = m ∨ (m = 0 ∧ M = 1 / 2) := by
  have hid : roundingPeak 8 m M = 1 - 2 * ((M - m) * (1 / 2 - (M - m))) := by
    unfold roundingPeak
    ring
  rw [hid]
  constructor
  · intro h
    have hz : (M - m) * (1 / 2 - (M - m)) = 0 := by linarith
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr ⟨by linarith, by linarith⟩
  · rintro (h | ⟨h, h'⟩)
    · rw [h]
      ring
    · rw [h, h']
      norm_num

/-- The secant bound for a family of folded coordinates. -/
theorem folded_square_sum_le {ι : Type*} (s : Finset ι) (r : ι → ℝ) (m M : ℝ)
    (hm : ∀ i ∈ s, m ≤ r i) (hM : ∀ i ∈ s, r i ≤ M) :
    (∑ i ∈ s, r i ^ 2) ≤ (m + M) * (∑ i ∈ s, r i) - (s.card : ℝ) * m * M := by
  have hs : (∑ i ∈ s, r i ^ 2) ≤ ∑ i ∈ s, ((m + M) * r i - m * M) := by
    apply Finset.sum_le_sum
    intro i hi
    have := mul_nonneg (sub_nonneg.mpr (hm i hi)) (sub_nonneg.mpr (hM i hi))
    linarith
  simpa [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc] using hs

end PaperVerification.Lattice

#print axioms PaperVerification.Lattice.roundingEnvelope_eq_iff
#print axioms PaperVerification.Lattice.folded_square_sum_le
