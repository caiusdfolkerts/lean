module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
@[expose] public section
/-!
# Gaussian sums used in the cold-spots manuscript

The sums in this file are actual infinite series over the integers. In particular,
convergence is proved before positivity or rearrangements are used. Nothing in this
file assumes a cold-spot inequality.
-/

noncomputable section

open scoped BigOperators

namespace PaperVerification.ColdSpots

/-- The one-dimensional Gaussian lattice sum, in the manuscript's normalization. -/
def gaussian (α t : ℝ) : ℝ :=
  ∑' z : ℤ, Real.exp (-α * ((z : ℝ) - t) ^ 2)

/-- The parity character of the integer lattice, with values in the reals. -/
def paritySign (z : ℤ) : ℝ := if Even z then 1 else -1

/-- The alternating Gaussian series of Section 2. -/
def alternatingGaussian (α t : ℝ) : ℝ :=
  ∑' z : ℤ, paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)

lemma summable_gaussian_nat {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ ↦ Real.exp (-α * (n : ℝ) ^ 2)) := by
  apply Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hα)
  intro n
  exact_mod_cast (show n ≤ n ^ 2 by simpa only [pow_two] using Nat.le_mul_self n)

lemma summable_gaussian_zero {α : ℝ} (hα : 0 < α) :
    Summable (fun z : ℤ ↦ Real.exp (-α * (z : ℝ) ^ 2)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa using summable_gaussian_nat hα
  · simpa using summable_gaussian_nat hα

/-- A translated Gaussian is dominated by a constant times a centered Gaussian. -/
lemma gaussian_term_bound (α : ℝ) (hα : 0 ≤ α) (t z : ℝ) :
    Real.exp (-α * (z - t) ^ 2) ≤
      Real.exp (α * t ^ 2) * Real.exp (-(α / 2) * z ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hα (sq_nonneg (z - 2 * t))]

lemma summable_gaussian {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Summable (fun z : ℤ ↦ Real.exp (-α * ((z : ℝ) - t) ^ 2)) := by
  refine ((summable_gaussian_zero (half_pos hα)).mul_left
    (Real.exp (α * t ^ 2))).of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) ?_
  intro z
  exact gaussian_term_bound α hα.le t z

lemma hasSum_gaussian {α : ℝ} (hα : 0 < α) (t : ℝ) :
    HasSum (fun z : ℤ ↦ Real.exp (-α * ((z : ℝ) - t) ^ 2)) (gaussian α t) := by
  unfold gaussian
  exact (summable_gaussian hα t).hasSum

lemma norm_paritySign (z : ℤ) : ‖paritySign z‖ = 1 := by
  unfold paritySign
  split_ifs <;> norm_num

lemma paritySign_zero : paritySign 0 = 1 := by simp [paritySign]

lemma paritySign_neg (z : ℤ) : paritySign (-z) = paritySign z := by
  simp [paritySign]

lemma paritySign_add (z w : ℤ) : paritySign (z + w) = paritySign z * paritySign w := by
  by_cases hz : Even z <;> by_cases hw : Even w <;>
    simp [paritySign, Int.even_add, hz, hw]

lemma paritySign_add_one (z : ℤ) : paritySign (z + 1) = -paritySign z := by
  rw [paritySign_add]
  have h1 : paritySign 1 = -1 := by norm_num [paritySign]
  rw [h1, mul_neg_one]

lemma summable_alternatingGaussian {α : ℝ} (hα : 0 < α) (t : ℝ) :
    Summable (fun z : ℤ ↦ paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)) := by
  apply (summable_gaussian hα t).of_norm_bounded
  intro z
  have hs : |paritySign z| = 1 := by
    simpa only [Real.norm_eq_abs] using norm_paritySign z
  simp [norm_mul, Real.norm_eq_abs, hs, abs_of_pos (Real.exp_pos _)]

lemma hasSum_alternatingGaussian {α : ℝ} (hα : 0 < α) (t : ℝ) :
    HasSum (fun z : ℤ ↦ paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2))
      (alternatingGaussian α t) := by
  unfold alternatingGaussian
  exact (summable_alternatingGaussian hα t).hasSum

lemma gaussian_pos {α : ℝ} (hα : 0 < α) (t : ℝ) : 0 < gaussian α t := by
  exact (summable_gaussian hα t).tsum_pos
    (fun z ↦ (Real.exp_pos _).le) 0 (Real.exp_pos _)

lemma alternatingGaussian_lt {α : ℝ} (hα : 0 < α) (t : ℝ) :
    alternatingGaussian α t < gaussian α t := by
  have hsum := (summable_gaussian hα t).sub (summable_alternatingGaussian hα t)
  have hp : 0 < ∑' z : ℤ, (Real.exp (-α * ((z : ℝ) - t) ^ 2) -
      paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)) := by
    refine hsum.tsum_pos ?_ (1 : ℤ) ?_
    · intro z
      unfold paritySign
      split_ifs <;> nlinarith [Real.exp_pos (-α * ((z : ℝ) - t) ^ 2)]
    · norm_num [paritySign]
      positivity
  rw [(summable_gaussian hα t).tsum_sub (summable_alternatingGaussian hα t)] at hp
  exact sub_pos.mp hp

lemma neg_gaussian_lt_alternatingGaussian {α : ℝ} (hα : 0 < α) (t : ℝ) :
    -gaussian α t < alternatingGaussian α t := by
  have hsum := (summable_gaussian hα t).add (summable_alternatingGaussian hα t)
  have hp : 0 < ∑' z : ℤ, (Real.exp (-α * ((z : ℝ) - t) ^ 2) +
      paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)) := by
    refine hsum.tsum_pos ?_ (0 : ℤ) ?_
    · intro z
      unfold paritySign
      split_ifs <;> nlinarith [Real.exp_pos (-α * ((z : ℝ) - t) ^ 2)]
    · norm_num [paritySign]
      positivity
  rw [(summable_gaussian hα t).tsum_add (summable_alternatingGaussian hα t)] at hp
  change 0 < gaussian α t + alternatingGaussian α t at hp
  linarith

lemma abs_alternatingGaussian_lt {α : ℝ} (hα : 0 < α) (t : ℝ) :
    |alternatingGaussian α t| < gaussian α t :=
  abs_lt.mpr ⟨neg_gaussian_lt_alternatingGaussian hα t, alternatingGaussian_lt hα t⟩

lemma gaussian_even (α t : ℝ) : gaussian α (-t) = gaussian α t := by
  unfold gaussian
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro z
  congr 1
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

lemma gaussian_int_period (α t : ℝ) (k : ℤ) :
    gaussian α (t + k) = gaussian α t := by
  unfold gaussian
  rw [← (Equiv.addRight k).tsum_eq]
  apply tsum_congr
  intro z
  congr 1
  simp only [Equiv.coe_addRight, Int.cast_add]
  ring

lemma gaussian_one_period (α : ℝ) : Function.Periodic (gaussian α) 1 := by
  intro t
  simpa using gaussian_int_period α t 1

lemma alternatingGaussian_even (α t : ℝ) :
    alternatingGaussian α (-t) = alternatingGaussian α t := by
  unfold alternatingGaussian
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro z
  simp only [Equiv.neg_apply, paritySign_neg, Int.cast_neg]
  congr 2
  ring

lemma alternatingGaussian_antiperiod (α t : ℝ) :
    alternatingGaussian α (t + 1) = -alternatingGaussian α t := by
  unfold alternatingGaussian
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq, ← tsum_neg]
  apply tsum_congr
  intro z
  simp only [Equiv.coe_addRight, paritySign_add_one, Int.cast_add, Int.cast_one]
  rw [show (z : ℝ) + 1 - (t + 1) = (z : ℝ) - t by ring]
  ring

lemma alternatingGaussian_half (α : ℝ) : alternatingGaussian α (1 / 2) = 0 := by
  have h := alternatingGaussian_antiperiod α (-(1 / 2))
  rw [alternatingGaussian_even] at h
  norm_num at h
  linarith

end PaperVerification.ColdSpots
