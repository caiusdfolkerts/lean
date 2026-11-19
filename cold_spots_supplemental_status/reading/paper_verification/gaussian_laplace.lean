module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The low-temperature limit of a discrete Gaussian sum

For any nonempty family of nonnegative energies, summability at a single
positive parameter suffices for the normalized negative logarithm of the
partition sum to converge to the infimum of the energies. The infimum need
not be attained and the index type is not assumed finite or countable.

This supplies the general limiting principle used in Sections 6 and 8 of
the cold-spots manuscript. The principal lattice proofs do not depend on
this additional module.
-/

noncomputable section

namespace PaperVerification.ColdSpots

open Filter Set
open scoped BigOperators Topology

variable {ι κ : Type*}

def discreteGaussianSum (d : ι → ℝ) (α : ℝ) : ℝ :=
  ∑' i, Real.exp (-α * d i)

def discreteGroundEnergy (d : ι → ℝ) : ℝ := sInf (Set.range d)

lemma discreteGroundEnergy_le (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (i : ι) :
    discreteGroundEnergy d ≤ d i :=
  csInf_le ⟨0, by rintro x ⟨j,rfl⟩; exact hd j⟩ (Set.mem_range_self i)

lemma discreteGroundEnergy_nonneg [Nonempty ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) : 0 ≤ discreteGroundEnergy d := by
  apply le_csInf (Set.range_nonempty _)
  rintro x ⟨i,rfl⟩
  exact hd i

lemma summable_discreteGaussian_of_ge (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    {α₀ α : ℝ} (hs : Summable (fun i => Real.exp (-α₀ * d i)))
    (hα : α₀ ≤ α) : Summable (fun i => Real.exp (-α * d i)) := by
  apply hs.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
  intro i
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right hα (hd i)]

lemma discreteGaussianSum_pos [Nonempty ι] (d : ι → ℝ) {α : ℝ}
    (hs : Summable (fun i => Real.exp (-α * d i))) :
    0 < discreteGaussianSum d α := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact hs.tsum_pos (fun _ => (Real.exp_pos _).le) i (Real.exp_pos _)

lemma discreteGaussianTerm_le_sum (d : ι → ℝ) {α : ℝ}
    (hs : Summable (fun i => Real.exp (-α * d i))) (i : ι) :
    Real.exp (-α * d i) ≤ discreteGaussianSum d α :=
  hs.le_tsum i (fun _ _ => (Real.exp_pos _).le)

/-- Uniform exponential bound using only one convergent Gaussian sum. -/
theorem discreteGaussianSum_upper (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    {α₀ α : ℝ} (hs : Summable (fun i => Real.exp (-α₀ * d i)))
    (hα : α₀ ≤ α) :
    discreteGaussianSum d α ≤
      Real.exp (-(α - α₀) * discreteGroundEnergy d) * discreteGaussianSum d α₀ := by
  have hsα := summable_discreteGaussian_of_ge d hd hs hα
  have hterm (i : ι) : Real.exp (-α * d i) ≤
      Real.exp (-(α - α₀) * discreteGroundEnergy d) * Real.exp (-α₀ * d i) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_nonneg (sub_nonneg.mpr hα)
      (sub_nonneg.mpr (discreteGroundEnergy_le d hd i))
    nlinarith only [h]
  have h := hsα.tsum_le_tsum hterm
    (hs.mul_left (Real.exp (-(α - α₀) * discreteGroundEnergy d)))
  simpa only [tsum_mul_left, discreteGaussianSum] using h

lemma discreteGaussian_log_lower [Nonempty ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) {α₀ α : ℝ}
    (hs : Summable (fun i => Real.exp (-α₀ * d i))) (hα : α₀ ≤ α)
    (hpos : 0 < α) :
    discreteGroundEnergy d -
        (α₀ * discreteGroundEnergy d + Real.log (discreteGaussianSum d α₀)) / α ≤
      -Real.log (discreteGaussianSum d α) / α := by
  have hsα := summable_discreteGaussian_of_ge d hd hs hα
  have hp := discreteGaussianSum_pos d hsα
  have hp₀ := discreteGaussianSum_pos d hs
  have hlog := Real.log_le_log hp (discreteGaussianSum_upper d hd hs hα)
  rw [Real.log_mul (Real.exp_pos _).ne' hp₀.ne', Real.log_exp] at hlog
  have hmul :
      (discreteGroundEnergy d -
        (α₀ * discreteGroundEnergy d + Real.log (discreteGaussianSum d α₀)) / α) * α =
      (α - α₀) * discreteGroundEnergy d - Real.log (discreteGaussianSum d α₀) := by
    field_simp [hpos.ne'] <;> ring
  apply (le_div_iff₀ hpos).mpr
  rw [hmul]
  linarith

lemma discreteGaussian_log_upper (d : ι → ℝ) {α : ℝ}
    (hs : Summable (fun i => Real.exp (-α * d i))) (hα : 0 < α) (i : ι) :
    -Real.log (discreteGaussianSum d α) / α ≤ d i := by
  have hlog := Real.log_le_log (Real.exp_pos (-α * d i))
    (discreteGaussianTerm_le_sum d hs i)
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ hα).mpr
  linarith

lemma discreteGaussian_log_le_infimum [Nonempty ι] (d : ι → ℝ) {α : ℝ}
    (hs : Summable (fun i => Real.exp (-α * d i))) (hα : 0 < α) :
    -Real.log (discreteGaussianSum d α) / α ≤ discreteGroundEnergy d := by
  apply le_csInf (Set.range_nonempty d)
  rintro x ⟨i,rfl⟩
  exact discreteGaussian_log_upper d hs hα i

/-- The quantitative two-sided estimate behind the low-temperature limit. -/
theorem discreteGaussian_log_sandwich [Nonempty ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) {α₀ α : ℝ}
    (hs : Summable (fun i => Real.exp (-α₀ * d i))) (hα : α₀ ≤ α)
    (hpos : 0 < α) :
    (discreteGroundEnergy d -
        (α₀ * discreteGroundEnergy d + Real.log (discreteGaussianSum d α₀)) / α ≤
      -Real.log (discreteGaussianSum d α) / α) ∧
    (-Real.log (discreteGaussianSum d α) / α ≤ discreteGroundEnergy d) :=
  ⟨discreteGaussian_log_lower d hd hs hα hpos,
    discreteGaussian_log_le_infimum d (summable_discreteGaussian_of_ge d hd hs hα) hpos⟩

/-- The discrete Gaussian Laplace principle. There is no nearest-point
attainment hypothesis and no finiteness restriction on the index family. -/
theorem discreteGaussian_laplace_limit [Nonempty ι] (d : ι → ℝ)
    (hd : ∀ i, 0 ≤ d i) {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hs : Summable (fun i => Real.exp (-α₀ * d i))) :
    Tendsto (fun α : ℝ => -Real.log (discreteGaussianSum d α) / α)
      atTop (𝓝 (discreteGroundEnergy d)) := by
  have hlower : Tendsto (fun α : ℝ => discreteGroundEnergy d -
      (α₀ * discreteGroundEnergy d + Real.log (discreteGaussianSum d α₀)) / α)
      atTop (𝓝 (discreteGroundEnergy d)) := by
    have hzero : Tendsto (fun α : ℝ =>
        (α₀ * discreteGroundEnergy d + Real.log (discreteGaussianSum d α₀)) / α)
        atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop tendsto_id
    have hconst : Tendsto (fun _ : ℝ => discreteGroundEnergy d) atTop
        (𝓝 (discreteGroundEnergy d)) := tendsto_const_nhds
    simpa only [sub_zero] using hconst.sub hzero
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [(tendsto_order.mp hlower).1 b hb, eventually_ge_atTop α₀]
      with α hlt hα
    exact hlt.trans_le (discreteGaussian_log_lower d hd hs hα (hα₀.trans_le hα))
  · intro b hb
    filter_upwards [eventually_ge_atTop α₀] with α hα
    exact (discreteGaussian_log_le_infimum d
      (summable_discreteGaussian_of_ge d hd hs hα) (hα₀.trans_le hα)).trans_lt hb

/-- Eventual equality of Gaussian sums determines the infimum of the
underlying squared-distance families. -/
theorem gaussian_infimum_eq_of_eventually_equal_sums [Nonempty ι] [Nonempty κ]
    (d : ι → ℝ) (e : κ → ℝ) (hd : ∀ i, 0 ≤ d i) (he : ∀ j, 0 ≤ e j)
    {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hsd : Summable (fun i => Real.exp (-α₀ * d i)))
    (hse : Summable (fun j => Real.exp (-α₀ * e j)))
    (hEq : (fun α : ℝ => ∑' i, Real.exp (-α * d i)) =ᶠ[atTop]
      fun α => ∑' j, Real.exp (-α * e j)) :
    sInf (Set.range d) = sInf (Set.range e) := by
  have hdlim := discreteGaussian_laplace_limit d hd hα₀ hsd
  have helim := discreteGaussian_laplace_limit e he hα₀ hse
  have hlog : (fun α : ℝ => -Real.log (discreteGaussianSum d α) / α) =ᶠ[atTop]
      fun α => -Real.log (discreteGaussianSum e α) / α := by
    filter_upwards [hEq] with α hα
    simp only [discreteGaussianSum, hα]
  exact tendsto_nhds_unique (hdlim.congr' hlog) helim

/-- The exact all-positive-parameter form used in the projection transfer
argument of Section 6. -/
theorem gaussian_infimum_eq_of_equal_sums [Nonempty ι] [Nonempty κ]
    (d : ι → ℝ) (e : κ → ℝ) (hd : ∀ i, 0 ≤ d i) (he : ∀ j, 0 ≤ e j)
    {α₀ : ℝ} (hα₀ : 0 < α₀)
    (hsd : Summable (fun i => Real.exp (-α₀ * d i)))
    (hse : Summable (fun j => Real.exp (-α₀ * e j)))
    (hEq : ∀ α : ℝ, 0 < α → (∑' i, Real.exp (-α * d i)) =
      ∑' j, Real.exp (-α * e j)) :
    sInf (Set.range d) = sInf (Set.range e) := by
  apply gaussian_infimum_eq_of_eventually_equal_sums d e hd he hα₀ hsd hse
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
  exact hEq α hα

end PaperVerification.ColdSpots

#print axioms PaperVerification.ColdSpots.discreteGaussian_laplace_limit
#print axioms PaperVerification.ColdSpots.gaussian_infimum_eq_of_equal_sums
