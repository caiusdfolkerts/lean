module
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
/-! # Boundary first variation

The algebra is stated with the one-sided condition on the scale derivative.
This is stronger than the stationary identity in Lemma 5.1 and permits compact
minimization over a bounded interval of scales, eliminating the asymptotic
compactness argument of Lemma 5.2.
-/

noncomputable section

namespace PaperVerification.Hyperbolic

open Real Set

def boundaryA (u z t : ℝ) : ℝ := (1 - u) ^ (1 - t) * (1 - u * z) ^ t

def boundaryB (u z t : ℝ) : ℝ := u * z ^ t

def boundaryK (u z : ℝ) : ℝ := u * z * (1 - z) / (1 - u * z)

def boundaryRatio (u z t : ℝ) : ℝ :=
  (1 + boundaryA u z t ^ 2 - boundaryB u z t ^ 2) /
    (2 * boundaryA u z t * (1 - boundaryK u z ^ 2) ^ (t / 2))

def boundaryUVariation (u z t X Y η : ℝ) : ℝ :=
  X * ((t - 1) / (1 - u) - t * z / (1 - u * z)) - Y / u +
    t * η / (u * (1 - u * z))

def boundaryZVariation (u z t X Y η : ℝ) : ℝ :=
  -X * t * u / (1 - u * z) - Y * t / z +
    t * η * (1 - 2 * z + u * z ^ 2) / (z * (1 - z) * (1 - u * z))

def boundaryQNormalized (u z t X Y : ℝ) : ℝ :=
  t * ((X + 1) * (1 - z) / (1 - u * z) - (1 - X + Y) * z +
    Y / (u * z) - (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2))

def boundaryRNormalized (u z t X Y : ℝ) : ℝ :=
  (1 - X + Y) * ((2 - t) + t * z) - Y * ((2 - t) / u + t / (u * z)) -
    (2 - t / 2) + t / 2 * (1 - 2 * z + u * z ^ 2) / (1 - 2 * u * z + u * z ^ 2)

theorem boundary_cd_pos {u z : ℝ} (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) :
    0 < 1 - 2 * u * z + u * z ^ 2 ∧ 0 < 1 - u * z ^ 2 := by
  have hc : 1 - 2 * u * z + u * z ^ 2 = (1 - u) + u * (1 - z) ^ 2 := by ring
  have hz2 : z ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one z).mpr (by rw [abs_of_pos hz.1]; exact hz.2)
  constructor
  · rw [hc]
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr hu.2) (mul_nonneg hu.1.le (sq_nonneg _))
  · have h := mul_lt_mul_of_pos_left hz2 hu.1
    nlinarith only [h, hu.2]

/-- Elimination directly in the original `R,q` coordinates.  This identity
avoids any need to assume a reparametrization formula for the boundary ratio. -/
theorem boundary_direct_identity (u z t X Y : ℝ)
    (hu : u ≠ 0) (hz : z ≠ 0) (hb : 1 - u * z ≠ 0)
    (hc : 1 - 2 * u * z + u * z ^ 2 ≠ 0) (hd : 1 - u * z ^ 2 ≠ 0)
    (ht : t - 1 ≠ 0) :
    X + (1 - u) / u * Y =
      boundaryRNormalized u z t X Y / (2 * (t - 1)) +
        (1 + z) * (1 - u * z) / (2 * (t - 1) * (1 - u * z ^ 2)) *
          boundaryQNormalized u z t X Y -
        t * u * z ^ 3 * (1 - z) * (1 - u) /
          ((t - 1) * (1 - 2 * u * z + u * z ^ 2) * (1 - u * z ^ 2)) := by
  unfold boundaryRNormalized boundaryQNormalized
  have hc' : 1 - u * z * 2 + u * z ^ 2 ≠ 0 := by
    convert hc using 1 <;> ring
  field_simp [hu, hz, hb, hc, hc', hd, ht] <;>
    ring_nf <;> field_simp [hc'] <;> ring

theorem boundary_direct_inward_negative {u z t X Y : ℝ}
    (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) (ht : 1 < t)
    (hR : boundaryRNormalized u z t X Y ≤ 0)
    (hQ : boundaryQNormalized u z t X Y = 0) :
    X + (1 - u) / u * Y < 0 := by
  have hb : 0 < 1 - u * z := by
    have h := mul_lt_mul_of_pos_left hz.2 hu.1
    nlinarith only [h, hu.2]
  obtain ⟨hc, hd⟩ := boundary_cd_pos hu hz
  rw [boundary_direct_identity u z t X Y hu.1.ne' hz.1.ne' hb.ne' hc.ne' hd.ne'
    (sub_pos.mpr ht).ne', hQ, mul_zero, add_zero]
  have hfirst : boundaryRNormalized u z t X Y / (2 * (t - 1)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hR (mul_pos (by norm_num) (sub_pos.mpr ht)).le
  have hlast : 0 < t * u * z ^ 3 * (1 - z) * (1 - u) /
      ((t - 1) * (1 - 2 * u * z + u * z ^ 2) * (1 - u * z ^ 2)) :=
    div_pos (mul_pos (mul_pos (mul_pos (mul_pos (zero_lt_one.trans ht) hu.1)
      (pow_pos hz.1 3)) (sub_pos.mpr hz.2)) (sub_pos.mpr hu.2))
      (mul_pos (mul_pos (sub_pos.mpr ht) hc) hd)
  linarith

theorem boundary_parameters_pos {u z : ℝ} (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) :
    0 < 1 - u ∧ 0 < 1 - u * z ∧ 0 < boundaryK u z ∧ boundaryK u z < 1 := by
  have huz : u * z < 1 := (mul_lt_mul_of_pos_left hz.2 hu.1).trans (by simpa using hu.2)
  have ha : 0 < 1 - u := sub_pos.mpr hu.2
  have hb : 0 < 1 - u * z := sub_pos.mpr huz
  refine ⟨ha, hb, div_pos (mul_pos (mul_pos hu.1 hz.1) (sub_pos.mpr hz.2)) hb, ?_⟩
  apply (div_lt_iff₀ hb).mpr
  have hsq := mul_nonneg hu.1.le (sq_nonneg (1 - z))
  nlinarith only [ha, hsq]

theorem boundaryA_pos {u z t : ℝ} (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) :
    0 < boundaryA u z t := by
  obtain ⟨ha, hb, _⟩ := boundary_parameters_pos hu hz
  exact mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)

theorem boundaryB_mem {u z t : ℝ} (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) (ht : 0 < t) :
    boundaryB u z t ∈ Ioo 0 1 := by
  have hzt : z ^ t < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hz.1.le hz.2 ht
  exact ⟨mul_pos hu.1 (Real.rpow_pos_of_pos hz.1 _),
    (mul_lt_mul_of_pos_left hzt hu.1).trans (by simpa only [mul_one] using hu.2)⟩

theorem boundaryRatio_pos {u z t : ℝ} (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) (ht : 0 < t) :
    0 < boundaryRatio u z t := by
  have hA := boundaryA_pos (t := t) hu hz
  have hB := boundaryB_mem hu hz ht
  obtain ⟨_, _, hk0, hk1⟩ := boundary_parameters_pos hu hz
  have hB2 : boundaryB u z t ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one _).mpr (by rw [abs_of_pos hB.1]; exact hB.2)
  have hk2 : boundaryK u z ^ 2 < 1 :=
    (sq_lt_one_iff_abs_lt_one _).mpr (by rw [abs_of_pos hk0]; exact hk1)
  exact div_pos (by nlinarith only [hB2, sq_nonneg (boundaryA u z t)])
    (mul_pos (mul_pos (by norm_num) hA) (Real.rpow_pos_of_pos (sub_pos.mpr hk2) _))

/-- Exact elimination identity, retaining both derivative residuals. -/
theorem boundary_inward_identity (u z t X Y η : ℝ)
    (hu : u ≠ 0) (ha : 1 - u ≠ 0) (hb : 1 - u * z ≠ 0)
    (hz : z ≠ 0) (hz1 : 1 - z ≠ 0) (ht : t - 1 ≠ 0) :
    X + (1 - u) / u * Y =
      (1 - u) / (t - 1) * boundaryUVariation u z t X Y η -
        (1 - u) * z / (u * (t - 1)) * boundaryZVariation u z t X Y η -
          t * η * (1 - u) * z / (u * (t - 1) * (1 - z)) := by
  unfold boundaryUVariation boundaryZVariation
  field_simp [hu, ha, hb, hz, hz1, ht] <;> ring

/-- A minimum at the upper allowed scale still has a strictly decreasing
inward direction; equality of the scale derivative is not needed. -/
theorem boundary_inward_negative {u z t X Y η : ℝ}
    (hu : u ∈ Ioo 0 1) (hz : z ∈ Ioo 0 1) (ht : 1 < t) (hη : 0 < η)
    (hU : boundaryUVariation u z t X Y η ≤ 0)
    (hZ : boundaryZVariation u z t X Y η = 0) : X + (1 - u) / u * Y < 0 := by
  obtain ⟨ha, hb, _⟩ := boundary_parameters_pos hu hz
  rw [boundary_inward_identity u z t X Y η hu.1.ne' ha.ne' hb.ne' hz.1.ne'
    (sub_pos.mpr hz.2).ne' (sub_pos.mpr ht).ne', hZ, mul_zero, sub_zero]
  have hfirst : (1 - u) / (t - 1) * boundaryUVariation u z t X Y η ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_pos ha (sub_pos.mpr ht)).le hU
  have hlast : 0 < t * η * (1 - u) * z / (u * (t - 1) * (1 - z)) :=
    div_pos (mul_pos (mul_pos (mul_pos (zero_lt_one.trans ht) hη) ha) hz.1)
      (mul_pos (mul_pos hu.1 (sub_pos.mpr ht)) (sub_pos.mpr hz.2))
  linarith

end PaperVerification.Hyperbolic

#print axioms PaperVerification.Hyperbolic.boundary_inward_identity
#print axioms PaperVerification.Hyperbolic.boundary_inward_negative
