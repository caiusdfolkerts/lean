module

public import VolumePolynomials.HolonomyDeterminants
public import VolumePolynomials.InfiniteZonotopeArea
public import VolumePolynomials.AreaTranscendence

@[expose] public section
noncomputable section

namespace VolumePolynomials.Holonomy

open scoped Topology
open Set MeasureTheory

theorem weighted_determinant_series (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    (∑' j, ∑ i ∈ Finset.range j,
      |PlanarExtrusion.determinant (weightedOrbit lam i) (weightedOrbit lam j)|) =
      realAreaSeries angle lam := by
  first
  | let c : ℕ → ℝ := fun n =>
      |Real.sin (((n + 1 : ℕ) : ℝ) * angle)| * lam ^ (n + 1) / Real.sin angle
    have hgeom : Summable (fun n : ℕ => lam ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hlam₀ hlam₁)
    have hc : Summable c := by
      have hsin : 0 < Real.sin angle := sin_angle_pos
      apply (hgeom.div_const (Real.sin angle)).of_norm_bounded
      intro n
      have hnonneg : 0 ≤ c n := by dsimp [c]; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_left (pow_nonneg hlam₀ (n + 1)) (Real.abs_sin_le_one _))
        sin_angle_pos.le
    have hlamsq : lam ^ 2 < 1 := (sq_lt_one_iff₀ hlam₀).mpr hlam₁
    have ha : Summable (fun n : ℕ => (lam ^ 2) ^ n) :=
      summable_geometric_of_lt_one (sq_nonneg lam) hlamsq
    have hrow (n : ℕ) :
        (∑ i ∈ Finset.range (n + 1),
          |PlanarExtrusion.determinant (weightedOrbit lam i) (weightedOrbit lam (n + 1))|) =
        ∑ i ∈ Finset.range (n + 1), (lam ^ 2) ^ i * c (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hind : n + 1 = i + ((n - i) + 1) := by
        have h := Finset.mem_range.mp hi
        omega
      change |det (weightedOrbit lam i) (weightedOrbit lam (n + 1))| = _
      rw [hind]
      exact abs_det_weighted_gap lam hlam₀ i (n - i)
    have hrows := determinant_rows_summable (weightedOrbit lam) (weightedOrbit_summable lam hlam₀ hlam₁)
    rw [hrows.tsum_eq_zero_add]
    simp only [Finset.range_zero, Finset.sum_empty, zero_add]
    simp_rw [hrow]
    rw [← tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm ha.norm hc.norm]
    have hnormsq : ‖lam ^ 2‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg lam)]
      using hlamsq
    rw [tsum_geometric_of_norm_lt_one hnormsq]
    change (1 - lam ^ 2)⁻¹ *
      (∑' n : ℕ, |Real.sin (((n + 1 : ℕ) : ℝ) * angle)| * lam ^ (n + 1) /
        Real.sin angle) = realAreaSeries angle lam
    rw [tsum_div_const]
    simp only [realAreaSeries, div_eq_mul_inv, mul_inv_rev]
    ring

/-- Formula (7.11) is the actual Lebesgue area of the uniquely forced compact convex body. -/
theorem forcedBody_area (lam : ℝ) (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) :
    volume.real (forcedBody lam hlam₀ hlam₁ : Set (ℝ × ℝ)) = realAreaSeries angle lam := by
  first
  | rw [forcedBody, area_infinite_segment_series, weighted_determinant_series lam hlam₀ hlam₁]

theorem forcedBody_area_positive (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1) :
    0 < volume.real (forcedBody lam hlam₀.le hlam₁ : Set (ℝ × ℝ)) := by
  first
  | rw [forcedBody, area_infinite_segment_series]
    have hs := determinant_rows_summable (weightedOrbit lam)
      (weightedOrbit_summable lam hlam₀.le hlam₁)
    have hle := hs.le_tsum 1 (fun j _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
    have hone : (∑ i ∈ Finset.range 1,
        |PlanarExtrusion.determinant (weightedOrbit lam i) (weightedOrbit lam 1)|) = lam := by
      simp [weightedOrbit, orbit, returnMap, PlanarExtrusion.determinant, abs_of_pos hlam₀]
    rw [hone] at hle
    exact hlam₀.trans_le hle

end VolumePolynomials.Holonomy
