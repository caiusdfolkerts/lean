module
public import PaperVerification.E7Projection
public import PaperVerification.ThetaRelations
@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

open scoped BigOperators

def e8Axis : Fin 8 → ℝ := intVec (fun i ↦ if i = 0 then 1 else 0)

def e7Witness : zeroSumSpace := project8 e8Axis

lemma e8Axis_sum : (∑ i, e8Axis i) = 1 := by simp [e8Axis, intVec]

theorem e7Slice_witness : e7Slice e7Witness = e8Axis := by
  ext i
  simp only [e7Slice, e7Witness, project8_apply, e8Axis_sum]
  ring

theorem e8Axis_folded_hole : E8FoldedHole e8Axis := by
  apply Or.inl
  constructor
  · intro i
    simp only [foldedRadius, roundedInt, e8Axis, intVec, round_intCast, sub_self, abs_zero]
  · change ¬Even (∑ i, round ((if i = 0 then 1 else 0 : ℤ) : ℝ))
    simp only [round_intCast]
    have hs : (∑ i : Fin 8, (if i = 0 then 1 else 0 : ℤ)) = 1 := by simp
    rw [hs]
    decide

theorem e8Axis_depth : squaredDepth (dPlusSet 8) e8Axis = 1 :=
  (squaredDepth_E8_eq_one_iff e8Axis).mpr e8Axis_folded_hole

theorem e7Witness_depth : e7SquaredDepth e7Witness = 7 / 8 := by
  have h := e8_slice_depth_factorization e7Witness
  rw [e7Slice_witness, e8Axis_depth] at h
  linarith

/-- The squared covering radius is exactly 7/8, in the true hyperplane ambient space. -/
theorem e7_covering_radius :
    (∀ x, e7SquaredDepth x ≤ 7 / 8) ∧ ∃ x, e7SquaredDepth x = 7 / 8 :=
  ⟨e7SquaredDepth_le_seven_eighths, e7Witness, e7Witness_depth⟩

theorem isE7DeepHole_iff_depth (x : zeroSumSpace) :
    IsE7DeepHole x ↔ e7SquaredDepth x = 7 / 8 := by
  constructor
  · intro hx
    apply le_antisymm (e7SquaredDepth_le_seven_eighths x)
    simpa only [e7Witness_depth] using hx e7Witness
  · intro hx y
    rw [hx]
    exact e7SquaredDepth_le_seven_eighths y

theorem isDeepHole_slice_iff (x : zeroSumSpace) :
    IsDeepHole (dPlusSet 8) (e7Slice x) ↔ IsE7DeepHole x := by
  rw [isDeepHole_dPlus_iff_depth (by decide : 8 ≤ 8) (by decide : Even 8),
    isE7DeepHole_iff_depth, e8_slice_depth_factorization]
  norm_num
  constructor <;> intro h <;> linarith

theorem dPlusGaussian_axis {α : ℝ} (hα : 0 < α) :
    dPlusGaussian α e8Axis = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 := by
  have hA1 : gaussian α 1 = gaussian α 0 := by simpa using gaussian_one_period α 0
  have hB1 : alternatingGaussian α 1 = -alternatingGaussian α 0 := by
    simpa using alternatingGaussian_antiperiod α 0
  have hdiag : thetaDiagonal α 0 = (gaussian α 0 * gaussian α (1 / 2)) ^ 4 := by
    apply (thetaDiagonal_min_iff hα 0).mpr
    exact ⟨0, by norm_num⟩
  rw [← hdiag, dPlusGaussian_eq_product hα]
  norm_num [e8Axis, intVec, Fin.prod_univ_succ, hA1, hB1, thetaDiagonal,
    gaussian_even, alternatingGaussian_even, alternatingGaussian_half]
  ring

theorem e7Gaussian_witness {α : ℝ} (hα : 0 < α) :
    e7Gaussian α e7Witness =
      (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) := by
  have h := e8_slice_gaussian_factorization hα e7Witness
  rw [e7Slice_witness, setGaussian_dPlus_eq (by decide : 0 < 8) hα,
    dPlusGaussian_axis hα] at h
  apply (eq_div_iff (gaussian_pos (show 0 < 2 * α by positivity) _).ne').mpr
  linarith

/-- Projection transfer with its only substantive input explicitly displayed:
the full E8 cold-spot/deep-hole equivalence at this parameter. -/
theorem e7_coldSpot_iff_deepHole_of_E8 {α : ℝ} (hα : 0 < α)
    (hE8 : ∀ v : Fin 8 → ℝ,
      IsColdSpot (dPlusSet 8) α v ↔ IsDeepHole (dPlusSet 8) v)
    (x : zeroSumSpace) : IsE7ColdSpot α x ↔ IsE7DeepHole x := by
  have hc : 0 < gaussian (2 * α) (1 / 4) := gaussian_pos (by positivity) _
  have haxis : IsColdSpot (dPlusSet 8) α e8Axis :=
    (hE8 e8Axis).mpr ((isDeepHole_E8_iff e8Axis).mpr e8Axis_folded_hole)
  constructor
  · intro hx
    apply (isDeepHole_slice_iff x).mp
    apply (hE8 (e7Slice x)).mp
    intro v
    have hle := mul_le_mul_of_nonneg_left (hx e7Witness) hc.le
    rw [← e8_slice_gaussian_factorization hα x,
      ← e8_slice_gaussian_factorization hα e7Witness, e7Slice_witness] at hle
    exact hle.trans (haxis v)
  · intro hx y
    have hglobal := (hE8 (e7Slice x)).mpr ((isDeepHole_slice_iff x).mpr hx)
    have h := hglobal (e7Slice y)
    rw [e8_slice_gaussian_factorization hα x, e8_slice_gaussian_factorization hα y] at h
    exact (mul_le_mul_iff_of_pos_left hc).mp h

theorem e7Gaussian_minimum_of_E8 {α : ℝ} (hα : 0 < α)
    (hE8 : ∀ v : Fin 8 → ℝ,
      IsColdSpot (dPlusSet 8) α v ↔ IsDeepHole (dPlusSet 8) v) :
    (∀ x, (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) ≤
      e7Gaussian α x) ∧
    (∀ x, e7Gaussian α x =
      (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) ↔
        IsE7DeepHole x) := by
  have hwdeep := (isE7DeepHole_iff_depth e7Witness).mpr e7Witness_depth
  have hwcold := (e7_coldSpot_iff_deepHole_of_E8 hα hE8 e7Witness).mpr hwdeep
  have hbound : ∀ x, (gaussian α 0 * gaussian α (1 / 2)) ^ 4 /
      gaussian (2 * α) (1 / 4) ≤ e7Gaussian α x := by
    intro x
    simpa only [e7Gaussian_witness hα] using hwcold x
  refine ⟨hbound, ?_⟩
  intro x
  constructor
  · intro heq
    apply (e7_coldSpot_iff_deepHole_of_E8 hα hE8 x).mp
    intro y
    rw [heq]
    exact hbound y
  · intro hx
    have hcold := (e7_coldSpot_iff_deepHole_of_E8 hα hE8 x).mpr hx
    apply le_antisymm _ (hbound x)
    simpa only [e7Gaussian_witness hα] using hcold e7Witness

end PaperVerification.ColdSpots
