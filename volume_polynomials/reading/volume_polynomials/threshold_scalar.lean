module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Exact scalar optimization in the logarithmic slice

These are identities and inequalities in real numbers used in equations (5.7)
and (5.8) of the supplied paper. Their assumptions are stated explicitly; no
geometric statement about mixed volumes is built into their definitions.
-/

namespace VolumePolynomials

/-- The larger root used in Section 5.4. -/
noncomputable def comparisonRoot (s : ℝ) : ℝ :=
  (1 + s + Real.sqrt (1 + s ^ 2)) / 2

/-- The comparison area deficit. -/
noncomputable def comparisonDeficit (s : ℝ) : ℝ :=
  s / (4 * comparisonRoot s ^ 2)

/-- The scalar lower bound after normalizing the three planar bodies. -/
noncomputable def sliceLowerBound (s δ η : ℝ) : ℝ :=
  (1 + s - Real.sqrt (4 * s * δ * (1 + 2 * η))) / (1 - 2 * δ)

theorem comparisonRoot_quadratic (s : ℝ) :
    comparisonRoot s ^ 2 - (1 + s) * comparisonRoot s + s / 2 = 0 := by
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)
  dsimp [comparisonRoot]
  nlinarith

theorem comparisonRoot_ge_one {s : ℝ} (hs : 0 ≤ s) :
    1 ≤ comparisonRoot s := by
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)
  have hnonneg := Real.sqrt_nonneg (1 + s ^ 2)
  have hge : 1 ≤ Real.sqrt (1 + s ^ 2) := by nlinarith [sq_nonneg s]
  dsimp [comparisonRoot]
  linarith

theorem comparisonRoot_pos {s : ℝ} (hs : 0 ≤ s) :
    0 < comparisonRoot s := lt_of_lt_of_le zero_lt_one (comparisonRoot_ge_one hs)

theorem comparisonRoot_le_one_add {s : ℝ} (hs : 0 ≤ s) :
    comparisonRoot s ≤ 1 + s := by
  have hsqrt : Real.sqrt (1 + s ^ 2) ≤ 1 + s := by
    apply (Real.sqrt_le_left (by linarith)).mpr
    nlinarith
  dsimp [comparisonRoot]
  linarith

theorem comparisonDeficit_pos {s : ℝ} (hs : 0 < s) :
    0 < comparisonDeficit s := by
  dsimp [comparisonDeficit]
  exact div_pos hs (mul_pos (by norm_num) (sq_pos_of_pos (comparisonRoot_pos hs.le)))

theorem comparisonDeficit_le_quarter {s : ℝ} (hs : 0 ≤ s) :
    comparisonDeficit s ≤ s / 4 := by
  have hr := comparisonRoot_ge_one hs
  have hr2 : 1 ≤ comparisonRoot s ^ 2 := by nlinarith
  dsimp [comparisonDeficit]
  apply div_le_div_of_nonneg_left hs (by norm_num)
  nlinarith

theorem comparisonDeficit_ge_sixteenth {s : ℝ} (hs : 0 ≤ s) (hsle : s ≤ 1) :
    s / 16 ≤ comparisonDeficit s := by
  have hrpos := comparisonRoot_pos hs
  have hr := comparisonRoot_le_one_add hs
  have hr2 : comparisonRoot s ^ 2 ≤ 4 := by nlinarith
  dsimp [comparisonDeficit]
  apply div_le_div_of_nonneg_left hs (by positivity)
  nlinarith

/-- The completed square in (5.8). -/
theorem comparison_completed_square {s r δ : ℝ} (hr : r ≠ 0) :
    (s / (2 * r) + 2 * r * δ) ^ 2 - 4 * s * δ =
      4 * r ^ 2 * (δ - s / (4 * r ^ 2)) ^ 2 := by
  field_simp [hr]
  ring

/-- The exact gap expression, prior to any square-root estimate. -/
theorem root_sub_sliceLowerBound {s r δ η : ℝ}
    (hr : r ≠ 0) (hδ : 1 - 2 * δ ≠ 0)
    (hroot : r ^ 2 - (1 + s) * r + s / 2 = 0) :
    r - sliceLowerBound s δ η =
      (Real.sqrt (4 * s * δ * (1 + 2 * η)) -
        (s / (2 * r) + 2 * r * δ)) / (1 - 2 * δ) := by
  have hbase : s / (2 * r) = 1 + s - r := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hr)).mpr
    nlinarith [hroot]
  dsimp [sliceLowerBound]
  apply (eq_div_iff hδ).mpr
  rw [sub_mul, div_mul_cancel₀ _ hδ, hbase]
  ring

/-- With zero interaction deficit, the comparison value is a lower bound. -/
theorem comparison_le_sliceLowerBound_zero {s r δ : ℝ}
    (hs : 0 ≤ s) (hr : 0 < r) (hδ : 0 ≤ δ) (hδlt : δ < 1 / 2)
    (hroot : r ^ 2 - (1 + s) * r + s / 2 = 0) :
    r ≤ sliceLowerBound s δ 0 := by
  have hden : 0 < 1 - 2 * δ := by linarith
  have hw : 0 ≤ s / (2 * r) + 2 * r * δ := by positivity
  have hcomplete := comparison_completed_square (s := s) (δ := δ) hr.ne'
  have hupper : Real.sqrt (4 * s * δ) ≤ s / (2 * r) + 2 * r * δ := by
    apply (Real.sqrt_le_left hw).mpr
    have hnonneg : 0 ≤ 4 * r ^ 2 * (δ - s / (4 * r ^ 2)) ^ 2 := by positivity
    linarith
  have heq := root_sub_sliceLowerBound (s := s) (r := r) (δ := δ) (η := 0)
    hr.ne' hden.ne' hroot
  simp only [mul_zero, add_zero, mul_one] at heq
  have : r - sliceLowerBound s δ 0 ≤ 0 := by
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hupper) hden.le
  linarith

/-- An improving candidate must have positive interaction deficit. -/
theorem positive_interaction_of_improvement {s r δ η : ℝ}
    (hs : 0 ≤ s) (hr : 0 < r) (hδ : 0 ≤ δ) (hδlt : δ < 1 / 2)
    (hroot : r ^ 2 - (1 + s) * r + s / 2 = 0)
    (himprove : sliceLowerBound s δ η < r) : 0 < η := by
  by_contra hn
  have hη : η ≤ 0 := le_of_not_gt hn
  have hden : 0 < 1 - 2 * δ := by linarith
  have hprod : 4 * s * δ * (1 + 2 * η) ≤ 4 * s * δ := by
    have hterm : s * δ * η ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs hδ) hη
    nlinarith
  have hmono := Real.sqrt_le_sqrt hprod
  have hbound : sliceLowerBound s δ 0 ≤ sliceLowerBound s δ η := by
    dsimp [sliceLowerBound]
    simp only [mul_zero, add_zero, mul_one]
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  exact (not_lt_of_ge ((comparison_le_sliceLowerBound_zero hs hr hδ hδlt hroot).trans
    hbound)) himprove

/-- The exact localization inequality in the proof of Theorem 5.5. -/
theorem completed_square_lt_of_improvement {s r δ η : ℝ}
    (hs : 0 ≤ s) (hr : 0 < r) (hδ : 0 ≤ δ) (hδlt : δ < 1 / 2)
    (hroot : r ^ 2 - (1 + s) * r + s / 2 = 0)
    (himprove : sliceLowerBound s δ η < r) :
    (δ - s / (4 * r ^ 2)) ^ 2 < 8 * (s / (4 * r ^ 2)) * δ * η := by
  have hη := positive_interaction_of_improvement hs hr hδ hδlt hroot himprove
  have hden : 0 < 1 - 2 * δ := by linarith
  have heq := root_sub_sliceLowerBound hr.ne' hden.ne' hroot (η := η)
  have hgap : 0 < Real.sqrt (4 * s * δ * (1 + 2 * η)) -
      (s / (2 * r) + 2 * r * δ) := by
    exact (div_pos_iff_of_pos_right hden).mp (by rw [← heq]; linarith)
  have hw : 0 ≤ s / (2 * r) + 2 * r * δ := by positivity
  have hsqrt := Real.sq_sqrt
    (show 0 ≤ 4 * s * δ * (1 + 2 * η) by positivity)
  have hsquare : (s / (2 * r) + 2 * r * δ) ^ 2 <
      4 * s * δ * (1 + 2 * η) := by
    nlinarith [Real.sqrt_nonneg (4 * s * δ * (1 + 2 * η))]
  have hcomplete := comparison_completed_square (s := s) (δ := δ) hr.ne'
  have hscaled : 4 * r ^ 2 * (δ - s / (4 * r ^ 2)) ^ 2 < 8 * s * δ * η := by
    nlinarith [hsquare, hcomplete]
  apply (mul_lt_mul_iff_right₀ (show 0 < 4 * r ^ 2 by positivity)).mp
  calc
    (4 * r ^ 2) * (δ - s / (4 * r ^ 2)) ^ 2
        < 8 * s * δ * η := hscaled
    _ = (4 * r ^ 2) * (8 * (s / (4 * r ^ 2)) * δ * η) := by
      field_simp [hr.ne']

/-- A purely scalar form of the small-deficit localization. -/
theorem deficit_lt_twice_reference {δ η t : ℝ}
    (hδ : 0 < δ) (ht : 0 ≤ t) (htsmall : t < 1 / 32)
    (hη : η ≤ δ) (hsquare : (δ - t) ^ 2 < 8 * t * δ * η) :
    δ < 2 * t := by
  by_contra hn
  have hhalf : δ / 2 ≤ δ - t := by linarith
  have hnonneg : 0 ≤ δ - t := by linarith
  have hlower : δ ^ 2 / 4 ≤ (δ - t) ^ 2 := by nlinarith
  have hprod : δ * η ≤ δ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hη hδ.le]
  have hupper : 8 * t * δ * η ≤ (8 * t) * δ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 8 * t by positivity)
    nlinarith
  have hstrict : (8 * t) * δ ^ 2 < δ ^ 2 / 4 := by
    have := mul_lt_mul_of_pos_right (show 8 * t < 1 / 4 by linarith) (sq_pos_of_pos hδ)
    nlinarith
  linarith

/-- Every scalar candidate improving the reference curve lies in the small
deficit regime needed for the logarithmic energy estimate. -/
theorem improving_deficit_localization {s δ η : ℝ}
    (hs : 0 < s) (hssmall : s < 1 / 8)
    (hδ : 0 ≤ δ) (hδlt : δ < 1 / 2) (hηδ : η ≤ δ)
    (himprove : sliceLowerBound s δ η < comparisonRoot s) :
    0 < δ ∧ 0 < η ∧ δ < 2 * comparisonDeficit s ∧ δ ≤ s / 2 := by
  have hr := comparisonRoot_pos hs.le
  have hroot := comparisonRoot_quadratic s
  have hη := positive_interaction_of_improvement hs.le hr hδ hδlt hroot himprove
  have hsq := completed_square_lt_of_improvement hs.le hr hδ hδlt hroot himprove
  change (δ - comparisonDeficit s) ^ 2 < 8 * comparisonDeficit s * δ * η at hsq
  have hδpos : 0 < δ := lt_of_lt_of_le hη hηδ
  have htpos := comparisonDeficit_pos hs
  have htbound := comparisonDeficit_le_quarter hs.le
  have htsmall : comparisonDeficit s < 1 / 32 := by linarith
  have hlocal := deficit_lt_twice_reference hδpos htpos.le htsmall hηδ hsq
  exact ⟨hδpos, hη, hlocal, by linarith⟩

/-- The square root appearing at the exact comparison deficit. -/
theorem sqrt_at_comparisonDeficit {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt (4 * s * comparisonDeficit s) = s / comparisonRoot s := by
  have hr := comparisonRoot_pos hs
  apply (Real.sqrt_eq_iff_eq_sq (by
    have hδ : 0 ≤ comparisonDeficit s := by
      dsimp [comparisonDeficit]
      positivity
    positivity) (by positivity)).mpr
  dsimp [comparisonDeficit]
  field_simp [hr.ne']

/-- The algebraic reference minimum is attained at exactly the stated deficit. -/
theorem sliceLowerBound_at_comparisonDeficit {s : ℝ}
    (hs : 0 ≤ s) (hslt : s < 1) :
    sliceLowerBound s (comparisonDeficit s) 0 = comparisonRoot s := by
  have hr := comparisonRoot_pos hs
  have hδ := comparisonDeficit_le_quarter hs
  have hden : 1 - 2 * comparisonDeficit s ≠ 0 := by linarith
  have heq := root_sub_sliceLowerBound (s := s) (r := comparisonRoot s)
    (δ := comparisonDeficit s) (η := 0) hr.ne' hden (comparisonRoot_quadratic s)
  simp only [mul_zero, add_zero, mul_one, sqrt_at_comparisonDeficit hs] at heq
  have hz : s / comparisonRoot s -
      (s / (2 * comparisonRoot s) + 2 * comparisonRoot s * comparisonDeficit s) = 0 := by
    dsimp [comparisonDeficit]
    field_simp [hr.ne']
    ring
  rw [hz, zero_div] at heq
  linarith

/-- The exact improvement at the algebraic comparison deficit. -/
theorem root_sub_sliceLowerBound_at_comparisonDeficit {s η : ℝ}
    (hs : 0 ≤ s) (hslt : s < 1) :
    comparisonRoot s - sliceLowerBound s (comparisonDeficit s) η =
      (s / comparisonRoot s) * (Real.sqrt (1 + 2 * η) - 1) /
        (1 - 2 * comparisonDeficit s) := by
  have hr := comparisonRoot_pos hs
  have hδnonneg : 0 ≤ comparisonDeficit s := by
    dsimp [comparisonDeficit]
    positivity
  have hδ := comparisonDeficit_le_quarter hs
  have hden : 1 - 2 * comparisonDeficit s ≠ 0 := by linarith
  rw [root_sub_sliceLowerBound hr.ne' hden (comparisonRoot_quadratic s),
    Real.sqrt_mul (by positivity), sqrt_at_comparisonDeficit hs]
  congr 1
  dsimp [comparisonDeficit]
  field_simp [hr.ne']
  ring

theorem sqrt_one_add_twice_sub_one_upper {η : ℝ} (hη : 0 ≤ η) :
    Real.sqrt (1 + 2 * η) - 1 ≤ η := by
  have hupper : Real.sqrt (1 + 2 * η) ≤ 1 + η := by
    apply (Real.sqrt_le_left (by linarith)).mpr
    nlinarith [sq_nonneg η]
  linarith

theorem sqrt_one_add_twice_sub_one_lower {η : ℝ} (hη : 0 ≤ η) (hηle : η ≤ 1) :
    η / 2 ≤ Real.sqrt (1 + 2 * η) - 1 := by
  have hlower : 1 + η / 2 ≤ Real.sqrt (1 + 2 * η) := by
    apply (Real.le_sqrt (by linarith) (by linarith)).mpr
    nlinarith [mul_nonneg hη (show 0 ≤ 1 - η by linarith)]
  linarith

/-- The improvement at the reference deficit is uniformly comparable to `s*η`.
Both constants are explicit. -/
theorem reference_improvement_bounds {s η : ℝ}
    (hs : 0 ≤ s) (hsle : s ≤ 1 / 2) (hη : 0 ≤ η) (hηle : η ≤ 1) :
    s * η / 4 ≤ comparisonRoot s - sliceLowerBound s (comparisonDeficit s) η ∧
    comparisonRoot s - sliceLowerBound s (comparisonDeficit s) η ≤ 2 * s * η := by
  have hrpos := comparisonRoot_pos hs
  have hrlo := comparisonRoot_ge_one hs
  have hrhi : comparisonRoot s ≤ 2 := by
    have := comparisonRoot_le_one_add hs
    linarith
  have hδnonneg : 0 ≤ comparisonDeficit s := by
    dsimp [comparisonDeficit]
    positivity
  have hδhi := comparisonDeficit_le_quarter hs
  have hdenlo : 1 / 2 ≤ 1 - 2 * comparisonDeficit s := by linarith
  have hdenhi : 1 - 2 * comparisonDeficit s ≤ 1 := by linarith
  have hdenpos : 0 < 1 - 2 * comparisonDeficit s := by linarith
  have hratio_lo : s / 2 ≤ s / comparisonRoot s :=
    div_le_div_of_nonneg_left hs hrpos hrhi
  have hratio_hi : s / comparisonRoot s ≤ s := by
    simpa using div_le_div_of_nonneg_left hs (show (0 : ℝ) < 1 by norm_num) hrlo
  have hglo := sqrt_one_add_twice_sub_one_lower hη hηle
  have hghi := sqrt_one_add_twice_sub_one_upper hη
  have hgpos : 0 ≤ Real.sqrt (1 + 2 * η) - 1 := by linarith
  rw [root_sub_sliceLowerBound_at_comparisonDeficit hs (by linarith)]
  constructor
  · apply (le_div_iff₀ hdenpos).mpr
    have hprod := mul_le_mul hratio_lo hglo (show 0 ≤ η / 2 by positivity)
      (show 0 ≤ s / comparisonRoot s by positivity)
    have hscale := mul_le_mul_of_nonneg_left hdenhi (show 0 ≤ s * η / 4 by positivity)
    nlinarith
  · apply (div_le_iff₀ hdenpos).mpr
    have hprod := mul_le_mul hratio_hi hghi hgpos hs
    have hscale := mul_le_mul_of_nonneg_left hdenlo (show 0 ≤ 2 * s * η by positivity)
    nlinarith

/-- After localization, every improvement is bounded above by `4*s*η`. -/
theorem improvement_le_four_mul {s δ η : ℝ}
    (hs : 0 < s) (hssmall : s < 1 / 8)
    (hδ : 0 ≤ δ) (hδlt : δ < 1 / 2) (hηδ : η ≤ δ)
    (himprove : sliceLowerBound s δ η < comparisonRoot s) :
    comparisonRoot s - sliceLowerBound s δ η ≤ 4 * s * η := by
  obtain ⟨hδpos, hηpos, hlocal, hδbound⟩ :=
    improving_deficit_localization hs hssmall hδ hδlt hηδ himprove
  have hr := comparisonRoot_pos hs.le
  have hden : 0 < 1 - 2 * δ := by linarith
  have hdenhalf : 1 / 2 ≤ 1 - 2 * δ := by linarith
  have hvpos : 0 ≤ 4 * s * δ := by positivity
  have hrootupper : Real.sqrt (4 * s * δ) ≤ 2 * s := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδbound hs.le]
  have hw : 0 ≤ s / (2 * comparisonRoot s) + 2 * comparisonRoot s * δ := by positivity
  have hcomplete := comparison_completed_square (s := s) (δ := δ) hr.ne'
  have hrootle : Real.sqrt (4 * s * δ) ≤
      s / (2 * comparisonRoot s) + 2 * comparisonRoot s * δ := by
    apply (Real.sqrt_le_left hw).mpr
    have hnonneg : 0 ≤ 4 * comparisonRoot s ^ 2 *
        (δ - s / (4 * comparisonRoot s ^ 2)) ^ 2 := by positivity
    linarith
  rw [root_sub_sliceLowerBound hr.ne' hden.ne' (comparisonRoot_quadratic s),
    Real.sqrt_mul hvpos]
  apply (div_le_iff₀ hden).mpr
  have hnum : Real.sqrt (4 * s * δ) * Real.sqrt (1 + 2 * η) -
      (s / (2 * comparisonRoot s) + 2 * comparisonRoot s * δ) ≤ 2 * s * η := by
    calc
      _ ≤ Real.sqrt (4 * s * δ) * (Real.sqrt (1 + 2 * η) - 1) := by nlinarith
      _ ≤ Real.sqrt (4 * s * δ) * η :=
        mul_le_mul_of_nonneg_left (sqrt_one_add_twice_sub_one_upper hηpos.le)
          (Real.sqrt_nonneg _)
      _ ≤ 2 * s * η := mul_le_mul_of_nonneg_right hrootupper hηpos.le
  have hscale := mul_le_mul_of_nonneg_left hdenhalf (show 0 ≤ 4 * s * η by positivity)
  nlinarith

end VolumePolynomials
