import cubical_indecomposability.rigidity.constraints

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

/-! Each coordinate identity below is an exact linear consequence
of edge equations and identities in earlier modules. No rank result or
external solver is assumed. -/

/-- Coordinate 3.1, recovered from interface cube. -/
theorem value_013 (h : Assignment) (H : Constraints h) :
    h 3 1 = h 1 1 := by
  have r0 := H 5 1
  change ((1 : ℤ) : ℝ) * (h 3 1 - h 1 1) - ((0 : ℤ) : ℝ) * (h 3 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 3.2, recovered from interface cube. -/
theorem value_014 (h : Assignment) (H : Constraints h) :
    h 3 2 = h 1 2 := by
  have r0 := H 5 2
  change ((1 : ℤ) : ℝ) * (h 3 2 - h 1 2) - ((0 : ℤ) : ℝ) * (h 3 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 3.3, recovered from interface cube. -/
theorem value_015 (h : Assignment) (H : Constraints h) :
    h 3 3 = h 1 3 := by
  have r0 := H 5 3
  change ((1 : ℤ) : ℝ) * (h 3 3 - h 1 3) - ((0 : ℤ) : ℝ) * (h 3 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 5.0, recovered from interface cube. -/
theorem value_020 (h : Assignment) (H : Constraints h) :
    h 5 0 = h 1 0 := by
  have r0 := H 6 0
  change ((1 : ℤ) : ℝ) * (h 5 0 - h 1 0) - ((0 : ℤ) : ℝ) * (h 5 1 - h 1 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 5.2, recovered from interface cube. -/
theorem value_022 (h : Assignment) (H : Constraints h) :
    h 5 2 = h 1 2 := by
  have r0 := H 6 2
  change ((1 : ℤ) : ℝ) * (h 5 2 - h 1 2) - ((0 : ℤ) : ℝ) * (h 5 1 - h 1 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 5.3, recovered from interface cube. -/
theorem value_023 (h : Assignment) (H : Constraints h) :
    h 5 3 = h 1 3 := by
  have r0 := H 6 3
  change ((1 : ℤ) : ℝ) * (h 5 3 - h 1 3) - ((0 : ℤ) : ℝ) * (h 5 1 - h 1 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 7.0, recovered from interface cube. -/
theorem value_028 (h : Assignment) (H : Constraints h) :
    h 7 0 = h 3 0 := by
  have r0 := H 15 0
  change ((1 : ℤ) : ℝ) * (h 7 0 - h 3 0) - ((0 : ℤ) : ℝ) * (h 7 1 - h 3 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 7.1, recovered from interface cube. -/
theorem value_029 (h : Assignment) (H : Constraints h) :
    h 7 1 = h 5 1 := by
  have r0 := H 24 1
  change ((1 : ℤ) : ℝ) * (h 7 1 - h 5 1) - ((0 : ℤ) : ℝ) * (h 7 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 7.2, recovered from interface cube. -/
theorem value_030 (h : Assignment) (H : Constraints h) :
    h 7 2 = h 1 2 := by
  have r0 := H 5 2
  change ((1 : ℤ) : ℝ) * (h 3 2 - h 1 2) - ((0 : ℤ) : ℝ) * (h 3 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 15 2
  change ((1 : ℤ) : ℝ) * (h 7 2 - h 3 2) - ((0 : ℤ) : ℝ) * (h 7 1 - h 3 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1

/-- Coordinate 7.3, recovered from interface cube. -/
theorem value_031 (h : Assignment) (H : Constraints h) :
    h 7 3 = h 1 3 := by
  have r0 := H 5 3
  change ((1 : ℤ) : ℝ) * (h 3 3 - h 1 3) - ((0 : ℤ) : ℝ) * (h 3 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 15 3
  change ((1 : ℤ) : ℝ) * (h 7 3 - h 3 3) - ((0 : ℤ) : ℝ) * (h 7 1 - h 3 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1

/-- Coordinate 9.0, recovered from interface cube. -/
theorem value_036 (h : Assignment) (H : Constraints h) :
    h 9 0 = h 1 0 := by
  have r0 := H 7 0
  change ((1 : ℤ) : ℝ) * (h 9 0 - h 1 0) - ((0 : ℤ) : ℝ) * (h 9 2 - h 1 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 9.1, recovered from interface cube. -/
theorem value_037 (h : Assignment) (H : Constraints h) :
    h 9 1 = h 1 1 := by
  have r0 := H 7 1
  change ((1 : ℤ) : ℝ) * (h 9 1 - h 1 1) - ((0 : ℤ) : ℝ) * (h 9 2 - h 1 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 9.3, recovered from interface cube. -/
theorem value_039 (h : Assignment) (H : Constraints h) :
    h 9 3 = h 1 3 := by
  have r0 := H 7 3
  change ((1 : ℤ) : ℝ) * (h 9 3 - h 1 3) - ((0 : ℤ) : ℝ) * (h 9 2 - h 1 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 11.0, recovered from interface cube. -/
theorem value_044 (h : Assignment) (H : Constraints h) :
    h 11 0 = h 3 0 := by
  have r0 := H 16 0
  change ((1 : ℤ) : ℝ) * (h 11 0 - h 3 0) - ((0 : ℤ) : ℝ) * (h 11 2 - h 3 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 11.1, recovered from interface cube. -/
theorem value_045 (h : Assignment) (H : Constraints h) :
    h 11 1 = h 1 1 := by
  have r0 := H 5 1
  change ((1 : ℤ) : ℝ) * (h 3 1 - h 1 1) - ((0 : ℤ) : ℝ) * (h 3 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 16 1
  change ((1 : ℤ) : ℝ) * (h 11 1 - h 3 1) - ((0 : ℤ) : ℝ) * (h 11 2 - h 3 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1

/-- Coordinate 11.2, recovered from interface cube. -/
theorem value_046 (h : Assignment) (H : Constraints h) :
    h 11 2 = h 9 2 := by
  have r0 := H 42 2
  change ((1 : ℤ) : ℝ) * (h 11 2 - h 9 2) - ((0 : ℤ) : ℝ) * (h 11 0 - h 9 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 11.3, recovered from interface cube. -/
theorem value_047 (h : Assignment) (H : Constraints h) :
    h 11 3 = h 1 3 := by
  have r0 := H 5 3
  change ((1 : ℤ) : ℝ) * (h 3 3 - h 1 3) - ((0 : ℤ) : ℝ) * (h 3 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 16 3
  change ((1 : ℤ) : ℝ) * (h 11 3 - h 3 3) - ((0 : ℤ) : ℝ) * (h 11 2 - h 3 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1

/-- Coordinate 13.0, recovered from interface cube. -/
theorem value_052 (h : Assignment) (H : Constraints h) :
    h 13 0 = h 1 0 := by
  have r0 := H 6 0
  change ((1 : ℤ) : ℝ) * (h 5 0 - h 1 0) - ((0 : ℤ) : ℝ) * (h 5 1 - h 1 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 25 0
  change ((1 : ℤ) : ℝ) * (h 13 0 - h 5 0) - ((0 : ℤ) : ℝ) * (h 13 2 - h 5 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1

/-- Coordinate 13.1, recovered from interface cube. -/
theorem value_053 (h : Assignment) (H : Constraints h) :
    h 13 1 = h 5 1 := by
  have r0 := H 25 1
  change ((1 : ℤ) : ℝ) * (h 13 1 - h 5 1) - ((0 : ℤ) : ℝ) * (h 13 2 - h 5 2) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 13.2, recovered from interface cube. -/
theorem value_054 (h : Assignment) (H : Constraints h) :
    h 13 2 = h 9 2 := by
  have r0 := H 43 2
  change ((1 : ℤ) : ℝ) * (h 13 2 - h 9 2) - ((0 : ℤ) : ℝ) * (h 13 1 - h 9 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0

/-- Coordinate 13.3, recovered from interface cube. -/
theorem value_055 (h : Assignment) (H : Constraints h) :
    h 13 3 = h 1 3 := by
  have r0 := H 6 3
  change ((1 : ℤ) : ℝ) * (h 5 3 - h 1 3) - ((0 : ℤ) : ℝ) * (h 5 1 - h 1 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 25 3
  change ((1 : ℤ) : ℝ) * (h 13 3 - h 5 3) - ((0 : ℤ) : ℝ) * (h 13 2 - h 5 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1

/-- Coordinate 15.0, recovered from interface cube. -/
theorem value_060 (h : Assignment) (H : Constraints h) :
    h 15 0 = h 3 0 := by
  have r0 := H 15 0
  change ((1 : ℤ) : ℝ) * (h 7 0 - h 3 0) - ((0 : ℤ) : ℝ) * (h 7 1 - h 3 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 32 0
  change ((1 : ℤ) : ℝ) * (h 15 0 - h 7 0) - ((0 : ℤ) : ℝ) * (h 15 2 - h 7 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1

/-- Coordinate 15.1, recovered from interface cube. -/
theorem value_061 (h : Assignment) (H : Constraints h) :
    h 15 1 = h 5 1 := by
  have r0 := H 24 1
  change ((1 : ℤ) : ℝ) * (h 7 1 - h 5 1) - ((0 : ℤ) : ℝ) * (h 7 0 - h 5 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 32 1
  change ((1 : ℤ) : ℝ) * (h 15 1 - h 7 1) - ((0 : ℤ) : ℝ) * (h 15 2 - h 7 2) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1

/-- Coordinate 15.2, recovered from interface cube. -/
theorem value_062 (h : Assignment) (H : Constraints h) :
    h 15 2 = h 9 2 := by
  have r0 := H 42 2
  change ((1 : ℤ) : ℝ) * (h 11 2 - h 9 2) - ((0 : ℤ) : ℝ) * (h 11 0 - h 9 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 52 2
  change ((1 : ℤ) : ℝ) * (h 15 2 - h 11 2) - ((0 : ℤ) : ℝ) * (h 15 1 - h 11 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1

/-- Coordinate 15.3, recovered from interface cube. -/
theorem value_063 (h : Assignment) (H : Constraints h) :
    h 15 3 = h 1 3 := by
  have r0 := H 5 3
  change ((1 : ℤ) : ℝ) * (h 3 3 - h 1 3) - ((0 : ℤ) : ℝ) * (h 3 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 15 3
  change ((1 : ℤ) : ℝ) * (h 7 3 - h 3 3) - ((0 : ℤ) : ℝ) * (h 7 1 - h 3 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 32 3
  change ((1 : ℤ) : ℝ) * (h 15 3 - h 7 3) - ((0 : ℤ) : ℝ) * (h 15 2 - h 7 2) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * r1 + (1 : ℝ) * r2

/-- Coordinate 0.0, recovered from nonplanar cycle 0. -/
theorem value_000 (h : Assignment) (H : Constraints h) :
    h 0 0 = ((74819036228 : ℝ) / 120001635295) * (h 1 0) + ((45182599067 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 0 1
  change ((-45182599067 : ℤ) : ℝ) * (h 1 1 - h 0 1) - ((-45182599067 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 0 3
  change ((-45182599067 : ℤ) : ℝ) * (h 1 3 - h 0 3) - ((-29636437161 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 1 1
  change ((1739295768452 : ℤ) : ℝ) * (h 2 1 - h 0 1) - ((-300732031563 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 1 3
  change ((1739295768452 : ℤ) : ℝ) * (h 2 3 - h 0 3) - ((-118545748644 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 11 1
  change ((480006541180 : ℤ) : ℝ) * (h 3 1 - h 2 1) - ((-351581980149 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 11 3
  change ((480006541180 : ℤ) : ℝ) * (h 3 3 - h 2 3) - ((-237091497288 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-12 : ℝ) / 120001635295) * r0 + ((467372152576 : ℝ) / 3556420923637507197495) * r1 + ((-135547797201 : ℝ) / 52179584118978417678335) * r2 + ((5279272146230539811648 : ℝ) / 1546416965829217423039186738606935) * r3 + ((-135547797201 : ℝ) / 14400392473474189737025) * r4 + ((5279272146230539811648 : ℝ) / 426776326633855183496732527586025) * r5 + ((542191188804 : ℝ) / 120001635295) * (value_013 h H) + ((-21117088584922159246592 : ℝ) / 3556420923637507197495) * (value_015 h H)

/-- Coordinate 0.1, recovered from nonplanar cycle 0. -/
theorem value_001 (h : Assignment) (H : Constraints h) :
    h 0 1 = ((-45182599067 : ℝ) / 120001635295) * (h 1 0) + h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 0 1
  change ((-45182599067 : ℤ) : ℝ) * (h 1 1 - h 0 1) - ((-45182599067 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 0 3
  change ((-45182599067 : ℤ) : ℝ) * (h 1 3 - h 0 3) - ((-29636437161 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 1 1
  change ((1739295768452 : ℤ) : ℝ) * (h 2 1 - h 0 1) - ((-300732031563 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 1 3
  change ((1739295768452 : ℤ) : ℝ) * (h 2 3 - h 0 3) - ((-118545748644 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 11 1
  change ((480006541180 : ℤ) : ℝ) * (h 3 1 - h 2 1) - ((-351581980149 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 11 3
  change ((480006541180 : ℤ) : ℝ) * (h 3 3 - h 2 3) - ((-237091497288 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-422189553509 : ℝ) / 5421985774918341269765) * r0 + ((467372152576 : ℝ) / 3556420923637507197495) * r1 + ((-135547797201 : ℝ) / 52179584118978417678335) * r2 + ((5279272146230539811648 : ℝ) / 1546416965829217423039186738606935) * r3 + ((-135547797201 : ℝ) / 14400392473474189737025) * r4 + ((5279272146230539811648 : ℝ) / 426776326633855183496732527586025) * r5 + ((542191188804 : ℝ) / 120001635295) * (value_013 h H) + ((-21117088584922159246592 : ℝ) / 3556420923637507197495) * (value_015 h H)

/-- Coordinate 0.2, recovered from nonplanar cycle 0. -/
theorem value_002 (h : Assignment) (H : Constraints h) :
    h 0 2 = ((-45182599067 : ℝ) / 120001635295) * (h 1 0) + h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 0 1
  change ((-45182599067 : ℤ) : ℝ) * (h 1 1 - h 0 1) - ((-45182599067 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 0 2
  change ((-45182599067 : ℤ) : ℝ) * (h 1 2 - h 0 2) - ((-45182599067 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 0 3
  change ((-45182599067 : ℤ) : ℝ) * (h 1 3 - h 0 3) - ((-29636437161 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 1 1
  change ((1739295768452 : ℤ) : ℝ) * (h 2 1 - h 0 1) - ((-300732031563 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 1 3
  change ((1739295768452 : ℤ) : ℝ) * (h 2 3 - h 0 3) - ((-118545748644 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 11 1
  change ((480006541180 : ℤ) : ℝ) * (h 3 1 - h 2 1) - ((-351581980149 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 11 3
  change ((480006541180 : ℤ) : ℝ) * (h 3 3 - h 2 3) - ((-237091497288 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-12 : ℝ) / 120001635295) * r0 + ((1 : ℝ) / 45182599067) * r1 + ((467372152576 : ℝ) / 3556420923637507197495) * r2 + ((-135547797201 : ℝ) / 52179584118978417678335) * r3 + ((5279272146230539811648 : ℝ) / 1546416965829217423039186738606935) * r4 + ((-135547797201 : ℝ) / 14400392473474189737025) * r5 + ((5279272146230539811648 : ℝ) / 426776326633855183496732527586025) * r6 + ((542191188804 : ℝ) / 120001635295) * (value_013 h H) + ((-21117088584922159246592 : ℝ) / 3556420923637507197495) * (value_015 h H)

/-- Coordinate 0.3, recovered from nonplanar cycle 0. -/
theorem value_003 (h : Assignment) (H : Constraints h) :
    h 0 3 = ((-29636437161 : ℝ) / 120001635295) * (h 1 0) + h 1 3 + ((29636437161 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 0 1
  change ((-45182599067 : ℤ) : ℝ) * (h 1 1 - h 0 1) - ((-45182599067 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 0 3
  change ((-45182599067 : ℤ) : ℝ) * (h 1 3 - h 0 3) - ((-29636437161 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 1 1
  change ((1739295768452 : ℤ) : ℝ) * (h 2 1 - h 0 1) - ((-300732031563 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 1 3
  change ((1739295768452 : ℤ) : ℝ) * (h 2 3 - h 0 3) - ((-118545748644 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 11 1
  change ((480006541180 : ℤ) : ℝ) * (h 3 1 - h 2 1) - ((-351581980149 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 11 3
  change ((480006541180 : ℤ) : ℝ) * (h 3 3 - h 2 3) - ((-237091497288 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-355637245932 : ℝ) / 5421985774918341269765) * r0 + ((13 : ℝ) / 120001635295) * r1 + ((-88909311483 : ℝ) / 52179584118978417678335) * r2 + ((116843038144 : ℝ) / 52179584118978417678335) * r3 + ((-88909311483 : ℝ) / 14400392473474189737025) * r4 + ((116843038144 : ℝ) / 14400392473474189737025) * r5 + ((355637245932 : ℝ) / 120001635295) * (value_013 h H) + ((-467372152576 : ℝ) / 120001635295) * (value_015 h H)

/-- Coordinate 2.0, recovered from nonplanar cycle 0. -/
theorem value_008 (h : Assignment) (H : Constraints h) :
    h 2 0 = ((120001635295 : ℝ) / 249882082977) * (h 1 0) + ((129880447682 : ℝ) / 249882082977) * (h 3 0) := by
  have r0 := H 0 1
  change ((-45182599067 : ℤ) : ℝ) * (h 1 1 - h 0 1) - ((-45182599067 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 0 3
  change ((-45182599067 : ℤ) : ℝ) * (h 1 3 - h 0 3) - ((-29636437161 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 1 1
  change ((1739295768452 : ℤ) : ℝ) * (h 2 1 - h 0 1) - ((-300732031563 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 1 3
  change ((1739295768452 : ℤ) : ℝ) * (h 2 3 - h 0 3) - ((-118545748644 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 11 1
  change ((480006541180 : ℤ) : ℝ) * (h 3 1 - h 2 1) - ((-351581980149 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 11 3
  change ((480006541180 : ℤ) : ℝ) * (h 3 3 - h 2 3) - ((-237091497288 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1920026164720 : ℝ) / 11290321969176616782459) * r0 + ((-120001635295 : ℝ) / 435624391165155782841) * r1 + ((480006541180 : ℝ) / 108654712383466910710401) * r2 + ((-5421985774918341269765 : ℝ) / 757679660188034266962728730732132) * r3 + ((4 : ℝ) / 249882082977) * r4 + ((-45182599067 : ℝ) / 1742497564660623131364) * r5 + ((-1920026164720 : ℝ) / 249882082977) * (value_013 h H) + ((5421985774918341269765 : ℝ) / 435624391165155782841) * (value_015 h H)

/-- Coordinate 2.1, recovered from nonplanar cycle 0. -/
theorem value_009 (h : Assignment) (H : Constraints h) :
    h 2 1 = ((-117193993383 : ℝ) / 333176110636) * (h 1 0) + h 1 1 + ((117193993383 : ℝ) / 333176110636) * (h 3 0) := by
  have r0 := H 0 1
  change ((-45182599067 : ℤ) : ℝ) * (h 1 1 - h 0 1) - ((-45182599067 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 0 3
  change ((-45182599067 : ℤ) : ℝ) * (h 1 3 - h 0 3) - ((-29636437161 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 1 1
  change ((1739295768452 : ℤ) : ℝ) * (h 2 1 - h 0 1) - ((-300732031563 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 1 3
  change ((1739295768452 : ℤ) : ℝ) * (h 2 3 - h 0 3) - ((-118545748644 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 11 1
  change ((480006541180 : ℤ) : ℝ) * (h 3 1 - h 2 1) - ((-351581980149 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 11 3
  change ((480006541180 : ℤ) : ℝ) * (h 3 3 - h 2 3) - ((-237091497288 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-468775973532 : ℝ) / 3763440656392205594153) * r0 + ((39064664461 : ℝ) / 193610840517847014596) * r1 + ((-1137805761 : ℝ) / 351633373409278028189) * r2 + ((17136340505128608329 : ℝ) / 3269383646981809134682756119664) * r3 + ((-552070001191 : ℝ) / 39981678117547842497620) * r4 + ((1765043072028246657887 : ℝ) / 92934469891924345536614935063280) * r5 + ((552070001191 : ℝ) / 83294027659) * (value_013 h H) + ((-1765043072028246657887 : ℝ) / 193610840517847014596) * (value_015 h H)

/-- Coordinate 2.2, recovered from nonplanar cycle 0. -/
theorem value_010 (h : Assignment) (H : Constraints h) :
    h 2 2 = ((-117193993383 : ℝ) / 333176110636) * (h 1 0) + h 1 2 + ((117193993383 : ℝ) / 333176110636) * (h 3 0) := by
  have r0 := H 0 1
  change ((-45182599067 : ℤ) : ℝ) * (h 1 1 - h 0 1) - ((-45182599067 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 0 2
  change ((-45182599067 : ℤ) : ℝ) * (h 1 2 - h 0 2) - ((-45182599067 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 0 3
  change ((-45182599067 : ℤ) : ℝ) * (h 1 3 - h 0 3) - ((-29636437161 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 1 1
  change ((1739295768452 : ℤ) : ℝ) * (h 2 1 - h 0 1) - ((-300732031563 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 1 2
  change ((1739295768452 : ℤ) : ℝ) * (h 2 2 - h 0 2) - ((-300732031563 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 1 3
  change ((1739295768452 : ℤ) : ℝ) * (h 2 3 - h 0 3) - ((-118545748644 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 11 1
  change ((480006541180 : ℤ) : ℝ) * (h 3 1 - h 2 1) - ((-351581980149 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 11 3
  change ((480006541180 : ℤ) : ℝ) * (h 3 3 - h 2 3) - ((-237091497288 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((-552070001191 : ℝ) / 3763440656392205594153) * r0 + ((1 : ℝ) / 45182599067) * r1 + ((39064664461 : ℝ) / 193610840517847014596) * r2 + ((-552070001191 : ℝ) / 144872949844622547613868) * r3 + ((1 : ℝ) / 1739295768452) * r4 + ((17136340505128608329 : ℝ) / 3269383646981809134682756119664) * r5 + ((-552070001191 : ℝ) / 39981678117547842497620) * r6 + ((1765043072028246657887 : ℝ) / 92934469891924345536614935063280) * r7 + ((552070001191 : ℝ) / 83294027659) * (value_013 h H) + ((-1765043072028246657887 : ℝ) / 193610840517847014596) * (value_015 h H)

/-- Coordinate 2.3, recovered from nonplanar cycle 0. -/
theorem value_011 (h : Assignment) (H : Constraints h) :
    h 2 3 = ((-19757624774 : ℝ) / 83294027659) * (h 1 0) + h 1 3 + ((19757624774 : ℝ) / 83294027659) * (h 3 0) := by
  have r0 := H 0 1
  change ((-45182599067 : ℤ) : ℝ) * (h 1 1 - h 0 1) - ((-45182599067 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 0 3
  change ((-45182599067 : ℤ) : ℝ) * (h 1 3 - h 0 3) - ((-29636437161 : ℤ) : ℝ) * (h 1 0 - h 0 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 1 1
  change ((1739295768452 : ℤ) : ℝ) * (h 2 1 - h 0 1) - ((-300732031563 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 1 3
  change ((1739295768452 : ℤ) : ℝ) * (h 2 3 - h 0 3) - ((-118545748644 : ℤ) : ℝ) * (h 2 0 - h 0 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 11 1
  change ((480006541180 : ℤ) : ℝ) * (h 3 1 - h 2 1) - ((-351581980149 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 11 3
  change ((480006541180 : ℤ) : ℝ) * (h 3 3 - h 2 3) - ((-237091497288 : ℤ) : ℝ) * (h 3 0 - h 2 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-316121996384 : ℝ) / 3763440656392205594153) * r0 + ((34 : ℝ) / 249882082977) * r1 + ((-79030499096 : ℝ) / 36218237461155636903467) * r2 + ((768104184139 : ℝ) / 217309424766933821420802) * r3 + ((-79030499096 : ℝ) / 9995419529386960624405) * r4 + ((1286326285301 : ℝ) / 119945034352643527492860) * r5 + ((316121996384 : ℝ) / 83294027659) * (value_013 h H) + ((-1286326285301 : ℝ) / 249882082977) * (value_015 h H)

/-- Coordinate 76.0, recovered from nonplanar cycle 1. -/
theorem value_304 (h : Assignment) (H : Constraints h) :
    h 76 0 = h 1 0 + ((-45182599067 : ℝ) / 120001635295) * (h 1 1) + ((45182599067 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 9 1
  change ((45182599067 : ℤ) : ℝ) * (h 76 1 - h 1 1) - ((45182599067 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 9 3
  change ((45182599067 : ℤ) : ℝ) * (h 76 3 - h 1 3) - ((-29636437161 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 27 1
  change ((351581980149 : ℤ) : ℝ) * (h 77 1 - h 5 1) - ((-480006541180 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 27 3
  change ((351581980149 : ℤ) : ℝ) * (h 77 3 - h 5 3) - ((-237091497288 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 224 1
  change ((-300732031563 : ℤ) : ℝ) * (h 77 1 - h 76 1) - ((1739295768452 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 224 3
  change ((-300732031563 : ℤ) : ℝ) * (h 77 3 - h 76 3) - ((118545748644 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1 : ℝ) / 120001635295) * r0 + ((-467372152576 : ℝ) / 3556420923637507197495) * r1 + ((45182599067 : ℝ) / 42190412558134227758955) * r2 + ((21117088584922159246592 : ℝ) / 1250373510575810300381531712526755) * r3 + ((45182599067 : ℝ) / 36088335573147554816085) * r4 + ((21117088584922159246592 : ℝ) / 1069529689458668427287706014534685) * r5 + ((542191188804 : ℝ) / 120001635295) * (value_020 h H) + ((21117088584922159246592 : ℝ) / 3556420923637507197495) * (value_023 h H)

/-- Coordinate 76.1, recovered from nonplanar cycle 1. -/
theorem value_305 (h : Assignment) (H : Constraints h) :
    h 76 1 = ((74819036228 : ℝ) / 120001635295) * (h 1 1) + ((45182599067 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 9 1
  change ((45182599067 : ℤ) : ℝ) * (h 76 1 - h 1 1) - ((45182599067 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 9 3
  change ((45182599067 : ℤ) : ℝ) * (h 76 3 - h 1 3) - ((-29636437161 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 27 1
  change ((351581980149 : ℤ) : ℝ) * (h 77 1 - h 5 1) - ((-480006541180 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 27 3
  change ((351581980149 : ℤ) : ℝ) * (h 77 3 - h 5 3) - ((-237091497288 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 224 1
  change ((-300732031563 : ℤ) : ℝ) * (h 77 1 - h 76 1) - ((1739295768452 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 224 3
  change ((-300732031563 : ℤ) : ℝ) * (h 77 3 - h 76 3) - ((118545748644 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((74819036228 : ℝ) / 5421985774918341269765) * r0 + ((-467372152576 : ℝ) / 3556420923637507197495) * r1 + ((45182599067 : ℝ) / 42190412558134227758955) * r2 + ((21117088584922159246592 : ℝ) / 1250373510575810300381531712526755) * r3 + ((45182599067 : ℝ) / 36088335573147554816085) * r4 + ((21117088584922159246592 : ℝ) / 1069529689458668427287706014534685) * r5 + ((542191188804 : ℝ) / 120001635295) * (value_020 h H) + ((21117088584922159246592 : ℝ) / 3556420923637507197495) * (value_023 h H)

/-- Coordinate 76.2, recovered from nonplanar cycle 1. -/
theorem value_306 (h : Assignment) (H : Constraints h) :
    h 76 2 = ((-45182599067 : ℝ) / 120001635295) * (h 1 1) + h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 9 1
  change ((45182599067 : ℤ) : ℝ) * (h 76 1 - h 1 1) - ((45182599067 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 9 2
  change ((45182599067 : ℤ) : ℝ) * (h 76 2 - h 1 2) - ((45182599067 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 9 3
  change ((45182599067 : ℤ) : ℝ) * (h 76 3 - h 1 3) - ((-29636437161 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 27 1
  change ((351581980149 : ℤ) : ℝ) * (h 77 1 - h 5 1) - ((-480006541180 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 27 3
  change ((351581980149 : ℤ) : ℝ) * (h 77 3 - h 5 3) - ((-237091497288 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 224 1
  change ((-300732031563 : ℤ) : ℝ) * (h 77 1 - h 76 1) - ((1739295768452 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 224 3
  change ((-300732031563 : ℤ) : ℝ) * (h 77 3 - h 76 3) - ((118545748644 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-1 : ℝ) / 120001635295) * r0 + ((1 : ℝ) / 45182599067) * r1 + ((-467372152576 : ℝ) / 3556420923637507197495) * r2 + ((45182599067 : ℝ) / 42190412558134227758955) * r3 + ((21117088584922159246592 : ℝ) / 1250373510575810300381531712526755) * r4 + ((45182599067 : ℝ) / 36088335573147554816085) * r5 + ((21117088584922159246592 : ℝ) / 1069529689458668427287706014534685) * r6 + ((542191188804 : ℝ) / 120001635295) * (value_020 h H) + ((21117088584922159246592 : ℝ) / 3556420923637507197495) * (value_023 h H)

/-- Coordinate 76.3, recovered from nonplanar cycle 1. -/
theorem value_307 (h : Assignment) (H : Constraints h) :
    h 76 3 = ((29636437161 : ℝ) / 120001635295) * (h 1 1) + h 1 3 + ((-29636437161 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 9 1
  change ((45182599067 : ℤ) : ℝ) * (h 76 1 - h 1 1) - ((45182599067 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 9 3
  change ((45182599067 : ℤ) : ℝ) * (h 76 3 - h 1 3) - ((-29636437161 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 27 1
  change ((351581980149 : ℤ) : ℝ) * (h 77 1 - h 5 1) - ((-480006541180 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 27 3
  change ((351581980149 : ℤ) : ℝ) * (h 77 3 - h 5 3) - ((-237091497288 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 224 1
  change ((-300732031563 : ℤ) : ℝ) * (h 77 1 - h 76 1) - ((1739295768452 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 224 3
  change ((-300732031563 : ℤ) : ℝ) * (h 77 3 - h 76 3) - ((118545748644 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((29636437161 : ℝ) / 5421985774918341269765) * r0 + ((13 : ℝ) / 120001635295) * r1 + ((-9878812387 : ℝ) / 14063470852711409252985) * r2 + ((-467372152576 : ℝ) / 42190412558134227758955) * r3 + ((-9878812387 : ℝ) / 12029445191049184938695) * r4 + ((-467372152576 : ℝ) / 36088335573147554816085) * r5 + ((-355637245932 : ℝ) / 120001635295) * (value_020 h H) + ((-467372152576 : ℝ) / 120001635295) * (value_023 h H)

/-- Coordinate 77.0, recovered from nonplanar cycle 1. -/
theorem value_308 (h : Assignment) (H : Constraints h) :
    h 77 0 = h 1 0 + ((-117193993383 : ℝ) / 333176110636) * (h 1 1) + ((117193993383 : ℝ) / 333176110636) * (h 5 1) := by
  have r0 := H 9 1
  change ((45182599067 : ℤ) : ℝ) * (h 76 1 - h 1 1) - ((45182599067 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 9 3
  change ((45182599067 : ℤ) : ℝ) * (h 76 3 - h 1 3) - ((-29636437161 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 27 1
  change ((351581980149 : ℤ) : ℝ) * (h 77 1 - h 5 1) - ((-480006541180 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 27 3
  change ((351581980149 : ℤ) : ℝ) * (h 77 3 - h 5 3) - ((-237091497288 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 224 1
  change ((-300732031563 : ℤ) : ℝ) * (h 77 1 - h 76 1) - ((1739295768452 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 224 3
  change ((-300732031563 : ℤ) : ℝ) * (h 77 3 - h 76 3) - ((118545748644 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-117193993383 : ℝ) / 15053762625568822376612) * r0 + ((-39064664461 : ℝ) / 193610840517847014596) * r1 + ((1 : ℝ) / 999528331908) * r2 + ((45182599067 : ℝ) / 1742497564660623131364) * r3 + ((39064664461 : ℝ) / 33398909539941044001356) * r4 + ((1765043072028246657887 : ℝ) / 58224981401552127658289593693548) * r5 + ((552070001191 : ℝ) / 83294027659) * (value_020 h H) + ((1765043072028246657887 : ℝ) / 193610840517847014596) * (value_023 h H)

/-- Coordinate 77.1, recovered from nonplanar cycle 1. -/
theorem value_309 (h : Assignment) (H : Constraints h) :
    h 77 1 = ((120001635295 : ℝ) / 249882082977) * (h 1 1) + ((129880447682 : ℝ) / 249882082977) * (h 5 1) := by
  have r0 := H 9 1
  change ((45182599067 : ℤ) : ℝ) * (h 76 1 - h 1 1) - ((45182599067 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 9 3
  change ((45182599067 : ℤ) : ℝ) * (h 76 3 - h 1 3) - ((-29636437161 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 27 1
  change ((351581980149 : ℤ) : ℝ) * (h 77 1 - h 5 1) - ((-480006541180 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 27 3
  change ((351581980149 : ℤ) : ℝ) * (h 77 3 - h 5 3) - ((-237091497288 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 224 1
  change ((-300732031563 : ℤ) : ℝ) * (h 77 1 - h 76 1) - ((1739295768452 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 224 3
  change ((-300732031563 : ℤ) : ℝ) * (h 77 3 - h 76 3) - ((118545748644 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((120001635295 : ℝ) / 11290321969176616782459) * r0 + ((120001635295 : ℝ) / 435624391165155782841) * r1 + ((129880447682 : ℝ) / 87854037536810384823573) * r2 + ((-5421985774918341269765 : ℝ) / 153157686047048011423297016823309) * r3 + ((-120001635295 : ℝ) / 75147546464867349003051) * r4 + ((-5421985774918341269765 : ℝ) / 131006208153492287231151585810483) * r5 + ((-1920026164720 : ℝ) / 249882082977) * (value_020 h H) + ((-5421985774918341269765 : ℝ) / 435624391165155782841) * (value_023 h H)

/-- Coordinate 77.2, recovered from nonplanar cycle 1. -/
theorem value_310 (h : Assignment) (H : Constraints h) :
    h 77 2 = ((-117193993383 : ℝ) / 333176110636) * (h 1 1) + h 1 2 + ((117193993383 : ℝ) / 333176110636) * (h 5 1) := by
  have r0 := H 9 1
  change ((45182599067 : ℤ) : ℝ) * (h 76 1 - h 1 1) - ((45182599067 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 9 3
  change ((45182599067 : ℤ) : ℝ) * (h 76 3 - h 1 3) - ((-29636437161 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 27 1
  change ((351581980149 : ℤ) : ℝ) * (h 77 1 - h 5 1) - ((-480006541180 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 27 2
  change ((351581980149 : ℤ) : ℝ) * (h 77 2 - h 5 2) - ((351581980149 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 27 3
  change ((351581980149 : ℤ) : ℝ) * (h 77 3 - h 5 3) - ((-237091497288 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 224 1
  change ((-300732031563 : ℤ) : ℝ) * (h 77 1 - h 76 1) - ((1739295768452 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 224 3
  change ((-300732031563 : ℤ) : ℝ) * (h 77 3 - h 76 3) - ((118545748644 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-117193993383 : ℝ) / 15053762625568822376612) * r0 + ((-39064664461 : ℝ) / 193610840517847014596) * r1 + ((1 : ℝ) / 999528331908) * r2 + ((1 : ℝ) / 351581980149) * r3 + ((45182599067 : ℝ) / 1742497564660623131364) * r4 + ((39064664461 : ℝ) / 33398909539941044001356) * r5 + ((1765043072028246657887 : ℝ) / 58224981401552127658289593693548) * r6 + ((468775973532 : ℝ) / 83294027659) * (value_020 h H) + (1 : ℝ) * (value_022 h H) + ((1765043072028246657887 : ℝ) / 193610840517847014596) * (value_023 h H)

/-- Coordinate 77.3, recovered from nonplanar cycle 1. -/
theorem value_311 (h : Assignment) (H : Constraints h) :
    h 77 3 = ((19757624774 : ℝ) / 83294027659) * (h 1 1) + h 1 3 + ((-19757624774 : ℝ) / 83294027659) * (h 5 1) := by
  have r0 := H 9 1
  change ((45182599067 : ℤ) : ℝ) * (h 76 1 - h 1 1) - ((45182599067 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 9 3
  change ((45182599067 : ℤ) : ℝ) * (h 76 3 - h 1 3) - ((-29636437161 : ℤ) : ℝ) * (h 76 0 - h 1 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 27 1
  change ((351581980149 : ℤ) : ℝ) * (h 77 1 - h 5 1) - ((-480006541180 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 27 3
  change ((351581980149 : ℤ) : ℝ) * (h 77 3 - h 5 3) - ((-237091497288 : ℤ) : ℝ) * (h 77 0 - h 5 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 224 1
  change ((-300732031563 : ℤ) : ℝ) * (h 77 1 - h 76 1) - ((1739295768452 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 224 3
  change ((-300732031563 : ℤ) : ℝ) * (h 77 3 - h 76 3) - ((118545748644 : ℤ) : ℝ) * (h 77 0 - h 76 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((19757624774 : ℝ) / 3763440656392205594153) * r0 + ((34 : ℝ) / 249882082977) * r1 + ((-19757624774 : ℝ) / 29284679178936794941191) * r2 + ((-1286326285301 : ℝ) / 87854037536810384823573) * r3 + ((-19757624774 : ℝ) / 25049182154955783001017) * r4 + ((-1536208368278 : ℝ) / 75147546464867349003051) * r5 + ((-316121996384 : ℝ) / 83294027659) * (value_020 h H) + ((-1286326285301 : ℝ) / 249882082977) * (value_023 h H)

/-- Coordinate 80.0, recovered from nonplanar cycle 2. -/
theorem value_320 (h : Assignment) (H : Constraints h) :
    h 80 0 = ((45182599067 : ℝ) / 120001635295) * (h 1 1) + h 3 0 + ((-45182599067 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 18 1
  change ((-45182599067 : ℤ) : ℝ) * (h 80 1 - h 3 1) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 18 2
  change ((-45182599067 : ℤ) : ℝ) * (h 80 2 - h 3 2) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 34 1
  change ((-341703167762 : ℤ) : ℝ) * (h 81 1 - h 7 1) - ((-480006541180 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 34 2
  change ((-341703167762 : ℤ) : ℝ) * (h 81 2 - h 7 2) - ((351581980149 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 236 1
  change ((420733666858 : ℤ) : ℝ) * (h 81 1 - h 80 1) - ((1739295768452 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 236 2
  change ((420733666858 : ℤ) : ℝ) * (h 81 2 - h 80 2) - ((-300732031563 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-1 : ℝ) / 120001635295) * r0 + ((392553116348 : ℝ) / 5421985774918341269765) * r1 + ((45182599067 : ℝ) / 41004938916921725359790) * r2 + ((-196276558174 : ℝ) / 20502469458460862679895) * r3 + ((45182599067 : ℝ) / 50488728046621744553110) * r4 + ((-196276558174 : ℝ) / 25244364023310872276555) * r5 + ((45182599067 : ℝ) / 120001635295) * (value_013 h H) + ((-392553116348 : ℝ) / 120001635295) * (value_014 h H) + ((-45182599067 : ℝ) / 120001635295) * (value_029 h H) + ((467372152576 : ℝ) / 120001635295) * (value_028 h H) + ((392553116348 : ℝ) / 120001635295) * (value_030 h H)

/-- Coordinate 80.1, recovered from nonplanar cycle 2. -/
theorem value_321 (h : Assignment) (H : Constraints h) :
    h 80 1 = ((74819036228 : ℝ) / 120001635295) * (h 1 1) + ((45182599067 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 18 1
  change ((-45182599067 : ℤ) : ℝ) * (h 80 1 - h 3 1) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 18 2
  change ((-45182599067 : ℤ) : ℝ) * (h 80 2 - h 3 2) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 34 1
  change ((-341703167762 : ℤ) : ℝ) * (h 81 1 - h 7 1) - ((-480006541180 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 34 2
  change ((-341703167762 : ℤ) : ℝ) * (h 81 2 - h 7 2) - ((351581980149 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 236 1
  change ((420733666858 : ℤ) : ℝ) * (h 81 1 - h 80 1) - ((1739295768452 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 236 2
  change ((420733666858 : ℤ) : ℝ) * (h 81 2 - h 80 2) - ((-300732031563 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-74819036228 : ℝ) / 5421985774918341269765) * r0 + ((-392553116348 : ℝ) / 5421985774918341269765) * r1 + ((-45182599067 : ℝ) / 41004938916921725359790) * r2 + ((196276558174 : ℝ) / 20502469458460862679895) * r3 + ((-45182599067 : ℝ) / 50488728046621744553110) * r4 + ((196276558174 : ℝ) / 25244364023310872276555) * r5 + ((74819036228 : ℝ) / 120001635295) * (value_013 h H) + ((392553116348 : ℝ) / 120001635295) * (value_014 h H) + ((45182599067 : ℝ) / 120001635295) * (value_029 h H) + ((-467372152576 : ℝ) / 120001635295) * (value_028 h H) + ((-392553116348 : ℝ) / 120001635295) * (value_030 h H)

/-- Coordinate 80.2, recovered from nonplanar cycle 2. -/
theorem value_322 (h : Assignment) (H : Constraints h) :
    h 80 2 = ((-45182599067 : ℝ) / 120001635295) * (h 1 1) + h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 18 1
  change ((-45182599067 : ℤ) : ℝ) * (h 80 1 - h 3 1) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 18 2
  change ((-45182599067 : ℤ) : ℝ) * (h 80 2 - h 3 2) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 34 1
  change ((-341703167762 : ℤ) : ℝ) * (h 81 1 - h 7 1) - ((-480006541180 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 34 2
  change ((-341703167762 : ℤ) : ℝ) * (h 81 2 - h 7 2) - ((351581980149 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 236 1
  change ((420733666858 : ℤ) : ℝ) * (h 81 1 - h 80 1) - ((1739295768452 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 236 2
  change ((420733666858 : ℤ) : ℝ) * (h 81 2 - h 80 2) - ((-300732031563 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1 : ℝ) / 120001635295) * r0 + ((-512554751643 : ℝ) / 5421985774918341269765) * r1 + ((-45182599067 : ℝ) / 41004938916921725359790) * r2 + ((196276558174 : ℝ) / 20502469458460862679895) * r3 + ((-45182599067 : ℝ) / 50488728046621744553110) * r4 + ((196276558174 : ℝ) / 25244364023310872276555) * r5 + ((-45182599067 : ℝ) / 120001635295) * (value_013 h H) + ((512554751643 : ℝ) / 120001635295) * (value_014 h H) + ((45182599067 : ℝ) / 120001635295) * (value_029 h H) + ((-467372152576 : ℝ) / 120001635295) * (value_028 h H) + ((-392553116348 : ℝ) / 120001635295) * (value_030 h H)

/-- Coordinate 80.3, recovered from nonplanar cycle 2. -/
theorem value_323 (h : Assignment) (H : Constraints h) :
    h 80 3 = ((29636437161 : ℝ) / 120001635295) * (h 1 1) + h 1 3 + ((-29636437161 : ℝ) / 120001635295) * (h 5 1) := by
  have r0 := H 18 1
  change ((-45182599067 : ℤ) : ℝ) * (h 80 1 - h 3 1) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 18 2
  change ((-45182599067 : ℤ) : ℝ) * (h 80 2 - h 3 2) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 18 3
  change ((-45182599067 : ℤ) : ℝ) * (h 80 3 - h 3 3) - ((-29636437161 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 34 1
  change ((-341703167762 : ℤ) : ℝ) * (h 81 1 - h 7 1) - ((-480006541180 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 34 2
  change ((-341703167762 : ℤ) : ℝ) * (h 81 2 - h 7 2) - ((351581980149 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 236 1
  change ((420733666858 : ℤ) : ℝ) * (h 81 1 - h 80 1) - ((1739295768452 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 236 2
  change ((420733666858 : ℤ) : ℝ) * (h 81 2 - h 80 2) - ((-300732031563 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-29636437161 : ℝ) / 5421985774918341269765) * r0 + ((11633875765002223808028 : ℝ) / 244979409415112718256471684309255) * r1 + ((-1 : ℝ) / 45182599067) * r2 + ((29636437161 : ℝ) / 41004938916921725359790) * r3 + ((-5816937882501111904014 : ℝ) / 926354857425049769376638946657965) * r4 + ((29636437161 : ℝ) / 50488728046621744553110) * r5 + ((-5816937882501111904014 : ℝ) / 1140605978366654183973630108974185) * r6 + ((29636437161 : ℝ) / 120001635295) * (value_013 h H) + ((-11633875765002223808028 : ℝ) / 5421985774918341269765) * (value_014 h H) + (1 : ℝ) * (value_015 h H) + ((-29636437161 : ℝ) / 120001635295) * (value_029 h H) + ((13851245430619928276736 : ℝ) / 5421985774918341269765) * (value_028 h H) + ((11633875765002223808028 : ℝ) / 5421985774918341269765) * (value_030 h H)

/-- Coordinate 81.0, recovered from nonplanar cycle 2. -/
theorem value_324 (h : Assignment) (H : Constraints h) :
    h 81 0 = ((170851583881 : ℝ) / 499764165954) * (h 1 1) + h 3 0 + ((-170851583881 : ℝ) / 499764165954) * (h 5 1) := by
  have r0 := H 18 1
  change ((-45182599067 : ℤ) : ℝ) * (h 80 1 - h 3 1) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 18 2
  change ((-45182599067 : ℤ) : ℝ) * (h 80 2 - h 3 2) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 34 1
  change ((-341703167762 : ℤ) : ℝ) * (h 81 1 - h 7 1) - ((-480006541180 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 34 2
  change ((-341703167762 : ℤ) : ℝ) * (h 81 2 - h 7 2) - ((351581980149 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 236 1
  change ((420733666858 : ℤ) : ℝ) * (h 81 1 - h 80 1) - ((1739295768452 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 236 2
  change ((420733666858 : ℤ) : ℝ) * (h 81 2 - h 80 2) - ((-300732031563 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-170851583881 : ℝ) / 22580643938353233564918) * r0 + ((512554751643 : ℝ) / 3763440656392205594153) * r1 + ((1 : ℝ) / 999528331908) * r2 + ((-3 : ℝ) / 166588055318) * r3 + ((170851583881 : ℝ) / 210267610106056461752532) * r4 + ((-512554751643 : ℝ) / 35044601684342743625422) * r5 + ((170851583881 : ℝ) / 499764165954) * (value_013 h H) + ((-512554751643 : ℝ) / 83294027659) * (value_014 h H) + ((-170851583881 : ℝ) / 499764165954) * (value_029 h H) + ((3404241091931 : ℝ) / 499764165954) * (value_028 h H) + ((512554751643 : ℝ) / 83294027659) * (value_030 h H)

/-- Coordinate 81.1, recovered from nonplanar cycle 2. -/
theorem value_325 (h : Assignment) (H : Constraints h) :
    h 81 1 = ((120001635295 : ℝ) / 249882082977) * (h 1 1) + ((129880447682 : ℝ) / 249882082977) * (h 5 1) := by
  have r0 := H 18 1
  change ((-45182599067 : ℤ) : ℝ) * (h 80 1 - h 3 1) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 18 2
  change ((-45182599067 : ℤ) : ℝ) * (h 80 2 - h 3 2) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 34 1
  change ((-341703167762 : ℤ) : ℝ) * (h 81 1 - h 7 1) - ((-480006541180 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 34 2
  change ((-341703167762 : ℤ) : ℝ) * (h 81 2 - h 7 2) - ((351581980149 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 236 1
  change ((420733666858 : ℤ) : ℝ) * (h 81 1 - h 80 1) - ((1739295768452 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 236 2
  change ((420733666858 : ℤ) : ℝ) * (h 81 2 - h 80 2) - ((-300732031563 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-120001635295 : ℝ) / 11290321969176616782459) * r0 + ((720009811770 : ℝ) / 3763440656392205594153) * r1 + ((-64940223841 : ℝ) / 42692749660103917693737) * r2 + ((-360004905885 : ℝ) / 14230916553367972564579) * r3 + ((120001635295 : ℝ) / 105133805053028230876266) * r4 + ((-360004905885 : ℝ) / 17522300842171371812711) * r5 + ((120001635295 : ℝ) / 249882082977) * (value_013 h H) + ((-720009811770 : ℝ) / 83294027659) * (value_014 h H) + ((129880447682 : ℝ) / 249882082977) * (value_029 h H) + ((2040027800015 : ℝ) / 249882082977) * (value_028 h H) + ((720009811770 : ℝ) / 83294027659) * (value_030 h H)

/-- Coordinate 81.2, recovered from nonplanar cycle 2. -/
theorem value_326 (h : Assignment) (H : Constraints h) :
    h 81 2 = ((-117193993383 : ℝ) / 333176110636) * (h 1 1) + h 1 2 + ((117193993383 : ℝ) / 333176110636) * (h 5 1) := by
  have r0 := H 18 1
  change ((-45182599067 : ℤ) : ℝ) * (h 80 1 - h 3 1) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 18 2
  change ((-45182599067 : ℤ) : ℝ) * (h 80 2 - h 3 2) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 34 1
  change ((-341703167762 : ℤ) : ℝ) * (h 81 1 - h 7 1) - ((-480006541180 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 34 2
  change ((-341703167762 : ℤ) : ℝ) * (h 81 2 - h 7 2) - ((351581980149 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 236 1
  change ((420733666858 : ℤ) : ℝ) * (h 81 1 - h 80 1) - ((1739295768452 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 236 2
  change ((420733666858 : ℤ) : ℝ) * (h 81 2 - h 80 2) - ((-300732031563 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((117193993383 : ℝ) / 15053762625568822376612) * r0 + ((-1054745940447 : ℝ) / 7526881312784411188306) * r1 + ((-117193993383 : ℝ) / 113847332426943780516632) * r2 + ((888157885129 : ℝ) / 56923666213471890258316) * r3 + ((-117193993383 : ℝ) / 140178406737370974501688) * r4 + ((1054745940447 : ℝ) / 70089203368685487250844) * r5 + ((-117193993383 : ℝ) / 333176110636) * (value_013 h H) + ((1054745940447 : ℝ) / 166588055318) * (value_014 h H) + ((117193993383 : ℝ) / 333176110636) * (value_029 h H) + ((-1992297887511 : ℝ) / 333176110636) * (value_028 h H) + ((-888157885129 : ℝ) / 166588055318) * (value_030 h H)

/-- Coordinate 81.3, recovered from nonplanar cycle 2. -/
theorem value_327 (h : Assignment) (H : Constraints h) :
    h 81 3 = ((19757624774 : ℝ) / 83294027659) * (h 1 1) + h 1 3 + ((-19757624774 : ℝ) / 83294027659) * (h 5 1) := by
  have r0 := H 18 1
  change ((-45182599067 : ℤ) : ℝ) * (h 80 1 - h 3 1) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 18 2
  change ((-45182599067 : ℤ) : ℝ) * (h 80 2 - h 3 2) - ((45182599067 : ℤ) : ℝ) * (h 80 0 - h 3 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 34 1
  change ((-341703167762 : ℤ) : ℝ) * (h 81 1 - h 7 1) - ((-480006541180 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 34 2
  change ((-341703167762 : ℤ) : ℝ) * (h 81 2 - h 7 2) - ((351581980149 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 34 3
  change ((-341703167762 : ℤ) : ℝ) * (h 81 3 - h 7 3) - ((-237091497288 : ℤ) : ℝ) * (h 81 0 - h 7 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 236 1
  change ((420733666858 : ℤ) : ℝ) * (h 81 1 - h 80 1) - ((1739295768452 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 236 2
  change ((420733666858 : ℤ) : ℝ) * (h 81 2 - h 80 2) - ((-300732031563 : ℤ) : ℝ) * (h 81 0 - h 80 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-19757624774 : ℝ) / 3763440656392205594153) * r0 + ((355637245932 : ℝ) / 3763440656392205594153) * r1 + ((9878812387 : ℝ) / 14230916553367972564579) * r2 + ((-177818622966 : ℝ) / 14230916553367972564579) * r3 + ((-1 : ℝ) / 341703167762) * r4 + ((9878812387 : ℝ) / 17522300842171371812711) * r5 + ((-177818622966 : ℝ) / 17522300842171371812711) * r6 + ((19757624774 : ℝ) / 83294027659) * (value_013 h H) + ((-355637245932 : ℝ) / 83294027659) * (value_014 h H) + ((-19757624774 : ℝ) / 83294027659) * (value_029 h H) + ((335879621158 : ℝ) / 83294027659) * (value_028 h H) + ((355637245932 : ℝ) / 83294027659) * (value_030 h H) + (1 : ℝ) * (value_031 h H)

/-- Coordinate 4.0, recovered from nonplanar cycle 3. -/
theorem value_016 (h : Assignment) (H : Constraints h) :
    h 4 0 = ((74819036228 : ℝ) / 120001635295) * (h 1 0) + ((45182599067 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 20 1
  change ((-90365198134 : ℤ) : ℝ) * (h 5 1 - h 4 1) - ((79324172525 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 20 2
  change ((-90365198134 : ℤ) : ℝ) * (h 5 2 - h 4 2) - ((-90365198134 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 21 1
  change ((3478591536904 : ℤ) : ℝ) * (h 6 1 - h 4 1) - ((437298325395 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 21 2
  change ((3478591536904 : ℤ) : ℝ) * (h 6 2 - h 4 2) - ((-601464063126 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 29 1
  change ((960013082360 : ℤ) : ℝ) * (h 7 1 - h 6 1) - ((624714567813 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 29 2
  change ((960013082360 : ℤ) : ℝ) * (h 7 2 - h 6 2) - ((-703163960298 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-233686076288 : ℝ) / 2048522323252184000055) * r0 + ((-219267758518 : ℝ) / 2048522323252184000055) * r1 + ((-2639636073115269905824 : ℝ) / 890746552102995929540740108816215) * r2 + ((-4953543610719284051353 : ℝ) / 1781493104205991859081480217632430) * r3 + ((-2639636073115269905824 : ℝ) / 245826028728574682686834369941225) * r4 + ((-4953543610719284051353 : ℝ) / 491652057457149365373668739882450) * r5 + ((74819036228 : ℝ) / 120001635295) * (value_020 h H) + ((-19814174442877136205412 : ℝ) / 2048522323252184000055) * (value_022 h H) + ((21117088584922159246592 : ℝ) / 2048522323252184000055) * (value_029 h H) + ((45182599067 : ℝ) / 120001635295) * (value_028 h H) + ((19814174442877136205412 : ℝ) / 2048522323252184000055) * (value_030 h H)

/-- Coordinate 4.1, recovered from nonplanar cycle 3. -/
theorem value_017 (h : Assignment) (H : Constraints h) :
    h 4 1 = ((15864834505 : ℝ) / 48000654118) * (h 1 0) + ((-15864834505 : ℝ) / 48000654118) * (h 3 0) + h 5 1 := by
  have r0 := H 20 1
  change ((-90365198134 : ℤ) : ℝ) * (h 5 1 - h 4 1) - ((79324172525 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 20 2
  change ((-90365198134 : ℤ) : ℝ) * (h 5 2 - h 4 2) - ((-90365198134 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 21 1
  change ((3478591536904 : ℤ) : ℝ) * (h 6 1 - h 4 1) - ((437298325395 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 21 2
  change ((3478591536904 : ℤ) : ℝ) * (h 6 2 - h 4 2) - ((-601464063126 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 29 1
  change ((960013082360 : ℤ) : ℝ) * (h 7 1 - h 6 1) - ((624714567813 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 29 2
  change ((960013082360 : ℤ) : ℝ) * (h 7 2 - h 6 2) - ((-703163960298 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((91121260753 : ℝ) / 819408929300873600022) * r0 + ((1739323350585187031795 : ℝ) / 18511512562260560241319474189737) * r1 + ((463423865803990589680 : ℝ) / 178149310420599185908148021763243) * r2 + ((1739323350585187031795 : ℝ) / 712597241682396743632592087052972) * r3 + ((92684773160798117936 : ℝ) / 9833041149142987307473374797649) * r4 + ((347864670117037406359 : ℝ) / 39332164596571949229893499190596) * r5 + ((15864834505 : ℝ) / 48000654118) * (value_020 h H) + ((3478646701170374063590 : ℝ) / 409704464650436800011) * (value_022 h H) + ((-3707390926431924717440 : ℝ) / 409704464650436800011) * (value_029 h H) + ((-15864834505 : ℝ) / 48000654118) * (value_028 h H) + ((-3478646701170374063590 : ℝ) / 409704464650436800011) * (value_030 h H)

/-- Coordinate 4.2, recovered from nonplanar cycle 3. -/
theorem value_018 (h : Assignment) (H : Constraints h) :
    h 4 2 = ((-45182599067 : ℝ) / 120001635295) * (h 1 0) + h 1 2 + ((45182599067 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 20 1
  change ((-90365198134 : ℤ) : ℝ) * (h 5 1 - h 4 1) - ((79324172525 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 20 2
  change ((-90365198134 : ℤ) : ℝ) * (h 5 2 - h 4 2) - ((-90365198134 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 21 1
  change ((3478591536904 : ℤ) : ℝ) * (h 6 1 - h 4 1) - ((437298325395 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 21 2
  change ((3478591536904 : ℤ) : ℝ) * (h 6 2 - h 4 2) - ((-601464063126 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 29 1
  change ((960013082360 : ℤ) : ℝ) * (h 7 1 - h 6 1) - ((624714567813 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 29 2
  change ((960013082360 : ℤ) : ℝ) * (h 7 2 - h 6 2) - ((-703163960298 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-233686076288 : ℝ) / 2048522323252184000055) * r0 + ((-17765652119624952205357 : ℝ) / 185115125622605602413194741897370) * r1 + ((-2639636073115269905824 : ℝ) / 890746552102995929540740108816215) * r2 + ((-4953543610719284051353 : ℝ) / 1781493104205991859081480217632430) * r3 + ((-2639636073115269905824 : ℝ) / 245826028728574682686834369941225) * r4 + ((-4953543610719284051353 : ℝ) / 491652057457149365373668739882450) * r5 + ((-45182599067 : ℝ) / 120001635295) * (value_020 h H) + ((-17765652119624952205357 : ℝ) / 2048522323252184000055) * (value_022 h H) + ((21117088584922159246592 : ℝ) / 2048522323252184000055) * (value_029 h H) + ((45182599067 : ℝ) / 120001635295) * (value_028 h H) + ((19814174442877136205412 : ℝ) / 2048522323252184000055) * (value_030 h H)

/-- Coordinate 4.3, recovered from nonplanar cycle 3. -/
theorem value_019 (h : Assignment) (H : Constraints h) :
    h 4 3 = ((-29636437161 : ℝ) / 120001635295) * (h 1 0) + h 1 3 + ((29636437161 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 20 1
  change ((-90365198134 : ℤ) : ℝ) * (h 5 1 - h 4 1) - ((79324172525 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 20 2
  change ((-90365198134 : ℤ) : ℝ) * (h 5 2 - h 4 2) - ((-90365198134 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 20 3
  change ((-90365198134 : ℤ) : ℝ) * (h 5 3 - h 4 3) - ((-59272874322 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 21 1
  change ((3478591536904 : ℤ) : ℝ) * (h 6 1 - h 4 1) - ((437298325395 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 21 2
  change ((3478591536904 : ℤ) : ℝ) * (h 6 2 - h 4 2) - ((-601464063126 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 29 1
  change ((960013082360 : ℤ) : ℝ) * (h 7 1 - h 6 1) - ((624714567813 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 29 2
  change ((960013082360 : ℤ) : ℝ) * (h 7 2 - h 6 2) - ((-703163960298 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((-2308540905103321379456 : ℝ) / 30852520937100933735532456982895) * r0 + ((-2166105048917343162466 : ℝ) / 30852520937100933735532456982895) * r1 + ((1 : ℝ) / 90365198134) * r2 + ((-577135226275830344864 : ℝ) / 296915517367665309846913369605405) * r3 + ((-1083052524458671581233 : ℝ) / 593831034735330619693826739210810) * r4 + ((-577135226275830344864 : ℝ) / 81942009576191560895611456647075) * r5 + ((-1083052524458671581233 : ℝ) / 163884019152383121791222913294150) * r6 + ((-29636437161 : ℝ) / 120001635295) * (value_020 h H) + ((-4332210097834686324932 : ℝ) / 682840774417394666685) * (value_022 h H) + (1 : ℝ) * (value_023 h H) + ((4617081810206642758912 : ℝ) / 682840774417394666685) * (value_029 h H) + ((29636437161 : ℝ) / 120001635295) * (value_028 h H) + ((4332210097834686324932 : ℝ) / 682840774417394666685) * (value_030 h H)

/-- Coordinate 6.0, recovered from nonplanar cycle 3. -/
theorem value_024 (h : Assignment) (H : Constraints h) :
    h 6 0 = ((120001635295 : ℝ) / 249882082977) * (h 1 0) + ((129880447682 : ℝ) / 249882082977) * (h 3 0) := by
  have r0 := H 20 1
  change ((-90365198134 : ℤ) : ℝ) * (h 5 1 - h 4 1) - ((79324172525 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 20 2
  change ((-90365198134 : ℤ) : ℝ) * (h 5 2 - h 4 2) - ((-90365198134 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 21 1
  change ((3478591536904 : ℤ) : ℝ) * (h 6 1 - h 4 1) - ((437298325395 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 21 2
  change ((3478591536904 : ℤ) : ℝ) * (h 6 2 - h 4 2) - ((-601464063126 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 29 1
  change ((960013082360 : ℤ) : ℝ) * (h 7 1 - h 6 1) - ((624714567813 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 29 2
  change ((960013082360 : ℤ) : ℝ) * (h 7 2 - h 6 2) - ((-703163960298 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((2040027800015 : ℝ) / 8531367491797296824466) * r0 + ((157726472517681689587765 : ℝ) / 770938713750229347308479108746444) * r1 + ((92173758173611801586005 : ℝ) / 14838571377591991186925930824546632) * r2 + ((157726472517681689587765 : ℝ) / 29677142755183982373851861649093264) * r3 + ((768104184139 : ℝ) / 34125469967189187297864) * r4 + ((1314369359467 : ℝ) / 68250939934378374595728) * r5 + ((120001635295 : ℝ) / 249882082977) * (value_020 h H) + ((157726472517681689587765 : ℝ) / 8531367491797296824466) * (value_022 h H) + ((-92173758173611801586005 : ℝ) / 4265683745898648412233) * (value_029 h H) + ((129880447682 : ℝ) / 249882082977) * (value_028 h H) + ((-157726472517681689587765 : ℝ) / 8531367491797296824466) * (value_030 h H)

/-- Coordinate 6.1, recovered from nonplanar cycle 3. -/
theorem value_025 (h : Assignment) (H : Constraints h) :
    h 6 1 = ((208238189271 : ℝ) / 666352221272) * (h 1 0) + ((-208238189271 : ℝ) / 666352221272) * (h 3 0) + h 5 1 := by
  have r0 := H 20 1
  change ((-90365198134 : ℤ) : ℝ) * (h 5 1 - h 4 1) - ((79324172525 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 20 2
  change ((-90365198134 : ℤ) : ℝ) * (h 5 2 - h 4 2) - ((-90365198134 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 21 1
  change ((3478591536904 : ℤ) : ℝ) * (h 6 1 - h 4 1) - ((437298325395 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 21 2
  change ((3478591536904 : ℤ) : ℝ) * (h 6 2 - h 4 2) - ((-601464063126 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 29 1
  change ((960013082360 : ℤ) : ℝ) * (h 7 1 - h 6 1) - ((624714567813 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 29 2
  change ((960013082360 : ℤ) : ℝ) * (h 7 2 - h 6 2) - ((-703163960298 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1180016405869 : ℝ) / 7583437770486486066192) * r0 + ((91233965149564060559519 : ℝ) / 685278856666870530940870318885728) * r1 + ((53316208158861372724223 : ℝ) / 13189841224526214388378605177374784) * r2 + ((91233965149564060559519 : ℝ) / 26379682449052428776757210354749568) * r3 + ((49524489273618129691127 : ℝ) / 3640099734464988862565086453786560) * r4 + ((91233965149564060559519 : ℝ) / 7280199468929977725130172907573120) * r5 + ((208238189271 : ℝ) / 666352221272) * (value_020 h H) + ((91233965149564060559519 : ℝ) / 7583437770486486066192) * (value_022 h H) + ((-49524489273618129691127 : ℝ) / 3791718885243243033096) * (value_029 h H) + ((-208238189271 : ℝ) / 666352221272) * (value_028 h H) + ((-91233965149564060559519 : ℝ) / 7583437770486486066192) * (value_030 h H)

/-- Coordinate 6.2, recovered from nonplanar cycle 3. -/
theorem value_026 (h : Assignment) (H : Constraints h) :
    h 6 2 = ((-117193993383 : ℝ) / 333176110636) * (h 1 0) + h 1 2 + ((117193993383 : ℝ) / 333176110636) * (h 3 0) := by
  have r0 := H 20 1
  change ((-90365198134 : ℤ) : ℝ) * (h 5 1 - h 4 1) - ((79324172525 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 20 2
  change ((-90365198134 : ℤ) : ℝ) * (h 5 2 - h 4 2) - ((-90365198134 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 21 1
  change ((3478591536904 : ℤ) : ℝ) * (h 6 1 - h 4 1) - ((437298325395 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 21 2
  change ((3478591536904 : ℤ) : ℝ) * (h 6 2 - h 4 2) - ((-601464063126 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 29 1
  change ((960013082360 : ℤ) : ℝ) * (h 7 1 - h 6 1) - ((624714567813 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 29 2
  change ((960013082360 : ℤ) : ℝ) * (h 7 2 - h 6 2) - ((-703163960298 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-664099295837 : ℝ) / 3791718885243243033096) * r0 + ((-51345398005397848802287 : ℝ) / 342639428333435265470435159442864) * r1 + ((-291317788587186341593 : ℝ) / 64028355458865118390187403773664) * r2 + ((-498499009761144163129 : ℝ) / 128056710917730236780374807547328) * r3 + ((-30005732224480193184079 : ℝ) / 1820049867232494431282543226893280) * r4 + ((-55137116890641091835383 : ℝ) / 3640099734464988862565086453786560) * r5 + ((-117193993383 : ℝ) / 333176110636) * (value_020 h H) + ((-51345398005397848802287 : ℝ) / 3791718885243243033096) * (value_022 h H) + ((30005732224480193184079 : ℝ) / 1895859442621621516548) * (value_029 h H) + ((117193993383 : ℝ) / 333176110636) * (value_028 h H) + ((55137116890641091835383 : ℝ) / 3791718885243243033096) * (value_030 h H)

/-- Coordinate 6.3, recovered from nonplanar cycle 3. -/
theorem value_027 (h : Assignment) (H : Constraints h) :
    h 6 3 = ((-19757624774 : ℝ) / 83294027659) * (h 1 0) + h 1 3 + ((19757624774 : ℝ) / 83294027659) * (h 3 0) := by
  have r0 := H 20 1
  change ((-90365198134 : ℤ) : ℝ) * (h 5 1 - h 4 1) - ((79324172525 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 20 2
  change ((-90365198134 : ℤ) : ℝ) * (h 5 2 - h 4 2) - ((-90365198134 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 20 3
  change ((-90365198134 : ℤ) : ℝ) * (h 5 3 - h 4 3) - ((-59272874322 : ℤ) : ℝ) * (h 5 0 - h 4 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 21 1
  change ((3478591536904 : ℤ) : ℝ) * (h 6 1 - h 4 1) - ((437298325395 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 21 2
  change ((3478591536904 : ℤ) : ℝ) * (h 6 2 - h 4 2) - ((-601464063126 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 21 3
  change ((3478591536904 : ℤ) : ℝ) * (h 6 3 - h 4 3) - ((-237091497288 : ℤ) : ℝ) * (h 6 0 - h 4 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 29 1
  change ((960013082360 : ℤ) : ℝ) * (h 7 1 - h 6 1) - ((624714567813 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 29 2
  change ((960013082360 : ℤ) : ℝ) * (h 7 2 - h 6 2) - ((-703163960298 : ℤ) : ℝ) * (h 7 0 - h 6 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((-12707376040955214823487 : ℝ) / 128489785625038224551413184791074) * r0 + ((-23500278402189161199359 : ℝ) / 256979571250076449102826369582148) * r1 + ((1 : ℝ) / 90365198134) * r2 + ((-12707376040955214823487 : ℝ) / 4946190459197330395641976941515544) * r3 + ((-23500278402189161199359 : ℝ) / 9892380918394660791283953883031088) * r4 + ((1 : ℝ) / 3478591536904) * r5 + ((-12707376040955214823487 : ℝ) / 1365037400424370823461907420169960) * r6 + ((-23500278402189161199359 : ℝ) / 2730074800848741646923814840339920) * r7 + ((-19757624774 : ℝ) / 83294027659) * (value_020 h H) + ((-23500278402189161199359 : ℝ) / 2843789163932432274822) * (value_022 h H) + (1 : ℝ) * (value_023 h H) + ((12707376040955214823487 : ℝ) / 1421894581966216137411) * (value_029 h H) + ((19757624774 : ℝ) / 83294027659) * (value_028 h H) + ((23500278402189161199359 : ℝ) / 2843789163932432274822) * (value_030 h H)

/-- Coordinate 8.0, recovered from nonplanar cycle 4. -/
theorem value_032 (h : Assignment) (H : Constraints h) :
    h 8 0 = ((74819036228 : ℝ) / 120001635295) * (h 1 0) + ((45182599067 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 36 1
  change ((-45182599067 : ℤ) : ℝ) * (h 9 1 - h 8 1) - ((-45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 36 2
  change ((-45182599067 : ℤ) : ℝ) * (h 9 2 - h 8 2) - ((45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 37 1
  change ((1739295768452 : ℤ) : ℝ) * (h 10 1 - h 8 1) - ((-300732031563 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 37 2
  change ((1739295768452 : ℤ) : ℝ) * (h 10 2 - h 8 2) - ((420733666858 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 47 1
  change ((480006541180 : ℤ) : ℝ) * (h 11 1 - h 10 1) - ((-351581980149 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 47 2
  change ((480006541180 : ℤ) : ℝ) * (h 11 2 - h 10 2) - ((341703167762 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((392553116348 : ℝ) / 5421985774918341269765) * r0 + ((467372152576 : ℝ) / 5421985774918341269765) * r1 + ((98138279087 : ℝ) / 52179584118978417678335) * r2 + ((116843038144 : ℝ) / 52179584118978417678335) * r3 + ((98138279087 : ℝ) / 14400392473474189737025) * r4 + ((116843038144 : ℝ) / 14400392473474189737025) * r5 + ((392553116348 : ℝ) / 120001635295) * (value_037 h H) + ((74819036228 : ℝ) / 120001635295) * (value_036 h H) + ((-392553116348 : ℝ) / 120001635295) * (value_045 h H) + ((45182599067 : ℝ) / 120001635295) * (value_044 h H) + ((-467372152576 : ℝ) / 120001635295) * (value_046 h H)

/-- Coordinate 8.1, recovered from nonplanar cycle 4. -/
theorem value_033 (h : Assignment) (H : Constraints h) :
    h 8 1 = ((-45182599067 : ℝ) / 120001635295) * (h 1 0) + h 1 1 + ((45182599067 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 36 1
  change ((-45182599067 : ℤ) : ℝ) * (h 9 1 - h 8 1) - ((-45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 36 2
  change ((-45182599067 : ℤ) : ℝ) * (h 9 2 - h 8 2) - ((45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 37 1
  change ((1739295768452 : ℤ) : ℝ) * (h 10 1 - h 8 1) - ((-300732031563 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 37 2
  change ((1739295768452 : ℤ) : ℝ) * (h 10 2 - h 8 2) - ((420733666858 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 47 1
  change ((480006541180 : ℤ) : ℝ) * (h 11 1 - h 10 1) - ((-351581980149 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 47 2
  change ((480006541180 : ℤ) : ℝ) * (h 11 2 - h 10 2) - ((341703167762 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((512554751643 : ℝ) / 5421985774918341269765) * r0 + ((467372152576 : ℝ) / 5421985774918341269765) * r1 + ((98138279087 : ℝ) / 52179584118978417678335) * r2 + ((116843038144 : ℝ) / 52179584118978417678335) * r3 + ((98138279087 : ℝ) / 14400392473474189737025) * r4 + ((116843038144 : ℝ) / 14400392473474189737025) * r5 + ((512554751643 : ℝ) / 120001635295) * (value_037 h H) + ((-45182599067 : ℝ) / 120001635295) * (value_036 h H) + ((-392553116348 : ℝ) / 120001635295) * (value_045 h H) + ((45182599067 : ℝ) / 120001635295) * (value_044 h H) + ((-467372152576 : ℝ) / 120001635295) * (value_046 h H)

/-- Coordinate 8.2, recovered from nonplanar cycle 4. -/
theorem value_034 (h : Assignment) (H : Constraints h) :
    h 8 2 = ((45182599067 : ℝ) / 120001635295) * (h 1 0) + ((-45182599067 : ℝ) / 120001635295) * (h 3 0) + h 9 2 := by
  have r0 := H 36 1
  change ((-45182599067 : ℤ) : ℝ) * (h 9 1 - h 8 1) - ((-45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 36 2
  change ((-45182599067 : ℤ) : ℝ) * (h 9 2 - h 8 2) - ((45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 37 1
  change ((1739295768452 : ℤ) : ℝ) * (h 10 1 - h 8 1) - ((-300732031563 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 37 2
  change ((1739295768452 : ℤ) : ℝ) * (h 10 2 - h 8 2) - ((420733666858 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 47 1
  change ((480006541180 : ℤ) : ℝ) * (h 11 1 - h 10 1) - ((-351581980149 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 47 2
  change ((480006541180 : ℤ) : ℝ) * (h 11 2 - h 10 2) - ((341703167762 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-392553116348 : ℝ) / 5421985774918341269765) * r0 + ((-347370517281 : ℝ) / 5421985774918341269765) * r1 + ((-98138279087 : ℝ) / 52179584118978417678335) * r2 + ((-116843038144 : ℝ) / 52179584118978417678335) * r3 + ((-98138279087 : ℝ) / 14400392473474189737025) * r4 + ((-116843038144 : ℝ) / 14400392473474189737025) * r5 + ((-392553116348 : ℝ) / 120001635295) * (value_037 h H) + ((45182599067 : ℝ) / 120001635295) * (value_036 h H) + ((392553116348 : ℝ) / 120001635295) * (value_045 h H) + ((-45182599067 : ℝ) / 120001635295) * (value_044 h H) + ((467372152576 : ℝ) / 120001635295) * (value_046 h H)

/-- Coordinate 8.3, recovered from nonplanar cycle 4. -/
theorem value_035 (h : Assignment) (H : Constraints h) :
    h 8 3 = ((-29636437161 : ℝ) / 120001635295) * (h 1 0) + h 1 3 + ((29636437161 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 36 1
  change ((-45182599067 : ℤ) : ℝ) * (h 9 1 - h 8 1) - ((-45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 36 2
  change ((-45182599067 : ℤ) : ℝ) * (h 9 2 - h 8 2) - ((45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 36 3
  change ((-45182599067 : ℤ) : ℝ) * (h 9 3 - h 8 3) - ((-29636437161 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 37 1
  change ((1739295768452 : ℤ) : ℝ) * (h 10 1 - h 8 1) - ((-300732031563 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 37 2
  change ((1739295768452 : ℤ) : ℝ) * (h 10 2 - h 8 2) - ((420733666858 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 47 1
  change ((480006541180 : ℤ) : ℝ) * (h 11 1 - h 10 1) - ((-351581980149 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 47 2
  change ((480006541180 : ℤ) : ℝ) * (h 11 2 - h 10 2) - ((341703167762 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  linear_combination ((11633875765002223808028 : ℝ) / 244979409415112718256471684309255) * r0 + ((13851245430619928276736 : ℝ) / 244979409415112718256471684309255) * r1 + ((1 : ℝ) / 45182599067) * r2 + ((2908468941250555952007 : ℝ) / 2357609228730602271586275277113445) * r3 + ((3462811357654982069184 : ℝ) / 2357609228730602271586275277113445) * r4 + ((2908468941250555952007 : ℝ) / 650647159536428747460686740355675) * r5 + ((3462811357654982069184 : ℝ) / 650647159536428747460686740355675) * r6 + ((11633875765002223808028 : ℝ) / 5421985774918341269765) * (value_037 h H) + ((-29636437161 : ℝ) / 120001635295) * (value_036 h H) + (1 : ℝ) * (value_039 h H) + ((-11633875765002223808028 : ℝ) / 5421985774918341269765) * (value_045 h H) + ((29636437161 : ℝ) / 120001635295) * (value_044 h H) + ((-13851245430619928276736 : ℝ) / 5421985774918341269765) * (value_046 h H)

/-- Coordinate 10.0, recovered from nonplanar cycle 4. -/
theorem value_040 (h : Assignment) (H : Constraints h) :
    h 10 0 = ((120001635295 : ℝ) / 249882082977) * (h 1 0) + ((129880447682 : ℝ) / 249882082977) * (h 3 0) := by
  have r0 := H 36 1
  change ((-45182599067 : ℤ) : ℝ) * (h 9 1 - h 8 1) - ((-45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 36 2
  change ((-45182599067 : ℤ) : ℝ) * (h 9 2 - h 8 2) - ((45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 37 1
  change ((1739295768452 : ℤ) : ℝ) * (h 10 1 - h 8 1) - ((-300732031563 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 37 2
  change ((1739295768452 : ℤ) : ℝ) * (h 10 2 - h 8 2) - ((420733666858 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 47 1
  change ((480006541180 : ℤ) : ℝ) * (h 11 1 - h 10 1) - ((-351581980149 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 47 2
  change ((480006541180 : ℤ) : ℝ) * (h 11 2 - h 10 2) - ((341703167762 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-720009811770 : ℝ) / 3763440656392205594153) * r0 + ((-2040027800015 : ℝ) / 11290321969176616782459) * r1 + ((-360004905885 : ℝ) / 72436474922311273806934) * r2 + ((-2040027800015 : ℝ) / 434618849533867642841604) * r3 + ((-3 : ℝ) / 166588055318) * r4 + ((-17 : ℝ) / 999528331908) * r5 + ((-720009811770 : ℝ) / 83294027659) * (value_037 h H) + ((120001635295 : ℝ) / 249882082977) * (value_036 h H) + ((720009811770 : ℝ) / 83294027659) * (value_045 h H) + ((129880447682 : ℝ) / 249882082977) * (value_044 h H) + ((2040027800015 : ℝ) / 249882082977) * (value_046 h H)

/-- Coordinate 10.1, recovered from nonplanar cycle 4. -/
theorem value_041 (h : Assignment) (H : Constraints h) :
    h 10 1 = ((-117193993383 : ℝ) / 333176110636) * (h 1 0) + h 1 1 + ((117193993383 : ℝ) / 333176110636) * (h 3 0) := by
  have r0 := H 36 1
  change ((-45182599067 : ℤ) : ℝ) * (h 9 1 - h 8 1) - ((-45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 36 2
  change ((-45182599067 : ℤ) : ℝ) * (h 9 2 - h 8 2) - ((45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 37 1
  change ((1739295768452 : ℤ) : ℝ) * (h 10 1 - h 8 1) - ((-300732031563 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 37 2
  change ((1739295768452 : ℤ) : ℝ) * (h 10 2 - h 8 2) - ((420733666858 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 47 1
  change ((480006541180 : ℤ) : ℝ) * (h 11 1 - h 10 1) - ((-351581980149 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 47 2
  change ((480006541180 : ℤ) : ℝ) * (h 11 2 - h 10 2) - ((341703167762 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((1054745940447 : ℝ) / 7526881312784411188306) * r0 + ((1992297887511 : ℝ) / 15053762625568822376612) * r1 + ((10240251849 : ℝ) / 2813066987274224225512) * r2 + ((19342697937 : ℝ) / 5626133974548448451024) * r3 + ((888157885129 : ℝ) / 79963356235095684995240) * r4 + ((1992297887511 : ℝ) / 159926712470191369990480) * r5 + ((1054745940447 : ℝ) / 166588055318) * (value_037 h H) + ((-117193993383 : ℝ) / 333176110636) * (value_036 h H) + ((-888157885129 : ℝ) / 166588055318) * (value_045 h H) + ((117193993383 : ℝ) / 333176110636) * (value_044 h H) + ((-1992297887511 : ℝ) / 333176110636) * (value_046 h H)

/-- Coordinate 10.2, recovered from nonplanar cycle 4. -/
theorem value_042 (h : Assignment) (H : Constraints h) :
    h 10 2 = ((170851583881 : ℝ) / 499764165954) * (h 1 0) + ((-170851583881 : ℝ) / 499764165954) * (h 3 0) + h 9 2 := by
  have r0 := H 36 1
  change ((-45182599067 : ℤ) : ℝ) * (h 9 1 - h 8 1) - ((-45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 36 2
  change ((-45182599067 : ℤ) : ℝ) * (h 9 2 - h 8 2) - ((45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 37 1
  change ((1739295768452 : ℤ) : ℝ) * (h 10 1 - h 8 1) - ((-300732031563 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 37 2
  change ((1739295768452 : ℤ) : ℝ) * (h 10 2 - h 8 2) - ((420733666858 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 47 1
  change ((480006541180 : ℤ) : ℝ) * (h 11 1 - h 10 1) - ((-351581980149 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 47 2
  change ((480006541180 : ℤ) : ℝ) * (h 11 2 - h 10 2) - ((341703167762 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  linear_combination ((-512554751643 : ℝ) / 3763440656392205594153) * r0 + ((-2904476925977 : ℝ) / 22580643938353233564918) * r1 + ((-46595886513 : ℝ) / 13170268167692958873988) * r2 + ((-264043356907 : ℝ) / 79021609006157753243928) * r3 + ((-512554751643 : ℝ) / 39981678117547842497620) * r4 + ((-3404241091931 : ℝ) / 239890068705287054985720) * r5 + ((-512554751643 : ℝ) / 83294027659) * (value_037 h H) + ((170851583881 : ℝ) / 499764165954) * (value_036 h H) + ((512554751643 : ℝ) / 83294027659) * (value_045 h H) + ((-170851583881 : ℝ) / 499764165954) * (value_044 h H) + ((3404241091931 : ℝ) / 499764165954) * (value_046 h H)

/-- Coordinate 10.3, recovered from nonplanar cycle 4. -/
theorem value_043 (h : Assignment) (H : Constraints h) :
    h 10 3 = ((-19757624774 : ℝ) / 83294027659) * (h 1 0) + h 1 3 + ((19757624774 : ℝ) / 83294027659) * (h 3 0) := by
  have r0 := H 36 1
  change ((-45182599067 : ℤ) : ℝ) * (h 9 1 - h 8 1) - ((-45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 36 2
  change ((-45182599067 : ℤ) : ℝ) * (h 9 2 - h 8 2) - ((45182599067 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 36 3
  change ((-45182599067 : ℤ) : ℝ) * (h 9 3 - h 8 3) - ((-29636437161 : ℤ) : ℝ) * (h 9 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 37 1
  change ((1739295768452 : ℤ) : ℝ) * (h 10 1 - h 8 1) - ((-300732031563 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 37 2
  change ((1739295768452 : ℤ) : ℝ) * (h 10 2 - h 8 2) - ((420733666858 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 37 3
  change ((1739295768452 : ℤ) : ℝ) * (h 10 3 - h 8 3) - ((-118545748644 : ℤ) : ℝ) * (h 10 0 - h 8 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 47 1
  change ((480006541180 : ℤ) : ℝ) * (h 11 1 - h 10 1) - ((-351581980149 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 47 2
  change ((480006541180 : ℤ) : ℝ) * (h 11 2 - h 10 2) - ((341703167762 : ℤ) : ℝ) * (h 11 0 - h 10 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  linear_combination ((11131538663032533873246 : ℝ) / 170042030290216336064449518455251) * r0 + ((12707376040955214823487 : ℝ) / 170042030290216336064449518455251) * r1 + ((1 : ℝ) / 45182599067) * r2 + ((5565769331516266936623 : ℝ) / 3272868204241590257392757686530578) * r3 + ((12707376040955214823487 : ℝ) / 6545736408483180514785515373061156) * r4 + ((1 : ℝ) / 1739295768452) * r5 + ((5565769331516266936623 : ℝ) / 903238066205505732380414180860270) * r6 + ((12707376040955214823487 : ℝ) / 1806476132411011464760828361720540) * r7 + ((11131538663032533873246 : ℝ) / 3763440656392205594153) * (value_037 h H) + ((-19757624774 : ℝ) / 83294027659) * (value_036 h H) + (1 : ℝ) * (value_039 h H) + ((-11131538663032533873246 : ℝ) / 3763440656392205594153) * (value_045 h H) + ((19757624774 : ℝ) / 83294027659) * (value_044 h H) + ((-12707376040955214823487 : ℝ) / 3763440656392205594153) * (value_046 h H)

/-- Coordinate 12.0, recovered from skew spokes on cycle 5. -/
theorem value_048 (h : Assignment) (H : Constraints h) :
    h 12 0 = ((74819036228 : ℝ) / 120001635295) * (h 1 0) + ((45182599067 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 38 0
  change ((1 : ℤ) : ℝ) * (h 12 0 - h 8 0) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_032 h H)

/-- Coordinate 12.1, recovered from skew spokes on cycle 5. -/
theorem value_049 (h : Assignment) (H : Constraints h) :
    h 12 1 = ((15864834505 : ℝ) / 48000654118) * (h 1 0) + ((-15864834505 : ℝ) / 48000654118) * (h 3 0) + h 5 1 := by
  have r0 := H 38 0
  change ((1 : ℤ) : ℝ) * (h 12 0 - h 8 0) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 56 1
  change ((-90365198134 : ℤ) : ℝ) * (h 13 1 - h 12 1) - ((79324172525 : ℤ) : ℝ) * (h 13 0 - h 12 0) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  linear_combination ((-79324172525 : ℝ) / 90365198134) * r0 + ((1 : ℝ) / 90365198134) * r1 + ((-79324172525 : ℝ) / 90365198134) * (value_032 h H) + (1 : ℝ) * (value_053 h H) + ((79324172525 : ℝ) / 90365198134) * (value_052 h H)

/-- Coordinate 12.2, recovered from skew spokes on cycle 5. -/
theorem value_050 (h : Assignment) (H : Constraints h) :
    h 12 2 = ((45182599067 : ℝ) / 120001635295) * (h 1 0) + ((-45182599067 : ℝ) / 120001635295) * (h 3 0) + h 9 2 := by
  have r0 := H 38 2
  change ((1 : ℤ) : ℝ) * (h 12 2 - h 8 2) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_034 h H)

/-- Coordinate 12.3, recovered from skew spokes on cycle 5. -/
theorem value_051 (h : Assignment) (H : Constraints h) :
    h 12 3 = ((-29636437161 : ℝ) / 120001635295) * (h 1 0) + h 1 3 + ((29636437161 : ℝ) / 120001635295) * (h 3 0) := by
  have r0 := H 38 3
  change ((1 : ℤ) : ℝ) * (h 12 3 - h 8 3) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  linear_combination (1 : ℝ) * r0 + (1 : ℝ) * (value_035 h H)

/-- Coordinate 49.0, recovered from skew spokes on cycle 5. -/
theorem value_196 (h : Assignment) (H : Constraints h) :
    h 49 0 = ((7713355567306296627106247603 : ℝ) / 8971371669482483594692034863) * (h 1 0) + ((-2998253794527737665871750838 : ℝ) / 8971371669482483594692034863) * (h 1 1) + ((1258016102176186967585787260 : ℝ) / 8971371669482483594692034863) * (h 3 0) + ((2998253794527737665871750838 : ℝ) / 8971371669482483594692034863) * (h 5 1) := by
  have r0 := H 38 0
  change ((1 : ℤ) : ℝ) * (h 12 0 - h 8 0) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 38 2
  change ((1 : ℤ) : ℝ) * (h 12 2 - h 8 2) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 41 1
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 1 - h 8 1) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 41 2
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 2 - h 8 2) - ((8768931170325661731634311128 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 56 1
  change ((-90365198134 : ℤ) : ℝ) * (h 13 1 - h 12 1) - ((79324172525 : ℤ) : ℝ) * (h 13 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 60 1
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 1 - h 12 1) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 60 2
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 2 - h 12 2) - ((41939996702647862210333536 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 176 1
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 1 - h 49 1) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 176 2
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 2 - h 49 2) - ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((341431078601979532407586671052659688806214635366040753041123882751 : ℝ) / 5384592902854199087493576502488437139457895928676918539022839624) * r0 + ((-2289593089891036589809366201483294279457361007637197661 : ℝ) / 59587020380008887454353672567674172698537735590120236) * r1 + ((-9 : ℝ) / 143541946711719737515072557808) * r2 + ((233674509738096693004220441807 : ℝ) / 32415339086724834775168397876814749948004528161025408384) * r3 + ((1499126897263868832935875419 : ℝ) / 405349889223269495638375140553315272821) * r4 + ((6783379625628365759890839 : ℝ) / 517288243996393696668323762405130519446756016685976) * r5 + ((-176122545376233583831489707806407252265950846741322897 : ℝ) / 116816541915761093255536385970554483279118066430056201402003938871072844506048) * r6 + ((9798215014796528319842323 : ℝ) / 331509963494489205190590498206412475109831624157139830960) * r7 + ((-2289593089891036589809366201483294279457361007637197661 : ℝ) / 673768700447883496212583847084444272074804736741086095633633619325527313007424462720) * r8 + ((286432888587842413885599356554652609846 : ℝ) / 405349889223269495638375140553315272821) * (value_032 h H) + ((-2998253794527737665871750838 : ℝ) / 8971371669482483594692034863) * (value_033 h H) + ((2998253794527737665871750838 : ℝ) / 8971371669482483594692034863) * (value_053 h H) + ((118917000635427081752775783998662662975 : ℝ) / 405349889223269495638375140553315272821) * (value_052 h H)

/-- Coordinate 49.1, recovered from skew spokes on cycle 5. -/
theorem value_197 (h : Assignment) (H : Constraints h) :
    h 49 1 = ((-4393522730936721890853175693 : ℝ) / 287083893423439475030145115616) * (h 1 0) + ((70208145694016106016574415265 : ℝ) / 143541946711719737515072557808) * (h 1 1) + ((4393522730936721890853175693 : ℝ) / 287083893423439475030145115616) * (h 3 0) + ((73333801017703631498498142543 : ℝ) / 143541946711719737515072557808) * (h 5 1) := by
  have r0 := H 38 0
  change ((1 : ℤ) : ℝ) * (h 12 0 - h 8 0) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 38 2
  change ((1 : ℤ) : ℝ) * (h 12 2 - h 8 2) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 41 1
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 1 - h 8 1) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 41 2
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 2 - h 8 2) - ((8768931170325661731634311128 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 56 1
  change ((-90365198134 : ℤ) : ℝ) * (h 13 1 - h 12 1) - ((79324172525 : ℤ) : ℝ) * (h 13 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 60 1
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 1 - h 12 1) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 60 2
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 2 - h 12 2) - ((41939996702647862210333536 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 176 1
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 1 - h 49 1) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 176 2
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 2 - h 49 2) - ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((94644747336523845518827249565904507457675991779024061344347736346033 : ℝ) / 976406179717561434532168539117903267955031795066747895076141585152) * r0 + ((-634675555557149348686113836998555015486773848796308240563 : ℝ) / 10805113028908278258389465958938249982668176053675136128) * r1 + ((70208145694016106016574415265 : ℝ) / 765111442492999145211698921560587809982357294613204343296) * r2 + ((48821196581319180668162602846042693498982603753562172351 : ℝ) / 4430286651517995500250314837047342146312553641177150256719640149260949609483497472) * r3 + ((73333801017703631498498142543 : ℝ) / 12971196455144623860428004497706088730272) * r4 + ((5641061616746433192192164811 : ℝ) / 281404804734038170987568126748391002579035273077170944) * r5 + ((-48821196581319180668162602846042693498982603753562172351 : ℝ) / 21182732934058011577003931322660546301280076045983524520896714248621209137096704) * r6 + ((2716066704359393759203634909 : ℝ) / 60113806713667375874560410341429462153249467847161356014080) * r7 + ((-634675555557149348686113836998555015486773848796308240563 : ℝ) / 122176724347882873979881870937979228002897925595716945341565562971028952758679635906560) * r8 + ((-5817143083842343444305890937472974231075 : ℝ) / 12971196455144623860428004497706088730272) * (value_032 h H) + ((70208145694016106016574415265 : ℝ) / 143541946711719737515072557808) * (value_033 h H) + ((73333801017703631498498142543 : ℝ) / 143541946711719737515072557808) * (value_053 h H) + ((5817143083842343444305890937472974231075 : ℝ) / 12971196455144623860428004497706088730272) * (value_052 h H)

/-- Coordinate 49.2, recovered from skew spokes on cycle 5. -/
theorem value_198 (h : Assignment) (H : Constraints h) :
    h 49 2 = ((2496476032402122435583484089 : ℝ) / 3262316970720903125342558132) * (h 1 0) + ((-896822506056033586189872729 : ℝ) / 1631158485360451562671279066) * (h 1 1) + ((-2496476032402122435583484089 : ℝ) / 3262316970720903125342558132) * (h 3 0) + ((896822506056033586189872729 : ℝ) / 1631158485360451562671279066) * (h 5 1) + h 9 2 := by
  have r0 := H 38 0
  change ((1 : ℤ) : ℝ) * (h 12 0 - h 8 0) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r0
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r0
  have r1 := H 38 2
  change ((1 : ℤ) : ℝ) * (h 12 2 - h 8 2) - ((0 : ℤ) : ℝ) * (h 12 1 - h 8 1) = 0 at r1
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r1
  have r2 := H 41 1
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 1 - h 8 1) - ((8148200113078181277610904727 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r2
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r2
  have r3 := H 41 2
  change ((5330228968049311405994223712 : ℤ) : ℝ) * (h 49 2 - h 8 2) - ((8768931170325661731634311128 : ℤ) : ℝ) * (h 49 0 - h 8 0) = 0 at r3
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r3
  have r4 := H 56 1
  change ((-90365198134 : ℤ) : ℝ) * (h 13 1 - h 12 1) - ((79324172525 : ℤ) : ℝ) * (h 13 0 - h 12 0) = 0 at r4
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r4
  have r5 := H 60 1
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 1 - h 12 1) - ((-35838253802164934597252055 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r5
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r5
  have r6 := H 60 2
  change ((25485668442894336741578384 : ℤ) : ℝ) * (h 53 2 - h 12 2) - ((41939996702647862210333536 : ℤ) : ℝ) * (h 53 0 - h 12 0) = 0 at r6
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r6
  have r7 := H 176 1
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 1 - h 49 1) - ((55449466212165971820005818475369 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r7
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r7
  have r8 := H 176 2
  change ((-11307306459544487178846274415520 : ℤ) : ℝ) * (h 53 2 - h 49 2) - ((-18263665793014896455620431974136 : ℤ) : ℝ) * (h 53 0 - h 49 0) = 0 at r8
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r8
  linear_combination ((204254273681639861716580299729272775879455870748819217047323448741 : ℝ) / 1958033782856072395452209637268522596166507610427970377826487136) * r0 + ((-1369703002776045102432310722766392073186516821604449551 : ℝ) / 21668007410912322710674062751881517344922812941861904) * r1 + ((-52754265062119622717051337 : ℝ) / 511438130008689268189638316551195060148634555222730176) * r2 + ((107028539245150571164844983501405660810110741118947035 : ℝ) / 8884264675504001671624962908517397352231056767066477787539385326058054029712896) * r3 + ((896822506056033586189872729 : ℝ) / 147399959717552543868500051110296462844) * r4 + ((52754265062119622717051337 : ℝ) / 2445362607982952020613894149551526091930119351606432) * r5 + ((-1369703002776045102432310722766392073186516821604449551 : ℝ) / 552223652692688804480717460951712102774012677669356588445836801935980719483136) * r6 + ((5861585006902180301894593 : ℝ) / 120549077634359710978396544802331809130847863329869029440) * r7 + ((-1369703002776045102432310722766392073186516821604449551 : ℝ) / 245006800162866725895485035303434280754474449724031307503139497936555386548154350080) * r8 + ((-71139703194691665508119921762988570725 : ℝ) / 147399959717552543868500051110296462844) * (value_032 h H) + (1 : ℝ) * (value_034 h H) + ((-896822506056033586189872729 : ℝ) / 1631158485360451562671279066) * (value_033 h H) + ((896822506056033586189872729 : ℝ) / 1631158485360451562671279066) * (value_053 h H) + ((71139703194691665508119921762988570725 : ℝ) / 147399959717552543868500051110296462844) * (value_052 h H)

end CubicalIndecomposability.Rigidity
