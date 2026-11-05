import cubical_indecomposability.rigidity.values07

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CubicalIndecomposability.Rigidity

theorem residual0 (h : Assignment) (H : Constraints h) :
    ((-89453649138583686649772245 : ℝ) / 6) * (h 1 0) + (119012246245246122238392639 : ℝ) * (h 1 1) + ((-624619828332893046780583589 : ℝ) / 6) * (h 1 2) + ((89453649138583686649772245 : ℝ) / 6) * (h 3 0) + (-119012246245246122238392639 : ℝ) * (h 5 1) + ((624619828332893046780583589 : ℝ) / 6) * (h 9 2) = 0 := by
  have r := H 50 1
  change ((-13686096792730261051639696 : ℤ) : ℝ) * (h 43 1 - h 10 1) - ((66289502033667579980694885 : ℤ) : ℝ) * (h 43 0 - h 10 0) = 0 at r
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r
  linear_combination r + (13686096792730261051639696 : ℝ) * (value_173 h H) + (-13686096792730261051639696 : ℝ) * (value_041 h H) + (66289502033667579980694885 : ℝ) * (value_172 h H) + (-66289502033667579980694885 : ℝ) * (value_040 h H)

theorem residual1 (h : Assignment) (H : Constraints h) :
    ((938188934778543954396183172 : ℝ) / 13) * (h 1 0) + ((134360806350600939919752260 : ℝ) / 13) * (h 1 1) + ((-1072549741129144894315935432 : ℝ) / 13) * (h 1 2) + ((-938188934778543954396183172 : ℝ) / 13) * (h 3 0) + ((-134360806350600939919752260 : ℝ) / 13) * (h 5 1) + ((1072549741129144894315935432 : ℝ) / 13) * (h 9 2) = 0 := by
  have r := H 243 1
  change ((41003288748152153775469552 : ℤ) : ℝ) * (h 111 1 - h 81 1) - ((-13686096792730261051639696 : ℤ) : ℝ) * (h 111 0 - h 81 0) = 0 at r
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_zero, Int.cast_one] at r
  linear_combination r + (-41003288748152153775469552 : ℝ) * (value_445 h H) + (41003288748152153775469552 : ℝ) * (value_325 h H) + (-13686096792730261051639696 : ℝ) * (value_444 h H) + (13686096792730261051639696 : ℝ) * (value_324 h H)

/-- The explicit plane condition on the three interface scales. -/
theorem cube_scale_relation0 (h : Assignment) (H : Constraints h) :
    (115 : ℝ) * (h 3 0 - h 1 0) + (-918 : ℝ) * (h 5 1 - h 1 1) + (803 : ℝ) * (h 9 2 - h 1 2) = 0 := by
  linear_combination ((6 : ℝ) / 777857818596379883911063) * (residual0 h H)

/-- The explicit plane condition on the three interface scales. -/
theorem cube_scale_relation1 (h : Assignment) (H : Constraints h) :
    (-803 : ℝ) * (h 3 0 - h 1 0) + (-115 : ℝ) * (h 5 1 - h 1 1) + (918 : ℝ) * (h 9 2 - h 1 2) = 0 := by
  linear_combination ((13 : ℝ) / 1168354837831312521041324) * (residual1 h H)

/-- The surviving cube scales must agree (relation 1). -/
theorem scales0 (h : Assignment) (H : Constraints h) :
    h 1 0 + (-1 : ℝ) * (h 1 1) + (-1 : ℝ) * (h 3 0) + h 5 1 = 0 := by
  linear_combination ((-918 : ℝ) / 750379) * (cube_scale_relation0 h H) + ((803 : ℝ) / 750379) * (cube_scale_relation1 h H)

/-- The surviving cube scales must agree (relation 2). -/
theorem scales1 (h : Assignment) (H : Constraints h) :
    h 1 0 + (-1 : ℝ) * (h 1 2) + (-1 : ℝ) * (h 3 0) + h 9 2 = 0 := by
  linear_combination ((-115 : ℝ) / 750379) * (cube_scale_relation0 h H) + ((918 : ℝ) / 750379) * (cube_scale_relation1 h H)

end CubicalIndecomposability.Rigidity
