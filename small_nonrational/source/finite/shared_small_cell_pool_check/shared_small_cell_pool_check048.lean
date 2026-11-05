module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check048.part6144 : Interval test 6144 6160 :=
  interval_of_check _ 6144 16 (by decide +kernel)
theorem Check048.part6160 : Interval test 6160 6176 :=
  interval_of_check _ 6160 16 (by decide +kernel)
theorem Check048.part6176 : Interval test 6176 6192 :=
  interval_of_check _ 6176 16 (by decide +kernel)
theorem Check048.part6192 : Interval test 6192 6208 :=
  interval_of_check _ 6192 16 (by decide +kernel)
theorem Check048.part6208 : Interval test 6208 6224 :=
  interval_of_check _ 6208 16 (by decide +kernel)
theorem Check048.part6224 : Interval test 6224 6240 :=
  interval_of_check _ 6224 16 (by decide +kernel)
theorem Check048.part6240 : Interval test 6240 6256 :=
  interval_of_check _ 6240 16 (by decide +kernel)
theorem Check048.part6256 : Interval test 6256 6272 :=
  interval_of_check _ 6256 16 (by decide +kernel)
theorem Check048.checked : Interval test 6144 6272 :=
  (FiniteChecks.interval_append test 6144 6208 6272
  (FiniteChecks.interval_append test 6144 6176 6208
  (FiniteChecks.interval_append test 6144 6160 6176
  Check048.part6144
  Check048.part6160)
  (FiniteChecks.interval_append test 6176 6192 6208
  Check048.part6176
  Check048.part6192))
  (FiniteChecks.interval_append test 6208 6240 6272
  (FiniteChecks.interval_append test 6208 6224 6240
  Check048.part6208
  Check048.part6224)
  (FiniteChecks.interval_append test 6240 6256 6272
  Check048.part6240
  Check048.part6256)))
#print axioms Check048.checked
end Papers.RationalityTen.SharedSmallCellPool
