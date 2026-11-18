module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check049.part6272 : Interval test 6272 6288 :=
  interval_of_check _ 6272 16 (by decide +kernel)
theorem Check049.part6288 : Interval test 6288 6304 :=
  interval_of_check _ 6288 16 (by decide +kernel)
theorem Check049.part6304 : Interval test 6304 6320 :=
  interval_of_check _ 6304 16 (by decide +kernel)
theorem Check049.part6320 : Interval test 6320 6336 :=
  interval_of_check _ 6320 16 (by decide +kernel)
theorem Check049.part6336 : Interval test 6336 6352 :=
  interval_of_check _ 6336 16 (by decide +kernel)
theorem Check049.part6352 : Interval test 6352 6368 :=
  interval_of_check _ 6352 16 (by decide +kernel)
theorem Check049.part6368 : Interval test 6368 6384 :=
  interval_of_check _ 6368 16 (by decide +kernel)
theorem Check049.part6384 : Interval test 6384 6400 :=
  interval_of_check _ 6384 16 (by decide +kernel)
theorem Check049.checked : Interval test 6272 6400 :=
  (FiniteChecks.interval_append test 6272 6336 6400
  (FiniteChecks.interval_append test 6272 6304 6336
  (FiniteChecks.interval_append test 6272 6288 6304
  Check049.part6272
  Check049.part6288)
  (FiniteChecks.interval_append test 6304 6320 6336
  Check049.part6304
  Check049.part6320))
  (FiniteChecks.interval_append test 6336 6368 6400
  (FiniteChecks.interval_append test 6336 6352 6368
  Check049.part6336
  Check049.part6352)
  (FiniteChecks.interval_append test 6368 6384 6400
  Check049.part6368
  Check049.part6384)))
#print axioms Check049.checked
end Papers.RationalityTen.SharedSmallCellPool
