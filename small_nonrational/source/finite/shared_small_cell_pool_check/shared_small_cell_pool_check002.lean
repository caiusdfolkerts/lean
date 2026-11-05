module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check002.part256 : Interval test 256 272 :=
  interval_of_check _ 256 16 (by decide +kernel)
theorem Check002.part272 : Interval test 272 288 :=
  interval_of_check _ 272 16 (by decide +kernel)
theorem Check002.part288 : Interval test 288 304 :=
  interval_of_check _ 288 16 (by decide +kernel)
theorem Check002.part304 : Interval test 304 320 :=
  interval_of_check _ 304 16 (by decide +kernel)
theorem Check002.part320 : Interval test 320 336 :=
  interval_of_check _ 320 16 (by decide +kernel)
theorem Check002.part336 : Interval test 336 352 :=
  interval_of_check _ 336 16 (by decide +kernel)
theorem Check002.part352 : Interval test 352 368 :=
  interval_of_check _ 352 16 (by decide +kernel)
theorem Check002.part368 : Interval test 368 384 :=
  interval_of_check _ 368 16 (by decide +kernel)
theorem Check002.checked : Interval test 256 384 :=
  (FiniteChecks.interval_append test 256 320 384
  (FiniteChecks.interval_append test 256 288 320
  (FiniteChecks.interval_append test 256 272 288
  Check002.part256
  Check002.part272)
  (FiniteChecks.interval_append test 288 304 320
  Check002.part288
  Check002.part304))
  (FiniteChecks.interval_append test 320 352 384
  (FiniteChecks.interval_append test 320 336 352
  Check002.part320
  Check002.part336)
  (FiniteChecks.interval_append test 352 368 384
  Check002.part352
  Check002.part368)))
#print axioms Check002.checked
end Papers.RationalityTen.SharedSmallCellPool
