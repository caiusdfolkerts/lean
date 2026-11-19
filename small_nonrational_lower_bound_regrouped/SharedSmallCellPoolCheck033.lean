module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check033.part4224 : Interval test 4224 4240 :=
  interval_of_check _ 4224 16 (by decide +kernel)
theorem Check033.part4240 : Interval test 4240 4256 :=
  interval_of_check _ 4240 16 (by decide +kernel)
theorem Check033.part4256 : Interval test 4256 4272 :=
  interval_of_check _ 4256 16 (by decide +kernel)
theorem Check033.part4272 : Interval test 4272 4288 :=
  interval_of_check _ 4272 16 (by decide +kernel)
theorem Check033.part4288 : Interval test 4288 4304 :=
  interval_of_check _ 4288 16 (by decide +kernel)
theorem Check033.part4304 : Interval test 4304 4320 :=
  interval_of_check _ 4304 16 (by decide +kernel)
theorem Check033.part4320 : Interval test 4320 4336 :=
  interval_of_check _ 4320 16 (by decide +kernel)
theorem Check033.part4336 : Interval test 4336 4352 :=
  interval_of_check _ 4336 16 (by decide +kernel)
theorem Check033.checked : Interval test 4224 4352 :=
  (FiniteChecks.interval_append test 4224 4288 4352
  (FiniteChecks.interval_append test 4224 4256 4288
  (FiniteChecks.interval_append test 4224 4240 4256
  Check033.part4224
  Check033.part4240)
  (FiniteChecks.interval_append test 4256 4272 4288
  Check033.part4256
  Check033.part4272))
  (FiniteChecks.interval_append test 4288 4320 4352
  (FiniteChecks.interval_append test 4288 4304 4320
  Check033.part4288
  Check033.part4304)
  (FiniteChecks.interval_append test 4320 4336 4352
  Check033.part4320
  Check033.part4336)))
#print axioms Check033.checked
end Papers.RationalityTen.SharedSmallCellPool
