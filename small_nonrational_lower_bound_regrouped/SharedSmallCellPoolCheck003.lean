module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check003.part384 : Interval test 384 400 :=
  interval_of_check _ 384 16 (by decide +kernel)
theorem Check003.part400 : Interval test 400 416 :=
  interval_of_check _ 400 16 (by decide +kernel)
theorem Check003.part416 : Interval test 416 432 :=
  interval_of_check _ 416 16 (by decide +kernel)
theorem Check003.part432 : Interval test 432 448 :=
  interval_of_check _ 432 16 (by decide +kernel)
theorem Check003.part448 : Interval test 448 464 :=
  interval_of_check _ 448 16 (by decide +kernel)
theorem Check003.part464 : Interval test 464 480 :=
  interval_of_check _ 464 16 (by decide +kernel)
theorem Check003.part480 : Interval test 480 496 :=
  interval_of_check _ 480 16 (by decide +kernel)
theorem Check003.part496 : Interval test 496 512 :=
  interval_of_check _ 496 16 (by decide +kernel)
theorem Check003.checked : Interval test 384 512 :=
  (FiniteChecks.interval_append test 384 448 512
  (FiniteChecks.interval_append test 384 416 448
  (FiniteChecks.interval_append test 384 400 416
  Check003.part384
  Check003.part400)
  (FiniteChecks.interval_append test 416 432 448
  Check003.part416
  Check003.part432))
  (FiniteChecks.interval_append test 448 480 512
  (FiniteChecks.interval_append test 448 464 480
  Check003.part448
  Check003.part464)
  (FiniteChecks.interval_append test 480 496 512
  Check003.part480
  Check003.part496)))
#print axioms Check003.checked
end Papers.RationalityTen.SharedSmallCellPool
