module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check026.part3328 : Interval test 3328 3344 :=
  interval_of_check _ 3328 16 (by decide +kernel)
theorem Check026.part3344 : Interval test 3344 3360 :=
  interval_of_check _ 3344 16 (by decide +kernel)
theorem Check026.part3360 : Interval test 3360 3376 :=
  interval_of_check _ 3360 16 (by decide +kernel)
theorem Check026.part3376 : Interval test 3376 3392 :=
  interval_of_check _ 3376 16 (by decide +kernel)
theorem Check026.part3392 : Interval test 3392 3408 :=
  interval_of_check _ 3392 16 (by decide +kernel)
theorem Check026.part3408 : Interval test 3408 3424 :=
  interval_of_check _ 3408 16 (by decide +kernel)
theorem Check026.part3424 : Interval test 3424 3440 :=
  interval_of_check _ 3424 16 (by decide +kernel)
theorem Check026.part3440 : Interval test 3440 3456 :=
  interval_of_check _ 3440 16 (by decide +kernel)
theorem Check026.checked : Interval test 3328 3456 :=
  (FiniteChecks.interval_append test 3328 3392 3456
  (FiniteChecks.interval_append test 3328 3360 3392
  (FiniteChecks.interval_append test 3328 3344 3360
  Check026.part3328
  Check026.part3344)
  (FiniteChecks.interval_append test 3360 3376 3392
  Check026.part3360
  Check026.part3376))
  (FiniteChecks.interval_append test 3392 3424 3456
  (FiniteChecks.interval_append test 3392 3408 3424
  Check026.part3392
  Check026.part3408)
  (FiniteChecks.interval_append test 3424 3440 3456
  Check026.part3424
  Check026.part3440)))
#print axioms Check026.checked
end Papers.RationalityTen.SharedSmallCellPool
