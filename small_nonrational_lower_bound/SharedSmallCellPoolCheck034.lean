module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check034.part4352 : Interval test 4352 4368 :=
  interval_of_check _ 4352 16 (by decide +kernel)
theorem Check034.part4368 : Interval test 4368 4384 :=
  interval_of_check _ 4368 16 (by decide +kernel)
theorem Check034.part4384 : Interval test 4384 4400 :=
  interval_of_check _ 4384 16 (by decide +kernel)
theorem Check034.part4400 : Interval test 4400 4416 :=
  interval_of_check _ 4400 16 (by decide +kernel)
theorem Check034.part4416 : Interval test 4416 4432 :=
  interval_of_check _ 4416 16 (by decide +kernel)
theorem Check034.part4432 : Interval test 4432 4448 :=
  interval_of_check _ 4432 16 (by decide +kernel)
theorem Check034.part4448 : Interval test 4448 4464 :=
  interval_of_check _ 4448 16 (by decide +kernel)
theorem Check034.part4464 : Interval test 4464 4480 :=
  interval_of_check _ 4464 16 (by decide +kernel)
theorem Check034.checked : Interval test 4352 4480 :=
  (FiniteChecks.interval_append test 4352 4416 4480
  (FiniteChecks.interval_append test 4352 4384 4416
  (FiniteChecks.interval_append test 4352 4368 4384
  Check034.part4352
  Check034.part4368)
  (FiniteChecks.interval_append test 4384 4400 4416
  Check034.part4384
  Check034.part4400))
  (FiniteChecks.interval_append test 4416 4448 4480
  (FiniteChecks.interval_append test 4416 4432 4448
  Check034.part4416
  Check034.part4432)
  (FiniteChecks.interval_append test 4448 4464 4480
  Check034.part4448
  Check034.part4464)))
#print axioms Check034.checked
end Papers.RationalityTen.SharedSmallCellPool
