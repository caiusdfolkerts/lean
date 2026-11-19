module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check004.part512 : Interval test 512 528 :=
  interval_of_check _ 512 16 (by decide +kernel)
theorem Check004.part528 : Interval test 528 544 :=
  interval_of_check _ 528 16 (by decide +kernel)
theorem Check004.part544 : Interval test 544 560 :=
  interval_of_check _ 544 16 (by decide +kernel)
theorem Check004.part560 : Interval test 560 576 :=
  interval_of_check _ 560 16 (by decide +kernel)
theorem Check004.part576 : Interval test 576 592 :=
  interval_of_check _ 576 16 (by decide +kernel)
theorem Check004.part592 : Interval test 592 608 :=
  interval_of_check _ 592 16 (by decide +kernel)
theorem Check004.part608 : Interval test 608 624 :=
  interval_of_check _ 608 16 (by decide +kernel)
theorem Check004.part624 : Interval test 624 640 :=
  interval_of_check _ 624 16 (by decide +kernel)
theorem Check004.checked : Interval test 512 640 :=
  (FiniteChecks.interval_append test 512 576 640
  (FiniteChecks.interval_append test 512 544 576
  (FiniteChecks.interval_append test 512 528 544
  Check004.part512
  Check004.part528)
  (FiniteChecks.interval_append test 544 560 576
  Check004.part544
  Check004.part560))
  (FiniteChecks.interval_append test 576 608 640
  (FiniteChecks.interval_append test 576 592 608
  Check004.part576
  Check004.part592)
  (FiniteChecks.interval_append test 608 624 640
  Check004.part608
  Check004.part624)))
#print axioms Check004.checked
end Papers.RationalityTen.SharedSmallCellPool
