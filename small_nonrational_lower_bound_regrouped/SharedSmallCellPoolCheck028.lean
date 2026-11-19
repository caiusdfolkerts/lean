module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check028.part3584 : Interval test 3584 3600 :=
  interval_of_check _ 3584 16 (by decide +kernel)
theorem Check028.part3600 : Interval test 3600 3616 :=
  interval_of_check _ 3600 16 (by decide +kernel)
theorem Check028.part3616 : Interval test 3616 3632 :=
  interval_of_check _ 3616 16 (by decide +kernel)
theorem Check028.part3632 : Interval test 3632 3648 :=
  interval_of_check _ 3632 16 (by decide +kernel)
theorem Check028.part3648 : Interval test 3648 3664 :=
  interval_of_check _ 3648 16 (by decide +kernel)
theorem Check028.part3664 : Interval test 3664 3680 :=
  interval_of_check _ 3664 16 (by decide +kernel)
theorem Check028.part3680 : Interval test 3680 3696 :=
  interval_of_check _ 3680 16 (by decide +kernel)
theorem Check028.part3696 : Interval test 3696 3712 :=
  interval_of_check _ 3696 16 (by decide +kernel)
theorem Check028.checked : Interval test 3584 3712 :=
  (FiniteChecks.interval_append test 3584 3648 3712
  (FiniteChecks.interval_append test 3584 3616 3648
  (FiniteChecks.interval_append test 3584 3600 3616
  Check028.part3584
  Check028.part3600)
  (FiniteChecks.interval_append test 3616 3632 3648
  Check028.part3616
  Check028.part3632))
  (FiniteChecks.interval_append test 3648 3680 3712
  (FiniteChecks.interval_append test 3648 3664 3680
  Check028.part3648
  Check028.part3664)
  (FiniteChecks.interval_append test 3680 3696 3712
  Check028.part3680
  Check028.part3696)))
#print axioms Check028.checked
end Papers.RationalityTen.SharedSmallCellPool
