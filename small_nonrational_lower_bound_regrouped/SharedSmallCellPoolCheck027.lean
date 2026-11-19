module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check027.part3456 : Interval test 3456 3472 :=
  interval_of_check _ 3456 16 (by decide +kernel)
theorem Check027.part3472 : Interval test 3472 3488 :=
  interval_of_check _ 3472 16 (by decide +kernel)
theorem Check027.part3488 : Interval test 3488 3504 :=
  interval_of_check _ 3488 16 (by decide +kernel)
theorem Check027.part3504 : Interval test 3504 3520 :=
  interval_of_check _ 3504 16 (by decide +kernel)
theorem Check027.part3520 : Interval test 3520 3536 :=
  interval_of_check _ 3520 16 (by decide +kernel)
theorem Check027.part3536 : Interval test 3536 3552 :=
  interval_of_check _ 3536 16 (by decide +kernel)
theorem Check027.part3552 : Interval test 3552 3568 :=
  interval_of_check _ 3552 16 (by decide +kernel)
theorem Check027.part3568 : Interval test 3568 3584 :=
  interval_of_check _ 3568 16 (by decide +kernel)
theorem Check027.checked : Interval test 3456 3584 :=
  (FiniteChecks.interval_append test 3456 3520 3584
  (FiniteChecks.interval_append test 3456 3488 3520
  (FiniteChecks.interval_append test 3456 3472 3488
  Check027.part3456
  Check027.part3472)
  (FiniteChecks.interval_append test 3488 3504 3520
  Check027.part3488
  Check027.part3504))
  (FiniteChecks.interval_append test 3520 3552 3584
  (FiniteChecks.interval_append test 3520 3536 3552
  Check027.part3520
  Check027.part3536)
  (FiniteChecks.interval_append test 3552 3568 3584
  Check027.part3552
  Check027.part3568)))
#print axioms Check027.checked
end Papers.RationalityTen.SharedSmallCellPool
