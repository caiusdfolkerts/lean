module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check029.part3712 : Interval test 3712 3728 :=
  interval_of_check _ 3712 16 (by decide +kernel)
theorem Check029.part3728 : Interval test 3728 3744 :=
  interval_of_check _ 3728 16 (by decide +kernel)
theorem Check029.part3744 : Interval test 3744 3760 :=
  interval_of_check _ 3744 16 (by decide +kernel)
theorem Check029.part3760 : Interval test 3760 3776 :=
  interval_of_check _ 3760 16 (by decide +kernel)
theorem Check029.part3776 : Interval test 3776 3792 :=
  interval_of_check _ 3776 16 (by decide +kernel)
theorem Check029.part3792 : Interval test 3792 3808 :=
  interval_of_check _ 3792 16 (by decide +kernel)
theorem Check029.part3808 : Interval test 3808 3824 :=
  interval_of_check _ 3808 16 (by decide +kernel)
theorem Check029.part3824 : Interval test 3824 3840 :=
  interval_of_check _ 3824 16 (by decide +kernel)
theorem Check029.checked : Interval test 3712 3840 :=
  (FiniteChecks.interval_append test 3712 3776 3840
  (FiniteChecks.interval_append test 3712 3744 3776
  (FiniteChecks.interval_append test 3712 3728 3744
  Check029.part3712
  Check029.part3728)
  (FiniteChecks.interval_append test 3744 3760 3776
  Check029.part3744
  Check029.part3760))
  (FiniteChecks.interval_append test 3776 3808 3840
  (FiniteChecks.interval_append test 3776 3792 3808
  Check029.part3776
  Check029.part3792)
  (FiniteChecks.interval_append test 3808 3824 3840
  Check029.part3808
  Check029.part3824)))
#print axioms Check029.checked
end Papers.RationalityTen.SharedSmallCellPool
