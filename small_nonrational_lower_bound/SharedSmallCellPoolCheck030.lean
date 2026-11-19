module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check030.part3840 : Interval test 3840 3856 :=
  interval_of_check _ 3840 16 (by decide +kernel)
theorem Check030.part3856 : Interval test 3856 3872 :=
  interval_of_check _ 3856 16 (by decide +kernel)
theorem Check030.part3872 : Interval test 3872 3888 :=
  interval_of_check _ 3872 16 (by decide +kernel)
theorem Check030.part3888 : Interval test 3888 3904 :=
  interval_of_check _ 3888 16 (by decide +kernel)
theorem Check030.part3904 : Interval test 3904 3920 :=
  interval_of_check _ 3904 16 (by decide +kernel)
theorem Check030.part3920 : Interval test 3920 3936 :=
  interval_of_check _ 3920 16 (by decide +kernel)
theorem Check030.part3936 : Interval test 3936 3952 :=
  interval_of_check _ 3936 16 (by decide +kernel)
theorem Check030.part3952 : Interval test 3952 3968 :=
  interval_of_check _ 3952 16 (by decide +kernel)
theorem Check030.checked : Interval test 3840 3968 :=
  (FiniteChecks.interval_append test 3840 3904 3968
  (FiniteChecks.interval_append test 3840 3872 3904
  (FiniteChecks.interval_append test 3840 3856 3872
  Check030.part3840
  Check030.part3856)
  (FiniteChecks.interval_append test 3872 3888 3904
  Check030.part3872
  Check030.part3888))
  (FiniteChecks.interval_append test 3904 3936 3968
  (FiniteChecks.interval_append test 3904 3920 3936
  Check030.part3904
  Check030.part3920)
  (FiniteChecks.interval_append test 3936 3952 3968
  Check030.part3936
  Check030.part3952)))
#print axioms Check030.checked
end Papers.RationalityTen.SharedSmallCellPool
