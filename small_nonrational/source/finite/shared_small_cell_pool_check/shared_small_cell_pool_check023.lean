module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check023.part2944 : Interval test 2944 2960 :=
  interval_of_check _ 2944 16 (by decide +kernel)
theorem Check023.part2960 : Interval test 2960 2976 :=
  interval_of_check _ 2960 16 (by decide +kernel)
theorem Check023.part2976 : Interval test 2976 2992 :=
  interval_of_check _ 2976 16 (by decide +kernel)
theorem Check023.part2992 : Interval test 2992 3008 :=
  interval_of_check _ 2992 16 (by decide +kernel)
theorem Check023.part3008 : Interval test 3008 3024 :=
  interval_of_check _ 3008 16 (by decide +kernel)
theorem Check023.part3024 : Interval test 3024 3040 :=
  interval_of_check _ 3024 16 (by decide +kernel)
theorem Check023.part3040 : Interval test 3040 3056 :=
  interval_of_check _ 3040 16 (by decide +kernel)
theorem Check023.part3056 : Interval test 3056 3072 :=
  interval_of_check _ 3056 16 (by decide +kernel)
theorem Check023.checked : Interval test 2944 3072 :=
  (FiniteChecks.interval_append test 2944 3008 3072
  (FiniteChecks.interval_append test 2944 2976 3008
  (FiniteChecks.interval_append test 2944 2960 2976
  Check023.part2944
  Check023.part2960)
  (FiniteChecks.interval_append test 2976 2992 3008
  Check023.part2976
  Check023.part2992))
  (FiniteChecks.interval_append test 3008 3040 3072
  (FiniteChecks.interval_append test 3008 3024 3040
  Check023.part3008
  Check023.part3024)
  (FiniteChecks.interval_append test 3040 3056 3072
  Check023.part3040
  Check023.part3056)))
#print axioms Check023.checked
end Papers.RationalityTen.SharedSmallCellPool
