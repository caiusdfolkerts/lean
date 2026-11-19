module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check046.part5888 : Interval test 5888 5904 :=
  interval_of_check _ 5888 16 (by decide +kernel)
theorem Check046.part5904 : Interval test 5904 5920 :=
  interval_of_check _ 5904 16 (by decide +kernel)
theorem Check046.part5920 : Interval test 5920 5936 :=
  interval_of_check _ 5920 16 (by decide +kernel)
theorem Check046.part5936 : Interval test 5936 5952 :=
  interval_of_check _ 5936 16 (by decide +kernel)
theorem Check046.part5952 : Interval test 5952 5968 :=
  interval_of_check _ 5952 16 (by decide +kernel)
theorem Check046.part5968 : Interval test 5968 5984 :=
  interval_of_check _ 5968 16 (by decide +kernel)
theorem Check046.part5984 : Interval test 5984 6000 :=
  interval_of_check _ 5984 16 (by decide +kernel)
theorem Check046.part6000 : Interval test 6000 6016 :=
  interval_of_check _ 6000 16 (by decide +kernel)
theorem Check046.checked : Interval test 5888 6016 :=
  (FiniteChecks.interval_append test 5888 5952 6016
  (FiniteChecks.interval_append test 5888 5920 5952
  (FiniteChecks.interval_append test 5888 5904 5920
  Check046.part5888
  Check046.part5904)
  (FiniteChecks.interval_append test 5920 5936 5952
  Check046.part5920
  Check046.part5936))
  (FiniteChecks.interval_append test 5952 5984 6016
  (FiniteChecks.interval_append test 5952 5968 5984
  Check046.part5952
  Check046.part5968)
  (FiniteChecks.interval_append test 5984 6000 6016
  Check046.part5984
  Check046.part6000)))
#print axioms Check046.checked
end Papers.RationalityTen.SharedSmallCellPool
