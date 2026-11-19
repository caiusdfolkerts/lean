module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check008.part1024 : Interval test 1024 1040 :=
  interval_of_check _ 1024 16 (by decide +kernel)
theorem Check008.part1040 : Interval test 1040 1056 :=
  interval_of_check _ 1040 16 (by decide +kernel)
theorem Check008.part1056 : Interval test 1056 1072 :=
  interval_of_check _ 1056 16 (by decide +kernel)
theorem Check008.part1072 : Interval test 1072 1088 :=
  interval_of_check _ 1072 16 (by decide +kernel)
theorem Check008.part1088 : Interval test 1088 1104 :=
  interval_of_check _ 1088 16 (by decide +kernel)
theorem Check008.part1104 : Interval test 1104 1120 :=
  interval_of_check _ 1104 16 (by decide +kernel)
theorem Check008.part1120 : Interval test 1120 1136 :=
  interval_of_check _ 1120 16 (by decide +kernel)
theorem Check008.part1136 : Interval test 1136 1152 :=
  interval_of_check _ 1136 16 (by decide +kernel)
theorem Check008.checked : Interval test 1024 1152 :=
  (FiniteChecks.interval_append test 1024 1088 1152
  (FiniteChecks.interval_append test 1024 1056 1088
  (FiniteChecks.interval_append test 1024 1040 1056
  Check008.part1024
  Check008.part1040)
  (FiniteChecks.interval_append test 1056 1072 1088
  Check008.part1056
  Check008.part1072))
  (FiniteChecks.interval_append test 1088 1120 1152
  (FiniteChecks.interval_append test 1088 1104 1120
  Check008.part1088
  Check008.part1104)
  (FiniteChecks.interval_append test 1120 1136 1152
  Check008.part1120
  Check008.part1136)))
#print axioms Check008.checked
end Papers.RationalityTen.SharedSmallCellPool
