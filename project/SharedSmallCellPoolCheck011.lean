module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check011.part1408 : Interval test 1408 1424 :=
  interval_of_check _ 1408 16 (by decide +kernel)
theorem Check011.part1424 : Interval test 1424 1440 :=
  interval_of_check _ 1424 16 (by decide +kernel)
theorem Check011.part1440 : Interval test 1440 1456 :=
  interval_of_check _ 1440 16 (by decide +kernel)
theorem Check011.part1456 : Interval test 1456 1472 :=
  interval_of_check _ 1456 16 (by decide +kernel)
theorem Check011.part1472 : Interval test 1472 1488 :=
  interval_of_check _ 1472 16 (by decide +kernel)
theorem Check011.part1488 : Interval test 1488 1504 :=
  interval_of_check _ 1488 16 (by decide +kernel)
theorem Check011.part1504 : Interval test 1504 1520 :=
  interval_of_check _ 1504 16 (by decide +kernel)
theorem Check011.part1520 : Interval test 1520 1536 :=
  interval_of_check _ 1520 16 (by decide +kernel)
theorem Check011.checked : Interval test 1408 1536 :=
  (FiniteChecks.interval_append test 1408 1472 1536
  (FiniteChecks.interval_append test 1408 1440 1472
  (FiniteChecks.interval_append test 1408 1424 1440
  Check011.part1408
  Check011.part1424)
  (FiniteChecks.interval_append test 1440 1456 1472
  Check011.part1440
  Check011.part1456))
  (FiniteChecks.interval_append test 1472 1504 1536
  (FiniteChecks.interval_append test 1472 1488 1504
  Check011.part1472
  Check011.part1488)
  (FiniteChecks.interval_append test 1504 1520 1536
  Check011.part1504
  Check011.part1520)))
#print axioms Check011.checked
end Papers.RationalityTen.SharedSmallCellPool
