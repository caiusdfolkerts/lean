module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check010.part1280 : Interval test 1280 1296 :=
  interval_of_check _ 1280 16 (by decide +kernel)
theorem Check010.part1296 : Interval test 1296 1312 :=
  interval_of_check _ 1296 16 (by decide +kernel)
theorem Check010.part1312 : Interval test 1312 1328 :=
  interval_of_check _ 1312 16 (by decide +kernel)
theorem Check010.part1328 : Interval test 1328 1344 :=
  interval_of_check _ 1328 16 (by decide +kernel)
theorem Check010.part1344 : Interval test 1344 1360 :=
  interval_of_check _ 1344 16 (by decide +kernel)
theorem Check010.part1360 : Interval test 1360 1376 :=
  interval_of_check _ 1360 16 (by decide +kernel)
theorem Check010.part1376 : Interval test 1376 1392 :=
  interval_of_check _ 1376 16 (by decide +kernel)
theorem Check010.part1392 : Interval test 1392 1408 :=
  interval_of_check _ 1392 16 (by decide +kernel)
theorem Check010.checked : Interval test 1280 1408 :=
  (FiniteChecks.interval_append test 1280 1344 1408
  (FiniteChecks.interval_append test 1280 1312 1344
  (FiniteChecks.interval_append test 1280 1296 1312
  Check010.part1280
  Check010.part1296)
  (FiniteChecks.interval_append test 1312 1328 1344
  Check010.part1312
  Check010.part1328))
  (FiniteChecks.interval_append test 1344 1376 1408
  (FiniteChecks.interval_append test 1344 1360 1376
  Check010.part1344
  Check010.part1360)
  (FiniteChecks.interval_append test 1376 1392 1408
  Check010.part1376
  Check010.part1392)))
#print axioms Check010.checked
end Papers.RationalityTen.SharedSmallCellPool
