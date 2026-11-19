module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check019.part2432 : Interval test 2432 2448 :=
  interval_of_check _ 2432 16 (by decide +kernel)
theorem Check019.part2448 : Interval test 2448 2464 :=
  interval_of_check _ 2448 16 (by decide +kernel)
theorem Check019.part2464 : Interval test 2464 2480 :=
  interval_of_check _ 2464 16 (by decide +kernel)
theorem Check019.part2480 : Interval test 2480 2496 :=
  interval_of_check _ 2480 16 (by decide +kernel)
theorem Check019.part2496 : Interval test 2496 2512 :=
  interval_of_check _ 2496 16 (by decide +kernel)
theorem Check019.part2512 : Interval test 2512 2528 :=
  interval_of_check _ 2512 16 (by decide +kernel)
theorem Check019.part2528 : Interval test 2528 2544 :=
  interval_of_check _ 2528 16 (by decide +kernel)
theorem Check019.part2544 : Interval test 2544 2560 :=
  interval_of_check _ 2544 16 (by decide +kernel)
theorem Check019.checked : Interval test 2432 2560 :=
  (FiniteChecks.interval_append test 2432 2496 2560
  (FiniteChecks.interval_append test 2432 2464 2496
  (FiniteChecks.interval_append test 2432 2448 2464
  Check019.part2432
  Check019.part2448)
  (FiniteChecks.interval_append test 2464 2480 2496
  Check019.part2464
  Check019.part2480))
  (FiniteChecks.interval_append test 2496 2528 2560
  (FiniteChecks.interval_append test 2496 2512 2528
  Check019.part2496
  Check019.part2512)
  (FiniteChecks.interval_append test 2528 2544 2560
  Check019.part2528
  Check019.part2544)))
#print axioms Check019.checked
end Papers.RationalityTen.SharedSmallCellPool
