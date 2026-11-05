module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check020.part2560 : Interval test 2560 2576 :=
  interval_of_check _ 2560 16 (by decide +kernel)
theorem Check020.part2576 : Interval test 2576 2592 :=
  interval_of_check _ 2576 16 (by decide +kernel)
theorem Check020.part2592 : Interval test 2592 2608 :=
  interval_of_check _ 2592 16 (by decide +kernel)
theorem Check020.part2608 : Interval test 2608 2624 :=
  interval_of_check _ 2608 16 (by decide +kernel)
theorem Check020.part2624 : Interval test 2624 2640 :=
  interval_of_check _ 2624 16 (by decide +kernel)
theorem Check020.part2640 : Interval test 2640 2656 :=
  interval_of_check _ 2640 16 (by decide +kernel)
theorem Check020.part2656 : Interval test 2656 2672 :=
  interval_of_check _ 2656 16 (by decide +kernel)
theorem Check020.part2672 : Interval test 2672 2688 :=
  interval_of_check _ 2672 16 (by decide +kernel)
theorem Check020.checked : Interval test 2560 2688 :=
  (FiniteChecks.interval_append test 2560 2624 2688
  (FiniteChecks.interval_append test 2560 2592 2624
  (FiniteChecks.interval_append test 2560 2576 2592
  Check020.part2560
  Check020.part2576)
  (FiniteChecks.interval_append test 2592 2608 2624
  Check020.part2592
  Check020.part2608))
  (FiniteChecks.interval_append test 2624 2656 2688
  (FiniteChecks.interval_append test 2624 2640 2656
  Check020.part2624
  Check020.part2640)
  (FiniteChecks.interval_append test 2656 2672 2688
  Check020.part2656
  Check020.part2672)))
#print axioms Check020.checked
end Papers.RationalityTen.SharedSmallCellPool
