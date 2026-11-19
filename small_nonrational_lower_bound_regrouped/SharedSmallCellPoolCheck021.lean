module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check021.part2688 : Interval test 2688 2704 :=
  interval_of_check _ 2688 16 (by decide +kernel)
theorem Check021.part2704 : Interval test 2704 2720 :=
  interval_of_check _ 2704 16 (by decide +kernel)
theorem Check021.part2720 : Interval test 2720 2736 :=
  interval_of_check _ 2720 16 (by decide +kernel)
theorem Check021.part2736 : Interval test 2736 2752 :=
  interval_of_check _ 2736 16 (by decide +kernel)
theorem Check021.part2752 : Interval test 2752 2768 :=
  interval_of_check _ 2752 16 (by decide +kernel)
theorem Check021.part2768 : Interval test 2768 2784 :=
  interval_of_check _ 2768 16 (by decide +kernel)
theorem Check021.part2784 : Interval test 2784 2800 :=
  interval_of_check _ 2784 16 (by decide +kernel)
theorem Check021.part2800 : Interval test 2800 2816 :=
  interval_of_check _ 2800 16 (by decide +kernel)
theorem Check021.checked : Interval test 2688 2816 :=
  (FiniteChecks.interval_append test 2688 2752 2816
  (FiniteChecks.interval_append test 2688 2720 2752
  (FiniteChecks.interval_append test 2688 2704 2720
  Check021.part2688
  Check021.part2704)
  (FiniteChecks.interval_append test 2720 2736 2752
  Check021.part2720
  Check021.part2736))
  (FiniteChecks.interval_append test 2752 2784 2816
  (FiniteChecks.interval_append test 2752 2768 2784
  Check021.part2752
  Check021.part2768)
  (FiniteChecks.interval_append test 2784 2800 2816
  Check021.part2784
  Check021.part2800)))
#print axioms Check021.checked
end Papers.RationalityTen.SharedSmallCellPool
