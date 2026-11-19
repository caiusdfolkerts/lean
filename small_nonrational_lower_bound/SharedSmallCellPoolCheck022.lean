module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check022.part2816 : Interval test 2816 2832 :=
  interval_of_check _ 2816 16 (by decide +kernel)
theorem Check022.part2832 : Interval test 2832 2848 :=
  interval_of_check _ 2832 16 (by decide +kernel)
theorem Check022.part2848 : Interval test 2848 2864 :=
  interval_of_check _ 2848 16 (by decide +kernel)
theorem Check022.part2864 : Interval test 2864 2880 :=
  interval_of_check _ 2864 16 (by decide +kernel)
theorem Check022.part2880 : Interval test 2880 2896 :=
  interval_of_check _ 2880 16 (by decide +kernel)
theorem Check022.part2896 : Interval test 2896 2912 :=
  interval_of_check _ 2896 16 (by decide +kernel)
theorem Check022.part2912 : Interval test 2912 2928 :=
  interval_of_check _ 2912 16 (by decide +kernel)
theorem Check022.part2928 : Interval test 2928 2944 :=
  interval_of_check _ 2928 16 (by decide +kernel)
theorem Check022.checked : Interval test 2816 2944 :=
  (FiniteChecks.interval_append test 2816 2880 2944
  (FiniteChecks.interval_append test 2816 2848 2880
  (FiniteChecks.interval_append test 2816 2832 2848
  Check022.part2816
  Check022.part2832)
  (FiniteChecks.interval_append test 2848 2864 2880
  Check022.part2848
  Check022.part2864))
  (FiniteChecks.interval_append test 2880 2912 2944
  (FiniteChecks.interval_append test 2880 2896 2912
  Check022.part2880
  Check022.part2896)
  (FiniteChecks.interval_append test 2912 2928 2944
  Check022.part2912
  Check022.part2928)))
#print axioms Check022.checked
end Papers.RationalityTen.SharedSmallCellPool
