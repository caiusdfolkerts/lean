module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check005.part640 : Interval test 640 656 :=
  interval_of_check _ 640 16 (by decide +kernel)
theorem Check005.part656 : Interval test 656 672 :=
  interval_of_check _ 656 16 (by decide +kernel)
theorem Check005.part672 : Interval test 672 688 :=
  interval_of_check _ 672 16 (by decide +kernel)
theorem Check005.part688 : Interval test 688 704 :=
  interval_of_check _ 688 16 (by decide +kernel)
theorem Check005.part704 : Interval test 704 720 :=
  interval_of_check _ 704 16 (by decide +kernel)
theorem Check005.part720 : Interval test 720 736 :=
  interval_of_check _ 720 16 (by decide +kernel)
theorem Check005.part736 : Interval test 736 752 :=
  interval_of_check _ 736 16 (by decide +kernel)
theorem Check005.part752 : Interval test 752 768 :=
  interval_of_check _ 752 16 (by decide +kernel)
theorem Check005.checked : Interval test 640 768 :=
  (FiniteChecks.interval_append test 640 704 768
  (FiniteChecks.interval_append test 640 672 704
  (FiniteChecks.interval_append test 640 656 672
  Check005.part640
  Check005.part656)
  (FiniteChecks.interval_append test 672 688 704
  Check005.part672
  Check005.part688))
  (FiniteChecks.interval_append test 704 736 768
  (FiniteChecks.interval_append test 704 720 736
  Check005.part704
  Check005.part720)
  (FiniteChecks.interval_append test 736 752 768
  Check005.part736
  Check005.part752)))
#print axioms Check005.checked
end Papers.RationalityTen.SharedSmallCellPool
