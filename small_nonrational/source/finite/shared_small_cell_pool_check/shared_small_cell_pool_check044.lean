module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check044.part5632 : Interval test 5632 5648 :=
  interval_of_check _ 5632 16 (by decide +kernel)
theorem Check044.part5648 : Interval test 5648 5664 :=
  interval_of_check _ 5648 16 (by decide +kernel)
theorem Check044.part5664 : Interval test 5664 5680 :=
  interval_of_check _ 5664 16 (by decide +kernel)
theorem Check044.part5680 : Interval test 5680 5696 :=
  interval_of_check _ 5680 16 (by decide +kernel)
theorem Check044.part5696 : Interval test 5696 5712 :=
  interval_of_check _ 5696 16 (by decide +kernel)
theorem Check044.part5712 : Interval test 5712 5728 :=
  interval_of_check _ 5712 16 (by decide +kernel)
theorem Check044.part5728 : Interval test 5728 5744 :=
  interval_of_check _ 5728 16 (by decide +kernel)
theorem Check044.part5744 : Interval test 5744 5760 :=
  interval_of_check _ 5744 16 (by decide +kernel)
theorem Check044.checked : Interval test 5632 5760 :=
  (FiniteChecks.interval_append test 5632 5696 5760
  (FiniteChecks.interval_append test 5632 5664 5696
  (FiniteChecks.interval_append test 5632 5648 5664
  Check044.part5632
  Check044.part5648)
  (FiniteChecks.interval_append test 5664 5680 5696
  Check044.part5664
  Check044.part5680))
  (FiniteChecks.interval_append test 5696 5728 5760
  (FiniteChecks.interval_append test 5696 5712 5728
  Check044.part5696
  Check044.part5712)
  (FiniteChecks.interval_append test 5728 5744 5760
  Check044.part5728
  Check044.part5744)))
#print axioms Check044.checked
end Papers.RationalityTen.SharedSmallCellPool
