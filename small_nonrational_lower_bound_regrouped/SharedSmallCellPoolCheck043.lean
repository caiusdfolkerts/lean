module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check043.part5504 : Interval test 5504 5520 :=
  interval_of_check _ 5504 16 (by decide +kernel)
theorem Check043.part5520 : Interval test 5520 5536 :=
  interval_of_check _ 5520 16 (by decide +kernel)
theorem Check043.part5536 : Interval test 5536 5552 :=
  interval_of_check _ 5536 16 (by decide +kernel)
theorem Check043.part5552 : Interval test 5552 5568 :=
  interval_of_check _ 5552 16 (by decide +kernel)
theorem Check043.part5568 : Interval test 5568 5584 :=
  interval_of_check _ 5568 16 (by decide +kernel)
theorem Check043.part5584 : Interval test 5584 5600 :=
  interval_of_check _ 5584 16 (by decide +kernel)
theorem Check043.part5600 : Interval test 5600 5616 :=
  interval_of_check _ 5600 16 (by decide +kernel)
theorem Check043.part5616 : Interval test 5616 5632 :=
  interval_of_check _ 5616 16 (by decide +kernel)
theorem Check043.checked : Interval test 5504 5632 :=
  (FiniteChecks.interval_append test 5504 5568 5632
  (FiniteChecks.interval_append test 5504 5536 5568
  (FiniteChecks.interval_append test 5504 5520 5536
  Check043.part5504
  Check043.part5520)
  (FiniteChecks.interval_append test 5536 5552 5568
  Check043.part5536
  Check043.part5552))
  (FiniteChecks.interval_append test 5568 5600 5632
  (FiniteChecks.interval_append test 5568 5584 5600
  Check043.part5568
  Check043.part5584)
  (FiniteChecks.interval_append test 5600 5616 5632
  Check043.part5600
  Check043.part5616)))
#print axioms Check043.checked
end Papers.RationalityTen.SharedSmallCellPool
