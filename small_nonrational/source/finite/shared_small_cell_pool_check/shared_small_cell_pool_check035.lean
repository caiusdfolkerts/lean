module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check035.part4480 : Interval test 4480 4496 :=
  interval_of_check _ 4480 16 (by decide +kernel)
theorem Check035.part4496 : Interval test 4496 4512 :=
  interval_of_check _ 4496 16 (by decide +kernel)
theorem Check035.part4512 : Interval test 4512 4528 :=
  interval_of_check _ 4512 16 (by decide +kernel)
theorem Check035.part4528 : Interval test 4528 4544 :=
  interval_of_check _ 4528 16 (by decide +kernel)
theorem Check035.part4544 : Interval test 4544 4560 :=
  interval_of_check _ 4544 16 (by decide +kernel)
theorem Check035.part4560 : Interval test 4560 4576 :=
  interval_of_check _ 4560 16 (by decide +kernel)
theorem Check035.part4576 : Interval test 4576 4592 :=
  interval_of_check _ 4576 16 (by decide +kernel)
theorem Check035.part4592 : Interval test 4592 4608 :=
  interval_of_check _ 4592 16 (by decide +kernel)
theorem Check035.checked : Interval test 4480 4608 :=
  (FiniteChecks.interval_append test 4480 4544 4608
  (FiniteChecks.interval_append test 4480 4512 4544
  (FiniteChecks.interval_append test 4480 4496 4512
  Check035.part4480
  Check035.part4496)
  (FiniteChecks.interval_append test 4512 4528 4544
  Check035.part4512
  Check035.part4528))
  (FiniteChecks.interval_append test 4544 4576 4608
  (FiniteChecks.interval_append test 4544 4560 4576
  Check035.part4544
  Check035.part4560)
  (FiniteChecks.interval_append test 4576 4592 4608
  Check035.part4576
  Check035.part4592)))
#print axioms Check035.checked
end Papers.RationalityTen.SharedSmallCellPool
