module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check037.part4736 : Interval test 4736 4752 :=
  interval_of_check _ 4736 16 (by decide +kernel)
theorem Check037.part4752 : Interval test 4752 4768 :=
  interval_of_check _ 4752 16 (by decide +kernel)
theorem Check037.part4768 : Interval test 4768 4784 :=
  interval_of_check _ 4768 16 (by decide +kernel)
theorem Check037.part4784 : Interval test 4784 4800 :=
  interval_of_check _ 4784 16 (by decide +kernel)
theorem Check037.part4800 : Interval test 4800 4816 :=
  interval_of_check _ 4800 16 (by decide +kernel)
theorem Check037.part4816 : Interval test 4816 4832 :=
  interval_of_check _ 4816 16 (by decide +kernel)
theorem Check037.part4832 : Interval test 4832 4848 :=
  interval_of_check _ 4832 16 (by decide +kernel)
theorem Check037.part4848 : Interval test 4848 4864 :=
  interval_of_check _ 4848 16 (by decide +kernel)
theorem Check037.checked : Interval test 4736 4864 :=
  (FiniteChecks.interval_append test 4736 4800 4864
  (FiniteChecks.interval_append test 4736 4768 4800
  (FiniteChecks.interval_append test 4736 4752 4768
  Check037.part4736
  Check037.part4752)
  (FiniteChecks.interval_append test 4768 4784 4800
  Check037.part4768
  Check037.part4784))
  (FiniteChecks.interval_append test 4800 4832 4864
  (FiniteChecks.interval_append test 4800 4816 4832
  Check037.part4800
  Check037.part4816)
  (FiniteChecks.interval_append test 4832 4848 4864
  Check037.part4832
  Check037.part4848)))
#print axioms Check037.checked
end Papers.RationalityTen.SharedSmallCellPool
