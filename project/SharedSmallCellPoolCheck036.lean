module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check036.part4608 : Interval test 4608 4624 :=
  interval_of_check _ 4608 16 (by decide +kernel)
theorem Check036.part4624 : Interval test 4624 4640 :=
  interval_of_check _ 4624 16 (by decide +kernel)
theorem Check036.part4640 : Interval test 4640 4656 :=
  interval_of_check _ 4640 16 (by decide +kernel)
theorem Check036.part4656 : Interval test 4656 4672 :=
  interval_of_check _ 4656 16 (by decide +kernel)
theorem Check036.part4672 : Interval test 4672 4688 :=
  interval_of_check _ 4672 16 (by decide +kernel)
theorem Check036.part4688 : Interval test 4688 4704 :=
  interval_of_check _ 4688 16 (by decide +kernel)
theorem Check036.part4704 : Interval test 4704 4720 :=
  interval_of_check _ 4704 16 (by decide +kernel)
theorem Check036.part4720 : Interval test 4720 4736 :=
  interval_of_check _ 4720 16 (by decide +kernel)
theorem Check036.checked : Interval test 4608 4736 :=
  (FiniteChecks.interval_append test 4608 4672 4736
  (FiniteChecks.interval_append test 4608 4640 4672
  (FiniteChecks.interval_append test 4608 4624 4640
  Check036.part4608
  Check036.part4624)
  (FiniteChecks.interval_append test 4640 4656 4672
  Check036.part4640
  Check036.part4656))
  (FiniteChecks.interval_append test 4672 4704 4736
  (FiniteChecks.interval_append test 4672 4688 4704
  Check036.part4672
  Check036.part4688)
  (FiniteChecks.interval_append test 4704 4720 4736
  Check036.part4704
  Check036.part4720)))
#print axioms Check036.checked
end Papers.RationalityTen.SharedSmallCellPool
