module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check042.part5376 : Interval test 5376 5392 :=
  interval_of_check _ 5376 16 (by decide +kernel)
theorem Check042.part5392 : Interval test 5392 5408 :=
  interval_of_check _ 5392 16 (by decide +kernel)
theorem Check042.part5408 : Interval test 5408 5424 :=
  interval_of_check _ 5408 16 (by decide +kernel)
theorem Check042.part5424 : Interval test 5424 5440 :=
  interval_of_check _ 5424 16 (by decide +kernel)
theorem Check042.part5440 : Interval test 5440 5456 :=
  interval_of_check _ 5440 16 (by decide +kernel)
theorem Check042.part5456 : Interval test 5456 5472 :=
  interval_of_check _ 5456 16 (by decide +kernel)
theorem Check042.part5472 : Interval test 5472 5488 :=
  interval_of_check _ 5472 16 (by decide +kernel)
theorem Check042.part5488 : Interval test 5488 5504 :=
  interval_of_check _ 5488 16 (by decide +kernel)
theorem Check042.checked : Interval test 5376 5504 :=
  (FiniteChecks.interval_append test 5376 5440 5504
  (FiniteChecks.interval_append test 5376 5408 5440
  (FiniteChecks.interval_append test 5376 5392 5408
  Check042.part5376
  Check042.part5392)
  (FiniteChecks.interval_append test 5408 5424 5440
  Check042.part5408
  Check042.part5424))
  (FiniteChecks.interval_append test 5440 5472 5504
  (FiniteChecks.interval_append test 5440 5456 5472
  Check042.part5440
  Check042.part5456)
  (FiniteChecks.interval_append test 5472 5488 5504
  Check042.part5472
  Check042.part5488)))
#print axioms Check042.checked
end Papers.RationalityTen.SharedSmallCellPool
