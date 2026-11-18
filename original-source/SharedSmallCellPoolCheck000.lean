module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check000.part0 : Interval test 0 16 :=
  interval_of_check _ 0 16 (by decide +kernel)
theorem Check000.part16 : Interval test 16 32 :=
  interval_of_check _ 16 16 (by decide +kernel)
theorem Check000.part32 : Interval test 32 48 :=
  interval_of_check _ 32 16 (by decide +kernel)
theorem Check000.part48 : Interval test 48 64 :=
  interval_of_check _ 48 16 (by decide +kernel)
theorem Check000.part64 : Interval test 64 80 :=
  interval_of_check _ 64 16 (by decide +kernel)
theorem Check000.part80 : Interval test 80 96 :=
  interval_of_check _ 80 16 (by decide +kernel)
theorem Check000.part96 : Interval test 96 112 :=
  interval_of_check _ 96 16 (by decide +kernel)
theorem Check000.part112 : Interval test 112 128 :=
  interval_of_check _ 112 16 (by decide +kernel)
theorem Check000.checked : Interval test 0 128 :=
  (FiniteChecks.interval_append test 0 64 128
  (FiniteChecks.interval_append test 0 32 64
  (FiniteChecks.interval_append test 0 16 32
  Check000.part0
  Check000.part16)
  (FiniteChecks.interval_append test 32 48 64
  Check000.part32
  Check000.part48))
  (FiniteChecks.interval_append test 64 96 128
  (FiniteChecks.interval_append test 64 80 96
  Check000.part64
  Check000.part80)
  (FiniteChecks.interval_append test 96 112 128
  Check000.part96
  Check000.part112)))
#print axioms Check000.checked
end Papers.RationalityTen.SharedSmallCellPool
