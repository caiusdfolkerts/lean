module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check050.part6400 : Interval test 6400 6416 :=
  interval_of_check _ 6400 16 (by decide +kernel)
theorem Check050.part6416 : Interval test 6416 6432 :=
  interval_of_check _ 6416 16 (by decide +kernel)
theorem Check050.part6432 : Interval test 6432 6448 :=
  interval_of_check _ 6432 16 (by decide +kernel)
theorem Check050.part6448 : Interval test 6448 6464 :=
  interval_of_check _ 6448 16 (by decide +kernel)
theorem Check050.part6464 : Interval test 6464 6480 :=
  interval_of_check _ 6464 16 (by decide +kernel)
theorem Check050.part6480 : Interval test 6480 6496 :=
  interval_of_check _ 6480 16 (by decide +kernel)
theorem Check050.part6496 : Interval test 6496 6510 :=
  interval_of_check _ 6496 14 (by decide +kernel)
theorem Check050.checked : Interval test 6400 6510 :=
  (FiniteChecks.interval_append test 6400 6448 6510
  (FiniteChecks.interval_append test 6400 6416 6448
  Check050.part6400
  (FiniteChecks.interval_append test 6416 6432 6448
  Check050.part6416
  Check050.part6432))
  (FiniteChecks.interval_append test 6448 6480 6510
  (FiniteChecks.interval_append test 6448 6464 6480
  Check050.part6448
  Check050.part6464)
  (FiniteChecks.interval_append test 6480 6496 6510
  Check050.part6480
  Check050.part6496)))
#print axioms Check050.checked
end Papers.RationalityTen.SharedSmallCellPool
