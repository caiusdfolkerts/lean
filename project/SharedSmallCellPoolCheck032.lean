module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check032.part4096 : Interval test 4096 4112 :=
  interval_of_check _ 4096 16 (by decide +kernel)
theorem Check032.part4112 : Interval test 4112 4128 :=
  interval_of_check _ 4112 16 (by decide +kernel)
theorem Check032.part4128 : Interval test 4128 4144 :=
  interval_of_check _ 4128 16 (by decide +kernel)
theorem Check032.part4144 : Interval test 4144 4160 :=
  interval_of_check _ 4144 16 (by decide +kernel)
theorem Check032.part4160 : Interval test 4160 4176 :=
  interval_of_check _ 4160 16 (by decide +kernel)
theorem Check032.part4176 : Interval test 4176 4192 :=
  interval_of_check _ 4176 16 (by decide +kernel)
theorem Check032.part4192 : Interval test 4192 4208 :=
  interval_of_check _ 4192 16 (by decide +kernel)
theorem Check032.part4208 : Interval test 4208 4224 :=
  interval_of_check _ 4208 16 (by decide +kernel)
theorem Check032.checked : Interval test 4096 4224 :=
  (FiniteChecks.interval_append test 4096 4160 4224
  (FiniteChecks.interval_append test 4096 4128 4160
  (FiniteChecks.interval_append test 4096 4112 4128
  Check032.part4096
  Check032.part4112)
  (FiniteChecks.interval_append test 4128 4144 4160
  Check032.part4128
  Check032.part4144))
  (FiniteChecks.interval_append test 4160 4192 4224
  (FiniteChecks.interval_append test 4160 4176 4192
  Check032.part4160
  Check032.part4176)
  (FiniteChecks.interval_append test 4192 4208 4224
  Check032.part4192
  Check032.part4208)))
#print axioms Check032.checked
end Papers.RationalityTen.SharedSmallCellPool
