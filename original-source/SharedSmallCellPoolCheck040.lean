module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check040.part5120 : Interval test 5120 5136 :=
  interval_of_check _ 5120 16 (by decide +kernel)
theorem Check040.part5136 : Interval test 5136 5152 :=
  interval_of_check _ 5136 16 (by decide +kernel)
theorem Check040.part5152 : Interval test 5152 5168 :=
  interval_of_check _ 5152 16 (by decide +kernel)
theorem Check040.part5168 : Interval test 5168 5184 :=
  interval_of_check _ 5168 16 (by decide +kernel)
theorem Check040.part5184 : Interval test 5184 5200 :=
  interval_of_check _ 5184 16 (by decide +kernel)
theorem Check040.part5200 : Interval test 5200 5216 :=
  interval_of_check _ 5200 16 (by decide +kernel)
theorem Check040.part5216 : Interval test 5216 5232 :=
  interval_of_check _ 5216 16 (by decide +kernel)
theorem Check040.part5232 : Interval test 5232 5248 :=
  interval_of_check _ 5232 16 (by decide +kernel)
theorem Check040.checked : Interval test 5120 5248 :=
  (FiniteChecks.interval_append test 5120 5184 5248
  (FiniteChecks.interval_append test 5120 5152 5184
  (FiniteChecks.interval_append test 5120 5136 5152
  Check040.part5120
  Check040.part5136)
  (FiniteChecks.interval_append test 5152 5168 5184
  Check040.part5152
  Check040.part5168))
  (FiniteChecks.interval_append test 5184 5216 5248
  (FiniteChecks.interval_append test 5184 5200 5216
  Check040.part5184
  Check040.part5200)
  (FiniteChecks.interval_append test 5216 5232 5248
  Check040.part5216
  Check040.part5232)))
#print axioms Check040.checked
end Papers.RationalityTen.SharedSmallCellPool
