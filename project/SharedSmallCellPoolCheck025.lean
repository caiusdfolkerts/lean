module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check025.part3200 : Interval test 3200 3216 :=
  interval_of_check _ 3200 16 (by decide +kernel)
theorem Check025.part3216 : Interval test 3216 3232 :=
  interval_of_check _ 3216 16 (by decide +kernel)
theorem Check025.part3232 : Interval test 3232 3248 :=
  interval_of_check _ 3232 16 (by decide +kernel)
theorem Check025.part3248 : Interval test 3248 3264 :=
  interval_of_check _ 3248 16 (by decide +kernel)
theorem Check025.part3264 : Interval test 3264 3280 :=
  interval_of_check _ 3264 16 (by decide +kernel)
theorem Check025.part3280 : Interval test 3280 3296 :=
  interval_of_check _ 3280 16 (by decide +kernel)
theorem Check025.part3296 : Interval test 3296 3312 :=
  interval_of_check _ 3296 16 (by decide +kernel)
theorem Check025.part3312 : Interval test 3312 3328 :=
  interval_of_check _ 3312 16 (by decide +kernel)
theorem Check025.checked : Interval test 3200 3328 :=
  (FiniteChecks.interval_append test 3200 3264 3328
  (FiniteChecks.interval_append test 3200 3232 3264
  (FiniteChecks.interval_append test 3200 3216 3232
  Check025.part3200
  Check025.part3216)
  (FiniteChecks.interval_append test 3232 3248 3264
  Check025.part3232
  Check025.part3248))
  (FiniteChecks.interval_append test 3264 3296 3328
  (FiniteChecks.interval_append test 3264 3280 3296
  Check025.part3264
  Check025.part3280)
  (FiniteChecks.interval_append test 3296 3312 3328
  Check025.part3296
  Check025.part3312)))
#print axioms Check025.checked
end Papers.RationalityTen.SharedSmallCellPool
