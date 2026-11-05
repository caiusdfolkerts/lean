module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check041.part5248 : Interval test 5248 5264 :=
  interval_of_check _ 5248 16 (by decide +kernel)
theorem Check041.part5264 : Interval test 5264 5280 :=
  interval_of_check _ 5264 16 (by decide +kernel)
theorem Check041.part5280 : Interval test 5280 5296 :=
  interval_of_check _ 5280 16 (by decide +kernel)
theorem Check041.part5296 : Interval test 5296 5312 :=
  interval_of_check _ 5296 16 (by decide +kernel)
theorem Check041.part5312 : Interval test 5312 5328 :=
  interval_of_check _ 5312 16 (by decide +kernel)
theorem Check041.part5328 : Interval test 5328 5344 :=
  interval_of_check _ 5328 16 (by decide +kernel)
theorem Check041.part5344 : Interval test 5344 5360 :=
  interval_of_check _ 5344 16 (by decide +kernel)
theorem Check041.part5360 : Interval test 5360 5376 :=
  interval_of_check _ 5360 16 (by decide +kernel)
theorem Check041.checked : Interval test 5248 5376 :=
  (FiniteChecks.interval_append test 5248 5312 5376
  (FiniteChecks.interval_append test 5248 5280 5312
  (FiniteChecks.interval_append test 5248 5264 5280
  Check041.part5248
  Check041.part5264)
  (FiniteChecks.interval_append test 5280 5296 5312
  Check041.part5280
  Check041.part5296))
  (FiniteChecks.interval_append test 5312 5344 5376
  (FiniteChecks.interval_append test 5312 5328 5344
  Check041.part5312
  Check041.part5328)
  (FiniteChecks.interval_append test 5344 5360 5376
  Check041.part5344
  Check041.part5360)))
#print axioms Check041.checked
end Papers.RationalityTen.SharedSmallCellPool
