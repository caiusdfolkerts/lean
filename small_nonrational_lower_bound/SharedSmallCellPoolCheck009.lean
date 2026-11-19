module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check009.part1152 : Interval test 1152 1168 :=
  interval_of_check _ 1152 16 (by decide +kernel)
theorem Check009.part1168 : Interval test 1168 1184 :=
  interval_of_check _ 1168 16 (by decide +kernel)
theorem Check009.part1184 : Interval test 1184 1200 :=
  interval_of_check _ 1184 16 (by decide +kernel)
theorem Check009.part1200 : Interval test 1200 1216 :=
  interval_of_check _ 1200 16 (by decide +kernel)
theorem Check009.part1216 : Interval test 1216 1232 :=
  interval_of_check _ 1216 16 (by decide +kernel)
theorem Check009.part1232 : Interval test 1232 1248 :=
  interval_of_check _ 1232 16 (by decide +kernel)
theorem Check009.part1248 : Interval test 1248 1264 :=
  interval_of_check _ 1248 16 (by decide +kernel)
theorem Check009.part1264 : Interval test 1264 1280 :=
  interval_of_check _ 1264 16 (by decide +kernel)
theorem Check009.checked : Interval test 1152 1280 :=
  (FiniteChecks.interval_append test 1152 1216 1280
  (FiniteChecks.interval_append test 1152 1184 1216
  (FiniteChecks.interval_append test 1152 1168 1184
  Check009.part1152
  Check009.part1168)
  (FiniteChecks.interval_append test 1184 1200 1216
  Check009.part1184
  Check009.part1200))
  (FiniteChecks.interval_append test 1216 1248 1280
  (FiniteChecks.interval_append test 1216 1232 1248
  Check009.part1216
  Check009.part1232)
  (FiniteChecks.interval_append test 1248 1264 1280
  Check009.part1248
  Check009.part1264)))
#print axioms Check009.checked
end Papers.RationalityTen.SharedSmallCellPool
