module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check018.part2304 : Interval test 2304 2320 :=
  interval_of_check _ 2304 16 (by decide +kernel)
theorem Check018.part2320 : Interval test 2320 2336 :=
  interval_of_check _ 2320 16 (by decide +kernel)
theorem Check018.part2336 : Interval test 2336 2352 :=
  interval_of_check _ 2336 16 (by decide +kernel)
theorem Check018.part2352 : Interval test 2352 2368 :=
  interval_of_check _ 2352 16 (by decide +kernel)
theorem Check018.part2368 : Interval test 2368 2384 :=
  interval_of_check _ 2368 16 (by decide +kernel)
theorem Check018.part2384 : Interval test 2384 2400 :=
  interval_of_check _ 2384 16 (by decide +kernel)
theorem Check018.part2400 : Interval test 2400 2416 :=
  interval_of_check _ 2400 16 (by decide +kernel)
theorem Check018.part2416 : Interval test 2416 2432 :=
  interval_of_check _ 2416 16 (by decide +kernel)
theorem Check018.checked : Interval test 2304 2432 :=
  (FiniteChecks.interval_append test 2304 2368 2432
  (FiniteChecks.interval_append test 2304 2336 2368
  (FiniteChecks.interval_append test 2304 2320 2336
  Check018.part2304
  Check018.part2320)
  (FiniteChecks.interval_append test 2336 2352 2368
  Check018.part2336
  Check018.part2352))
  (FiniteChecks.interval_append test 2368 2400 2432
  (FiniteChecks.interval_append test 2368 2384 2400
  Check018.part2368
  Check018.part2384)
  (FiniteChecks.interval_append test 2400 2416 2432
  Check018.part2400
  Check018.part2416)))
#print axioms Check018.checked
end Papers.RationalityTen.SharedSmallCellPool
