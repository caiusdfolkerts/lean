module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check017.part2176 : Interval test 2176 2192 :=
  interval_of_check _ 2176 16 (by decide +kernel)
theorem Check017.part2192 : Interval test 2192 2208 :=
  interval_of_check _ 2192 16 (by decide +kernel)
theorem Check017.part2208 : Interval test 2208 2224 :=
  interval_of_check _ 2208 16 (by decide +kernel)
theorem Check017.part2224 : Interval test 2224 2240 :=
  interval_of_check _ 2224 16 (by decide +kernel)
theorem Check017.part2240 : Interval test 2240 2256 :=
  interval_of_check _ 2240 16 (by decide +kernel)
theorem Check017.part2256 : Interval test 2256 2272 :=
  interval_of_check _ 2256 16 (by decide +kernel)
theorem Check017.part2272 : Interval test 2272 2288 :=
  interval_of_check _ 2272 16 (by decide +kernel)
theorem Check017.part2288 : Interval test 2288 2304 :=
  interval_of_check _ 2288 16 (by decide +kernel)
theorem Check017.checked : Interval test 2176 2304 :=
  (FiniteChecks.interval_append test 2176 2240 2304
  (FiniteChecks.interval_append test 2176 2208 2240
  (FiniteChecks.interval_append test 2176 2192 2208
  Check017.part2176
  Check017.part2192)
  (FiniteChecks.interval_append test 2208 2224 2240
  Check017.part2208
  Check017.part2224))
  (FiniteChecks.interval_append test 2240 2272 2304
  (FiniteChecks.interval_append test 2240 2256 2272
  Check017.part2240
  Check017.part2256)
  (FiniteChecks.interval_append test 2272 2288 2304
  Check017.part2272
  Check017.part2288)))
#print axioms Check017.checked
end Papers.RationalityTen.SharedSmallCellPool
