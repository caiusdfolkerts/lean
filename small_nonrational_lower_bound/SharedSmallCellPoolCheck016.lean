module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check016.part2048 : Interval test 2048 2064 :=
  interval_of_check _ 2048 16 (by decide +kernel)
theorem Check016.part2064 : Interval test 2064 2080 :=
  interval_of_check _ 2064 16 (by decide +kernel)
theorem Check016.part2080 : Interval test 2080 2096 :=
  interval_of_check _ 2080 16 (by decide +kernel)
theorem Check016.part2096 : Interval test 2096 2112 :=
  interval_of_check _ 2096 16 (by decide +kernel)
theorem Check016.part2112 : Interval test 2112 2128 :=
  interval_of_check _ 2112 16 (by decide +kernel)
theorem Check016.part2128 : Interval test 2128 2144 :=
  interval_of_check _ 2128 16 (by decide +kernel)
theorem Check016.part2144 : Interval test 2144 2160 :=
  interval_of_check _ 2144 16 (by decide +kernel)
theorem Check016.part2160 : Interval test 2160 2176 :=
  interval_of_check _ 2160 16 (by decide +kernel)
theorem Check016.checked : Interval test 2048 2176 :=
  (FiniteChecks.interval_append test 2048 2112 2176
  (FiniteChecks.interval_append test 2048 2080 2112
  (FiniteChecks.interval_append test 2048 2064 2080
  Check016.part2048
  Check016.part2064)
  (FiniteChecks.interval_append test 2080 2096 2112
  Check016.part2080
  Check016.part2096))
  (FiniteChecks.interval_append test 2112 2144 2176
  (FiniteChecks.interval_append test 2112 2128 2144
  Check016.part2112
  Check016.part2128)
  (FiniteChecks.interval_append test 2144 2160 2176
  Check016.part2144
  Check016.part2160)))
#print axioms Check016.checked
end Papers.RationalityTen.SharedSmallCellPool
