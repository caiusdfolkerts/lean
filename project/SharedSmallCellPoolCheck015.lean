module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check015.part1920 : Interval test 1920 1936 :=
  interval_of_check _ 1920 16 (by decide +kernel)
theorem Check015.part1936 : Interval test 1936 1952 :=
  interval_of_check _ 1936 16 (by decide +kernel)
theorem Check015.part1952 : Interval test 1952 1968 :=
  interval_of_check _ 1952 16 (by decide +kernel)
theorem Check015.part1968 : Interval test 1968 1984 :=
  interval_of_check _ 1968 16 (by decide +kernel)
theorem Check015.part1984 : Interval test 1984 2000 :=
  interval_of_check _ 1984 16 (by decide +kernel)
theorem Check015.part2000 : Interval test 2000 2016 :=
  interval_of_check _ 2000 16 (by decide +kernel)
theorem Check015.part2016 : Interval test 2016 2032 :=
  interval_of_check _ 2016 16 (by decide +kernel)
theorem Check015.part2032 : Interval test 2032 2048 :=
  interval_of_check _ 2032 16 (by decide +kernel)
theorem Check015.checked : Interval test 1920 2048 :=
  (FiniteChecks.interval_append test 1920 1984 2048
  (FiniteChecks.interval_append test 1920 1952 1984
  (FiniteChecks.interval_append test 1920 1936 1952
  Check015.part1920
  Check015.part1936)
  (FiniteChecks.interval_append test 1952 1968 1984
  Check015.part1952
  Check015.part1968))
  (FiniteChecks.interval_append test 1984 2016 2048
  (FiniteChecks.interval_append test 1984 2000 2016
  Check015.part1984
  Check015.part2000)
  (FiniteChecks.interval_append test 2016 2032 2048
  Check015.part2016
  Check015.part2032)))
#print axioms Check015.checked
end Papers.RationalityTen.SharedSmallCellPool
