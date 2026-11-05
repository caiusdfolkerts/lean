module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check012.part1536 : Interval test 1536 1552 :=
  interval_of_check _ 1536 16 (by decide +kernel)
theorem Check012.part1552 : Interval test 1552 1568 :=
  interval_of_check _ 1552 16 (by decide +kernel)
theorem Check012.part1568 : Interval test 1568 1584 :=
  interval_of_check _ 1568 16 (by decide +kernel)
theorem Check012.part1584 : Interval test 1584 1600 :=
  interval_of_check _ 1584 16 (by decide +kernel)
theorem Check012.part1600 : Interval test 1600 1616 :=
  interval_of_check _ 1600 16 (by decide +kernel)
theorem Check012.part1616 : Interval test 1616 1632 :=
  interval_of_check _ 1616 16 (by decide +kernel)
theorem Check012.part1632 : Interval test 1632 1648 :=
  interval_of_check _ 1632 16 (by decide +kernel)
theorem Check012.part1648 : Interval test 1648 1664 :=
  interval_of_check _ 1648 16 (by decide +kernel)
theorem Check012.checked : Interval test 1536 1664 :=
  (FiniteChecks.interval_append test 1536 1600 1664
  (FiniteChecks.interval_append test 1536 1568 1600
  (FiniteChecks.interval_append test 1536 1552 1568
  Check012.part1536
  Check012.part1552)
  (FiniteChecks.interval_append test 1568 1584 1600
  Check012.part1568
  Check012.part1584))
  (FiniteChecks.interval_append test 1600 1632 1664
  (FiniteChecks.interval_append test 1600 1616 1632
  Check012.part1600
  Check012.part1616)
  (FiniteChecks.interval_append test 1632 1648 1664
  Check012.part1632
  Check012.part1648)))
#print axioms Check012.checked
end Papers.RationalityTen.SharedSmallCellPool
