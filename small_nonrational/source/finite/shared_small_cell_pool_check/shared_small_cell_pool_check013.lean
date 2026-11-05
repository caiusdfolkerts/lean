module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check013.part1664 : Interval test 1664 1680 :=
  interval_of_check _ 1664 16 (by decide +kernel)
theorem Check013.part1680 : Interval test 1680 1696 :=
  interval_of_check _ 1680 16 (by decide +kernel)
theorem Check013.part1696 : Interval test 1696 1712 :=
  interval_of_check _ 1696 16 (by decide +kernel)
theorem Check013.part1712 : Interval test 1712 1728 :=
  interval_of_check _ 1712 16 (by decide +kernel)
theorem Check013.part1728 : Interval test 1728 1744 :=
  interval_of_check _ 1728 16 (by decide +kernel)
theorem Check013.part1744 : Interval test 1744 1760 :=
  interval_of_check _ 1744 16 (by decide +kernel)
theorem Check013.part1760 : Interval test 1760 1776 :=
  interval_of_check _ 1760 16 (by decide +kernel)
theorem Check013.part1776 : Interval test 1776 1792 :=
  interval_of_check _ 1776 16 (by decide +kernel)
theorem Check013.checked : Interval test 1664 1792 :=
  (FiniteChecks.interval_append test 1664 1728 1792
  (FiniteChecks.interval_append test 1664 1696 1728
  (FiniteChecks.interval_append test 1664 1680 1696
  Check013.part1664
  Check013.part1680)
  (FiniteChecks.interval_append test 1696 1712 1728
  Check013.part1696
  Check013.part1712))
  (FiniteChecks.interval_append test 1728 1760 1792
  (FiniteChecks.interval_append test 1728 1744 1760
  Check013.part1728
  Check013.part1744)
  (FiniteChecks.interval_append test 1760 1776 1792
  Check013.part1760
  Check013.part1776)))
#print axioms Check013.checked
end Papers.RationalityTen.SharedSmallCellPool
