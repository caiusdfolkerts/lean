module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check014.part1792 : Interval test 1792 1808 :=
  interval_of_check _ 1792 16 (by decide +kernel)
theorem Check014.part1808 : Interval test 1808 1824 :=
  interval_of_check _ 1808 16 (by decide +kernel)
theorem Check014.part1824 : Interval test 1824 1840 :=
  interval_of_check _ 1824 16 (by decide +kernel)
theorem Check014.part1840 : Interval test 1840 1856 :=
  interval_of_check _ 1840 16 (by decide +kernel)
theorem Check014.part1856 : Interval test 1856 1872 :=
  interval_of_check _ 1856 16 (by decide +kernel)
theorem Check014.part1872 : Interval test 1872 1888 :=
  interval_of_check _ 1872 16 (by decide +kernel)
theorem Check014.part1888 : Interval test 1888 1904 :=
  interval_of_check _ 1888 16 (by decide +kernel)
theorem Check014.part1904 : Interval test 1904 1920 :=
  interval_of_check _ 1904 16 (by decide +kernel)
theorem Check014.checked : Interval test 1792 1920 :=
  (FiniteChecks.interval_append test 1792 1856 1920
  (FiniteChecks.interval_append test 1792 1824 1856
  (FiniteChecks.interval_append test 1792 1808 1824
  Check014.part1792
  Check014.part1808)
  (FiniteChecks.interval_append test 1824 1840 1856
  Check014.part1824
  Check014.part1840))
  (FiniteChecks.interval_append test 1856 1888 1920
  (FiniteChecks.interval_append test 1856 1872 1888
  Check014.part1856
  Check014.part1872)
  (FiniteChecks.interval_append test 1888 1904 1920
  Check014.part1888
  Check014.part1904)))
#print axioms Check014.checked
end Papers.RationalityTen.SharedSmallCellPool
