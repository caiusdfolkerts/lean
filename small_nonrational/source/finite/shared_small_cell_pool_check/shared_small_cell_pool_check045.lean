module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check045.part5760 : Interval test 5760 5776 :=
  interval_of_check _ 5760 16 (by decide +kernel)
theorem Check045.part5776 : Interval test 5776 5792 :=
  interval_of_check _ 5776 16 (by decide +kernel)
theorem Check045.part5792 : Interval test 5792 5808 :=
  interval_of_check _ 5792 16 (by decide +kernel)
theorem Check045.part5808 : Interval test 5808 5824 :=
  interval_of_check _ 5808 16 (by decide +kernel)
theorem Check045.part5824 : Interval test 5824 5840 :=
  interval_of_check _ 5824 16 (by decide +kernel)
theorem Check045.part5840 : Interval test 5840 5856 :=
  interval_of_check _ 5840 16 (by decide +kernel)
theorem Check045.part5856 : Interval test 5856 5872 :=
  interval_of_check _ 5856 16 (by decide +kernel)
theorem Check045.part5872 : Interval test 5872 5888 :=
  interval_of_check _ 5872 16 (by decide +kernel)
theorem Check045.checked : Interval test 5760 5888 :=
  (FiniteChecks.interval_append test 5760 5824 5888
  (FiniteChecks.interval_append test 5760 5792 5824
  (FiniteChecks.interval_append test 5760 5776 5792
  Check045.part5760
  Check045.part5776)
  (FiniteChecks.interval_append test 5792 5808 5824
  Check045.part5792
  Check045.part5808))
  (FiniteChecks.interval_append test 5824 5856 5888
  (FiniteChecks.interval_append test 5824 5840 5856
  Check045.part5824
  Check045.part5840)
  (FiniteChecks.interval_append test 5856 5872 5888
  Check045.part5856
  Check045.part5872)))
#print axioms Check045.checked
end Papers.RationalityTen.SharedSmallCellPool
