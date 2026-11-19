module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check039.part4992 : Interval test 4992 5008 :=
  interval_of_check _ 4992 16 (by decide +kernel)
theorem Check039.part5008 : Interval test 5008 5024 :=
  interval_of_check _ 5008 16 (by decide +kernel)
theorem Check039.part5024 : Interval test 5024 5040 :=
  interval_of_check _ 5024 16 (by decide +kernel)
theorem Check039.part5040 : Interval test 5040 5056 :=
  interval_of_check _ 5040 16 (by decide +kernel)
theorem Check039.part5056 : Interval test 5056 5072 :=
  interval_of_check _ 5056 16 (by decide +kernel)
theorem Check039.part5072 : Interval test 5072 5088 :=
  interval_of_check _ 5072 16 (by decide +kernel)
theorem Check039.part5088 : Interval test 5088 5104 :=
  interval_of_check _ 5088 16 (by decide +kernel)
theorem Check039.part5104 : Interval test 5104 5120 :=
  interval_of_check _ 5104 16 (by decide +kernel)
theorem Check039.checked : Interval test 4992 5120 :=
  (FiniteChecks.interval_append test 4992 5056 5120
  (FiniteChecks.interval_append test 4992 5024 5056
  (FiniteChecks.interval_append test 4992 5008 5024
  Check039.part4992
  Check039.part5008)
  (FiniteChecks.interval_append test 5024 5040 5056
  Check039.part5024
  Check039.part5040))
  (FiniteChecks.interval_append test 5056 5088 5120
  (FiniteChecks.interval_append test 5056 5072 5088
  Check039.part5056
  Check039.part5072)
  (FiniteChecks.interval_append test 5088 5104 5120
  Check039.part5088
  Check039.part5104)))
#print axioms Check039.checked
end Papers.RationalityTen.SharedSmallCellPool
