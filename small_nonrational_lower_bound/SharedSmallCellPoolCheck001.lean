module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check001.part128 : Interval test 128 144 :=
  interval_of_check _ 128 16 (by decide +kernel)
theorem Check001.part144 : Interval test 144 160 :=
  interval_of_check _ 144 16 (by decide +kernel)
theorem Check001.part160 : Interval test 160 176 :=
  interval_of_check _ 160 16 (by decide +kernel)
theorem Check001.part176 : Interval test 176 192 :=
  interval_of_check _ 176 16 (by decide +kernel)
theorem Check001.part192 : Interval test 192 208 :=
  interval_of_check _ 192 16 (by decide +kernel)
theorem Check001.part208 : Interval test 208 224 :=
  interval_of_check _ 208 16 (by decide +kernel)
theorem Check001.part224 : Interval test 224 240 :=
  interval_of_check _ 224 16 (by decide +kernel)
theorem Check001.part240 : Interval test 240 256 :=
  interval_of_check _ 240 16 (by decide +kernel)
theorem Check001.checked : Interval test 128 256 :=
  (FiniteChecks.interval_append test 128 192 256
  (FiniteChecks.interval_append test 128 160 192
  (FiniteChecks.interval_append test 128 144 160
  Check001.part128
  Check001.part144)
  (FiniteChecks.interval_append test 160 176 192
  Check001.part160
  Check001.part176))
  (FiniteChecks.interval_append test 192 224 256
  (FiniteChecks.interval_append test 192 208 224
  Check001.part192
  Check001.part208)
  (FiniteChecks.interval_append test 224 240 256
  Check001.part224
  Check001.part240)))
#print axioms Check001.checked
end Papers.RationalityTen.SharedSmallCellPool
