module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check024.part3072 : Interval test 3072 3088 :=
  interval_of_check _ 3072 16 (by decide +kernel)
theorem Check024.part3088 : Interval test 3088 3104 :=
  interval_of_check _ 3088 16 (by decide +kernel)
theorem Check024.part3104 : Interval test 3104 3120 :=
  interval_of_check _ 3104 16 (by decide +kernel)
theorem Check024.part3120 : Interval test 3120 3136 :=
  interval_of_check _ 3120 16 (by decide +kernel)
theorem Check024.part3136 : Interval test 3136 3152 :=
  interval_of_check _ 3136 16 (by decide +kernel)
theorem Check024.part3152 : Interval test 3152 3168 :=
  interval_of_check _ 3152 16 (by decide +kernel)
theorem Check024.part3168 : Interval test 3168 3184 :=
  interval_of_check _ 3168 16 (by decide +kernel)
theorem Check024.part3184 : Interval test 3184 3200 :=
  interval_of_check _ 3184 16 (by decide +kernel)
theorem Check024.checked : Interval test 3072 3200 :=
  (FiniteChecks.interval_append test 3072 3136 3200
  (FiniteChecks.interval_append test 3072 3104 3136
  (FiniteChecks.interval_append test 3072 3088 3104
  Check024.part3072
  Check024.part3088)
  (FiniteChecks.interval_append test 3104 3120 3136
  Check024.part3104
  Check024.part3120))
  (FiniteChecks.interval_append test 3136 3168 3200
  (FiniteChecks.interval_append test 3136 3152 3168
  Check024.part3136
  Check024.part3152)
  (FiniteChecks.interval_append test 3168 3184 3200
  Check024.part3168
  Check024.part3184)))
#print axioms Check024.checked
end Papers.RationalityTen.SharedSmallCellPool
