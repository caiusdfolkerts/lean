module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check031.part3968 : Interval test 3968 3984 :=
  interval_of_check _ 3968 16 (by decide +kernel)
theorem Check031.part3984 : Interval test 3984 4000 :=
  interval_of_check _ 3984 16 (by decide +kernel)
theorem Check031.part4000 : Interval test 4000 4016 :=
  interval_of_check _ 4000 16 (by decide +kernel)
theorem Check031.part4016 : Interval test 4016 4032 :=
  interval_of_check _ 4016 16 (by decide +kernel)
theorem Check031.part4032 : Interval test 4032 4048 :=
  interval_of_check _ 4032 16 (by decide +kernel)
theorem Check031.part4048 : Interval test 4048 4064 :=
  interval_of_check _ 4048 16 (by decide +kernel)
theorem Check031.part4064 : Interval test 4064 4080 :=
  interval_of_check _ 4064 16 (by decide +kernel)
theorem Check031.part4080 : Interval test 4080 4096 :=
  interval_of_check _ 4080 16 (by decide +kernel)
theorem Check031.checked : Interval test 3968 4096 :=
  (FiniteChecks.interval_append test 3968 4032 4096
  (FiniteChecks.interval_append test 3968 4000 4032
  (FiniteChecks.interval_append test 3968 3984 4000
  Check031.part3968
  Check031.part3984)
  (FiniteChecks.interval_append test 4000 4016 4032
  Check031.part4000
  Check031.part4016))
  (FiniteChecks.interval_append test 4032 4064 4096
  (FiniteChecks.interval_append test 4032 4048 4064
  Check031.part4032
  Check031.part4048)
  (FiniteChecks.interval_append test 4064 4080 4096
  Check031.part4064
  Check031.part4080)))
#print axioms Check031.checked
end Papers.RationalityTen.SharedSmallCellPool
