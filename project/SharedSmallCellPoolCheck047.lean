module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check047.part6016 : Interval test 6016 6032 :=
  interval_of_check _ 6016 16 (by decide +kernel)
theorem Check047.part6032 : Interval test 6032 6048 :=
  interval_of_check _ 6032 16 (by decide +kernel)
theorem Check047.part6048 : Interval test 6048 6064 :=
  interval_of_check _ 6048 16 (by decide +kernel)
theorem Check047.part6064 : Interval test 6064 6080 :=
  interval_of_check _ 6064 16 (by decide +kernel)
theorem Check047.part6080 : Interval test 6080 6096 :=
  interval_of_check _ 6080 16 (by decide +kernel)
theorem Check047.part6096 : Interval test 6096 6112 :=
  interval_of_check _ 6096 16 (by decide +kernel)
theorem Check047.part6112 : Interval test 6112 6128 :=
  interval_of_check _ 6112 16 (by decide +kernel)
theorem Check047.part6128 : Interval test 6128 6144 :=
  interval_of_check _ 6128 16 (by decide +kernel)
theorem Check047.checked : Interval test 6016 6144 :=
  (FiniteChecks.interval_append test 6016 6080 6144
  (FiniteChecks.interval_append test 6016 6048 6080
  (FiniteChecks.interval_append test 6016 6032 6048
  Check047.part6016
  Check047.part6032)
  (FiniteChecks.interval_append test 6048 6064 6080
  Check047.part6048
  Check047.part6064))
  (FiniteChecks.interval_append test 6080 6112 6144
  (FiniteChecks.interval_append test 6080 6096 6112
  Check047.part6080
  Check047.part6096)
  (FiniteChecks.interval_append test 6112 6128 6144
  Check047.part6112
  Check047.part6128)))
#print axioms Check047.checked
end Papers.RationalityTen.SharedSmallCellPool
