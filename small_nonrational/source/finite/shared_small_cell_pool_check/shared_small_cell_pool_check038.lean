module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check038.part4864 : Interval test 4864 4880 :=
  interval_of_check _ 4864 16 (by decide +kernel)
theorem Check038.part4880 : Interval test 4880 4896 :=
  interval_of_check _ 4880 16 (by decide +kernel)
theorem Check038.part4896 : Interval test 4896 4912 :=
  interval_of_check _ 4896 16 (by decide +kernel)
theorem Check038.part4912 : Interval test 4912 4928 :=
  interval_of_check _ 4912 16 (by decide +kernel)
theorem Check038.part4928 : Interval test 4928 4944 :=
  interval_of_check _ 4928 16 (by decide +kernel)
theorem Check038.part4944 : Interval test 4944 4960 :=
  interval_of_check _ 4944 16 (by decide +kernel)
theorem Check038.part4960 : Interval test 4960 4976 :=
  interval_of_check _ 4960 16 (by decide +kernel)
theorem Check038.part4976 : Interval test 4976 4992 :=
  interval_of_check _ 4976 16 (by decide +kernel)
theorem Check038.checked : Interval test 4864 4992 :=
  (FiniteChecks.interval_append test 4864 4928 4992
  (FiniteChecks.interval_append test 4864 4896 4928
  (FiniteChecks.interval_append test 4864 4880 4896
  Check038.part4864
  Check038.part4880)
  (FiniteChecks.interval_append test 4896 4912 4928
  Check038.part4896
  Check038.part4912))
  (FiniteChecks.interval_append test 4928 4960 4992
  (FiniteChecks.interval_append test 4928 4944 4960
  Check038.part4928
  Check038.part4944)
  (FiniteChecks.interval_append test 4960 4976 4992
  Check038.part4960
  Check038.part4976)))
#print axioms Check038.checked
end Papers.RationalityTen.SharedSmallCellPool
