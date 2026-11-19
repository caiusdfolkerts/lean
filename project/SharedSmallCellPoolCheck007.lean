module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check007.part896 : Interval test 896 912 :=
  interval_of_check _ 896 16 (by decide +kernel)
theorem Check007.part912 : Interval test 912 928 :=
  interval_of_check _ 912 16 (by decide +kernel)
theorem Check007.part928 : Interval test 928 944 :=
  interval_of_check _ 928 16 (by decide +kernel)
theorem Check007.part944 : Interval test 944 960 :=
  interval_of_check _ 944 16 (by decide +kernel)
theorem Check007.part960 : Interval test 960 976 :=
  interval_of_check _ 960 16 (by decide +kernel)
theorem Check007.part976 : Interval test 976 992 :=
  interval_of_check _ 976 16 (by decide +kernel)
theorem Check007.part992 : Interval test 992 1008 :=
  interval_of_check _ 992 16 (by decide +kernel)
theorem Check007.part1008 : Interval test 1008 1024 :=
  interval_of_check _ 1008 16 (by decide +kernel)
theorem Check007.checked : Interval test 896 1024 :=
  (FiniteChecks.interval_append test 896 960 1024
  (FiniteChecks.interval_append test 896 928 960
  (FiniteChecks.interval_append test 896 912 928
  Check007.part896
  Check007.part912)
  (FiniteChecks.interval_append test 928 944 960
  Check007.part928
  Check007.part944))
  (FiniteChecks.interval_append test 960 992 1024
  (FiniteChecks.interval_append test 960 976 992
  Check007.part960
  Check007.part976)
  (FiniteChecks.interval_append test 992 1008 1024
  Check007.part992
  Check007.part1008)))
#print axioms Check007.checked
end Papers.RationalityTen.SharedSmallCellPool
