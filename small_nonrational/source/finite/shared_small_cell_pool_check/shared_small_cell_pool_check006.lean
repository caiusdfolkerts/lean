module
prelude
public import SharedSmallCellPoolData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SharedSmallCellPool
open ConcreteGrowth PackedRawNatGrowth SharedGraphCellPool FiniteChecks
theorem Check006.part768 : Interval test 768 784 :=
  interval_of_check _ 768 16 (by decide +kernel)
theorem Check006.part784 : Interval test 784 800 :=
  interval_of_check _ 784 16 (by decide +kernel)
theorem Check006.part800 : Interval test 800 816 :=
  interval_of_check _ 800 16 (by decide +kernel)
theorem Check006.part816 : Interval test 816 832 :=
  interval_of_check _ 816 16 (by decide +kernel)
theorem Check006.part832 : Interval test 832 848 :=
  interval_of_check _ 832 16 (by decide +kernel)
theorem Check006.part848 : Interval test 848 864 :=
  interval_of_check _ 848 16 (by decide +kernel)
theorem Check006.part864 : Interval test 864 880 :=
  interval_of_check _ 864 16 (by decide +kernel)
theorem Check006.part880 : Interval test 880 896 :=
  interval_of_check _ 880 16 (by decide +kernel)
theorem Check006.checked : Interval test 768 896 :=
  (FiniteChecks.interval_append test 768 832 896
  (FiniteChecks.interval_append test 768 800 832
  (FiniteChecks.interval_append test 768 784 800
  Check006.part768
  Check006.part784)
  (FiniteChecks.interval_append test 800 816 832
  Check006.part800
  Check006.part816))
  (FiniteChecks.interval_append test 832 864 896
  (FiniteChecks.interval_append test 832 848 864
  Check006.part832
  Check006.part848)
  (FiniteChecks.interval_append test 864 880 896
  Check006.part864
  Check006.part880)))
#print axioms Check006.checked
end Papers.RationalityTen.SharedSmallCellPool
