module
prelude
public import RootedSixExtra05FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_12288 : FiniteChecks.Interval test 12288 12416 :=
  FiniteChecks.interval_of_check test 12288 128 (by decide +kernel)
theorem checked_12416 : FiniteChecks.Interval test 12416 12544 :=
  FiniteChecks.interval_of_check test 12416 128 (by decide +kernel)
theorem checked_12544 : FiniteChecks.Interval test 12544 12672 :=
  FiniteChecks.interval_of_check test 12544 128 (by decide +kernel)
theorem checked_12672 : FiniteChecks.Interval test 12672 12800 :=
  FiniteChecks.interval_of_check test 12672 128 (by decide +kernel)
theorem checked_12800 : FiniteChecks.Interval test 12800 12928 :=
  FiniteChecks.interval_of_check test 12800 128 (by decide +kernel)
theorem checked_12928 : FiniteChecks.Interval test 12928 13020 :=
  FiniteChecks.interval_of_check test 12928 92 (by decide +kernel)
theorem interval_12288 : FiniteChecks.Interval test 12288 13020 :=
  (FiniteChecks.interval_append test 12288 12672 13020
  (FiniteChecks.interval_append test 12288 12416 12672
  checked_12288
  (FiniteChecks.interval_append test 12416 12544 12672
  checked_12416
  checked_12544))
  (FiniteChecks.interval_append test 12672 12800 13020
  checked_12672
  (FiniteChecks.interval_append test 12800 12928 13020
  checked_12800
  checked_12928)))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Fast
