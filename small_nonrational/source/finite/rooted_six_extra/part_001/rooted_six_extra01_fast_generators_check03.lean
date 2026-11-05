module
prelude
public import RootedSixExtra01FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_12288 : FiniteChecks.Interval test 12288 12416 :=
  FiniteChecks.interval_of_check test 12288 128 (by decide +kernel)
theorem checked_12416 : FiniteChecks.Interval test 12416 12544 :=
  FiniteChecks.interval_of_check test 12416 128 (by decide +kernel)
theorem checked_12544 : FiniteChecks.Interval test 12544 12600 :=
  FiniteChecks.interval_of_check test 12544 56 (by decide +kernel)
theorem interval_12288 : FiniteChecks.Interval test 12288 12600 :=
  (FiniteChecks.interval_append test 12288 12416 12600
  checked_12288
  (FiniteChecks.interval_append test 12416 12544 12600
  checked_12416
  checked_12544))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.Fast
