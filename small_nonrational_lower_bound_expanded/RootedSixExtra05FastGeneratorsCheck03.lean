module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_9 12288 12416 128
cert_checked_9 12416 12544 128
cert_checked_9 12544 12672 128
cert_checked_9 12672 12800 128
cert_checked_9 12800 12928 128
cert_checked_9 12928 13020 92
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
