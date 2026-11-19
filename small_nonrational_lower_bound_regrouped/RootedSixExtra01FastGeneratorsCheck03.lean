module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra01FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_9 12288 12416 128
cert_checked_9 12416 12544 128
cert_checked_9 12544 12600 56
theorem interval_12288 : FiniteChecks.Interval test 12288 12600 :=
  (FiniteChecks.interval_append test 12288 12416 12600
  checked_12288
  (FiniteChecks.interval_append test 12416 12544 12600
  checked_12416
  checked_12544))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.Fast
