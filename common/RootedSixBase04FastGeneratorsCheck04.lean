module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase04FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 16384 16512 128
cert_checked_7 16512 16640 128
cert_checked_7 16640 16768 128
cert_checked_7 16768 16896 128
cert_checked_7 16896 16944 48
theorem interval_16384 : FiniteChecks.Interval test 16384 16944 :=
  (FiniteChecks.interval_append test 16384 16640 16944
  (FiniteChecks.interval_append test 16384 16512 16640
  checked_16384
  checked_16512)
  (FiniteChecks.interval_append test 16640 16768 16944
  checked_16640
  (FiniteChecks.interval_append test 16768 16896 16944
  checked_16768
  checked_16896)))
end Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.Fast
