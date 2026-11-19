module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 106496 106624 128
cert_checked_7 106624 106752 128
cert_checked_7 106752 106880 128
cert_checked_7 106880 107008 128
cert_checked_7 107008 107136 128
cert_checked_7 107136 107264 128
cert_checked_7 107264 107392 128
cert_checked_7 107392 107520 128
cert_checked_7 107520 107648 128
cert_checked_7 107648 107776 128
cert_checked_7 107776 107904 128
cert_checked_7 107904 108032 128
cert_checked_7 108032 108160 128
cert_checked_7 108160 108288 128
cert_checked_7 108288 108416 128
cert_checked_7 108416 108544 128
cert_checked_7 108544 108672 128
cert_checked_7 108672 108800 128
cert_checked_7 108800 108928 128
cert_checked_7 108928 109056 128
cert_checked_7 109056 109184 128
cert_checked_7 109184 109312 128
cert_checked_7 109312 109440 128
cert_checked_7 109440 109568 128
cert_checked_7 109568 109696 128
cert_checked_7 109696 109824 128
cert_checked_7 109824 109880 56
theorem interval_106496 : FiniteChecks.Interval test 106496 109880 :=
  (FiniteChecks.interval_append test 106496 108160 109880
  (FiniteChecks.interval_append test 106496 107264 108160
  (FiniteChecks.interval_append test 106496 106880 107264
  (FiniteChecks.interval_append test 106496 106624 106880
  checked_106496
  (FiniteChecks.interval_append test 106624 106752 106880
  checked_106624
  checked_106752))
  (FiniteChecks.interval_append test 106880 107008 107264
  checked_106880
  (FiniteChecks.interval_append test 107008 107136 107264
  checked_107008
  checked_107136)))
  (FiniteChecks.interval_append test 107264 107648 108160
  (FiniteChecks.interval_append test 107264 107392 107648
  checked_107264
  (FiniteChecks.interval_append test 107392 107520 107648
  checked_107392
  checked_107520))
  (FiniteChecks.interval_append test 107648 107904 108160
  (FiniteChecks.interval_append test 107648 107776 107904
  checked_107648
  checked_107776)
  (FiniteChecks.interval_append test 107904 108032 108160
  checked_107904
  checked_108032))))
  (FiniteChecks.interval_append test 108160 109056 109880
  (FiniteChecks.interval_append test 108160 108544 109056
  (FiniteChecks.interval_append test 108160 108288 108544
  checked_108160
  (FiniteChecks.interval_append test 108288 108416 108544
  checked_108288
  checked_108416))
  (FiniteChecks.interval_append test 108544 108800 109056
  (FiniteChecks.interval_append test 108544 108672 108800
  checked_108544
  checked_108672)
  (FiniteChecks.interval_append test 108800 108928 109056
  checked_108800
  checked_108928)))
  (FiniteChecks.interval_append test 109056 109440 109880
  (FiniteChecks.interval_append test 109056 109184 109440
  checked_109056
  (FiniteChecks.interval_append test 109184 109312 109440
  checked_109184
  checked_109312))
  (FiniteChecks.interval_append test 109440 109696 109880
  (FiniteChecks.interval_append test 109440 109568 109696
  checked_109440
  checked_109568)
  (FiniteChecks.interval_append test 109696 109824 109880
  checked_109696
  checked_109824)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
