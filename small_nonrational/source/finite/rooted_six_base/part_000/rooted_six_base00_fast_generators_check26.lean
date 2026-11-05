module
prelude
public import RootedSixBase00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_106496 : FiniteChecks.Interval test 106496 106624 :=
  FiniteChecks.interval_of_check test 106496 128 (by decide +kernel)
theorem checked_106624 : FiniteChecks.Interval test 106624 106752 :=
  FiniteChecks.interval_of_check test 106624 128 (by decide +kernel)
theorem checked_106752 : FiniteChecks.Interval test 106752 106880 :=
  FiniteChecks.interval_of_check test 106752 128 (by decide +kernel)
theorem checked_106880 : FiniteChecks.Interval test 106880 107008 :=
  FiniteChecks.interval_of_check test 106880 128 (by decide +kernel)
theorem checked_107008 : FiniteChecks.Interval test 107008 107136 :=
  FiniteChecks.interval_of_check test 107008 128 (by decide +kernel)
theorem checked_107136 : FiniteChecks.Interval test 107136 107264 :=
  FiniteChecks.interval_of_check test 107136 128 (by decide +kernel)
theorem checked_107264 : FiniteChecks.Interval test 107264 107392 :=
  FiniteChecks.interval_of_check test 107264 128 (by decide +kernel)
theorem checked_107392 : FiniteChecks.Interval test 107392 107520 :=
  FiniteChecks.interval_of_check test 107392 128 (by decide +kernel)
theorem checked_107520 : FiniteChecks.Interval test 107520 107648 :=
  FiniteChecks.interval_of_check test 107520 128 (by decide +kernel)
theorem checked_107648 : FiniteChecks.Interval test 107648 107776 :=
  FiniteChecks.interval_of_check test 107648 128 (by decide +kernel)
theorem checked_107776 : FiniteChecks.Interval test 107776 107904 :=
  FiniteChecks.interval_of_check test 107776 128 (by decide +kernel)
theorem checked_107904 : FiniteChecks.Interval test 107904 108032 :=
  FiniteChecks.interval_of_check test 107904 128 (by decide +kernel)
theorem checked_108032 : FiniteChecks.Interval test 108032 108160 :=
  FiniteChecks.interval_of_check test 108032 128 (by decide +kernel)
theorem checked_108160 : FiniteChecks.Interval test 108160 108288 :=
  FiniteChecks.interval_of_check test 108160 128 (by decide +kernel)
theorem checked_108288 : FiniteChecks.Interval test 108288 108416 :=
  FiniteChecks.interval_of_check test 108288 128 (by decide +kernel)
theorem checked_108416 : FiniteChecks.Interval test 108416 108544 :=
  FiniteChecks.interval_of_check test 108416 128 (by decide +kernel)
theorem checked_108544 : FiniteChecks.Interval test 108544 108672 :=
  FiniteChecks.interval_of_check test 108544 128 (by decide +kernel)
theorem checked_108672 : FiniteChecks.Interval test 108672 108800 :=
  FiniteChecks.interval_of_check test 108672 128 (by decide +kernel)
theorem checked_108800 : FiniteChecks.Interval test 108800 108928 :=
  FiniteChecks.interval_of_check test 108800 128 (by decide +kernel)
theorem checked_108928 : FiniteChecks.Interval test 108928 109056 :=
  FiniteChecks.interval_of_check test 108928 128 (by decide +kernel)
theorem checked_109056 : FiniteChecks.Interval test 109056 109184 :=
  FiniteChecks.interval_of_check test 109056 128 (by decide +kernel)
theorem checked_109184 : FiniteChecks.Interval test 109184 109312 :=
  FiniteChecks.interval_of_check test 109184 128 (by decide +kernel)
theorem checked_109312 : FiniteChecks.Interval test 109312 109440 :=
  FiniteChecks.interval_of_check test 109312 128 (by decide +kernel)
theorem checked_109440 : FiniteChecks.Interval test 109440 109568 :=
  FiniteChecks.interval_of_check test 109440 128 (by decide +kernel)
theorem checked_109568 : FiniteChecks.Interval test 109568 109696 :=
  FiniteChecks.interval_of_check test 109568 128 (by decide +kernel)
theorem checked_109696 : FiniteChecks.Interval test 109696 109824 :=
  FiniteChecks.interval_of_check test 109696 128 (by decide +kernel)
theorem checked_109824 : FiniteChecks.Interval test 109824 109880 :=
  FiniteChecks.interval_of_check test 109824 56 (by decide +kernel)
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
