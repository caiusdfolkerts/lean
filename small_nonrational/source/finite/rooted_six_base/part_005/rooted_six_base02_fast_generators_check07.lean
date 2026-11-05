module
prelude
public import RootedSixBase02FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_28672 : FiniteChecks.Interval test 28672 28800 :=
  FiniteChecks.interval_of_check test 28672 128 (by decide +kernel)
theorem checked_28800 : FiniteChecks.Interval test 28800 28928 :=
  FiniteChecks.interval_of_check test 28800 128 (by decide +kernel)
theorem checked_28928 : FiniteChecks.Interval test 28928 29056 :=
  FiniteChecks.interval_of_check test 28928 128 (by decide +kernel)
theorem checked_29056 : FiniteChecks.Interval test 29056 29184 :=
  FiniteChecks.interval_of_check test 29056 128 (by decide +kernel)
theorem checked_29184 : FiniteChecks.Interval test 29184 29312 :=
  FiniteChecks.interval_of_check test 29184 128 (by decide +kernel)
theorem checked_29312 : FiniteChecks.Interval test 29312 29440 :=
  FiniteChecks.interval_of_check test 29312 128 (by decide +kernel)
theorem checked_29440 : FiniteChecks.Interval test 29440 29568 :=
  FiniteChecks.interval_of_check test 29440 128 (by decide +kernel)
theorem checked_29568 : FiniteChecks.Interval test 29568 29696 :=
  FiniteChecks.interval_of_check test 29568 128 (by decide +kernel)
theorem checked_29696 : FiniteChecks.Interval test 29696 29824 :=
  FiniteChecks.interval_of_check test 29696 128 (by decide +kernel)
theorem checked_29824 : FiniteChecks.Interval test 29824 29952 :=
  FiniteChecks.interval_of_check test 29824 128 (by decide +kernel)
theorem checked_29952 : FiniteChecks.Interval test 29952 30080 :=
  FiniteChecks.interval_of_check test 29952 128 (by decide +kernel)
theorem checked_30080 : FiniteChecks.Interval test 30080 30208 :=
  FiniteChecks.interval_of_check test 30080 128 (by decide +kernel)
theorem checked_30208 : FiniteChecks.Interval test 30208 30336 :=
  FiniteChecks.interval_of_check test 30208 128 (by decide +kernel)
theorem checked_30336 : FiniteChecks.Interval test 30336 30464 :=
  FiniteChecks.interval_of_check test 30336 128 (by decide +kernel)
theorem checked_30464 : FiniteChecks.Interval test 30464 30592 :=
  FiniteChecks.interval_of_check test 30464 128 (by decide +kernel)
theorem checked_30592 : FiniteChecks.Interval test 30592 30720 :=
  FiniteChecks.interval_of_check test 30592 128 (by decide +kernel)
theorem checked_30720 : FiniteChecks.Interval test 30720 30848 :=
  FiniteChecks.interval_of_check test 30720 128 (by decide +kernel)
theorem checked_30848 : FiniteChecks.Interval test 30848 30976 :=
  FiniteChecks.interval_of_check test 30848 128 (by decide +kernel)
theorem checked_30976 : FiniteChecks.Interval test 30976 31104 :=
  FiniteChecks.interval_of_check test 30976 128 (by decide +kernel)
theorem checked_31104 : FiniteChecks.Interval test 31104 31232 :=
  FiniteChecks.interval_of_check test 31104 128 (by decide +kernel)
theorem checked_31232 : FiniteChecks.Interval test 31232 31360 :=
  FiniteChecks.interval_of_check test 31232 128 (by decide +kernel)
theorem checked_31360 : FiniteChecks.Interval test 31360 31488 :=
  FiniteChecks.interval_of_check test 31360 128 (by decide +kernel)
theorem checked_31488 : FiniteChecks.Interval test 31488 31616 :=
  FiniteChecks.interval_of_check test 31488 128 (by decide +kernel)
theorem checked_31616 : FiniteChecks.Interval test 31616 31744 :=
  FiniteChecks.interval_of_check test 31616 128 (by decide +kernel)
theorem checked_31744 : FiniteChecks.Interval test 31744 31872 :=
  FiniteChecks.interval_of_check test 31744 128 (by decide +kernel)
theorem checked_31872 : FiniteChecks.Interval test 31872 32000 :=
  FiniteChecks.interval_of_check test 31872 128 (by decide +kernel)
theorem checked_32000 : FiniteChecks.Interval test 32000 32128 :=
  FiniteChecks.interval_of_check test 32000 128 (by decide +kernel)
theorem checked_32128 : FiniteChecks.Interval test 32128 32256 :=
  FiniteChecks.interval_of_check test 32128 128 (by decide +kernel)
theorem checked_32256 : FiniteChecks.Interval test 32256 32336 :=
  FiniteChecks.interval_of_check test 32256 80 (by decide +kernel)
theorem interval_28672 : FiniteChecks.Interval test 28672 32336 :=
  (FiniteChecks.interval_append test 28672 30464 32336
  (FiniteChecks.interval_append test 28672 29568 30464
  (FiniteChecks.interval_append test 28672 29056 29568
  (FiniteChecks.interval_append test 28672 28800 29056
  checked_28672
  (FiniteChecks.interval_append test 28800 28928 29056
  checked_28800
  checked_28928))
  (FiniteChecks.interval_append test 29056 29312 29568
  (FiniteChecks.interval_append test 29056 29184 29312
  checked_29056
  checked_29184)
  (FiniteChecks.interval_append test 29312 29440 29568
  checked_29312
  checked_29440)))
  (FiniteChecks.interval_append test 29568 29952 30464
  (FiniteChecks.interval_append test 29568 29696 29952
  checked_29568
  (FiniteChecks.interval_append test 29696 29824 29952
  checked_29696
  checked_29824))
  (FiniteChecks.interval_append test 29952 30208 30464
  (FiniteChecks.interval_append test 29952 30080 30208
  checked_29952
  checked_30080)
  (FiniteChecks.interval_append test 30208 30336 30464
  checked_30208
  checked_30336))))
  (FiniteChecks.interval_append test 30464 31360 32336
  (FiniteChecks.interval_append test 30464 30848 31360
  (FiniteChecks.interval_append test 30464 30592 30848
  checked_30464
  (FiniteChecks.interval_append test 30592 30720 30848
  checked_30592
  checked_30720))
  (FiniteChecks.interval_append test 30848 31104 31360
  (FiniteChecks.interval_append test 30848 30976 31104
  checked_30848
  checked_30976)
  (FiniteChecks.interval_append test 31104 31232 31360
  checked_31104
  checked_31232)))
  (FiniteChecks.interval_append test 31360 31872 32336
  (FiniteChecks.interval_append test 31360 31616 31872
  (FiniteChecks.interval_append test 31360 31488 31616
  checked_31360
  checked_31488)
  (FiniteChecks.interval_append test 31616 31744 31872
  checked_31616
  checked_31744))
  (FiniteChecks.interval_append test 31872 32128 32336
  (FiniteChecks.interval_append test 31872 32000 32128
  checked_31872
  checked_32000)
  (FiniteChecks.interval_append test 32128 32256 32336
  checked_32128
  checked_32256)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
