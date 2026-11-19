module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase02FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 28672 28800 128
cert_checked_7 28800 28928 128
cert_checked_7 28928 29056 128
cert_checked_7 29056 29184 128
cert_checked_7 29184 29312 128
cert_checked_7 29312 29440 128
cert_checked_7 29440 29568 128
cert_checked_7 29568 29696 128
cert_checked_7 29696 29824 128
cert_checked_7 29824 29952 128
cert_checked_7 29952 30080 128
cert_checked_7 30080 30208 128
cert_checked_7 30208 30336 128
cert_checked_7 30336 30464 128
cert_checked_7 30464 30592 128
cert_checked_7 30592 30720 128
cert_checked_7 30720 30848 128
cert_checked_7 30848 30976 128
cert_checked_7 30976 31104 128
cert_checked_7 31104 31232 128
cert_checked_7 31232 31360 128
cert_checked_7 31360 31488 128
cert_checked_7 31488 31616 128
cert_checked_7 31616 31744 128
cert_checked_7 31744 31872 128
cert_checked_7 31872 32000 128
cert_checked_7 32000 32128 128
cert_checked_7 32128 32256 128
cert_checked_7 32256 32336 80
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
