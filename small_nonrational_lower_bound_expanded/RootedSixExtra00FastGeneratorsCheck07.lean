module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_9 28672 28800 128
cert_checked_9 28800 28928 128
cert_checked_9 28928 29056 128
cert_checked_9 29056 29184 128
cert_checked_9 29184 29312 128
cert_checked_9 29312 29440 128
cert_checked_9 29440 29568 128
cert_checked_9 29568 29696 128
cert_checked_9 29696 29824 128
cert_checked_9 29824 29952 128
cert_checked_9 29952 30080 128
cert_checked_9 30080 30208 128
cert_checked_9 30208 30336 128
cert_checked_9 30336 30464 128
cert_checked_9 30464 30592 128
cert_checked_9 30592 30720 128
cert_checked_9 30720 30848 128
cert_checked_9 30848 30976 128
cert_checked_9 30976 31104 128
cert_checked_9 31104 31232 128
cert_checked_9 31232 31360 128
cert_checked_9 31360 31488 128
cert_checked_9 31488 31616 128
cert_checked_9 31616 31744 128
cert_checked_9 31744 31872 128
cert_checked_9 31872 32000 128
cert_checked_9 32000 32128 128
cert_checked_9 32128 32256 128
cert_checked_9 32256 32384 128
cert_checked_9 32384 32512 128
cert_checked_9 32512 32640 128
cert_checked_9 32640 32768 128
theorem interval_28672 : FiniteChecks.Interval test 28672 32768 :=
  (FiniteChecks.interval_append test 28672 30720 32768
  (FiniteChecks.interval_append test 28672 29696 30720
  (FiniteChecks.interval_append test 28672 29184 29696
  (FiniteChecks.interval_append test 28672 28928 29184
  (FiniteChecks.interval_append test 28672 28800 28928
  checked_28672
  checked_28800)
  (FiniteChecks.interval_append test 28928 29056 29184
  checked_28928
  checked_29056))
  (FiniteChecks.interval_append test 29184 29440 29696
  (FiniteChecks.interval_append test 29184 29312 29440
  checked_29184
  checked_29312)
  (FiniteChecks.interval_append test 29440 29568 29696
  checked_29440
  checked_29568)))
  (FiniteChecks.interval_append test 29696 30208 30720
  (FiniteChecks.interval_append test 29696 29952 30208
  (FiniteChecks.interval_append test 29696 29824 29952
  checked_29696
  checked_29824)
  (FiniteChecks.interval_append test 29952 30080 30208
  checked_29952
  checked_30080))
  (FiniteChecks.interval_append test 30208 30464 30720
  (FiniteChecks.interval_append test 30208 30336 30464
  checked_30208
  checked_30336)
  (FiniteChecks.interval_append test 30464 30592 30720
  checked_30464
  checked_30592))))
  (FiniteChecks.interval_append test 30720 31744 32768
  (FiniteChecks.interval_append test 30720 31232 31744
  (FiniteChecks.interval_append test 30720 30976 31232
  (FiniteChecks.interval_append test 30720 30848 30976
  checked_30720
  checked_30848)
  (FiniteChecks.interval_append test 30976 31104 31232
  checked_30976
  checked_31104))
  (FiniteChecks.interval_append test 31232 31488 31744
  (FiniteChecks.interval_append test 31232 31360 31488
  checked_31232
  checked_31360)
  (FiniteChecks.interval_append test 31488 31616 31744
  checked_31488
  checked_31616)))
  (FiniteChecks.interval_append test 31744 32256 32768
  (FiniteChecks.interval_append test 31744 32000 32256
  (FiniteChecks.interval_append test 31744 31872 32000
  checked_31744
  checked_31872)
  (FiniteChecks.interval_append test 32000 32128 32256
  checked_32000
  checked_32128))
  (FiniteChecks.interval_append test 32256 32512 32768
  (FiniteChecks.interval_append test 32256 32384 32512
  checked_32256
  checked_32384)
  (FiniteChecks.interval_append test 32512 32640 32768
  checked_32512
  checked_32640)))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.Fast
