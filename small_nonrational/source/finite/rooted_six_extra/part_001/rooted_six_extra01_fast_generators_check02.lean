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
theorem checked_8192 : FiniteChecks.Interval test 8192 8320 :=
  FiniteChecks.interval_of_check test 8192 128 (by decide +kernel)
theorem checked_8320 : FiniteChecks.Interval test 8320 8448 :=
  FiniteChecks.interval_of_check test 8320 128 (by decide +kernel)
theorem checked_8448 : FiniteChecks.Interval test 8448 8576 :=
  FiniteChecks.interval_of_check test 8448 128 (by decide +kernel)
theorem checked_8576 : FiniteChecks.Interval test 8576 8704 :=
  FiniteChecks.interval_of_check test 8576 128 (by decide +kernel)
theorem checked_8704 : FiniteChecks.Interval test 8704 8832 :=
  FiniteChecks.interval_of_check test 8704 128 (by decide +kernel)
theorem checked_8832 : FiniteChecks.Interval test 8832 8960 :=
  FiniteChecks.interval_of_check test 8832 128 (by decide +kernel)
theorem checked_8960 : FiniteChecks.Interval test 8960 9088 :=
  FiniteChecks.interval_of_check test 8960 128 (by decide +kernel)
theorem checked_9088 : FiniteChecks.Interval test 9088 9216 :=
  FiniteChecks.interval_of_check test 9088 128 (by decide +kernel)
theorem checked_9216 : FiniteChecks.Interval test 9216 9344 :=
  FiniteChecks.interval_of_check test 9216 128 (by decide +kernel)
theorem checked_9344 : FiniteChecks.Interval test 9344 9472 :=
  FiniteChecks.interval_of_check test 9344 128 (by decide +kernel)
theorem checked_9472 : FiniteChecks.Interval test 9472 9600 :=
  FiniteChecks.interval_of_check test 9472 128 (by decide +kernel)
theorem checked_9600 : FiniteChecks.Interval test 9600 9728 :=
  FiniteChecks.interval_of_check test 9600 128 (by decide +kernel)
theorem checked_9728 : FiniteChecks.Interval test 9728 9856 :=
  FiniteChecks.interval_of_check test 9728 128 (by decide +kernel)
theorem checked_9856 : FiniteChecks.Interval test 9856 9984 :=
  FiniteChecks.interval_of_check test 9856 128 (by decide +kernel)
theorem checked_9984 : FiniteChecks.Interval test 9984 10112 :=
  FiniteChecks.interval_of_check test 9984 128 (by decide +kernel)
theorem checked_10112 : FiniteChecks.Interval test 10112 10240 :=
  FiniteChecks.interval_of_check test 10112 128 (by decide +kernel)
theorem checked_10240 : FiniteChecks.Interval test 10240 10368 :=
  FiniteChecks.interval_of_check test 10240 128 (by decide +kernel)
theorem checked_10368 : FiniteChecks.Interval test 10368 10496 :=
  FiniteChecks.interval_of_check test 10368 128 (by decide +kernel)
theorem checked_10496 : FiniteChecks.Interval test 10496 10624 :=
  FiniteChecks.interval_of_check test 10496 128 (by decide +kernel)
theorem checked_10624 : FiniteChecks.Interval test 10624 10752 :=
  FiniteChecks.interval_of_check test 10624 128 (by decide +kernel)
theorem checked_10752 : FiniteChecks.Interval test 10752 10880 :=
  FiniteChecks.interval_of_check test 10752 128 (by decide +kernel)
theorem checked_10880 : FiniteChecks.Interval test 10880 11008 :=
  FiniteChecks.interval_of_check test 10880 128 (by decide +kernel)
theorem checked_11008 : FiniteChecks.Interval test 11008 11136 :=
  FiniteChecks.interval_of_check test 11008 128 (by decide +kernel)
theorem checked_11136 : FiniteChecks.Interval test 11136 11264 :=
  FiniteChecks.interval_of_check test 11136 128 (by decide +kernel)
theorem checked_11264 : FiniteChecks.Interval test 11264 11392 :=
  FiniteChecks.interval_of_check test 11264 128 (by decide +kernel)
theorem checked_11392 : FiniteChecks.Interval test 11392 11520 :=
  FiniteChecks.interval_of_check test 11392 128 (by decide +kernel)
theorem checked_11520 : FiniteChecks.Interval test 11520 11648 :=
  FiniteChecks.interval_of_check test 11520 128 (by decide +kernel)
theorem checked_11648 : FiniteChecks.Interval test 11648 11776 :=
  FiniteChecks.interval_of_check test 11648 128 (by decide +kernel)
theorem checked_11776 : FiniteChecks.Interval test 11776 11904 :=
  FiniteChecks.interval_of_check test 11776 128 (by decide +kernel)
theorem checked_11904 : FiniteChecks.Interval test 11904 12032 :=
  FiniteChecks.interval_of_check test 11904 128 (by decide +kernel)
theorem checked_12032 : FiniteChecks.Interval test 12032 12160 :=
  FiniteChecks.interval_of_check test 12032 128 (by decide +kernel)
theorem checked_12160 : FiniteChecks.Interval test 12160 12288 :=
  FiniteChecks.interval_of_check test 12160 128 (by decide +kernel)
theorem interval_8192 : FiniteChecks.Interval test 8192 12288 :=
  (FiniteChecks.interval_append test 8192 10240 12288
  (FiniteChecks.interval_append test 8192 9216 10240
  (FiniteChecks.interval_append test 8192 8704 9216
  (FiniteChecks.interval_append test 8192 8448 8704
  (FiniteChecks.interval_append test 8192 8320 8448
  checked_8192
  checked_8320)
  (FiniteChecks.interval_append test 8448 8576 8704
  checked_8448
  checked_8576))
  (FiniteChecks.interval_append test 8704 8960 9216
  (FiniteChecks.interval_append test 8704 8832 8960
  checked_8704
  checked_8832)
  (FiniteChecks.interval_append test 8960 9088 9216
  checked_8960
  checked_9088)))
  (FiniteChecks.interval_append test 9216 9728 10240
  (FiniteChecks.interval_append test 9216 9472 9728
  (FiniteChecks.interval_append test 9216 9344 9472
  checked_9216
  checked_9344)
  (FiniteChecks.interval_append test 9472 9600 9728
  checked_9472
  checked_9600))
  (FiniteChecks.interval_append test 9728 9984 10240
  (FiniteChecks.interval_append test 9728 9856 9984
  checked_9728
  checked_9856)
  (FiniteChecks.interval_append test 9984 10112 10240
  checked_9984
  checked_10112))))
  (FiniteChecks.interval_append test 10240 11264 12288
  (FiniteChecks.interval_append test 10240 10752 11264
  (FiniteChecks.interval_append test 10240 10496 10752
  (FiniteChecks.interval_append test 10240 10368 10496
  checked_10240
  checked_10368)
  (FiniteChecks.interval_append test 10496 10624 10752
  checked_10496
  checked_10624))
  (FiniteChecks.interval_append test 10752 11008 11264
  (FiniteChecks.interval_append test 10752 10880 11008
  checked_10752
  checked_10880)
  (FiniteChecks.interval_append test 11008 11136 11264
  checked_11008
  checked_11136)))
  (FiniteChecks.interval_append test 11264 11776 12288
  (FiniteChecks.interval_append test 11264 11520 11776
  (FiniteChecks.interval_append test 11264 11392 11520
  checked_11264
  checked_11392)
  (FiniteChecks.interval_append test 11520 11648 11776
  checked_11520
  checked_11648))
  (FiniteChecks.interval_append test 11776 12032 12288
  (FiniteChecks.interval_append test 11776 11904 12032
  checked_11776
  checked_11904)
  (FiniteChecks.interval_append test 12032 12160 12288
  checked_12032
  checked_12160)))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.Fast
