module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra06FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_9 8192 8320 128
cert_checked_9 8320 8448 128
cert_checked_9 8448 8576 128
cert_checked_9 8576 8704 128
cert_checked_9 8704 8832 128
cert_checked_9 8832 8960 128
cert_checked_9 8960 9088 128
cert_checked_9 9088 9216 128
cert_checked_9 9216 9344 128
cert_checked_9 9344 9472 128
cert_checked_9 9472 9600 128
cert_checked_9 9600 9728 128
cert_checked_9 9728 9856 128
cert_checked_9 9856 9984 128
cert_checked_9 9984 10112 128
cert_checked_9 10112 10240 128
cert_checked_9 10240 10368 128
cert_checked_9 10368 10496 128
cert_checked_9 10496 10624 128
cert_checked_9 10624 10752 128
cert_checked_9 10752 10880 128
cert_checked_9 10880 11008 128
cert_checked_9 11008 11136 128
cert_checked_9 11136 11264 128
cert_checked_9 11264 11392 128
cert_checked_9 11392 11500 108
theorem interval_8192 : FiniteChecks.Interval test 8192 11500 :=
  (FiniteChecks.interval_append test 8192 9856 11500
  (FiniteChecks.interval_append test 8192 8960 9856
  (FiniteChecks.interval_append test 8192 8576 8960
  (FiniteChecks.interval_append test 8192 8320 8576
  checked_8192
  (FiniteChecks.interval_append test 8320 8448 8576
  checked_8320
  checked_8448))
  (FiniteChecks.interval_append test 8576 8704 8960
  checked_8576
  (FiniteChecks.interval_append test 8704 8832 8960
  checked_8704
  checked_8832)))
  (FiniteChecks.interval_append test 8960 9344 9856
  (FiniteChecks.interval_append test 8960 9088 9344
  checked_8960
  (FiniteChecks.interval_append test 9088 9216 9344
  checked_9088
  checked_9216))
  (FiniteChecks.interval_append test 9344 9600 9856
  (FiniteChecks.interval_append test 9344 9472 9600
  checked_9344
  checked_9472)
  (FiniteChecks.interval_append test 9600 9728 9856
  checked_9600
  checked_9728))))
  (FiniteChecks.interval_append test 9856 10624 11500
  (FiniteChecks.interval_append test 9856 10240 10624
  (FiniteChecks.interval_append test 9856 9984 10240
  checked_9856
  (FiniteChecks.interval_append test 9984 10112 10240
  checked_9984
  checked_10112))
  (FiniteChecks.interval_append test 10240 10368 10624
  checked_10240
  (FiniteChecks.interval_append test 10368 10496 10624
  checked_10368
  checked_10496)))
  (FiniteChecks.interval_append test 10624 11008 11500
  (FiniteChecks.interval_append test 10624 10752 11008
  checked_10624
  (FiniteChecks.interval_append test 10752 10880 11008
  checked_10752
  checked_10880))
  (FiniteChecks.interval_append test 11008 11264 11500
  (FiniteChecks.interval_append test 11008 11136 11264
  checked_11008
  checked_11136)
  (FiniteChecks.interval_append test 11264 11392 11500
  checked_11264
  checked_11392)))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.Fast
