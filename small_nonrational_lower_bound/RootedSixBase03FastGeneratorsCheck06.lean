module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase03FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 24576 24704 128
cert_checked_7 24704 24832 128
cert_checked_7 24832 24960 128
cert_checked_7 24960 25088 128
cert_checked_7 25088 25216 128
cert_checked_7 25216 25344 128
cert_checked_7 25344 25472 128
cert_checked_7 25472 25600 128
cert_checked_7 25600 25728 128
cert_checked_7 25728 25856 128
cert_checked_7 25856 25984 128
cert_checked_7 25984 26112 128
cert_checked_7 26112 26190 78
theorem interval_24576 : FiniteChecks.Interval test 24576 26190 :=
  (FiniteChecks.interval_append test 24576 25344 26190
  (FiniteChecks.interval_append test 24576 24960 25344
  (FiniteChecks.interval_append test 24576 24704 24960
  checked_24576
  (FiniteChecks.interval_append test 24704 24832 24960
  checked_24704
  checked_24832))
  (FiniteChecks.interval_append test 24960 25088 25344
  checked_24960
  (FiniteChecks.interval_append test 25088 25216 25344
  checked_25088
  checked_25216)))
  (FiniteChecks.interval_append test 25344 25728 26190
  (FiniteChecks.interval_append test 25344 25472 25728
  checked_25344
  (FiniteChecks.interval_append test 25472 25600 25728
  checked_25472
  checked_25600))
  (FiniteChecks.interval_append test 25728 25984 26190
  (FiniteChecks.interval_append test 25728 25856 25984
  checked_25728
  checked_25856)
  (FiniteChecks.interval_append test 25984 26112 26190
  checked_25984
  checked_26112))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.Fast
