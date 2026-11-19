module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra04FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_9 20480 20608 128
cert_checked_9 20608 20736 128
cert_checked_9 20736 20864 128
cert_checked_9 20864 20992 128
cert_checked_9 20992 21120 128
cert_checked_9 21120 21248 128
cert_checked_9 21248 21376 128
cert_checked_9 21376 21504 128
cert_checked_9 21504 21632 128
cert_checked_9 21632 21760 128
cert_checked_9 21760 21840 80
theorem interval_20480 : FiniteChecks.Interval test 20480 21840 :=
  (FiniteChecks.interval_append test 20480 21120 21840
  (FiniteChecks.interval_append test 20480 20736 21120
  (FiniteChecks.interval_append test 20480 20608 20736
  checked_20480
  checked_20608)
  (FiniteChecks.interval_append test 20736 20864 21120
  checked_20736
  (FiniteChecks.interval_append test 20864 20992 21120
  checked_20864
  checked_20992)))
  (FiniteChecks.interval_append test 21120 21504 21840
  (FiniteChecks.interval_append test 21120 21248 21504
  checked_21120
  (FiniteChecks.interval_append test 21248 21376 21504
  checked_21248
  checked_21376))
  (FiniteChecks.interval_append test 21504 21632 21840
  checked_21504
  (FiniteChecks.interval_append test 21632 21760 21840
  checked_21632
  checked_21760))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.Fast
