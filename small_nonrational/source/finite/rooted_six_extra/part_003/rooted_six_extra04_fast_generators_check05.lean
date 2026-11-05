module
prelude
public import RootedSixExtra04FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_20480 : FiniteChecks.Interval test 20480 20608 :=
  FiniteChecks.interval_of_check test 20480 128 (by decide +kernel)
theorem checked_20608 : FiniteChecks.Interval test 20608 20736 :=
  FiniteChecks.interval_of_check test 20608 128 (by decide +kernel)
theorem checked_20736 : FiniteChecks.Interval test 20736 20864 :=
  FiniteChecks.interval_of_check test 20736 128 (by decide +kernel)
theorem checked_20864 : FiniteChecks.Interval test 20864 20992 :=
  FiniteChecks.interval_of_check test 20864 128 (by decide +kernel)
theorem checked_20992 : FiniteChecks.Interval test 20992 21120 :=
  FiniteChecks.interval_of_check test 20992 128 (by decide +kernel)
theorem checked_21120 : FiniteChecks.Interval test 21120 21248 :=
  FiniteChecks.interval_of_check test 21120 128 (by decide +kernel)
theorem checked_21248 : FiniteChecks.Interval test 21248 21376 :=
  FiniteChecks.interval_of_check test 21248 128 (by decide +kernel)
theorem checked_21376 : FiniteChecks.Interval test 21376 21504 :=
  FiniteChecks.interval_of_check test 21376 128 (by decide +kernel)
theorem checked_21504 : FiniteChecks.Interval test 21504 21632 :=
  FiniteChecks.interval_of_check test 21504 128 (by decide +kernel)
theorem checked_21632 : FiniteChecks.Interval test 21632 21760 :=
  FiniteChecks.interval_of_check test 21632 128 (by decide +kernel)
theorem checked_21760 : FiniteChecks.Interval test 21760 21840 :=
  FiniteChecks.interval_of_check test 21760 80 (by decide +kernel)
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
