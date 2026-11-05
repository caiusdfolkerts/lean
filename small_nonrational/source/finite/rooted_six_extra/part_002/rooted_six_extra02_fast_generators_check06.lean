module
prelude
public import RootedSixExtra02FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_24576 : FiniteChecks.Interval test 24576 24704 :=
  FiniteChecks.interval_of_check test 24576 128 (by decide +kernel)
theorem checked_24704 : FiniteChecks.Interval test 24704 24832 :=
  FiniteChecks.interval_of_check test 24704 128 (by decide +kernel)
theorem checked_24832 : FiniteChecks.Interval test 24832 24960 :=
  FiniteChecks.interval_of_check test 24832 128 (by decide +kernel)
theorem checked_24960 : FiniteChecks.Interval test 24960 25088 :=
  FiniteChecks.interval_of_check test 24960 128 (by decide +kernel)
theorem checked_25088 : FiniteChecks.Interval test 25088 25216 :=
  FiniteChecks.interval_of_check test 25088 128 (by decide +kernel)
theorem checked_25216 : FiniteChecks.Interval test 25216 25344 :=
  FiniteChecks.interval_of_check test 25216 128 (by decide +kernel)
theorem checked_25344 : FiniteChecks.Interval test 25344 25472 :=
  FiniteChecks.interval_of_check test 25344 128 (by decide +kernel)
theorem checked_25472 : FiniteChecks.Interval test 25472 25600 :=
  FiniteChecks.interval_of_check test 25472 128 (by decide +kernel)
theorem checked_25600 : FiniteChecks.Interval test 25600 25728 :=
  FiniteChecks.interval_of_check test 25600 128 (by decide +kernel)
theorem checked_25728 : FiniteChecks.Interval test 25728 25856 :=
  FiniteChecks.interval_of_check test 25728 128 (by decide +kernel)
theorem checked_25856 : FiniteChecks.Interval test 25856 25984 :=
  FiniteChecks.interval_of_check test 25856 128 (by decide +kernel)
theorem checked_25984 : FiniteChecks.Interval test 25984 26112 :=
  FiniteChecks.interval_of_check test 25984 128 (by decide +kernel)
theorem checked_26112 : FiniteChecks.Interval test 26112 26240 :=
  FiniteChecks.interval_of_check test 26112 128 (by decide +kernel)
theorem checked_26240 : FiniteChecks.Interval test 26240 26368 :=
  FiniteChecks.interval_of_check test 26240 128 (by decide +kernel)
theorem checked_26368 : FiniteChecks.Interval test 26368 26480 :=
  FiniteChecks.interval_of_check test 26368 112 (by decide +kernel)
theorem interval_24576 : FiniteChecks.Interval test 24576 26480 :=
  (FiniteChecks.interval_append test 24576 25472 26480
  (FiniteChecks.interval_append test 24576 24960 25472
  (FiniteChecks.interval_append test 24576 24704 24960
  checked_24576
  (FiniteChecks.interval_append test 24704 24832 24960
  checked_24704
  checked_24832))
  (FiniteChecks.interval_append test 24960 25216 25472
  (FiniteChecks.interval_append test 24960 25088 25216
  checked_24960
  checked_25088)
  (FiniteChecks.interval_append test 25216 25344 25472
  checked_25216
  checked_25344)))
  (FiniteChecks.interval_append test 25472 25984 26480
  (FiniteChecks.interval_append test 25472 25728 25984
  (FiniteChecks.interval_append test 25472 25600 25728
  checked_25472
  checked_25600)
  (FiniteChecks.interval_append test 25728 25856 25984
  checked_25728
  checked_25856))
  (FiniteChecks.interval_append test 25984 26240 26480
  (FiniteChecks.interval_append test 25984 26112 26240
  checked_25984
  checked_26112)
  (FiniteChecks.interval_append test 26240 26368 26480
  checked_26240
  checked_26368))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Fast
