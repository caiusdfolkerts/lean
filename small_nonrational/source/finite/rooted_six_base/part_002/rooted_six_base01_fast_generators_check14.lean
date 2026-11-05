module
prelude
public import RootedSixBase01FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_57344 : FiniteChecks.Interval test 57344 57472 :=
  FiniteChecks.interval_of_check test 57344 128 (by decide +kernel)
theorem checked_57472 : FiniteChecks.Interval test 57472 57600 :=
  FiniteChecks.interval_of_check test 57472 128 (by decide +kernel)
theorem checked_57600 : FiniteChecks.Interval test 57600 57728 :=
  FiniteChecks.interval_of_check test 57600 128 (by decide +kernel)
theorem checked_57728 : FiniteChecks.Interval test 57728 57856 :=
  FiniteChecks.interval_of_check test 57728 128 (by decide +kernel)
theorem checked_57856 : FiniteChecks.Interval test 57856 57984 :=
  FiniteChecks.interval_of_check test 57856 128 (by decide +kernel)
theorem checked_57984 : FiniteChecks.Interval test 57984 58112 :=
  FiniteChecks.interval_of_check test 57984 128 (by decide +kernel)
theorem checked_58112 : FiniteChecks.Interval test 58112 58240 :=
  FiniteChecks.interval_of_check test 58112 128 (by decide +kernel)
theorem checked_58240 : FiniteChecks.Interval test 58240 58368 :=
  FiniteChecks.interval_of_check test 58240 128 (by decide +kernel)
theorem checked_58368 : FiniteChecks.Interval test 58368 58496 :=
  FiniteChecks.interval_of_check test 58368 128 (by decide +kernel)
theorem checked_58496 : FiniteChecks.Interval test 58496 58624 :=
  FiniteChecks.interval_of_check test 58496 128 (by decide +kernel)
theorem checked_58624 : FiniteChecks.Interval test 58624 58752 :=
  FiniteChecks.interval_of_check test 58624 128 (by decide +kernel)
theorem checked_58752 : FiniteChecks.Interval test 58752 58880 :=
  FiniteChecks.interval_of_check test 58752 128 (by decide +kernel)
theorem checked_58880 : FiniteChecks.Interval test 58880 59008 :=
  FiniteChecks.interval_of_check test 58880 128 (by decide +kernel)
theorem checked_59008 : FiniteChecks.Interval test 59008 59136 :=
  FiniteChecks.interval_of_check test 59008 128 (by decide +kernel)
theorem checked_59136 : FiniteChecks.Interval test 59136 59264 :=
  FiniteChecks.interval_of_check test 59136 128 (by decide +kernel)
theorem checked_59264 : FiniteChecks.Interval test 59264 59392 :=
  FiniteChecks.interval_of_check test 59264 128 (by decide +kernel)
theorem checked_59392 : FiniteChecks.Interval test 59392 59520 :=
  FiniteChecks.interval_of_check test 59392 128 (by decide +kernel)
theorem checked_59520 : FiniteChecks.Interval test 59520 59648 :=
  FiniteChecks.interval_of_check test 59520 128 (by decide +kernel)
theorem checked_59648 : FiniteChecks.Interval test 59648 59776 :=
  FiniteChecks.interval_of_check test 59648 128 (by decide +kernel)
theorem checked_59776 : FiniteChecks.Interval test 59776 59904 :=
  FiniteChecks.interval_of_check test 59776 128 (by decide +kernel)
theorem checked_59904 : FiniteChecks.Interval test 59904 60032 :=
  FiniteChecks.interval_of_check test 59904 128 (by decide +kernel)
theorem checked_60032 : FiniteChecks.Interval test 60032 60160 :=
  FiniteChecks.interval_of_check test 60032 128 (by decide +kernel)
theorem checked_60160 : FiniteChecks.Interval test 60160 60288 :=
  FiniteChecks.interval_of_check test 60160 128 (by decide +kernel)
theorem checked_60288 : FiniteChecks.Interval test 60288 60416 :=
  FiniteChecks.interval_of_check test 60288 128 (by decide +kernel)
theorem checked_60416 : FiniteChecks.Interval test 60416 60544 :=
  FiniteChecks.interval_of_check test 60416 128 (by decide +kernel)
theorem checked_60544 : FiniteChecks.Interval test 60544 60672 :=
  FiniteChecks.interval_of_check test 60544 128 (by decide +kernel)
theorem checked_60672 : FiniteChecks.Interval test 60672 60800 :=
  FiniteChecks.interval_of_check test 60672 128 (by decide +kernel)
theorem checked_60800 : FiniteChecks.Interval test 60800 60928 :=
  FiniteChecks.interval_of_check test 60800 128 (by decide +kernel)
theorem checked_60928 : FiniteChecks.Interval test 60928 60984 :=
  FiniteChecks.interval_of_check test 60928 56 (by decide +kernel)
theorem interval_57344 : FiniteChecks.Interval test 57344 60984 :=
  (FiniteChecks.interval_append test 57344 59136 60984
  (FiniteChecks.interval_append test 57344 58240 59136
  (FiniteChecks.interval_append test 57344 57728 58240
  (FiniteChecks.interval_append test 57344 57472 57728
  checked_57344
  (FiniteChecks.interval_append test 57472 57600 57728
  checked_57472
  checked_57600))
  (FiniteChecks.interval_append test 57728 57984 58240
  (FiniteChecks.interval_append test 57728 57856 57984
  checked_57728
  checked_57856)
  (FiniteChecks.interval_append test 57984 58112 58240
  checked_57984
  checked_58112)))
  (FiniteChecks.interval_append test 58240 58624 59136
  (FiniteChecks.interval_append test 58240 58368 58624
  checked_58240
  (FiniteChecks.interval_append test 58368 58496 58624
  checked_58368
  checked_58496))
  (FiniteChecks.interval_append test 58624 58880 59136
  (FiniteChecks.interval_append test 58624 58752 58880
  checked_58624
  checked_58752)
  (FiniteChecks.interval_append test 58880 59008 59136
  checked_58880
  checked_59008))))
  (FiniteChecks.interval_append test 59136 60032 60984
  (FiniteChecks.interval_append test 59136 59520 60032
  (FiniteChecks.interval_append test 59136 59264 59520
  checked_59136
  (FiniteChecks.interval_append test 59264 59392 59520
  checked_59264
  checked_59392))
  (FiniteChecks.interval_append test 59520 59776 60032
  (FiniteChecks.interval_append test 59520 59648 59776
  checked_59520
  checked_59648)
  (FiniteChecks.interval_append test 59776 59904 60032
  checked_59776
  checked_59904)))
  (FiniteChecks.interval_append test 60032 60544 60984
  (FiniteChecks.interval_append test 60032 60288 60544
  (FiniteChecks.interval_append test 60032 60160 60288
  checked_60032
  checked_60160)
  (FiniteChecks.interval_append test 60288 60416 60544
  checked_60288
  checked_60416))
  (FiniteChecks.interval_append test 60544 60800 60984
  (FiniteChecks.interval_append test 60544 60672 60800
  checked_60544
  checked_60672)
  (FiniteChecks.interval_append test 60800 60928 60984
  checked_60800
  checked_60928)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
