module
prelude
public import RootedSixBase00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_73728 : FiniteChecks.Interval test 73728 73856 :=
  FiniteChecks.interval_of_check test 73728 128 (by decide +kernel)
theorem checked_73856 : FiniteChecks.Interval test 73856 73984 :=
  FiniteChecks.interval_of_check test 73856 128 (by decide +kernel)
theorem checked_73984 : FiniteChecks.Interval test 73984 74112 :=
  FiniteChecks.interval_of_check test 73984 128 (by decide +kernel)
theorem checked_74112 : FiniteChecks.Interval test 74112 74240 :=
  FiniteChecks.interval_of_check test 74112 128 (by decide +kernel)
theorem checked_74240 : FiniteChecks.Interval test 74240 74368 :=
  FiniteChecks.interval_of_check test 74240 128 (by decide +kernel)
theorem checked_74368 : FiniteChecks.Interval test 74368 74496 :=
  FiniteChecks.interval_of_check test 74368 128 (by decide +kernel)
theorem checked_74496 : FiniteChecks.Interval test 74496 74624 :=
  FiniteChecks.interval_of_check test 74496 128 (by decide +kernel)
theorem checked_74624 : FiniteChecks.Interval test 74624 74752 :=
  FiniteChecks.interval_of_check test 74624 128 (by decide +kernel)
theorem checked_74752 : FiniteChecks.Interval test 74752 74880 :=
  FiniteChecks.interval_of_check test 74752 128 (by decide +kernel)
theorem checked_74880 : FiniteChecks.Interval test 74880 75008 :=
  FiniteChecks.interval_of_check test 74880 128 (by decide +kernel)
theorem checked_75008 : FiniteChecks.Interval test 75008 75136 :=
  FiniteChecks.interval_of_check test 75008 128 (by decide +kernel)
theorem checked_75136 : FiniteChecks.Interval test 75136 75264 :=
  FiniteChecks.interval_of_check test 75136 128 (by decide +kernel)
theorem checked_75264 : FiniteChecks.Interval test 75264 75392 :=
  FiniteChecks.interval_of_check test 75264 128 (by decide +kernel)
theorem checked_75392 : FiniteChecks.Interval test 75392 75520 :=
  FiniteChecks.interval_of_check test 75392 128 (by decide +kernel)
theorem checked_75520 : FiniteChecks.Interval test 75520 75648 :=
  FiniteChecks.interval_of_check test 75520 128 (by decide +kernel)
theorem checked_75648 : FiniteChecks.Interval test 75648 75776 :=
  FiniteChecks.interval_of_check test 75648 128 (by decide +kernel)
theorem checked_75776 : FiniteChecks.Interval test 75776 75904 :=
  FiniteChecks.interval_of_check test 75776 128 (by decide +kernel)
theorem checked_75904 : FiniteChecks.Interval test 75904 76032 :=
  FiniteChecks.interval_of_check test 75904 128 (by decide +kernel)
theorem checked_76032 : FiniteChecks.Interval test 76032 76160 :=
  FiniteChecks.interval_of_check test 76032 128 (by decide +kernel)
theorem checked_76160 : FiniteChecks.Interval test 76160 76288 :=
  FiniteChecks.interval_of_check test 76160 128 (by decide +kernel)
theorem checked_76288 : FiniteChecks.Interval test 76288 76416 :=
  FiniteChecks.interval_of_check test 76288 128 (by decide +kernel)
theorem checked_76416 : FiniteChecks.Interval test 76416 76544 :=
  FiniteChecks.interval_of_check test 76416 128 (by decide +kernel)
theorem checked_76544 : FiniteChecks.Interval test 76544 76672 :=
  FiniteChecks.interval_of_check test 76544 128 (by decide +kernel)
theorem checked_76672 : FiniteChecks.Interval test 76672 76800 :=
  FiniteChecks.interval_of_check test 76672 128 (by decide +kernel)
theorem checked_76800 : FiniteChecks.Interval test 76800 76928 :=
  FiniteChecks.interval_of_check test 76800 128 (by decide +kernel)
theorem checked_76928 : FiniteChecks.Interval test 76928 77056 :=
  FiniteChecks.interval_of_check test 76928 128 (by decide +kernel)
theorem checked_77056 : FiniteChecks.Interval test 77056 77184 :=
  FiniteChecks.interval_of_check test 77056 128 (by decide +kernel)
theorem checked_77184 : FiniteChecks.Interval test 77184 77312 :=
  FiniteChecks.interval_of_check test 77184 128 (by decide +kernel)
theorem checked_77312 : FiniteChecks.Interval test 77312 77440 :=
  FiniteChecks.interval_of_check test 77312 128 (by decide +kernel)
theorem checked_77440 : FiniteChecks.Interval test 77440 77568 :=
  FiniteChecks.interval_of_check test 77440 128 (by decide +kernel)
theorem checked_77568 : FiniteChecks.Interval test 77568 77696 :=
  FiniteChecks.interval_of_check test 77568 128 (by decide +kernel)
theorem checked_77696 : FiniteChecks.Interval test 77696 77824 :=
  FiniteChecks.interval_of_check test 77696 128 (by decide +kernel)
theorem interval_73728 : FiniteChecks.Interval test 73728 77824 :=
  (FiniteChecks.interval_append test 73728 75776 77824
  (FiniteChecks.interval_append test 73728 74752 75776
  (FiniteChecks.interval_append test 73728 74240 74752
  (FiniteChecks.interval_append test 73728 73984 74240
  (FiniteChecks.interval_append test 73728 73856 73984
  checked_73728
  checked_73856)
  (FiniteChecks.interval_append test 73984 74112 74240
  checked_73984
  checked_74112))
  (FiniteChecks.interval_append test 74240 74496 74752
  (FiniteChecks.interval_append test 74240 74368 74496
  checked_74240
  checked_74368)
  (FiniteChecks.interval_append test 74496 74624 74752
  checked_74496
  checked_74624)))
  (FiniteChecks.interval_append test 74752 75264 75776
  (FiniteChecks.interval_append test 74752 75008 75264
  (FiniteChecks.interval_append test 74752 74880 75008
  checked_74752
  checked_74880)
  (FiniteChecks.interval_append test 75008 75136 75264
  checked_75008
  checked_75136))
  (FiniteChecks.interval_append test 75264 75520 75776
  (FiniteChecks.interval_append test 75264 75392 75520
  checked_75264
  checked_75392)
  (FiniteChecks.interval_append test 75520 75648 75776
  checked_75520
  checked_75648))))
  (FiniteChecks.interval_append test 75776 76800 77824
  (FiniteChecks.interval_append test 75776 76288 76800
  (FiniteChecks.interval_append test 75776 76032 76288
  (FiniteChecks.interval_append test 75776 75904 76032
  checked_75776
  checked_75904)
  (FiniteChecks.interval_append test 76032 76160 76288
  checked_76032
  checked_76160))
  (FiniteChecks.interval_append test 76288 76544 76800
  (FiniteChecks.interval_append test 76288 76416 76544
  checked_76288
  checked_76416)
  (FiniteChecks.interval_append test 76544 76672 76800
  checked_76544
  checked_76672)))
  (FiniteChecks.interval_append test 76800 77312 77824
  (FiniteChecks.interval_append test 76800 77056 77312
  (FiniteChecks.interval_append test 76800 76928 77056
  checked_76800
  checked_76928)
  (FiniteChecks.interval_append test 77056 77184 77312
  checked_77056
  checked_77184))
  (FiniteChecks.interval_append test 77312 77568 77824
  (FiniteChecks.interval_append test 77312 77440 77568
  checked_77312
  checked_77440)
  (FiniteChecks.interval_append test 77568 77696 77824
  checked_77568
  checked_77696)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
