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
theorem checked_32768 : FiniteChecks.Interval test 32768 32896 :=
  FiniteChecks.interval_of_check test 32768 128 (by decide +kernel)
theorem checked_32896 : FiniteChecks.Interval test 32896 33024 :=
  FiniteChecks.interval_of_check test 32896 128 (by decide +kernel)
theorem checked_33024 : FiniteChecks.Interval test 33024 33152 :=
  FiniteChecks.interval_of_check test 33024 128 (by decide +kernel)
theorem checked_33152 : FiniteChecks.Interval test 33152 33280 :=
  FiniteChecks.interval_of_check test 33152 128 (by decide +kernel)
theorem checked_33280 : FiniteChecks.Interval test 33280 33408 :=
  FiniteChecks.interval_of_check test 33280 128 (by decide +kernel)
theorem checked_33408 : FiniteChecks.Interval test 33408 33536 :=
  FiniteChecks.interval_of_check test 33408 128 (by decide +kernel)
theorem checked_33536 : FiniteChecks.Interval test 33536 33664 :=
  FiniteChecks.interval_of_check test 33536 128 (by decide +kernel)
theorem checked_33664 : FiniteChecks.Interval test 33664 33792 :=
  FiniteChecks.interval_of_check test 33664 128 (by decide +kernel)
theorem checked_33792 : FiniteChecks.Interval test 33792 33920 :=
  FiniteChecks.interval_of_check test 33792 128 (by decide +kernel)
theorem checked_33920 : FiniteChecks.Interval test 33920 34048 :=
  FiniteChecks.interval_of_check test 33920 128 (by decide +kernel)
theorem checked_34048 : FiniteChecks.Interval test 34048 34176 :=
  FiniteChecks.interval_of_check test 34048 128 (by decide +kernel)
theorem checked_34176 : FiniteChecks.Interval test 34176 34304 :=
  FiniteChecks.interval_of_check test 34176 128 (by decide +kernel)
theorem checked_34304 : FiniteChecks.Interval test 34304 34432 :=
  FiniteChecks.interval_of_check test 34304 128 (by decide +kernel)
theorem checked_34432 : FiniteChecks.Interval test 34432 34560 :=
  FiniteChecks.interval_of_check test 34432 128 (by decide +kernel)
theorem checked_34560 : FiniteChecks.Interval test 34560 34688 :=
  FiniteChecks.interval_of_check test 34560 128 (by decide +kernel)
theorem checked_34688 : FiniteChecks.Interval test 34688 34816 :=
  FiniteChecks.interval_of_check test 34688 128 (by decide +kernel)
theorem checked_34816 : FiniteChecks.Interval test 34816 34944 :=
  FiniteChecks.interval_of_check test 34816 128 (by decide +kernel)
theorem checked_34944 : FiniteChecks.Interval test 34944 35072 :=
  FiniteChecks.interval_of_check test 34944 128 (by decide +kernel)
theorem checked_35072 : FiniteChecks.Interval test 35072 35200 :=
  FiniteChecks.interval_of_check test 35072 128 (by decide +kernel)
theorem checked_35200 : FiniteChecks.Interval test 35200 35328 :=
  FiniteChecks.interval_of_check test 35200 128 (by decide +kernel)
theorem checked_35328 : FiniteChecks.Interval test 35328 35456 :=
  FiniteChecks.interval_of_check test 35328 128 (by decide +kernel)
theorem checked_35456 : FiniteChecks.Interval test 35456 35584 :=
  FiniteChecks.interval_of_check test 35456 128 (by decide +kernel)
theorem checked_35584 : FiniteChecks.Interval test 35584 35712 :=
  FiniteChecks.interval_of_check test 35584 128 (by decide +kernel)
theorem checked_35712 : FiniteChecks.Interval test 35712 35840 :=
  FiniteChecks.interval_of_check test 35712 128 (by decide +kernel)
theorem checked_35840 : FiniteChecks.Interval test 35840 35968 :=
  FiniteChecks.interval_of_check test 35840 128 (by decide +kernel)
theorem checked_35968 : FiniteChecks.Interval test 35968 36096 :=
  FiniteChecks.interval_of_check test 35968 128 (by decide +kernel)
theorem checked_36096 : FiniteChecks.Interval test 36096 36224 :=
  FiniteChecks.interval_of_check test 36096 128 (by decide +kernel)
theorem checked_36224 : FiniteChecks.Interval test 36224 36352 :=
  FiniteChecks.interval_of_check test 36224 128 (by decide +kernel)
theorem checked_36352 : FiniteChecks.Interval test 36352 36480 :=
  FiniteChecks.interval_of_check test 36352 128 (by decide +kernel)
theorem checked_36480 : FiniteChecks.Interval test 36480 36608 :=
  FiniteChecks.interval_of_check test 36480 128 (by decide +kernel)
theorem checked_36608 : FiniteChecks.Interval test 36608 36736 :=
  FiniteChecks.interval_of_check test 36608 128 (by decide +kernel)
theorem checked_36736 : FiniteChecks.Interval test 36736 36864 :=
  FiniteChecks.interval_of_check test 36736 128 (by decide +kernel)
theorem interval_32768 : FiniteChecks.Interval test 32768 36864 :=
  (FiniteChecks.interval_append test 32768 34816 36864
  (FiniteChecks.interval_append test 32768 33792 34816
  (FiniteChecks.interval_append test 32768 33280 33792
  (FiniteChecks.interval_append test 32768 33024 33280
  (FiniteChecks.interval_append test 32768 32896 33024
  checked_32768
  checked_32896)
  (FiniteChecks.interval_append test 33024 33152 33280
  checked_33024
  checked_33152))
  (FiniteChecks.interval_append test 33280 33536 33792
  (FiniteChecks.interval_append test 33280 33408 33536
  checked_33280
  checked_33408)
  (FiniteChecks.interval_append test 33536 33664 33792
  checked_33536
  checked_33664)))
  (FiniteChecks.interval_append test 33792 34304 34816
  (FiniteChecks.interval_append test 33792 34048 34304
  (FiniteChecks.interval_append test 33792 33920 34048
  checked_33792
  checked_33920)
  (FiniteChecks.interval_append test 34048 34176 34304
  checked_34048
  checked_34176))
  (FiniteChecks.interval_append test 34304 34560 34816
  (FiniteChecks.interval_append test 34304 34432 34560
  checked_34304
  checked_34432)
  (FiniteChecks.interval_append test 34560 34688 34816
  checked_34560
  checked_34688))))
  (FiniteChecks.interval_append test 34816 35840 36864
  (FiniteChecks.interval_append test 34816 35328 35840
  (FiniteChecks.interval_append test 34816 35072 35328
  (FiniteChecks.interval_append test 34816 34944 35072
  checked_34816
  checked_34944)
  (FiniteChecks.interval_append test 35072 35200 35328
  checked_35072
  checked_35200))
  (FiniteChecks.interval_append test 35328 35584 35840
  (FiniteChecks.interval_append test 35328 35456 35584
  checked_35328
  checked_35456)
  (FiniteChecks.interval_append test 35584 35712 35840
  checked_35584
  checked_35712)))
  (FiniteChecks.interval_append test 35840 36352 36864
  (FiniteChecks.interval_append test 35840 36096 36352
  (FiniteChecks.interval_append test 35840 35968 36096
  checked_35840
  checked_35968)
  (FiniteChecks.interval_append test 36096 36224 36352
  checked_36096
  checked_36224))
  (FiniteChecks.interval_append test 36352 36608 36864
  (FiniteChecks.interval_append test 36352 36480 36608
  checked_36352
  checked_36480)
  (FiniteChecks.interval_append test 36608 36736 36864
  checked_36608
  checked_36736)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
