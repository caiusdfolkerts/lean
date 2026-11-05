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
theorem checked_81920 : FiniteChecks.Interval test 81920 82048 :=
  FiniteChecks.interval_of_check test 81920 128 (by decide +kernel)
theorem checked_82048 : FiniteChecks.Interval test 82048 82176 :=
  FiniteChecks.interval_of_check test 82048 128 (by decide +kernel)
theorem checked_82176 : FiniteChecks.Interval test 82176 82304 :=
  FiniteChecks.interval_of_check test 82176 128 (by decide +kernel)
theorem checked_82304 : FiniteChecks.Interval test 82304 82432 :=
  FiniteChecks.interval_of_check test 82304 128 (by decide +kernel)
theorem checked_82432 : FiniteChecks.Interval test 82432 82560 :=
  FiniteChecks.interval_of_check test 82432 128 (by decide +kernel)
theorem checked_82560 : FiniteChecks.Interval test 82560 82688 :=
  FiniteChecks.interval_of_check test 82560 128 (by decide +kernel)
theorem checked_82688 : FiniteChecks.Interval test 82688 82816 :=
  FiniteChecks.interval_of_check test 82688 128 (by decide +kernel)
theorem checked_82816 : FiniteChecks.Interval test 82816 82944 :=
  FiniteChecks.interval_of_check test 82816 128 (by decide +kernel)
theorem checked_82944 : FiniteChecks.Interval test 82944 83072 :=
  FiniteChecks.interval_of_check test 82944 128 (by decide +kernel)
theorem checked_83072 : FiniteChecks.Interval test 83072 83200 :=
  FiniteChecks.interval_of_check test 83072 128 (by decide +kernel)
theorem checked_83200 : FiniteChecks.Interval test 83200 83328 :=
  FiniteChecks.interval_of_check test 83200 128 (by decide +kernel)
theorem checked_83328 : FiniteChecks.Interval test 83328 83456 :=
  FiniteChecks.interval_of_check test 83328 128 (by decide +kernel)
theorem checked_83456 : FiniteChecks.Interval test 83456 83584 :=
  FiniteChecks.interval_of_check test 83456 128 (by decide +kernel)
theorem checked_83584 : FiniteChecks.Interval test 83584 83712 :=
  FiniteChecks.interval_of_check test 83584 128 (by decide +kernel)
theorem checked_83712 : FiniteChecks.Interval test 83712 83840 :=
  FiniteChecks.interval_of_check test 83712 128 (by decide +kernel)
theorem checked_83840 : FiniteChecks.Interval test 83840 83968 :=
  FiniteChecks.interval_of_check test 83840 128 (by decide +kernel)
theorem checked_83968 : FiniteChecks.Interval test 83968 84096 :=
  FiniteChecks.interval_of_check test 83968 128 (by decide +kernel)
theorem checked_84096 : FiniteChecks.Interval test 84096 84224 :=
  FiniteChecks.interval_of_check test 84096 128 (by decide +kernel)
theorem checked_84224 : FiniteChecks.Interval test 84224 84352 :=
  FiniteChecks.interval_of_check test 84224 128 (by decide +kernel)
theorem checked_84352 : FiniteChecks.Interval test 84352 84480 :=
  FiniteChecks.interval_of_check test 84352 128 (by decide +kernel)
theorem checked_84480 : FiniteChecks.Interval test 84480 84608 :=
  FiniteChecks.interval_of_check test 84480 128 (by decide +kernel)
theorem checked_84608 : FiniteChecks.Interval test 84608 84736 :=
  FiniteChecks.interval_of_check test 84608 128 (by decide +kernel)
theorem checked_84736 : FiniteChecks.Interval test 84736 84864 :=
  FiniteChecks.interval_of_check test 84736 128 (by decide +kernel)
theorem checked_84864 : FiniteChecks.Interval test 84864 84992 :=
  FiniteChecks.interval_of_check test 84864 128 (by decide +kernel)
theorem checked_84992 : FiniteChecks.Interval test 84992 85120 :=
  FiniteChecks.interval_of_check test 84992 128 (by decide +kernel)
theorem checked_85120 : FiniteChecks.Interval test 85120 85248 :=
  FiniteChecks.interval_of_check test 85120 128 (by decide +kernel)
theorem checked_85248 : FiniteChecks.Interval test 85248 85376 :=
  FiniteChecks.interval_of_check test 85248 128 (by decide +kernel)
theorem checked_85376 : FiniteChecks.Interval test 85376 85504 :=
  FiniteChecks.interval_of_check test 85376 128 (by decide +kernel)
theorem checked_85504 : FiniteChecks.Interval test 85504 85632 :=
  FiniteChecks.interval_of_check test 85504 128 (by decide +kernel)
theorem checked_85632 : FiniteChecks.Interval test 85632 85760 :=
  FiniteChecks.interval_of_check test 85632 128 (by decide +kernel)
theorem checked_85760 : FiniteChecks.Interval test 85760 85888 :=
  FiniteChecks.interval_of_check test 85760 128 (by decide +kernel)
theorem checked_85888 : FiniteChecks.Interval test 85888 86016 :=
  FiniteChecks.interval_of_check test 85888 128 (by decide +kernel)
theorem interval_81920 : FiniteChecks.Interval test 81920 86016 :=
  (FiniteChecks.interval_append test 81920 83968 86016
  (FiniteChecks.interval_append test 81920 82944 83968
  (FiniteChecks.interval_append test 81920 82432 82944
  (FiniteChecks.interval_append test 81920 82176 82432
  (FiniteChecks.interval_append test 81920 82048 82176
  checked_81920
  checked_82048)
  (FiniteChecks.interval_append test 82176 82304 82432
  checked_82176
  checked_82304))
  (FiniteChecks.interval_append test 82432 82688 82944
  (FiniteChecks.interval_append test 82432 82560 82688
  checked_82432
  checked_82560)
  (FiniteChecks.interval_append test 82688 82816 82944
  checked_82688
  checked_82816)))
  (FiniteChecks.interval_append test 82944 83456 83968
  (FiniteChecks.interval_append test 82944 83200 83456
  (FiniteChecks.interval_append test 82944 83072 83200
  checked_82944
  checked_83072)
  (FiniteChecks.interval_append test 83200 83328 83456
  checked_83200
  checked_83328))
  (FiniteChecks.interval_append test 83456 83712 83968
  (FiniteChecks.interval_append test 83456 83584 83712
  checked_83456
  checked_83584)
  (FiniteChecks.interval_append test 83712 83840 83968
  checked_83712
  checked_83840))))
  (FiniteChecks.interval_append test 83968 84992 86016
  (FiniteChecks.interval_append test 83968 84480 84992
  (FiniteChecks.interval_append test 83968 84224 84480
  (FiniteChecks.interval_append test 83968 84096 84224
  checked_83968
  checked_84096)
  (FiniteChecks.interval_append test 84224 84352 84480
  checked_84224
  checked_84352))
  (FiniteChecks.interval_append test 84480 84736 84992
  (FiniteChecks.interval_append test 84480 84608 84736
  checked_84480
  checked_84608)
  (FiniteChecks.interval_append test 84736 84864 84992
  checked_84736
  checked_84864)))
  (FiniteChecks.interval_append test 84992 85504 86016
  (FiniteChecks.interval_append test 84992 85248 85504
  (FiniteChecks.interval_append test 84992 85120 85248
  checked_84992
  checked_85120)
  (FiniteChecks.interval_append test 85248 85376 85504
  checked_85248
  checked_85376))
  (FiniteChecks.interval_append test 85504 85760 86016
  (FiniteChecks.interval_append test 85504 85632 85760
  checked_85504
  checked_85632)
  (FiniteChecks.interval_append test 85760 85888 86016
  checked_85760
  checked_85888)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
