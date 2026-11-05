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
theorem checked_98304 : FiniteChecks.Interval test 98304 98432 :=
  FiniteChecks.interval_of_check test 98304 128 (by decide +kernel)
theorem checked_98432 : FiniteChecks.Interval test 98432 98560 :=
  FiniteChecks.interval_of_check test 98432 128 (by decide +kernel)
theorem checked_98560 : FiniteChecks.Interval test 98560 98688 :=
  FiniteChecks.interval_of_check test 98560 128 (by decide +kernel)
theorem checked_98688 : FiniteChecks.Interval test 98688 98816 :=
  FiniteChecks.interval_of_check test 98688 128 (by decide +kernel)
theorem checked_98816 : FiniteChecks.Interval test 98816 98944 :=
  FiniteChecks.interval_of_check test 98816 128 (by decide +kernel)
theorem checked_98944 : FiniteChecks.Interval test 98944 99072 :=
  FiniteChecks.interval_of_check test 98944 128 (by decide +kernel)
theorem checked_99072 : FiniteChecks.Interval test 99072 99200 :=
  FiniteChecks.interval_of_check test 99072 128 (by decide +kernel)
theorem checked_99200 : FiniteChecks.Interval test 99200 99328 :=
  FiniteChecks.interval_of_check test 99200 128 (by decide +kernel)
theorem checked_99328 : FiniteChecks.Interval test 99328 99456 :=
  FiniteChecks.interval_of_check test 99328 128 (by decide +kernel)
theorem checked_99456 : FiniteChecks.Interval test 99456 99584 :=
  FiniteChecks.interval_of_check test 99456 128 (by decide +kernel)
theorem checked_99584 : FiniteChecks.Interval test 99584 99712 :=
  FiniteChecks.interval_of_check test 99584 128 (by decide +kernel)
theorem checked_99712 : FiniteChecks.Interval test 99712 99840 :=
  FiniteChecks.interval_of_check test 99712 128 (by decide +kernel)
theorem checked_99840 : FiniteChecks.Interval test 99840 99968 :=
  FiniteChecks.interval_of_check test 99840 128 (by decide +kernel)
theorem checked_99968 : FiniteChecks.Interval test 99968 100096 :=
  FiniteChecks.interval_of_check test 99968 128 (by decide +kernel)
theorem checked_100096 : FiniteChecks.Interval test 100096 100224 :=
  FiniteChecks.interval_of_check test 100096 128 (by decide +kernel)
theorem checked_100224 : FiniteChecks.Interval test 100224 100352 :=
  FiniteChecks.interval_of_check test 100224 128 (by decide +kernel)
theorem checked_100352 : FiniteChecks.Interval test 100352 100480 :=
  FiniteChecks.interval_of_check test 100352 128 (by decide +kernel)
theorem checked_100480 : FiniteChecks.Interval test 100480 100608 :=
  FiniteChecks.interval_of_check test 100480 128 (by decide +kernel)
theorem checked_100608 : FiniteChecks.Interval test 100608 100736 :=
  FiniteChecks.interval_of_check test 100608 128 (by decide +kernel)
theorem checked_100736 : FiniteChecks.Interval test 100736 100864 :=
  FiniteChecks.interval_of_check test 100736 128 (by decide +kernel)
theorem checked_100864 : FiniteChecks.Interval test 100864 100992 :=
  FiniteChecks.interval_of_check test 100864 128 (by decide +kernel)
theorem checked_100992 : FiniteChecks.Interval test 100992 101120 :=
  FiniteChecks.interval_of_check test 100992 128 (by decide +kernel)
theorem checked_101120 : FiniteChecks.Interval test 101120 101248 :=
  FiniteChecks.interval_of_check test 101120 128 (by decide +kernel)
theorem checked_101248 : FiniteChecks.Interval test 101248 101376 :=
  FiniteChecks.interval_of_check test 101248 128 (by decide +kernel)
theorem checked_101376 : FiniteChecks.Interval test 101376 101504 :=
  FiniteChecks.interval_of_check test 101376 128 (by decide +kernel)
theorem checked_101504 : FiniteChecks.Interval test 101504 101632 :=
  FiniteChecks.interval_of_check test 101504 128 (by decide +kernel)
theorem checked_101632 : FiniteChecks.Interval test 101632 101760 :=
  FiniteChecks.interval_of_check test 101632 128 (by decide +kernel)
theorem checked_101760 : FiniteChecks.Interval test 101760 101888 :=
  FiniteChecks.interval_of_check test 101760 128 (by decide +kernel)
theorem checked_101888 : FiniteChecks.Interval test 101888 102016 :=
  FiniteChecks.interval_of_check test 101888 128 (by decide +kernel)
theorem checked_102016 : FiniteChecks.Interval test 102016 102144 :=
  FiniteChecks.interval_of_check test 102016 128 (by decide +kernel)
theorem checked_102144 : FiniteChecks.Interval test 102144 102272 :=
  FiniteChecks.interval_of_check test 102144 128 (by decide +kernel)
theorem checked_102272 : FiniteChecks.Interval test 102272 102400 :=
  FiniteChecks.interval_of_check test 102272 128 (by decide +kernel)
theorem interval_98304 : FiniteChecks.Interval test 98304 102400 :=
  (FiniteChecks.interval_append test 98304 100352 102400
  (FiniteChecks.interval_append test 98304 99328 100352
  (FiniteChecks.interval_append test 98304 98816 99328
  (FiniteChecks.interval_append test 98304 98560 98816
  (FiniteChecks.interval_append test 98304 98432 98560
  checked_98304
  checked_98432)
  (FiniteChecks.interval_append test 98560 98688 98816
  checked_98560
  checked_98688))
  (FiniteChecks.interval_append test 98816 99072 99328
  (FiniteChecks.interval_append test 98816 98944 99072
  checked_98816
  checked_98944)
  (FiniteChecks.interval_append test 99072 99200 99328
  checked_99072
  checked_99200)))
  (FiniteChecks.interval_append test 99328 99840 100352
  (FiniteChecks.interval_append test 99328 99584 99840
  (FiniteChecks.interval_append test 99328 99456 99584
  checked_99328
  checked_99456)
  (FiniteChecks.interval_append test 99584 99712 99840
  checked_99584
  checked_99712))
  (FiniteChecks.interval_append test 99840 100096 100352
  (FiniteChecks.interval_append test 99840 99968 100096
  checked_99840
  checked_99968)
  (FiniteChecks.interval_append test 100096 100224 100352
  checked_100096
  checked_100224))))
  (FiniteChecks.interval_append test 100352 101376 102400
  (FiniteChecks.interval_append test 100352 100864 101376
  (FiniteChecks.interval_append test 100352 100608 100864
  (FiniteChecks.interval_append test 100352 100480 100608
  checked_100352
  checked_100480)
  (FiniteChecks.interval_append test 100608 100736 100864
  checked_100608
  checked_100736))
  (FiniteChecks.interval_append test 100864 101120 101376
  (FiniteChecks.interval_append test 100864 100992 101120
  checked_100864
  checked_100992)
  (FiniteChecks.interval_append test 101120 101248 101376
  checked_101120
  checked_101248)))
  (FiniteChecks.interval_append test 101376 101888 102400
  (FiniteChecks.interval_append test 101376 101632 101888
  (FiniteChecks.interval_append test 101376 101504 101632
  checked_101376
  checked_101504)
  (FiniteChecks.interval_append test 101632 101760 101888
  checked_101632
  checked_101760))
  (FiniteChecks.interval_append test 101888 102144 102400
  (FiniteChecks.interval_append test 101888 102016 102144
  checked_101888
  checked_102016)
  (FiniteChecks.interval_append test 102144 102272 102400
  checked_102144
  checked_102272)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
