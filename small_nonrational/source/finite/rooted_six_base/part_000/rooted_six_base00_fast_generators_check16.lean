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
theorem checked_65536 : FiniteChecks.Interval test 65536 65664 :=
  FiniteChecks.interval_of_check test 65536 128 (by decide +kernel)
theorem checked_65664 : FiniteChecks.Interval test 65664 65792 :=
  FiniteChecks.interval_of_check test 65664 128 (by decide +kernel)
theorem checked_65792 : FiniteChecks.Interval test 65792 65920 :=
  FiniteChecks.interval_of_check test 65792 128 (by decide +kernel)
theorem checked_65920 : FiniteChecks.Interval test 65920 66048 :=
  FiniteChecks.interval_of_check test 65920 128 (by decide +kernel)
theorem checked_66048 : FiniteChecks.Interval test 66048 66176 :=
  FiniteChecks.interval_of_check test 66048 128 (by decide +kernel)
theorem checked_66176 : FiniteChecks.Interval test 66176 66304 :=
  FiniteChecks.interval_of_check test 66176 128 (by decide +kernel)
theorem checked_66304 : FiniteChecks.Interval test 66304 66432 :=
  FiniteChecks.interval_of_check test 66304 128 (by decide +kernel)
theorem checked_66432 : FiniteChecks.Interval test 66432 66560 :=
  FiniteChecks.interval_of_check test 66432 128 (by decide +kernel)
theorem checked_66560 : FiniteChecks.Interval test 66560 66688 :=
  FiniteChecks.interval_of_check test 66560 128 (by decide +kernel)
theorem checked_66688 : FiniteChecks.Interval test 66688 66816 :=
  FiniteChecks.interval_of_check test 66688 128 (by decide +kernel)
theorem checked_66816 : FiniteChecks.Interval test 66816 66944 :=
  FiniteChecks.interval_of_check test 66816 128 (by decide +kernel)
theorem checked_66944 : FiniteChecks.Interval test 66944 67072 :=
  FiniteChecks.interval_of_check test 66944 128 (by decide +kernel)
theorem checked_67072 : FiniteChecks.Interval test 67072 67200 :=
  FiniteChecks.interval_of_check test 67072 128 (by decide +kernel)
theorem checked_67200 : FiniteChecks.Interval test 67200 67328 :=
  FiniteChecks.interval_of_check test 67200 128 (by decide +kernel)
theorem checked_67328 : FiniteChecks.Interval test 67328 67456 :=
  FiniteChecks.interval_of_check test 67328 128 (by decide +kernel)
theorem checked_67456 : FiniteChecks.Interval test 67456 67584 :=
  FiniteChecks.interval_of_check test 67456 128 (by decide +kernel)
theorem checked_67584 : FiniteChecks.Interval test 67584 67712 :=
  FiniteChecks.interval_of_check test 67584 128 (by decide +kernel)
theorem checked_67712 : FiniteChecks.Interval test 67712 67840 :=
  FiniteChecks.interval_of_check test 67712 128 (by decide +kernel)
theorem checked_67840 : FiniteChecks.Interval test 67840 67968 :=
  FiniteChecks.interval_of_check test 67840 128 (by decide +kernel)
theorem checked_67968 : FiniteChecks.Interval test 67968 68096 :=
  FiniteChecks.interval_of_check test 67968 128 (by decide +kernel)
theorem checked_68096 : FiniteChecks.Interval test 68096 68224 :=
  FiniteChecks.interval_of_check test 68096 128 (by decide +kernel)
theorem checked_68224 : FiniteChecks.Interval test 68224 68352 :=
  FiniteChecks.interval_of_check test 68224 128 (by decide +kernel)
theorem checked_68352 : FiniteChecks.Interval test 68352 68480 :=
  FiniteChecks.interval_of_check test 68352 128 (by decide +kernel)
theorem checked_68480 : FiniteChecks.Interval test 68480 68608 :=
  FiniteChecks.interval_of_check test 68480 128 (by decide +kernel)
theorem checked_68608 : FiniteChecks.Interval test 68608 68736 :=
  FiniteChecks.interval_of_check test 68608 128 (by decide +kernel)
theorem checked_68736 : FiniteChecks.Interval test 68736 68864 :=
  FiniteChecks.interval_of_check test 68736 128 (by decide +kernel)
theorem checked_68864 : FiniteChecks.Interval test 68864 68992 :=
  FiniteChecks.interval_of_check test 68864 128 (by decide +kernel)
theorem checked_68992 : FiniteChecks.Interval test 68992 69120 :=
  FiniteChecks.interval_of_check test 68992 128 (by decide +kernel)
theorem checked_69120 : FiniteChecks.Interval test 69120 69248 :=
  FiniteChecks.interval_of_check test 69120 128 (by decide +kernel)
theorem checked_69248 : FiniteChecks.Interval test 69248 69376 :=
  FiniteChecks.interval_of_check test 69248 128 (by decide +kernel)
theorem checked_69376 : FiniteChecks.Interval test 69376 69504 :=
  FiniteChecks.interval_of_check test 69376 128 (by decide +kernel)
theorem checked_69504 : FiniteChecks.Interval test 69504 69632 :=
  FiniteChecks.interval_of_check test 69504 128 (by decide +kernel)
theorem interval_65536 : FiniteChecks.Interval test 65536 69632 :=
  (FiniteChecks.interval_append test 65536 67584 69632
  (FiniteChecks.interval_append test 65536 66560 67584
  (FiniteChecks.interval_append test 65536 66048 66560
  (FiniteChecks.interval_append test 65536 65792 66048
  (FiniteChecks.interval_append test 65536 65664 65792
  checked_65536
  checked_65664)
  (FiniteChecks.interval_append test 65792 65920 66048
  checked_65792
  checked_65920))
  (FiniteChecks.interval_append test 66048 66304 66560
  (FiniteChecks.interval_append test 66048 66176 66304
  checked_66048
  checked_66176)
  (FiniteChecks.interval_append test 66304 66432 66560
  checked_66304
  checked_66432)))
  (FiniteChecks.interval_append test 66560 67072 67584
  (FiniteChecks.interval_append test 66560 66816 67072
  (FiniteChecks.interval_append test 66560 66688 66816
  checked_66560
  checked_66688)
  (FiniteChecks.interval_append test 66816 66944 67072
  checked_66816
  checked_66944))
  (FiniteChecks.interval_append test 67072 67328 67584
  (FiniteChecks.interval_append test 67072 67200 67328
  checked_67072
  checked_67200)
  (FiniteChecks.interval_append test 67328 67456 67584
  checked_67328
  checked_67456))))
  (FiniteChecks.interval_append test 67584 68608 69632
  (FiniteChecks.interval_append test 67584 68096 68608
  (FiniteChecks.interval_append test 67584 67840 68096
  (FiniteChecks.interval_append test 67584 67712 67840
  checked_67584
  checked_67712)
  (FiniteChecks.interval_append test 67840 67968 68096
  checked_67840
  checked_67968))
  (FiniteChecks.interval_append test 68096 68352 68608
  (FiniteChecks.interval_append test 68096 68224 68352
  checked_68096
  checked_68224)
  (FiniteChecks.interval_append test 68352 68480 68608
  checked_68352
  checked_68480)))
  (FiniteChecks.interval_append test 68608 69120 69632
  (FiniteChecks.interval_append test 68608 68864 69120
  (FiniteChecks.interval_append test 68608 68736 68864
  checked_68608
  checked_68736)
  (FiniteChecks.interval_append test 68864 68992 69120
  checked_68864
  checked_68992))
  (FiniteChecks.interval_append test 69120 69376 69632
  (FiniteChecks.interval_append test 69120 69248 69376
  checked_69120
  checked_69248)
  (FiniteChecks.interval_append test 69376 69504 69632
  checked_69376
  checked_69504)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
