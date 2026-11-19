module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase00FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 65536 65664 128
cert_checked_7 65664 65792 128
cert_checked_7 65792 65920 128
cert_checked_7 65920 66048 128
cert_checked_7 66048 66176 128
cert_checked_7 66176 66304 128
cert_checked_7 66304 66432 128
cert_checked_7 66432 66560 128
cert_checked_7 66560 66688 128
cert_checked_7 66688 66816 128
cert_checked_7 66816 66944 128
cert_checked_7 66944 67072 128
cert_checked_7 67072 67200 128
cert_checked_7 67200 67328 128
cert_checked_7 67328 67456 128
cert_checked_7 67456 67584 128
cert_checked_7 67584 67712 128
cert_checked_7 67712 67840 128
cert_checked_7 67840 67968 128
cert_checked_7 67968 68096 128
cert_checked_7 68096 68224 128
cert_checked_7 68224 68352 128
cert_checked_7 68352 68480 128
cert_checked_7 68480 68608 128
cert_checked_7 68608 68736 128
cert_checked_7 68736 68864 128
cert_checked_7 68864 68992 128
cert_checked_7 68992 69120 128
cert_checked_7 69120 69248 128
cert_checked_7 69248 69376 128
cert_checked_7 69376 69504 128
cert_checked_7 69504 69632 128
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
