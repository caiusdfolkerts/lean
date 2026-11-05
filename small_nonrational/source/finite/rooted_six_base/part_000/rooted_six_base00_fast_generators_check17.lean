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
theorem checked_69632 : FiniteChecks.Interval test 69632 69760 :=
  FiniteChecks.interval_of_check test 69632 128 (by decide +kernel)
theorem checked_69760 : FiniteChecks.Interval test 69760 69888 :=
  FiniteChecks.interval_of_check test 69760 128 (by decide +kernel)
theorem checked_69888 : FiniteChecks.Interval test 69888 70016 :=
  FiniteChecks.interval_of_check test 69888 128 (by decide +kernel)
theorem checked_70016 : FiniteChecks.Interval test 70016 70144 :=
  FiniteChecks.interval_of_check test 70016 128 (by decide +kernel)
theorem checked_70144 : FiniteChecks.Interval test 70144 70272 :=
  FiniteChecks.interval_of_check test 70144 128 (by decide +kernel)
theorem checked_70272 : FiniteChecks.Interval test 70272 70400 :=
  FiniteChecks.interval_of_check test 70272 128 (by decide +kernel)
theorem checked_70400 : FiniteChecks.Interval test 70400 70528 :=
  FiniteChecks.interval_of_check test 70400 128 (by decide +kernel)
theorem checked_70528 : FiniteChecks.Interval test 70528 70656 :=
  FiniteChecks.interval_of_check test 70528 128 (by decide +kernel)
theorem checked_70656 : FiniteChecks.Interval test 70656 70784 :=
  FiniteChecks.interval_of_check test 70656 128 (by decide +kernel)
theorem checked_70784 : FiniteChecks.Interval test 70784 70912 :=
  FiniteChecks.interval_of_check test 70784 128 (by decide +kernel)
theorem checked_70912 : FiniteChecks.Interval test 70912 71040 :=
  FiniteChecks.interval_of_check test 70912 128 (by decide +kernel)
theorem checked_71040 : FiniteChecks.Interval test 71040 71168 :=
  FiniteChecks.interval_of_check test 71040 128 (by decide +kernel)
theorem checked_71168 : FiniteChecks.Interval test 71168 71296 :=
  FiniteChecks.interval_of_check test 71168 128 (by decide +kernel)
theorem checked_71296 : FiniteChecks.Interval test 71296 71424 :=
  FiniteChecks.interval_of_check test 71296 128 (by decide +kernel)
theorem checked_71424 : FiniteChecks.Interval test 71424 71552 :=
  FiniteChecks.interval_of_check test 71424 128 (by decide +kernel)
theorem checked_71552 : FiniteChecks.Interval test 71552 71680 :=
  FiniteChecks.interval_of_check test 71552 128 (by decide +kernel)
theorem checked_71680 : FiniteChecks.Interval test 71680 71808 :=
  FiniteChecks.interval_of_check test 71680 128 (by decide +kernel)
theorem checked_71808 : FiniteChecks.Interval test 71808 71936 :=
  FiniteChecks.interval_of_check test 71808 128 (by decide +kernel)
theorem checked_71936 : FiniteChecks.Interval test 71936 72064 :=
  FiniteChecks.interval_of_check test 71936 128 (by decide +kernel)
theorem checked_72064 : FiniteChecks.Interval test 72064 72192 :=
  FiniteChecks.interval_of_check test 72064 128 (by decide +kernel)
theorem checked_72192 : FiniteChecks.Interval test 72192 72320 :=
  FiniteChecks.interval_of_check test 72192 128 (by decide +kernel)
theorem checked_72320 : FiniteChecks.Interval test 72320 72448 :=
  FiniteChecks.interval_of_check test 72320 128 (by decide +kernel)
theorem checked_72448 : FiniteChecks.Interval test 72448 72576 :=
  FiniteChecks.interval_of_check test 72448 128 (by decide +kernel)
theorem checked_72576 : FiniteChecks.Interval test 72576 72704 :=
  FiniteChecks.interval_of_check test 72576 128 (by decide +kernel)
theorem checked_72704 : FiniteChecks.Interval test 72704 72832 :=
  FiniteChecks.interval_of_check test 72704 128 (by decide +kernel)
theorem checked_72832 : FiniteChecks.Interval test 72832 72960 :=
  FiniteChecks.interval_of_check test 72832 128 (by decide +kernel)
theorem checked_72960 : FiniteChecks.Interval test 72960 73088 :=
  FiniteChecks.interval_of_check test 72960 128 (by decide +kernel)
theorem checked_73088 : FiniteChecks.Interval test 73088 73216 :=
  FiniteChecks.interval_of_check test 73088 128 (by decide +kernel)
theorem checked_73216 : FiniteChecks.Interval test 73216 73344 :=
  FiniteChecks.interval_of_check test 73216 128 (by decide +kernel)
theorem checked_73344 : FiniteChecks.Interval test 73344 73472 :=
  FiniteChecks.interval_of_check test 73344 128 (by decide +kernel)
theorem checked_73472 : FiniteChecks.Interval test 73472 73600 :=
  FiniteChecks.interval_of_check test 73472 128 (by decide +kernel)
theorem checked_73600 : FiniteChecks.Interval test 73600 73728 :=
  FiniteChecks.interval_of_check test 73600 128 (by decide +kernel)
theorem interval_69632 : FiniteChecks.Interval test 69632 73728 :=
  (FiniteChecks.interval_append test 69632 71680 73728
  (FiniteChecks.interval_append test 69632 70656 71680
  (FiniteChecks.interval_append test 69632 70144 70656
  (FiniteChecks.interval_append test 69632 69888 70144
  (FiniteChecks.interval_append test 69632 69760 69888
  checked_69632
  checked_69760)
  (FiniteChecks.interval_append test 69888 70016 70144
  checked_69888
  checked_70016))
  (FiniteChecks.interval_append test 70144 70400 70656
  (FiniteChecks.interval_append test 70144 70272 70400
  checked_70144
  checked_70272)
  (FiniteChecks.interval_append test 70400 70528 70656
  checked_70400
  checked_70528)))
  (FiniteChecks.interval_append test 70656 71168 71680
  (FiniteChecks.interval_append test 70656 70912 71168
  (FiniteChecks.interval_append test 70656 70784 70912
  checked_70656
  checked_70784)
  (FiniteChecks.interval_append test 70912 71040 71168
  checked_70912
  checked_71040))
  (FiniteChecks.interval_append test 71168 71424 71680
  (FiniteChecks.interval_append test 71168 71296 71424
  checked_71168
  checked_71296)
  (FiniteChecks.interval_append test 71424 71552 71680
  checked_71424
  checked_71552))))
  (FiniteChecks.interval_append test 71680 72704 73728
  (FiniteChecks.interval_append test 71680 72192 72704
  (FiniteChecks.interval_append test 71680 71936 72192
  (FiniteChecks.interval_append test 71680 71808 71936
  checked_71680
  checked_71808)
  (FiniteChecks.interval_append test 71936 72064 72192
  checked_71936
  checked_72064))
  (FiniteChecks.interval_append test 72192 72448 72704
  (FiniteChecks.interval_append test 72192 72320 72448
  checked_72192
  checked_72320)
  (FiniteChecks.interval_append test 72448 72576 72704
  checked_72448
  checked_72576)))
  (FiniteChecks.interval_append test 72704 73216 73728
  (FiniteChecks.interval_append test 72704 72960 73216
  (FiniteChecks.interval_append test 72704 72832 72960
  checked_72704
  checked_72832)
  (FiniteChecks.interval_append test 72960 73088 73216
  checked_72960
  checked_73088))
  (FiniteChecks.interval_append test 73216 73472 73728
  (FiniteChecks.interval_append test 73216 73344 73472
  checked_73216
  checked_73344)
  (FiniteChecks.interval_append test 73472 73600 73728
  checked_73472
  checked_73600)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
