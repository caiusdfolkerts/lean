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
theorem checked_49152 : FiniteChecks.Interval test 49152 49280 :=
  FiniteChecks.interval_of_check test 49152 128 (by decide +kernel)
theorem checked_49280 : FiniteChecks.Interval test 49280 49408 :=
  FiniteChecks.interval_of_check test 49280 128 (by decide +kernel)
theorem checked_49408 : FiniteChecks.Interval test 49408 49536 :=
  FiniteChecks.interval_of_check test 49408 128 (by decide +kernel)
theorem checked_49536 : FiniteChecks.Interval test 49536 49664 :=
  FiniteChecks.interval_of_check test 49536 128 (by decide +kernel)
theorem checked_49664 : FiniteChecks.Interval test 49664 49792 :=
  FiniteChecks.interval_of_check test 49664 128 (by decide +kernel)
theorem checked_49792 : FiniteChecks.Interval test 49792 49920 :=
  FiniteChecks.interval_of_check test 49792 128 (by decide +kernel)
theorem checked_49920 : FiniteChecks.Interval test 49920 50048 :=
  FiniteChecks.interval_of_check test 49920 128 (by decide +kernel)
theorem checked_50048 : FiniteChecks.Interval test 50048 50176 :=
  FiniteChecks.interval_of_check test 50048 128 (by decide +kernel)
theorem checked_50176 : FiniteChecks.Interval test 50176 50304 :=
  FiniteChecks.interval_of_check test 50176 128 (by decide +kernel)
theorem checked_50304 : FiniteChecks.Interval test 50304 50432 :=
  FiniteChecks.interval_of_check test 50304 128 (by decide +kernel)
theorem checked_50432 : FiniteChecks.Interval test 50432 50560 :=
  FiniteChecks.interval_of_check test 50432 128 (by decide +kernel)
theorem checked_50560 : FiniteChecks.Interval test 50560 50688 :=
  FiniteChecks.interval_of_check test 50560 128 (by decide +kernel)
theorem checked_50688 : FiniteChecks.Interval test 50688 50816 :=
  FiniteChecks.interval_of_check test 50688 128 (by decide +kernel)
theorem checked_50816 : FiniteChecks.Interval test 50816 50944 :=
  FiniteChecks.interval_of_check test 50816 128 (by decide +kernel)
theorem checked_50944 : FiniteChecks.Interval test 50944 51072 :=
  FiniteChecks.interval_of_check test 50944 128 (by decide +kernel)
theorem checked_51072 : FiniteChecks.Interval test 51072 51200 :=
  FiniteChecks.interval_of_check test 51072 128 (by decide +kernel)
theorem checked_51200 : FiniteChecks.Interval test 51200 51328 :=
  FiniteChecks.interval_of_check test 51200 128 (by decide +kernel)
theorem checked_51328 : FiniteChecks.Interval test 51328 51456 :=
  FiniteChecks.interval_of_check test 51328 128 (by decide +kernel)
theorem checked_51456 : FiniteChecks.Interval test 51456 51584 :=
  FiniteChecks.interval_of_check test 51456 128 (by decide +kernel)
theorem checked_51584 : FiniteChecks.Interval test 51584 51712 :=
  FiniteChecks.interval_of_check test 51584 128 (by decide +kernel)
theorem checked_51712 : FiniteChecks.Interval test 51712 51840 :=
  FiniteChecks.interval_of_check test 51712 128 (by decide +kernel)
theorem checked_51840 : FiniteChecks.Interval test 51840 51968 :=
  FiniteChecks.interval_of_check test 51840 128 (by decide +kernel)
theorem checked_51968 : FiniteChecks.Interval test 51968 52096 :=
  FiniteChecks.interval_of_check test 51968 128 (by decide +kernel)
theorem checked_52096 : FiniteChecks.Interval test 52096 52224 :=
  FiniteChecks.interval_of_check test 52096 128 (by decide +kernel)
theorem checked_52224 : FiniteChecks.Interval test 52224 52352 :=
  FiniteChecks.interval_of_check test 52224 128 (by decide +kernel)
theorem checked_52352 : FiniteChecks.Interval test 52352 52480 :=
  FiniteChecks.interval_of_check test 52352 128 (by decide +kernel)
theorem checked_52480 : FiniteChecks.Interval test 52480 52608 :=
  FiniteChecks.interval_of_check test 52480 128 (by decide +kernel)
theorem checked_52608 : FiniteChecks.Interval test 52608 52736 :=
  FiniteChecks.interval_of_check test 52608 128 (by decide +kernel)
theorem checked_52736 : FiniteChecks.Interval test 52736 52864 :=
  FiniteChecks.interval_of_check test 52736 128 (by decide +kernel)
theorem checked_52864 : FiniteChecks.Interval test 52864 52992 :=
  FiniteChecks.interval_of_check test 52864 128 (by decide +kernel)
theorem checked_52992 : FiniteChecks.Interval test 52992 53120 :=
  FiniteChecks.interval_of_check test 52992 128 (by decide +kernel)
theorem checked_53120 : FiniteChecks.Interval test 53120 53248 :=
  FiniteChecks.interval_of_check test 53120 128 (by decide +kernel)
theorem interval_49152 : FiniteChecks.Interval test 49152 53248 :=
  (FiniteChecks.interval_append test 49152 51200 53248
  (FiniteChecks.interval_append test 49152 50176 51200
  (FiniteChecks.interval_append test 49152 49664 50176
  (FiniteChecks.interval_append test 49152 49408 49664
  (FiniteChecks.interval_append test 49152 49280 49408
  checked_49152
  checked_49280)
  (FiniteChecks.interval_append test 49408 49536 49664
  checked_49408
  checked_49536))
  (FiniteChecks.interval_append test 49664 49920 50176
  (FiniteChecks.interval_append test 49664 49792 49920
  checked_49664
  checked_49792)
  (FiniteChecks.interval_append test 49920 50048 50176
  checked_49920
  checked_50048)))
  (FiniteChecks.interval_append test 50176 50688 51200
  (FiniteChecks.interval_append test 50176 50432 50688
  (FiniteChecks.interval_append test 50176 50304 50432
  checked_50176
  checked_50304)
  (FiniteChecks.interval_append test 50432 50560 50688
  checked_50432
  checked_50560))
  (FiniteChecks.interval_append test 50688 50944 51200
  (FiniteChecks.interval_append test 50688 50816 50944
  checked_50688
  checked_50816)
  (FiniteChecks.interval_append test 50944 51072 51200
  checked_50944
  checked_51072))))
  (FiniteChecks.interval_append test 51200 52224 53248
  (FiniteChecks.interval_append test 51200 51712 52224
  (FiniteChecks.interval_append test 51200 51456 51712
  (FiniteChecks.interval_append test 51200 51328 51456
  checked_51200
  checked_51328)
  (FiniteChecks.interval_append test 51456 51584 51712
  checked_51456
  checked_51584))
  (FiniteChecks.interval_append test 51712 51968 52224
  (FiniteChecks.interval_append test 51712 51840 51968
  checked_51712
  checked_51840)
  (FiniteChecks.interval_append test 51968 52096 52224
  checked_51968
  checked_52096)))
  (FiniteChecks.interval_append test 52224 52736 53248
  (FiniteChecks.interval_append test 52224 52480 52736
  (FiniteChecks.interval_append test 52224 52352 52480
  checked_52224
  checked_52352)
  (FiniteChecks.interval_append test 52480 52608 52736
  checked_52480
  checked_52608))
  (FiniteChecks.interval_append test 52736 52992 53248
  (FiniteChecks.interval_append test 52736 52864 52992
  checked_52736
  checked_52864)
  (FiniteChecks.interval_append test 52992 53120 53248
  checked_52992
  checked_53120)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
