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
theorem checked_16384 : FiniteChecks.Interval test 16384 16512 :=
  FiniteChecks.interval_of_check test 16384 128 (by decide +kernel)
theorem checked_16512 : FiniteChecks.Interval test 16512 16640 :=
  FiniteChecks.interval_of_check test 16512 128 (by decide +kernel)
theorem checked_16640 : FiniteChecks.Interval test 16640 16768 :=
  FiniteChecks.interval_of_check test 16640 128 (by decide +kernel)
theorem checked_16768 : FiniteChecks.Interval test 16768 16896 :=
  FiniteChecks.interval_of_check test 16768 128 (by decide +kernel)
theorem checked_16896 : FiniteChecks.Interval test 16896 17024 :=
  FiniteChecks.interval_of_check test 16896 128 (by decide +kernel)
theorem checked_17024 : FiniteChecks.Interval test 17024 17152 :=
  FiniteChecks.interval_of_check test 17024 128 (by decide +kernel)
theorem checked_17152 : FiniteChecks.Interval test 17152 17280 :=
  FiniteChecks.interval_of_check test 17152 128 (by decide +kernel)
theorem checked_17280 : FiniteChecks.Interval test 17280 17408 :=
  FiniteChecks.interval_of_check test 17280 128 (by decide +kernel)
theorem checked_17408 : FiniteChecks.Interval test 17408 17536 :=
  FiniteChecks.interval_of_check test 17408 128 (by decide +kernel)
theorem checked_17536 : FiniteChecks.Interval test 17536 17664 :=
  FiniteChecks.interval_of_check test 17536 128 (by decide +kernel)
theorem checked_17664 : FiniteChecks.Interval test 17664 17792 :=
  FiniteChecks.interval_of_check test 17664 128 (by decide +kernel)
theorem checked_17792 : FiniteChecks.Interval test 17792 17920 :=
  FiniteChecks.interval_of_check test 17792 128 (by decide +kernel)
theorem checked_17920 : FiniteChecks.Interval test 17920 18048 :=
  FiniteChecks.interval_of_check test 17920 128 (by decide +kernel)
theorem checked_18048 : FiniteChecks.Interval test 18048 18176 :=
  FiniteChecks.interval_of_check test 18048 128 (by decide +kernel)
theorem checked_18176 : FiniteChecks.Interval test 18176 18304 :=
  FiniteChecks.interval_of_check test 18176 128 (by decide +kernel)
theorem checked_18304 : FiniteChecks.Interval test 18304 18432 :=
  FiniteChecks.interval_of_check test 18304 128 (by decide +kernel)
theorem checked_18432 : FiniteChecks.Interval test 18432 18560 :=
  FiniteChecks.interval_of_check test 18432 128 (by decide +kernel)
theorem checked_18560 : FiniteChecks.Interval test 18560 18688 :=
  FiniteChecks.interval_of_check test 18560 128 (by decide +kernel)
theorem checked_18688 : FiniteChecks.Interval test 18688 18816 :=
  FiniteChecks.interval_of_check test 18688 128 (by decide +kernel)
theorem checked_18816 : FiniteChecks.Interval test 18816 18944 :=
  FiniteChecks.interval_of_check test 18816 128 (by decide +kernel)
theorem checked_18944 : FiniteChecks.Interval test 18944 19072 :=
  FiniteChecks.interval_of_check test 18944 128 (by decide +kernel)
theorem checked_19072 : FiniteChecks.Interval test 19072 19200 :=
  FiniteChecks.interval_of_check test 19072 128 (by decide +kernel)
theorem checked_19200 : FiniteChecks.Interval test 19200 19328 :=
  FiniteChecks.interval_of_check test 19200 128 (by decide +kernel)
theorem checked_19328 : FiniteChecks.Interval test 19328 19456 :=
  FiniteChecks.interval_of_check test 19328 128 (by decide +kernel)
theorem checked_19456 : FiniteChecks.Interval test 19456 19584 :=
  FiniteChecks.interval_of_check test 19456 128 (by decide +kernel)
theorem checked_19584 : FiniteChecks.Interval test 19584 19712 :=
  FiniteChecks.interval_of_check test 19584 128 (by decide +kernel)
theorem checked_19712 : FiniteChecks.Interval test 19712 19840 :=
  FiniteChecks.interval_of_check test 19712 128 (by decide +kernel)
theorem checked_19840 : FiniteChecks.Interval test 19840 19968 :=
  FiniteChecks.interval_of_check test 19840 128 (by decide +kernel)
theorem checked_19968 : FiniteChecks.Interval test 19968 20096 :=
  FiniteChecks.interval_of_check test 19968 128 (by decide +kernel)
theorem checked_20096 : FiniteChecks.Interval test 20096 20224 :=
  FiniteChecks.interval_of_check test 20096 128 (by decide +kernel)
theorem checked_20224 : FiniteChecks.Interval test 20224 20352 :=
  FiniteChecks.interval_of_check test 20224 128 (by decide +kernel)
theorem checked_20352 : FiniteChecks.Interval test 20352 20480 :=
  FiniteChecks.interval_of_check test 20352 128 (by decide +kernel)
theorem interval_16384 : FiniteChecks.Interval test 16384 20480 :=
  (FiniteChecks.interval_append test 16384 18432 20480
  (FiniteChecks.interval_append test 16384 17408 18432
  (FiniteChecks.interval_append test 16384 16896 17408
  (FiniteChecks.interval_append test 16384 16640 16896
  (FiniteChecks.interval_append test 16384 16512 16640
  checked_16384
  checked_16512)
  (FiniteChecks.interval_append test 16640 16768 16896
  checked_16640
  checked_16768))
  (FiniteChecks.interval_append test 16896 17152 17408
  (FiniteChecks.interval_append test 16896 17024 17152
  checked_16896
  checked_17024)
  (FiniteChecks.interval_append test 17152 17280 17408
  checked_17152
  checked_17280)))
  (FiniteChecks.interval_append test 17408 17920 18432
  (FiniteChecks.interval_append test 17408 17664 17920
  (FiniteChecks.interval_append test 17408 17536 17664
  checked_17408
  checked_17536)
  (FiniteChecks.interval_append test 17664 17792 17920
  checked_17664
  checked_17792))
  (FiniteChecks.interval_append test 17920 18176 18432
  (FiniteChecks.interval_append test 17920 18048 18176
  checked_17920
  checked_18048)
  (FiniteChecks.interval_append test 18176 18304 18432
  checked_18176
  checked_18304))))
  (FiniteChecks.interval_append test 18432 19456 20480
  (FiniteChecks.interval_append test 18432 18944 19456
  (FiniteChecks.interval_append test 18432 18688 18944
  (FiniteChecks.interval_append test 18432 18560 18688
  checked_18432
  checked_18560)
  (FiniteChecks.interval_append test 18688 18816 18944
  checked_18688
  checked_18816))
  (FiniteChecks.interval_append test 18944 19200 19456
  (FiniteChecks.interval_append test 18944 19072 19200
  checked_18944
  checked_19072)
  (FiniteChecks.interval_append test 19200 19328 19456
  checked_19200
  checked_19328)))
  (FiniteChecks.interval_append test 19456 19968 20480
  (FiniteChecks.interval_append test 19456 19712 19968
  (FiniteChecks.interval_append test 19456 19584 19712
  checked_19456
  checked_19584)
  (FiniteChecks.interval_append test 19712 19840 19968
  checked_19712
  checked_19840))
  (FiniteChecks.interval_append test 19968 20224 20480
  (FiniteChecks.interval_append test 19968 20096 20224
  checked_19968
  checked_20096)
  (FiniteChecks.interval_append test 20224 20352 20480
  checked_20224
  checked_20352)))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Fast
