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
cert_checked_7 16384 16512 128
cert_checked_7 16512 16640 128
cert_checked_7 16640 16768 128
cert_checked_7 16768 16896 128
cert_checked_7 16896 17024 128
cert_checked_7 17024 17152 128
cert_checked_7 17152 17280 128
cert_checked_7 17280 17408 128
cert_checked_7 17408 17536 128
cert_checked_7 17536 17664 128
cert_checked_7 17664 17792 128
cert_checked_7 17792 17920 128
cert_checked_7 17920 18048 128
cert_checked_7 18048 18176 128
cert_checked_7 18176 18304 128
cert_checked_7 18304 18432 128
cert_checked_7 18432 18560 128
cert_checked_7 18560 18688 128
cert_checked_7 18688 18816 128
cert_checked_7 18816 18944 128
cert_checked_7 18944 19072 128
cert_checked_7 19072 19200 128
cert_checked_7 19200 19328 128
cert_checked_7 19328 19456 128
cert_checked_7 19456 19584 128
cert_checked_7 19584 19712 128
cert_checked_7 19712 19840 128
cert_checked_7 19840 19968 128
cert_checked_7 19968 20096 128
cert_checked_7 20096 20224 128
cert_checked_7 20224 20352 128
cert_checked_7 20352 20480 128
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
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
