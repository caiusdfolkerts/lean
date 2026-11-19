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
cert_checked_7 36864 36992 128
cert_checked_7 36992 37120 128
cert_checked_7 37120 37248 128
cert_checked_7 37248 37376 128
cert_checked_7 37376 37504 128
cert_checked_7 37504 37632 128
cert_checked_7 37632 37760 128
cert_checked_7 37760 37888 128
cert_checked_7 37888 38016 128
cert_checked_7 38016 38144 128
cert_checked_7 38144 38272 128
cert_checked_7 38272 38400 128
cert_checked_7 38400 38528 128
cert_checked_7 38528 38656 128
cert_checked_7 38656 38784 128
cert_checked_7 38784 38912 128
cert_checked_7 38912 39040 128
cert_checked_7 39040 39168 128
cert_checked_7 39168 39296 128
cert_checked_7 39296 39424 128
cert_checked_7 39424 39552 128
cert_checked_7 39552 39680 128
cert_checked_7 39680 39808 128
cert_checked_7 39808 39936 128
cert_checked_7 39936 40064 128
cert_checked_7 40064 40192 128
cert_checked_7 40192 40320 128
cert_checked_7 40320 40448 128
cert_checked_7 40448 40576 128
cert_checked_7 40576 40704 128
cert_checked_7 40704 40832 128
cert_checked_7 40832 40960 128
theorem interval_36864 : FiniteChecks.Interval test 36864 40960 :=
  (FiniteChecks.interval_append test 36864 38912 40960
  (FiniteChecks.interval_append test 36864 37888 38912
  (FiniteChecks.interval_append test 36864 37376 37888
  (FiniteChecks.interval_append test 36864 37120 37376
  (FiniteChecks.interval_append test 36864 36992 37120
  checked_36864
  checked_36992)
  (FiniteChecks.interval_append test 37120 37248 37376
  checked_37120
  checked_37248))
  (FiniteChecks.interval_append test 37376 37632 37888
  (FiniteChecks.interval_append test 37376 37504 37632
  checked_37376
  checked_37504)
  (FiniteChecks.interval_append test 37632 37760 37888
  checked_37632
  checked_37760)))
  (FiniteChecks.interval_append test 37888 38400 38912
  (FiniteChecks.interval_append test 37888 38144 38400
  (FiniteChecks.interval_append test 37888 38016 38144
  checked_37888
  checked_38016)
  (FiniteChecks.interval_append test 38144 38272 38400
  checked_38144
  checked_38272))
  (FiniteChecks.interval_append test 38400 38656 38912
  (FiniteChecks.interval_append test 38400 38528 38656
  checked_38400
  checked_38528)
  (FiniteChecks.interval_append test 38656 38784 38912
  checked_38656
  checked_38784))))
  (FiniteChecks.interval_append test 38912 39936 40960
  (FiniteChecks.interval_append test 38912 39424 39936
  (FiniteChecks.interval_append test 38912 39168 39424
  (FiniteChecks.interval_append test 38912 39040 39168
  checked_38912
  checked_39040)
  (FiniteChecks.interval_append test 39168 39296 39424
  checked_39168
  checked_39296))
  (FiniteChecks.interval_append test 39424 39680 39936
  (FiniteChecks.interval_append test 39424 39552 39680
  checked_39424
  checked_39552)
  (FiniteChecks.interval_append test 39680 39808 39936
  checked_39680
  checked_39808)))
  (FiniteChecks.interval_append test 39936 40448 40960
  (FiniteChecks.interval_append test 39936 40192 40448
  (FiniteChecks.interval_append test 39936 40064 40192
  checked_39936
  checked_40064)
  (FiniteChecks.interval_append test 40192 40320 40448
  checked_40192
  checked_40320))
  (FiniteChecks.interval_append test 40448 40704 40960
  (FiniteChecks.interval_append test 40448 40576 40704
  checked_40448
  checked_40576)
  (FiniteChecks.interval_append test 40704 40832 40960
  checked_40704
  checked_40832)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
