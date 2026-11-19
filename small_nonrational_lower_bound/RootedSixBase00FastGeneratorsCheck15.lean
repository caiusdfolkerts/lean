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
cert_checked_7 61440 61568 128
cert_checked_7 61568 61696 128
cert_checked_7 61696 61824 128
cert_checked_7 61824 61952 128
cert_checked_7 61952 62080 128
cert_checked_7 62080 62208 128
cert_checked_7 62208 62336 128
cert_checked_7 62336 62464 128
cert_checked_7 62464 62592 128
cert_checked_7 62592 62720 128
cert_checked_7 62720 62848 128
cert_checked_7 62848 62976 128
cert_checked_7 62976 63104 128
cert_checked_7 63104 63232 128
cert_checked_7 63232 63360 128
cert_checked_7 63360 63488 128
cert_checked_7 63488 63616 128
cert_checked_7 63616 63744 128
cert_checked_7 63744 63872 128
cert_checked_7 63872 64000 128
cert_checked_7 64000 64128 128
cert_checked_7 64128 64256 128
cert_checked_7 64256 64384 128
cert_checked_7 64384 64512 128
cert_checked_7 64512 64640 128
cert_checked_7 64640 64768 128
cert_checked_7 64768 64896 128
cert_checked_7 64896 65024 128
cert_checked_7 65024 65152 128
cert_checked_7 65152 65280 128
cert_checked_7 65280 65408 128
cert_checked_7 65408 65536 128
theorem interval_61440 : FiniteChecks.Interval test 61440 65536 :=
  (FiniteChecks.interval_append test 61440 63488 65536
  (FiniteChecks.interval_append test 61440 62464 63488
  (FiniteChecks.interval_append test 61440 61952 62464
  (FiniteChecks.interval_append test 61440 61696 61952
  (FiniteChecks.interval_append test 61440 61568 61696
  checked_61440
  checked_61568)
  (FiniteChecks.interval_append test 61696 61824 61952
  checked_61696
  checked_61824))
  (FiniteChecks.interval_append test 61952 62208 62464
  (FiniteChecks.interval_append test 61952 62080 62208
  checked_61952
  checked_62080)
  (FiniteChecks.interval_append test 62208 62336 62464
  checked_62208
  checked_62336)))
  (FiniteChecks.interval_append test 62464 62976 63488
  (FiniteChecks.interval_append test 62464 62720 62976
  (FiniteChecks.interval_append test 62464 62592 62720
  checked_62464
  checked_62592)
  (FiniteChecks.interval_append test 62720 62848 62976
  checked_62720
  checked_62848))
  (FiniteChecks.interval_append test 62976 63232 63488
  (FiniteChecks.interval_append test 62976 63104 63232
  checked_62976
  checked_63104)
  (FiniteChecks.interval_append test 63232 63360 63488
  checked_63232
  checked_63360))))
  (FiniteChecks.interval_append test 63488 64512 65536
  (FiniteChecks.interval_append test 63488 64000 64512
  (FiniteChecks.interval_append test 63488 63744 64000
  (FiniteChecks.interval_append test 63488 63616 63744
  checked_63488
  checked_63616)
  (FiniteChecks.interval_append test 63744 63872 64000
  checked_63744
  checked_63872))
  (FiniteChecks.interval_append test 64000 64256 64512
  (FiniteChecks.interval_append test 64000 64128 64256
  checked_64000
  checked_64128)
  (FiniteChecks.interval_append test 64256 64384 64512
  checked_64256
  checked_64384)))
  (FiniteChecks.interval_append test 64512 65024 65536
  (FiniteChecks.interval_append test 64512 64768 65024
  (FiniteChecks.interval_append test 64512 64640 64768
  checked_64512
  checked_64640)
  (FiniteChecks.interval_append test 64768 64896 65024
  checked_64768
  checked_64896))
  (FiniteChecks.interval_append test 65024 65280 65536
  (FiniteChecks.interval_append test 65024 65152 65280
  checked_65024
  checked_65152)
  (FiniteChecks.interval_append test 65280 65408 65536
  checked_65280
  checked_65408)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
