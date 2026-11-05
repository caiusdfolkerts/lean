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
theorem checked_61440 : FiniteChecks.Interval test 61440 61568 :=
  FiniteChecks.interval_of_check test 61440 128 (by decide +kernel)
theorem checked_61568 : FiniteChecks.Interval test 61568 61696 :=
  FiniteChecks.interval_of_check test 61568 128 (by decide +kernel)
theorem checked_61696 : FiniteChecks.Interval test 61696 61824 :=
  FiniteChecks.interval_of_check test 61696 128 (by decide +kernel)
theorem checked_61824 : FiniteChecks.Interval test 61824 61952 :=
  FiniteChecks.interval_of_check test 61824 128 (by decide +kernel)
theorem checked_61952 : FiniteChecks.Interval test 61952 62080 :=
  FiniteChecks.interval_of_check test 61952 128 (by decide +kernel)
theorem checked_62080 : FiniteChecks.Interval test 62080 62208 :=
  FiniteChecks.interval_of_check test 62080 128 (by decide +kernel)
theorem checked_62208 : FiniteChecks.Interval test 62208 62336 :=
  FiniteChecks.interval_of_check test 62208 128 (by decide +kernel)
theorem checked_62336 : FiniteChecks.Interval test 62336 62464 :=
  FiniteChecks.interval_of_check test 62336 128 (by decide +kernel)
theorem checked_62464 : FiniteChecks.Interval test 62464 62592 :=
  FiniteChecks.interval_of_check test 62464 128 (by decide +kernel)
theorem checked_62592 : FiniteChecks.Interval test 62592 62720 :=
  FiniteChecks.interval_of_check test 62592 128 (by decide +kernel)
theorem checked_62720 : FiniteChecks.Interval test 62720 62848 :=
  FiniteChecks.interval_of_check test 62720 128 (by decide +kernel)
theorem checked_62848 : FiniteChecks.Interval test 62848 62976 :=
  FiniteChecks.interval_of_check test 62848 128 (by decide +kernel)
theorem checked_62976 : FiniteChecks.Interval test 62976 63104 :=
  FiniteChecks.interval_of_check test 62976 128 (by decide +kernel)
theorem checked_63104 : FiniteChecks.Interval test 63104 63232 :=
  FiniteChecks.interval_of_check test 63104 128 (by decide +kernel)
theorem checked_63232 : FiniteChecks.Interval test 63232 63360 :=
  FiniteChecks.interval_of_check test 63232 128 (by decide +kernel)
theorem checked_63360 : FiniteChecks.Interval test 63360 63488 :=
  FiniteChecks.interval_of_check test 63360 128 (by decide +kernel)
theorem checked_63488 : FiniteChecks.Interval test 63488 63616 :=
  FiniteChecks.interval_of_check test 63488 128 (by decide +kernel)
theorem checked_63616 : FiniteChecks.Interval test 63616 63744 :=
  FiniteChecks.interval_of_check test 63616 128 (by decide +kernel)
theorem checked_63744 : FiniteChecks.Interval test 63744 63872 :=
  FiniteChecks.interval_of_check test 63744 128 (by decide +kernel)
theorem checked_63872 : FiniteChecks.Interval test 63872 64000 :=
  FiniteChecks.interval_of_check test 63872 128 (by decide +kernel)
theorem checked_64000 : FiniteChecks.Interval test 64000 64128 :=
  FiniteChecks.interval_of_check test 64000 128 (by decide +kernel)
theorem checked_64128 : FiniteChecks.Interval test 64128 64256 :=
  FiniteChecks.interval_of_check test 64128 128 (by decide +kernel)
theorem checked_64256 : FiniteChecks.Interval test 64256 64384 :=
  FiniteChecks.interval_of_check test 64256 128 (by decide +kernel)
theorem checked_64384 : FiniteChecks.Interval test 64384 64512 :=
  FiniteChecks.interval_of_check test 64384 128 (by decide +kernel)
theorem checked_64512 : FiniteChecks.Interval test 64512 64640 :=
  FiniteChecks.interval_of_check test 64512 128 (by decide +kernel)
theorem checked_64640 : FiniteChecks.Interval test 64640 64768 :=
  FiniteChecks.interval_of_check test 64640 128 (by decide +kernel)
theorem checked_64768 : FiniteChecks.Interval test 64768 64896 :=
  FiniteChecks.interval_of_check test 64768 128 (by decide +kernel)
theorem checked_64896 : FiniteChecks.Interval test 64896 65024 :=
  FiniteChecks.interval_of_check test 64896 128 (by decide +kernel)
theorem checked_65024 : FiniteChecks.Interval test 65024 65152 :=
  FiniteChecks.interval_of_check test 65024 128 (by decide +kernel)
theorem checked_65152 : FiniteChecks.Interval test 65152 65280 :=
  FiniteChecks.interval_of_check test 65152 128 (by decide +kernel)
theorem checked_65280 : FiniteChecks.Interval test 65280 65408 :=
  FiniteChecks.interval_of_check test 65280 128 (by decide +kernel)
theorem checked_65408 : FiniteChecks.Interval test 65408 65536 :=
  FiniteChecks.interval_of_check test 65408 128 (by decide +kernel)
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
