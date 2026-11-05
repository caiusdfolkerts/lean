module
prelude
public import RootedSixBase01FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
theorem checked_12288 : FiniteChecks.Interval test 12288 12416 :=
  FiniteChecks.interval_of_check test 12288 128 (by decide +kernel)
theorem checked_12416 : FiniteChecks.Interval test 12416 12544 :=
  FiniteChecks.interval_of_check test 12416 128 (by decide +kernel)
theorem checked_12544 : FiniteChecks.Interval test 12544 12672 :=
  FiniteChecks.interval_of_check test 12544 128 (by decide +kernel)
theorem checked_12672 : FiniteChecks.Interval test 12672 12800 :=
  FiniteChecks.interval_of_check test 12672 128 (by decide +kernel)
theorem checked_12800 : FiniteChecks.Interval test 12800 12928 :=
  FiniteChecks.interval_of_check test 12800 128 (by decide +kernel)
theorem checked_12928 : FiniteChecks.Interval test 12928 13056 :=
  FiniteChecks.interval_of_check test 12928 128 (by decide +kernel)
theorem checked_13056 : FiniteChecks.Interval test 13056 13184 :=
  FiniteChecks.interval_of_check test 13056 128 (by decide +kernel)
theorem checked_13184 : FiniteChecks.Interval test 13184 13312 :=
  FiniteChecks.interval_of_check test 13184 128 (by decide +kernel)
theorem checked_13312 : FiniteChecks.Interval test 13312 13440 :=
  FiniteChecks.interval_of_check test 13312 128 (by decide +kernel)
theorem checked_13440 : FiniteChecks.Interval test 13440 13568 :=
  FiniteChecks.interval_of_check test 13440 128 (by decide +kernel)
theorem checked_13568 : FiniteChecks.Interval test 13568 13696 :=
  FiniteChecks.interval_of_check test 13568 128 (by decide +kernel)
theorem checked_13696 : FiniteChecks.Interval test 13696 13824 :=
  FiniteChecks.interval_of_check test 13696 128 (by decide +kernel)
theorem checked_13824 : FiniteChecks.Interval test 13824 13952 :=
  FiniteChecks.interval_of_check test 13824 128 (by decide +kernel)
theorem checked_13952 : FiniteChecks.Interval test 13952 14080 :=
  FiniteChecks.interval_of_check test 13952 128 (by decide +kernel)
theorem checked_14080 : FiniteChecks.Interval test 14080 14208 :=
  FiniteChecks.interval_of_check test 14080 128 (by decide +kernel)
theorem checked_14208 : FiniteChecks.Interval test 14208 14336 :=
  FiniteChecks.interval_of_check test 14208 128 (by decide +kernel)
theorem checked_14336 : FiniteChecks.Interval test 14336 14464 :=
  FiniteChecks.interval_of_check test 14336 128 (by decide +kernel)
theorem checked_14464 : FiniteChecks.Interval test 14464 14592 :=
  FiniteChecks.interval_of_check test 14464 128 (by decide +kernel)
theorem checked_14592 : FiniteChecks.Interval test 14592 14720 :=
  FiniteChecks.interval_of_check test 14592 128 (by decide +kernel)
theorem checked_14720 : FiniteChecks.Interval test 14720 14848 :=
  FiniteChecks.interval_of_check test 14720 128 (by decide +kernel)
theorem checked_14848 : FiniteChecks.Interval test 14848 14976 :=
  FiniteChecks.interval_of_check test 14848 128 (by decide +kernel)
theorem checked_14976 : FiniteChecks.Interval test 14976 15104 :=
  FiniteChecks.interval_of_check test 14976 128 (by decide +kernel)
theorem checked_15104 : FiniteChecks.Interval test 15104 15232 :=
  FiniteChecks.interval_of_check test 15104 128 (by decide +kernel)
theorem checked_15232 : FiniteChecks.Interval test 15232 15360 :=
  FiniteChecks.interval_of_check test 15232 128 (by decide +kernel)
theorem checked_15360 : FiniteChecks.Interval test 15360 15488 :=
  FiniteChecks.interval_of_check test 15360 128 (by decide +kernel)
theorem checked_15488 : FiniteChecks.Interval test 15488 15616 :=
  FiniteChecks.interval_of_check test 15488 128 (by decide +kernel)
theorem checked_15616 : FiniteChecks.Interval test 15616 15744 :=
  FiniteChecks.interval_of_check test 15616 128 (by decide +kernel)
theorem checked_15744 : FiniteChecks.Interval test 15744 15872 :=
  FiniteChecks.interval_of_check test 15744 128 (by decide +kernel)
theorem checked_15872 : FiniteChecks.Interval test 15872 16000 :=
  FiniteChecks.interval_of_check test 15872 128 (by decide +kernel)
theorem checked_16000 : FiniteChecks.Interval test 16000 16128 :=
  FiniteChecks.interval_of_check test 16000 128 (by decide +kernel)
theorem checked_16128 : FiniteChecks.Interval test 16128 16256 :=
  FiniteChecks.interval_of_check test 16128 128 (by decide +kernel)
theorem checked_16256 : FiniteChecks.Interval test 16256 16384 :=
  FiniteChecks.interval_of_check test 16256 128 (by decide +kernel)
theorem interval_12288 : FiniteChecks.Interval test 12288 16384 :=
  (FiniteChecks.interval_append test 12288 14336 16384
  (FiniteChecks.interval_append test 12288 13312 14336
  (FiniteChecks.interval_append test 12288 12800 13312
  (FiniteChecks.interval_append test 12288 12544 12800
  (FiniteChecks.interval_append test 12288 12416 12544
  checked_12288
  checked_12416)
  (FiniteChecks.interval_append test 12544 12672 12800
  checked_12544
  checked_12672))
  (FiniteChecks.interval_append test 12800 13056 13312
  (FiniteChecks.interval_append test 12800 12928 13056
  checked_12800
  checked_12928)
  (FiniteChecks.interval_append test 13056 13184 13312
  checked_13056
  checked_13184)))
  (FiniteChecks.interval_append test 13312 13824 14336
  (FiniteChecks.interval_append test 13312 13568 13824
  (FiniteChecks.interval_append test 13312 13440 13568
  checked_13312
  checked_13440)
  (FiniteChecks.interval_append test 13568 13696 13824
  checked_13568
  checked_13696))
  (FiniteChecks.interval_append test 13824 14080 14336
  (FiniteChecks.interval_append test 13824 13952 14080
  checked_13824
  checked_13952)
  (FiniteChecks.interval_append test 14080 14208 14336
  checked_14080
  checked_14208))))
  (FiniteChecks.interval_append test 14336 15360 16384
  (FiniteChecks.interval_append test 14336 14848 15360
  (FiniteChecks.interval_append test 14336 14592 14848
  (FiniteChecks.interval_append test 14336 14464 14592
  checked_14336
  checked_14464)
  (FiniteChecks.interval_append test 14592 14720 14848
  checked_14592
  checked_14720))
  (FiniteChecks.interval_append test 14848 15104 15360
  (FiniteChecks.interval_append test 14848 14976 15104
  checked_14848
  checked_14976)
  (FiniteChecks.interval_append test 15104 15232 15360
  checked_15104
  checked_15232)))
  (FiniteChecks.interval_append test 15360 15872 16384
  (FiniteChecks.interval_append test 15360 15616 15872
  (FiniteChecks.interval_append test 15360 15488 15616
  checked_15360
  checked_15488)
  (FiniteChecks.interval_append test 15616 15744 15872
  checked_15616
  checked_15744))
  (FiniteChecks.interval_append test 15872 16128 16384
  (FiniteChecks.interval_append test 15872 16000 16128
  checked_15872
  checked_16000)
  (FiniteChecks.interval_append test 16128 16256 16384
  checked_16128
  checked_16256)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
