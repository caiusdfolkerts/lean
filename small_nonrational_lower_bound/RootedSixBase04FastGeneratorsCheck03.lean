module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase04FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_7 12288 12416 128
cert_checked_7 12416 12544 128
cert_checked_7 12544 12672 128
cert_checked_7 12672 12800 128
cert_checked_7 12800 12928 128
cert_checked_7 12928 13056 128
cert_checked_7 13056 13184 128
cert_checked_7 13184 13312 128
cert_checked_7 13312 13440 128
cert_checked_7 13440 13568 128
cert_checked_7 13568 13696 128
cert_checked_7 13696 13824 128
cert_checked_7 13824 13952 128
cert_checked_7 13952 14080 128
cert_checked_7 14080 14208 128
cert_checked_7 14208 14336 128
cert_checked_7 14336 14464 128
cert_checked_7 14464 14592 128
cert_checked_7 14592 14720 128
cert_checked_7 14720 14848 128
cert_checked_7 14848 14976 128
cert_checked_7 14976 15104 128
cert_checked_7 15104 15232 128
cert_checked_7 15232 15360 128
cert_checked_7 15360 15488 128
cert_checked_7 15488 15616 128
cert_checked_7 15616 15744 128
cert_checked_7 15744 15872 128
cert_checked_7 15872 16000 128
cert_checked_7 16000 16128 128
cert_checked_7 16128 16256 128
cert_checked_7 16256 16384 128
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
end Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.Fast
