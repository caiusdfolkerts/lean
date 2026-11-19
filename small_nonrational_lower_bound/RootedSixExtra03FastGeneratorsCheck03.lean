module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra03FastGeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.Fast
open Papers.RationalityTen ConcreteGrowth
cert_checked_9 12288 12416 128
cert_checked_9 12416 12544 128
cert_checked_9 12544 12672 128
cert_checked_9 12672 12800 128
cert_checked_9 12800 12928 128
cert_checked_9 12928 13056 128
cert_checked_9 13056 13184 128
cert_checked_9 13184 13312 128
cert_checked_9 13312 13440 128
cert_checked_9 13440 13568 128
cert_checked_9 13568 13696 128
cert_checked_9 13696 13824 128
cert_checked_9 13824 13952 128
cert_checked_9 13952 14080 128
cert_checked_9 14080 14208 128
cert_checked_9 14208 14336 128
cert_checked_9 14336 14464 128
cert_checked_9 14464 14592 128
cert_checked_9 14592 14720 128
cert_checked_9 14720 14848 128
cert_checked_9 14848 14976 128
cert_checked_9 14976 15104 128
cert_checked_9 15104 15232 128
cert_checked_9 15232 15360 128
cert_checked_9 15360 15488 128
cert_checked_9 15488 15616 128
cert_checked_9 15616 15744 128
cert_checked_9 15744 15750 6
theorem interval_12288 : FiniteChecks.Interval test 12288 15750 :=
  (FiniteChecks.interval_append test 12288 14080 15750
  (FiniteChecks.interval_append test 12288 13184 14080
  (FiniteChecks.interval_append test 12288 12672 13184
  (FiniteChecks.interval_append test 12288 12416 12672
  checked_12288
  (FiniteChecks.interval_append test 12416 12544 12672
  checked_12416
  checked_12544))
  (FiniteChecks.interval_append test 12672 12928 13184
  (FiniteChecks.interval_append test 12672 12800 12928
  checked_12672
  checked_12800)
  (FiniteChecks.interval_append test 12928 13056 13184
  checked_12928
  checked_13056)))
  (FiniteChecks.interval_append test 13184 13568 14080
  (FiniteChecks.interval_append test 13184 13312 13568
  checked_13184
  (FiniteChecks.interval_append test 13312 13440 13568
  checked_13312
  checked_13440))
  (FiniteChecks.interval_append test 13568 13824 14080
  (FiniteChecks.interval_append test 13568 13696 13824
  checked_13568
  checked_13696)
  (FiniteChecks.interval_append test 13824 13952 14080
  checked_13824
  checked_13952))))
  (FiniteChecks.interval_append test 14080 14976 15750
  (FiniteChecks.interval_append test 14080 14464 14976
  (FiniteChecks.interval_append test 14080 14208 14464
  checked_14080
  (FiniteChecks.interval_append test 14208 14336 14464
  checked_14208
  checked_14336))
  (FiniteChecks.interval_append test 14464 14720 14976
  (FiniteChecks.interval_append test 14464 14592 14720
  checked_14464
  checked_14592)
  (FiniteChecks.interval_append test 14720 14848 14976
  checked_14720
  checked_14848)))
  (FiniteChecks.interval_append test 14976 15360 15750
  (FiniteChecks.interval_append test 14976 15104 15360
  checked_14976
  (FiniteChecks.interval_append test 15104 15232 15360
  checked_15104
  checked_15232))
  (FiniteChecks.interval_append test 15360 15616 15750
  (FiniteChecks.interval_append test 15360 15488 15616
  checked_15360
  checked_15488)
  (FiniteChecks.interval_append test 15616 15744 15750
  checked_15616
  checked_15744)))))
end Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.Fast
