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
theorem checked_20480 : FiniteChecks.Interval test 20480 20608 :=
  FiniteChecks.interval_of_check test 20480 128 (by decide +kernel)
theorem checked_20608 : FiniteChecks.Interval test 20608 20736 :=
  FiniteChecks.interval_of_check test 20608 128 (by decide +kernel)
theorem checked_20736 : FiniteChecks.Interval test 20736 20864 :=
  FiniteChecks.interval_of_check test 20736 128 (by decide +kernel)
theorem checked_20864 : FiniteChecks.Interval test 20864 20992 :=
  FiniteChecks.interval_of_check test 20864 128 (by decide +kernel)
theorem checked_20992 : FiniteChecks.Interval test 20992 21120 :=
  FiniteChecks.interval_of_check test 20992 128 (by decide +kernel)
theorem checked_21120 : FiniteChecks.Interval test 21120 21248 :=
  FiniteChecks.interval_of_check test 21120 128 (by decide +kernel)
theorem checked_21248 : FiniteChecks.Interval test 21248 21376 :=
  FiniteChecks.interval_of_check test 21248 128 (by decide +kernel)
theorem checked_21376 : FiniteChecks.Interval test 21376 21504 :=
  FiniteChecks.interval_of_check test 21376 128 (by decide +kernel)
theorem checked_21504 : FiniteChecks.Interval test 21504 21632 :=
  FiniteChecks.interval_of_check test 21504 128 (by decide +kernel)
theorem checked_21632 : FiniteChecks.Interval test 21632 21760 :=
  FiniteChecks.interval_of_check test 21632 128 (by decide +kernel)
theorem checked_21760 : FiniteChecks.Interval test 21760 21888 :=
  FiniteChecks.interval_of_check test 21760 128 (by decide +kernel)
theorem checked_21888 : FiniteChecks.Interval test 21888 22016 :=
  FiniteChecks.interval_of_check test 21888 128 (by decide +kernel)
theorem checked_22016 : FiniteChecks.Interval test 22016 22144 :=
  FiniteChecks.interval_of_check test 22016 128 (by decide +kernel)
theorem checked_22144 : FiniteChecks.Interval test 22144 22272 :=
  FiniteChecks.interval_of_check test 22144 128 (by decide +kernel)
theorem checked_22272 : FiniteChecks.Interval test 22272 22400 :=
  FiniteChecks.interval_of_check test 22272 128 (by decide +kernel)
theorem checked_22400 : FiniteChecks.Interval test 22400 22528 :=
  FiniteChecks.interval_of_check test 22400 128 (by decide +kernel)
theorem checked_22528 : FiniteChecks.Interval test 22528 22656 :=
  FiniteChecks.interval_of_check test 22528 128 (by decide +kernel)
theorem checked_22656 : FiniteChecks.Interval test 22656 22784 :=
  FiniteChecks.interval_of_check test 22656 128 (by decide +kernel)
theorem checked_22784 : FiniteChecks.Interval test 22784 22912 :=
  FiniteChecks.interval_of_check test 22784 128 (by decide +kernel)
theorem checked_22912 : FiniteChecks.Interval test 22912 23040 :=
  FiniteChecks.interval_of_check test 22912 128 (by decide +kernel)
theorem checked_23040 : FiniteChecks.Interval test 23040 23168 :=
  FiniteChecks.interval_of_check test 23040 128 (by decide +kernel)
theorem checked_23168 : FiniteChecks.Interval test 23168 23296 :=
  FiniteChecks.interval_of_check test 23168 128 (by decide +kernel)
theorem checked_23296 : FiniteChecks.Interval test 23296 23424 :=
  FiniteChecks.interval_of_check test 23296 128 (by decide +kernel)
theorem checked_23424 : FiniteChecks.Interval test 23424 23552 :=
  FiniteChecks.interval_of_check test 23424 128 (by decide +kernel)
theorem checked_23552 : FiniteChecks.Interval test 23552 23680 :=
  FiniteChecks.interval_of_check test 23552 128 (by decide +kernel)
theorem checked_23680 : FiniteChecks.Interval test 23680 23808 :=
  FiniteChecks.interval_of_check test 23680 128 (by decide +kernel)
theorem checked_23808 : FiniteChecks.Interval test 23808 23936 :=
  FiniteChecks.interval_of_check test 23808 128 (by decide +kernel)
theorem checked_23936 : FiniteChecks.Interval test 23936 24064 :=
  FiniteChecks.interval_of_check test 23936 128 (by decide +kernel)
theorem checked_24064 : FiniteChecks.Interval test 24064 24192 :=
  FiniteChecks.interval_of_check test 24064 128 (by decide +kernel)
theorem checked_24192 : FiniteChecks.Interval test 24192 24320 :=
  FiniteChecks.interval_of_check test 24192 128 (by decide +kernel)
theorem checked_24320 : FiniteChecks.Interval test 24320 24448 :=
  FiniteChecks.interval_of_check test 24320 128 (by decide +kernel)
theorem checked_24448 : FiniteChecks.Interval test 24448 24576 :=
  FiniteChecks.interval_of_check test 24448 128 (by decide +kernel)
theorem interval_20480 : FiniteChecks.Interval test 20480 24576 :=
  (FiniteChecks.interval_append test 20480 22528 24576
  (FiniteChecks.interval_append test 20480 21504 22528
  (FiniteChecks.interval_append test 20480 20992 21504
  (FiniteChecks.interval_append test 20480 20736 20992
  (FiniteChecks.interval_append test 20480 20608 20736
  checked_20480
  checked_20608)
  (FiniteChecks.interval_append test 20736 20864 20992
  checked_20736
  checked_20864))
  (FiniteChecks.interval_append test 20992 21248 21504
  (FiniteChecks.interval_append test 20992 21120 21248
  checked_20992
  checked_21120)
  (FiniteChecks.interval_append test 21248 21376 21504
  checked_21248
  checked_21376)))
  (FiniteChecks.interval_append test 21504 22016 22528
  (FiniteChecks.interval_append test 21504 21760 22016
  (FiniteChecks.interval_append test 21504 21632 21760
  checked_21504
  checked_21632)
  (FiniteChecks.interval_append test 21760 21888 22016
  checked_21760
  checked_21888))
  (FiniteChecks.interval_append test 22016 22272 22528
  (FiniteChecks.interval_append test 22016 22144 22272
  checked_22016
  checked_22144)
  (FiniteChecks.interval_append test 22272 22400 22528
  checked_22272
  checked_22400))))
  (FiniteChecks.interval_append test 22528 23552 24576
  (FiniteChecks.interval_append test 22528 23040 23552
  (FiniteChecks.interval_append test 22528 22784 23040
  (FiniteChecks.interval_append test 22528 22656 22784
  checked_22528
  checked_22656)
  (FiniteChecks.interval_append test 22784 22912 23040
  checked_22784
  checked_22912))
  (FiniteChecks.interval_append test 23040 23296 23552
  (FiniteChecks.interval_append test 23040 23168 23296
  checked_23040
  checked_23168)
  (FiniteChecks.interval_append test 23296 23424 23552
  checked_23296
  checked_23424)))
  (FiniteChecks.interval_append test 23552 24064 24576
  (FiniteChecks.interval_append test 23552 23808 24064
  (FiniteChecks.interval_append test 23552 23680 23808
  checked_23552
  checked_23680)
  (FiniteChecks.interval_append test 23808 23936 24064
  checked_23808
  checked_23936))
  (FiniteChecks.interval_append test 24064 24320 24576
  (FiniteChecks.interval_append test 24064 24192 24320
  checked_24064
  checked_24192)
  (FiniteChecks.interval_append test 24320 24448 24576
  checked_24320
  checked_24448)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
