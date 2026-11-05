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
theorem checked_86016 : FiniteChecks.Interval test 86016 86144 :=
  FiniteChecks.interval_of_check test 86016 128 (by decide +kernel)
theorem checked_86144 : FiniteChecks.Interval test 86144 86272 :=
  FiniteChecks.interval_of_check test 86144 128 (by decide +kernel)
theorem checked_86272 : FiniteChecks.Interval test 86272 86400 :=
  FiniteChecks.interval_of_check test 86272 128 (by decide +kernel)
theorem checked_86400 : FiniteChecks.Interval test 86400 86528 :=
  FiniteChecks.interval_of_check test 86400 128 (by decide +kernel)
theorem checked_86528 : FiniteChecks.Interval test 86528 86656 :=
  FiniteChecks.interval_of_check test 86528 128 (by decide +kernel)
theorem checked_86656 : FiniteChecks.Interval test 86656 86784 :=
  FiniteChecks.interval_of_check test 86656 128 (by decide +kernel)
theorem checked_86784 : FiniteChecks.Interval test 86784 86912 :=
  FiniteChecks.interval_of_check test 86784 128 (by decide +kernel)
theorem checked_86912 : FiniteChecks.Interval test 86912 87040 :=
  FiniteChecks.interval_of_check test 86912 128 (by decide +kernel)
theorem checked_87040 : FiniteChecks.Interval test 87040 87168 :=
  FiniteChecks.interval_of_check test 87040 128 (by decide +kernel)
theorem checked_87168 : FiniteChecks.Interval test 87168 87296 :=
  FiniteChecks.interval_of_check test 87168 128 (by decide +kernel)
theorem checked_87296 : FiniteChecks.Interval test 87296 87424 :=
  FiniteChecks.interval_of_check test 87296 128 (by decide +kernel)
theorem checked_87424 : FiniteChecks.Interval test 87424 87552 :=
  FiniteChecks.interval_of_check test 87424 128 (by decide +kernel)
theorem checked_87552 : FiniteChecks.Interval test 87552 87680 :=
  FiniteChecks.interval_of_check test 87552 128 (by decide +kernel)
theorem checked_87680 : FiniteChecks.Interval test 87680 87808 :=
  FiniteChecks.interval_of_check test 87680 128 (by decide +kernel)
theorem checked_87808 : FiniteChecks.Interval test 87808 87936 :=
  FiniteChecks.interval_of_check test 87808 128 (by decide +kernel)
theorem checked_87936 : FiniteChecks.Interval test 87936 88064 :=
  FiniteChecks.interval_of_check test 87936 128 (by decide +kernel)
theorem checked_88064 : FiniteChecks.Interval test 88064 88192 :=
  FiniteChecks.interval_of_check test 88064 128 (by decide +kernel)
theorem checked_88192 : FiniteChecks.Interval test 88192 88320 :=
  FiniteChecks.interval_of_check test 88192 128 (by decide +kernel)
theorem checked_88320 : FiniteChecks.Interval test 88320 88448 :=
  FiniteChecks.interval_of_check test 88320 128 (by decide +kernel)
theorem checked_88448 : FiniteChecks.Interval test 88448 88576 :=
  FiniteChecks.interval_of_check test 88448 128 (by decide +kernel)
theorem checked_88576 : FiniteChecks.Interval test 88576 88704 :=
  FiniteChecks.interval_of_check test 88576 128 (by decide +kernel)
theorem checked_88704 : FiniteChecks.Interval test 88704 88832 :=
  FiniteChecks.interval_of_check test 88704 128 (by decide +kernel)
theorem checked_88832 : FiniteChecks.Interval test 88832 88960 :=
  FiniteChecks.interval_of_check test 88832 128 (by decide +kernel)
theorem checked_88960 : FiniteChecks.Interval test 88960 89088 :=
  FiniteChecks.interval_of_check test 88960 128 (by decide +kernel)
theorem checked_89088 : FiniteChecks.Interval test 89088 89216 :=
  FiniteChecks.interval_of_check test 89088 128 (by decide +kernel)
theorem checked_89216 : FiniteChecks.Interval test 89216 89344 :=
  FiniteChecks.interval_of_check test 89216 128 (by decide +kernel)
theorem checked_89344 : FiniteChecks.Interval test 89344 89472 :=
  FiniteChecks.interval_of_check test 89344 128 (by decide +kernel)
theorem checked_89472 : FiniteChecks.Interval test 89472 89600 :=
  FiniteChecks.interval_of_check test 89472 128 (by decide +kernel)
theorem checked_89600 : FiniteChecks.Interval test 89600 89728 :=
  FiniteChecks.interval_of_check test 89600 128 (by decide +kernel)
theorem checked_89728 : FiniteChecks.Interval test 89728 89856 :=
  FiniteChecks.interval_of_check test 89728 128 (by decide +kernel)
theorem checked_89856 : FiniteChecks.Interval test 89856 89984 :=
  FiniteChecks.interval_of_check test 89856 128 (by decide +kernel)
theorem checked_89984 : FiniteChecks.Interval test 89984 90112 :=
  FiniteChecks.interval_of_check test 89984 128 (by decide +kernel)
theorem interval_86016 : FiniteChecks.Interval test 86016 90112 :=
  (FiniteChecks.interval_append test 86016 88064 90112
  (FiniteChecks.interval_append test 86016 87040 88064
  (FiniteChecks.interval_append test 86016 86528 87040
  (FiniteChecks.interval_append test 86016 86272 86528
  (FiniteChecks.interval_append test 86016 86144 86272
  checked_86016
  checked_86144)
  (FiniteChecks.interval_append test 86272 86400 86528
  checked_86272
  checked_86400))
  (FiniteChecks.interval_append test 86528 86784 87040
  (FiniteChecks.interval_append test 86528 86656 86784
  checked_86528
  checked_86656)
  (FiniteChecks.interval_append test 86784 86912 87040
  checked_86784
  checked_86912)))
  (FiniteChecks.interval_append test 87040 87552 88064
  (FiniteChecks.interval_append test 87040 87296 87552
  (FiniteChecks.interval_append test 87040 87168 87296
  checked_87040
  checked_87168)
  (FiniteChecks.interval_append test 87296 87424 87552
  checked_87296
  checked_87424))
  (FiniteChecks.interval_append test 87552 87808 88064
  (FiniteChecks.interval_append test 87552 87680 87808
  checked_87552
  checked_87680)
  (FiniteChecks.interval_append test 87808 87936 88064
  checked_87808
  checked_87936))))
  (FiniteChecks.interval_append test 88064 89088 90112
  (FiniteChecks.interval_append test 88064 88576 89088
  (FiniteChecks.interval_append test 88064 88320 88576
  (FiniteChecks.interval_append test 88064 88192 88320
  checked_88064
  checked_88192)
  (FiniteChecks.interval_append test 88320 88448 88576
  checked_88320
  checked_88448))
  (FiniteChecks.interval_append test 88576 88832 89088
  (FiniteChecks.interval_append test 88576 88704 88832
  checked_88576
  checked_88704)
  (FiniteChecks.interval_append test 88832 88960 89088
  checked_88832
  checked_88960)))
  (FiniteChecks.interval_append test 89088 89600 90112
  (FiniteChecks.interval_append test 89088 89344 89600
  (FiniteChecks.interval_append test 89088 89216 89344
  checked_89088
  checked_89216)
  (FiniteChecks.interval_append test 89344 89472 89600
  checked_89344
  checked_89472))
  (FiniteChecks.interval_append test 89600 89856 90112
  (FiniteChecks.interval_append test 89600 89728 89856
  checked_89600
  checked_89728)
  (FiniteChecks.interval_append test 89856 89984 90112
  checked_89856
  checked_89984)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
