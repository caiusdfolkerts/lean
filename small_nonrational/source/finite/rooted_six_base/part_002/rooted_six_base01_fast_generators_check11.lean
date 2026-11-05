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
theorem checked_45056 : FiniteChecks.Interval test 45056 45184 :=
  FiniteChecks.interval_of_check test 45056 128 (by decide +kernel)
theorem checked_45184 : FiniteChecks.Interval test 45184 45312 :=
  FiniteChecks.interval_of_check test 45184 128 (by decide +kernel)
theorem checked_45312 : FiniteChecks.Interval test 45312 45440 :=
  FiniteChecks.interval_of_check test 45312 128 (by decide +kernel)
theorem checked_45440 : FiniteChecks.Interval test 45440 45568 :=
  FiniteChecks.interval_of_check test 45440 128 (by decide +kernel)
theorem checked_45568 : FiniteChecks.Interval test 45568 45696 :=
  FiniteChecks.interval_of_check test 45568 128 (by decide +kernel)
theorem checked_45696 : FiniteChecks.Interval test 45696 45824 :=
  FiniteChecks.interval_of_check test 45696 128 (by decide +kernel)
theorem checked_45824 : FiniteChecks.Interval test 45824 45952 :=
  FiniteChecks.interval_of_check test 45824 128 (by decide +kernel)
theorem checked_45952 : FiniteChecks.Interval test 45952 46080 :=
  FiniteChecks.interval_of_check test 45952 128 (by decide +kernel)
theorem checked_46080 : FiniteChecks.Interval test 46080 46208 :=
  FiniteChecks.interval_of_check test 46080 128 (by decide +kernel)
theorem checked_46208 : FiniteChecks.Interval test 46208 46336 :=
  FiniteChecks.interval_of_check test 46208 128 (by decide +kernel)
theorem checked_46336 : FiniteChecks.Interval test 46336 46464 :=
  FiniteChecks.interval_of_check test 46336 128 (by decide +kernel)
theorem checked_46464 : FiniteChecks.Interval test 46464 46592 :=
  FiniteChecks.interval_of_check test 46464 128 (by decide +kernel)
theorem checked_46592 : FiniteChecks.Interval test 46592 46720 :=
  FiniteChecks.interval_of_check test 46592 128 (by decide +kernel)
theorem checked_46720 : FiniteChecks.Interval test 46720 46848 :=
  FiniteChecks.interval_of_check test 46720 128 (by decide +kernel)
theorem checked_46848 : FiniteChecks.Interval test 46848 46976 :=
  FiniteChecks.interval_of_check test 46848 128 (by decide +kernel)
theorem checked_46976 : FiniteChecks.Interval test 46976 47104 :=
  FiniteChecks.interval_of_check test 46976 128 (by decide +kernel)
theorem checked_47104 : FiniteChecks.Interval test 47104 47232 :=
  FiniteChecks.interval_of_check test 47104 128 (by decide +kernel)
theorem checked_47232 : FiniteChecks.Interval test 47232 47360 :=
  FiniteChecks.interval_of_check test 47232 128 (by decide +kernel)
theorem checked_47360 : FiniteChecks.Interval test 47360 47488 :=
  FiniteChecks.interval_of_check test 47360 128 (by decide +kernel)
theorem checked_47488 : FiniteChecks.Interval test 47488 47616 :=
  FiniteChecks.interval_of_check test 47488 128 (by decide +kernel)
theorem checked_47616 : FiniteChecks.Interval test 47616 47744 :=
  FiniteChecks.interval_of_check test 47616 128 (by decide +kernel)
theorem checked_47744 : FiniteChecks.Interval test 47744 47872 :=
  FiniteChecks.interval_of_check test 47744 128 (by decide +kernel)
theorem checked_47872 : FiniteChecks.Interval test 47872 48000 :=
  FiniteChecks.interval_of_check test 47872 128 (by decide +kernel)
theorem checked_48000 : FiniteChecks.Interval test 48000 48128 :=
  FiniteChecks.interval_of_check test 48000 128 (by decide +kernel)
theorem checked_48128 : FiniteChecks.Interval test 48128 48256 :=
  FiniteChecks.interval_of_check test 48128 128 (by decide +kernel)
theorem checked_48256 : FiniteChecks.Interval test 48256 48384 :=
  FiniteChecks.interval_of_check test 48256 128 (by decide +kernel)
theorem checked_48384 : FiniteChecks.Interval test 48384 48512 :=
  FiniteChecks.interval_of_check test 48384 128 (by decide +kernel)
theorem checked_48512 : FiniteChecks.Interval test 48512 48640 :=
  FiniteChecks.interval_of_check test 48512 128 (by decide +kernel)
theorem checked_48640 : FiniteChecks.Interval test 48640 48768 :=
  FiniteChecks.interval_of_check test 48640 128 (by decide +kernel)
theorem checked_48768 : FiniteChecks.Interval test 48768 48896 :=
  FiniteChecks.interval_of_check test 48768 128 (by decide +kernel)
theorem checked_48896 : FiniteChecks.Interval test 48896 49024 :=
  FiniteChecks.interval_of_check test 48896 128 (by decide +kernel)
theorem checked_49024 : FiniteChecks.Interval test 49024 49152 :=
  FiniteChecks.interval_of_check test 49024 128 (by decide +kernel)
theorem interval_45056 : FiniteChecks.Interval test 45056 49152 :=
  (FiniteChecks.interval_append test 45056 47104 49152
  (FiniteChecks.interval_append test 45056 46080 47104
  (FiniteChecks.interval_append test 45056 45568 46080
  (FiniteChecks.interval_append test 45056 45312 45568
  (FiniteChecks.interval_append test 45056 45184 45312
  checked_45056
  checked_45184)
  (FiniteChecks.interval_append test 45312 45440 45568
  checked_45312
  checked_45440))
  (FiniteChecks.interval_append test 45568 45824 46080
  (FiniteChecks.interval_append test 45568 45696 45824
  checked_45568
  checked_45696)
  (FiniteChecks.interval_append test 45824 45952 46080
  checked_45824
  checked_45952)))
  (FiniteChecks.interval_append test 46080 46592 47104
  (FiniteChecks.interval_append test 46080 46336 46592
  (FiniteChecks.interval_append test 46080 46208 46336
  checked_46080
  checked_46208)
  (FiniteChecks.interval_append test 46336 46464 46592
  checked_46336
  checked_46464))
  (FiniteChecks.interval_append test 46592 46848 47104
  (FiniteChecks.interval_append test 46592 46720 46848
  checked_46592
  checked_46720)
  (FiniteChecks.interval_append test 46848 46976 47104
  checked_46848
  checked_46976))))
  (FiniteChecks.interval_append test 47104 48128 49152
  (FiniteChecks.interval_append test 47104 47616 48128
  (FiniteChecks.interval_append test 47104 47360 47616
  (FiniteChecks.interval_append test 47104 47232 47360
  checked_47104
  checked_47232)
  (FiniteChecks.interval_append test 47360 47488 47616
  checked_47360
  checked_47488))
  (FiniteChecks.interval_append test 47616 47872 48128
  (FiniteChecks.interval_append test 47616 47744 47872
  checked_47616
  checked_47744)
  (FiniteChecks.interval_append test 47872 48000 48128
  checked_47872
  checked_48000)))
  (FiniteChecks.interval_append test 48128 48640 49152
  (FiniteChecks.interval_append test 48128 48384 48640
  (FiniteChecks.interval_append test 48128 48256 48384
  checked_48128
  checked_48256)
  (FiniteChecks.interval_append test 48384 48512 48640
  checked_48384
  checked_48512))
  (FiniteChecks.interval_append test 48640 48896 49152
  (FiniteChecks.interval_append test 48640 48768 48896
  checked_48640
  checked_48768)
  (FiniteChecks.interval_append test 48896 49024 49152
  checked_48896
  checked_49024)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
