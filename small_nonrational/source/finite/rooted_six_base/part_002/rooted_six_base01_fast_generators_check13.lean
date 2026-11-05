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
theorem checked_53248 : FiniteChecks.Interval test 53248 53376 :=
  FiniteChecks.interval_of_check test 53248 128 (by decide +kernel)
theorem checked_53376 : FiniteChecks.Interval test 53376 53504 :=
  FiniteChecks.interval_of_check test 53376 128 (by decide +kernel)
theorem checked_53504 : FiniteChecks.Interval test 53504 53632 :=
  FiniteChecks.interval_of_check test 53504 128 (by decide +kernel)
theorem checked_53632 : FiniteChecks.Interval test 53632 53760 :=
  FiniteChecks.interval_of_check test 53632 128 (by decide +kernel)
theorem checked_53760 : FiniteChecks.Interval test 53760 53888 :=
  FiniteChecks.interval_of_check test 53760 128 (by decide +kernel)
theorem checked_53888 : FiniteChecks.Interval test 53888 54016 :=
  FiniteChecks.interval_of_check test 53888 128 (by decide +kernel)
theorem checked_54016 : FiniteChecks.Interval test 54016 54144 :=
  FiniteChecks.interval_of_check test 54016 128 (by decide +kernel)
theorem checked_54144 : FiniteChecks.Interval test 54144 54272 :=
  FiniteChecks.interval_of_check test 54144 128 (by decide +kernel)
theorem checked_54272 : FiniteChecks.Interval test 54272 54400 :=
  FiniteChecks.interval_of_check test 54272 128 (by decide +kernel)
theorem checked_54400 : FiniteChecks.Interval test 54400 54528 :=
  FiniteChecks.interval_of_check test 54400 128 (by decide +kernel)
theorem checked_54528 : FiniteChecks.Interval test 54528 54656 :=
  FiniteChecks.interval_of_check test 54528 128 (by decide +kernel)
theorem checked_54656 : FiniteChecks.Interval test 54656 54784 :=
  FiniteChecks.interval_of_check test 54656 128 (by decide +kernel)
theorem checked_54784 : FiniteChecks.Interval test 54784 54912 :=
  FiniteChecks.interval_of_check test 54784 128 (by decide +kernel)
theorem checked_54912 : FiniteChecks.Interval test 54912 55040 :=
  FiniteChecks.interval_of_check test 54912 128 (by decide +kernel)
theorem checked_55040 : FiniteChecks.Interval test 55040 55168 :=
  FiniteChecks.interval_of_check test 55040 128 (by decide +kernel)
theorem checked_55168 : FiniteChecks.Interval test 55168 55296 :=
  FiniteChecks.interval_of_check test 55168 128 (by decide +kernel)
theorem checked_55296 : FiniteChecks.Interval test 55296 55424 :=
  FiniteChecks.interval_of_check test 55296 128 (by decide +kernel)
theorem checked_55424 : FiniteChecks.Interval test 55424 55552 :=
  FiniteChecks.interval_of_check test 55424 128 (by decide +kernel)
theorem checked_55552 : FiniteChecks.Interval test 55552 55680 :=
  FiniteChecks.interval_of_check test 55552 128 (by decide +kernel)
theorem checked_55680 : FiniteChecks.Interval test 55680 55808 :=
  FiniteChecks.interval_of_check test 55680 128 (by decide +kernel)
theorem checked_55808 : FiniteChecks.Interval test 55808 55936 :=
  FiniteChecks.interval_of_check test 55808 128 (by decide +kernel)
theorem checked_55936 : FiniteChecks.Interval test 55936 56064 :=
  FiniteChecks.interval_of_check test 55936 128 (by decide +kernel)
theorem checked_56064 : FiniteChecks.Interval test 56064 56192 :=
  FiniteChecks.interval_of_check test 56064 128 (by decide +kernel)
theorem checked_56192 : FiniteChecks.Interval test 56192 56320 :=
  FiniteChecks.interval_of_check test 56192 128 (by decide +kernel)
theorem checked_56320 : FiniteChecks.Interval test 56320 56448 :=
  FiniteChecks.interval_of_check test 56320 128 (by decide +kernel)
theorem checked_56448 : FiniteChecks.Interval test 56448 56576 :=
  FiniteChecks.interval_of_check test 56448 128 (by decide +kernel)
theorem checked_56576 : FiniteChecks.Interval test 56576 56704 :=
  FiniteChecks.interval_of_check test 56576 128 (by decide +kernel)
theorem checked_56704 : FiniteChecks.Interval test 56704 56832 :=
  FiniteChecks.interval_of_check test 56704 128 (by decide +kernel)
theorem checked_56832 : FiniteChecks.Interval test 56832 56960 :=
  FiniteChecks.interval_of_check test 56832 128 (by decide +kernel)
theorem checked_56960 : FiniteChecks.Interval test 56960 57088 :=
  FiniteChecks.interval_of_check test 56960 128 (by decide +kernel)
theorem checked_57088 : FiniteChecks.Interval test 57088 57216 :=
  FiniteChecks.interval_of_check test 57088 128 (by decide +kernel)
theorem checked_57216 : FiniteChecks.Interval test 57216 57344 :=
  FiniteChecks.interval_of_check test 57216 128 (by decide +kernel)
theorem interval_53248 : FiniteChecks.Interval test 53248 57344 :=
  (FiniteChecks.interval_append test 53248 55296 57344
  (FiniteChecks.interval_append test 53248 54272 55296
  (FiniteChecks.interval_append test 53248 53760 54272
  (FiniteChecks.interval_append test 53248 53504 53760
  (FiniteChecks.interval_append test 53248 53376 53504
  checked_53248
  checked_53376)
  (FiniteChecks.interval_append test 53504 53632 53760
  checked_53504
  checked_53632))
  (FiniteChecks.interval_append test 53760 54016 54272
  (FiniteChecks.interval_append test 53760 53888 54016
  checked_53760
  checked_53888)
  (FiniteChecks.interval_append test 54016 54144 54272
  checked_54016
  checked_54144)))
  (FiniteChecks.interval_append test 54272 54784 55296
  (FiniteChecks.interval_append test 54272 54528 54784
  (FiniteChecks.interval_append test 54272 54400 54528
  checked_54272
  checked_54400)
  (FiniteChecks.interval_append test 54528 54656 54784
  checked_54528
  checked_54656))
  (FiniteChecks.interval_append test 54784 55040 55296
  (FiniteChecks.interval_append test 54784 54912 55040
  checked_54784
  checked_54912)
  (FiniteChecks.interval_append test 55040 55168 55296
  checked_55040
  checked_55168))))
  (FiniteChecks.interval_append test 55296 56320 57344
  (FiniteChecks.interval_append test 55296 55808 56320
  (FiniteChecks.interval_append test 55296 55552 55808
  (FiniteChecks.interval_append test 55296 55424 55552
  checked_55296
  checked_55424)
  (FiniteChecks.interval_append test 55552 55680 55808
  checked_55552
  checked_55680))
  (FiniteChecks.interval_append test 55808 56064 56320
  (FiniteChecks.interval_append test 55808 55936 56064
  checked_55808
  checked_55936)
  (FiniteChecks.interval_append test 56064 56192 56320
  checked_56064
  checked_56192)))
  (FiniteChecks.interval_append test 56320 56832 57344
  (FiniteChecks.interval_append test 56320 56576 56832
  (FiniteChecks.interval_append test 56320 56448 56576
  checked_56320
  checked_56448)
  (FiniteChecks.interval_append test 56576 56704 56832
  checked_56576
  checked_56704))
  (FiniteChecks.interval_append test 56832 57088 57344
  (FiniteChecks.interval_append test 56832 56960 57088
  checked_56832
  checked_56960)
  (FiniteChecks.interval_append test 57088 57216 57344
  checked_57088
  checked_57216)))))
end Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
