module
prelude
public import RootedSevenMixed008ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed008.Validity
open Papers.RationalityTen
theorem checked_00512 : FiniteChecks.Interval test 512 544 :=
  FiniteChecks.interval_of_check test 512 32 (by decide +kernel)
theorem checked_00544 : FiniteChecks.Interval test 544 576 :=
  FiniteChecks.interval_of_check test 544 32 (by decide +kernel)
theorem checked_00576 : FiniteChecks.Interval test 576 608 :=
  FiniteChecks.interval_of_check test 576 32 (by decide +kernel)
theorem checked_00608 : FiniteChecks.Interval test 608 640 :=
  FiniteChecks.interval_of_check test 608 32 (by decide +kernel)
theorem checked_00640 : FiniteChecks.Interval test 640 672 :=
  FiniteChecks.interval_of_check test 640 32 (by decide +kernel)
theorem checked_00672 : FiniteChecks.Interval test 672 694 :=
  FiniteChecks.interval_of_check test 672 22 (by decide +kernel)
theorem part_001 : FiniteChecks.Interval test 512 694 :=
  (FiniteChecks.interval_append test 512 608 694
  (FiniteChecks.interval_append test 512 544 608
  checked_00512
  (FiniteChecks.interval_append test 544 576 608
  checked_00544
  checked_00576))
  (FiniteChecks.interval_append test 608 640 694
  checked_00608
  (FiniteChecks.interval_append test 640 672 694
  checked_00640
  checked_00672)))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed008.Validity
