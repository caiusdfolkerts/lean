module
prelude
public import RootedSevenPure000ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure000.Validity
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
theorem checked_00672 : FiniteChecks.Interval test 672 704 :=
  FiniteChecks.interval_of_check test 672 32 (by decide +kernel)
theorem checked_00704 : FiniteChecks.Interval test 704 736 :=
  FiniteChecks.interval_of_check test 704 32 (by decide +kernel)
theorem checked_00736 : FiniteChecks.Interval test 736 758 :=
  FiniteChecks.interval_of_check test 736 22 (by decide +kernel)
theorem part_001 : FiniteChecks.Interval test 512 758 :=
  (FiniteChecks.interval_append test 512 640 758
  (FiniteChecks.interval_append test 512 576 640
  (FiniteChecks.interval_append test 512 544 576
  checked_00512
  checked_00544)
  (FiniteChecks.interval_append test 576 608 640
  checked_00576
  checked_00608))
  (FiniteChecks.interval_append test 640 704 758
  (FiniteChecks.interval_append test 640 672 704
  checked_00640
  checked_00672)
  (FiniteChecks.interval_append test 704 736 758
  checked_00704
  checked_00736)))
end Papers.RationalityTen.FacetUniverses.RootedSevenPure000.Validity
