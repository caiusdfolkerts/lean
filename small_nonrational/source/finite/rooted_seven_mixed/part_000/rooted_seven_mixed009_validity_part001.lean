module
prelude
public import RootedSevenMixed009ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.Validity
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
theorem checked_00736 : FiniteChecks.Interval test 736 768 :=
  FiniteChecks.interval_of_check test 736 32 (by decide +kernel)
theorem checked_00768 : FiniteChecks.Interval test 768 800 :=
  FiniteChecks.interval_of_check test 768 32 (by decide +kernel)
theorem checked_00800 : FiniteChecks.Interval test 800 832 :=
  FiniteChecks.interval_of_check test 800 32 (by decide +kernel)
theorem checked_00832 : FiniteChecks.Interval test 832 864 :=
  FiniteChecks.interval_of_check test 832 32 (by decide +kernel)
theorem checked_00864 : FiniteChecks.Interval test 864 896 :=
  FiniteChecks.interval_of_check test 864 32 (by decide +kernel)
theorem checked_00896 : FiniteChecks.Interval test 896 910 :=
  FiniteChecks.interval_of_check test 896 14 (by decide +kernel)
theorem part_001 : FiniteChecks.Interval test 512 910 :=
  (FiniteChecks.interval_append test 512 704 910
  (FiniteChecks.interval_append test 512 608 704
  (FiniteChecks.interval_append test 512 544 608
  checked_00512
  (FiniteChecks.interval_append test 544 576 608
  checked_00544
  checked_00576))
  (FiniteChecks.interval_append test 608 640 704
  checked_00608
  (FiniteChecks.interval_append test 640 672 704
  checked_00640
  checked_00672)))
  (FiniteChecks.interval_append test 704 800 910
  (FiniteChecks.interval_append test 704 736 800
  checked_00704
  (FiniteChecks.interval_append test 736 768 800
  checked_00736
  checked_00768))
  (FiniteChecks.interval_append test 800 864 910
  (FiniteChecks.interval_append test 800 832 864
  checked_00800
  checked_00832)
  (FiniteChecks.interval_append test 864 896 910
  checked_00864
  checked_00896))))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed009.Validity
