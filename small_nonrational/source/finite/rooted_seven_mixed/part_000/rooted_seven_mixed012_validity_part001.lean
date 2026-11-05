module
prelude
public import RootedSevenMixed012ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.Validity
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
theorem checked_00832 : FiniteChecks.Interval test 832 838 :=
  FiniteChecks.interval_of_check test 832 6 (by decide +kernel)
theorem part_001 : FiniteChecks.Interval test 512 838 :=
  (FiniteChecks.interval_append test 512 672 838
  (FiniteChecks.interval_append test 512 576 672
  (FiniteChecks.interval_append test 512 544 576
  checked_00512
  checked_00544)
  (FiniteChecks.interval_append test 576 608 672
  checked_00576
  (FiniteChecks.interval_append test 608 640 672
  checked_00608
  checked_00640)))
  (FiniteChecks.interval_append test 672 768 838
  (FiniteChecks.interval_append test 672 704 768
  checked_00672
  (FiniteChecks.interval_append test 704 736 768
  checked_00704
  checked_00736))
  (FiniteChecks.interval_append test 768 800 838
  checked_00768
  (FiniteChecks.interval_append test 800 832 838
  checked_00800
  checked_00832))))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.Validity
