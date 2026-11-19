module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed012ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed012.Validity
open Papers.RationalityTen
cert_checked_4 00512 512 544 32
cert_checked_4 00544 544 576 32
cert_checked_4 00576 576 608 32
cert_checked_4 00608 608 640 32
cert_checked_4 00640 640 672 32
cert_checked_4 00672 672 704 32
cert_checked_4 00704 704 736 32
cert_checked_4 00736 736 768 32
cert_checked_4 00768 768 800 32
cert_checked_4 00800 800 832 32
cert_checked_4 00832 832 838 6
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
