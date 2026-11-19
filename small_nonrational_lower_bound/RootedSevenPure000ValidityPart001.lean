module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public import RootedSevenPure000ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure000.Validity
open Papers.RationalityTen
cert_checked_6 00512 512 544 32
cert_checked_6 00544 544 576 32
cert_checked_6 00576 576 608 32
cert_checked_6 00608 608 640 32
cert_checked_6 00640 640 672 32
cert_checked_6 00672 672 704 32
cert_checked_6 00704 704 736 32
cert_checked_6 00736 736 758 22
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
