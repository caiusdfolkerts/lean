module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed008ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed008.Validity
open Papers.RationalityTen
cert_checked_4 00512 512 544 32
cert_checked_4 00544 544 576 32
cert_checked_4 00576 576 608 32
cert_checked_4 00608 608 640 32
cert_checked_4 00640 640 672 32
cert_checked_4 00672 672 694 22
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
