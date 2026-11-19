module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed000ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed000.Validity
open Papers.RationalityTen
cert_checked_4 00512 512 544 32
cert_checked_4 00544 544 576 32
cert_checked_4 00576 576 608 32
cert_checked_4 00608 608 640 32
cert_checked_4 00640 640 646 6
theorem part_001 : FiniteChecks.Interval test 512 646 :=
  (FiniteChecks.interval_append test 512 576 646
  (FiniteChecks.interval_append test 512 544 576
  checked_00512
  checked_00544)
  (FiniteChecks.interval_append test 576 608 646
  checked_00576
  (FiniteChecks.interval_append test 608 640 646
  checked_00608
  checked_00640)))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed000.Validity
