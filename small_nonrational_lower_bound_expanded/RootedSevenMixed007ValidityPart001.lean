module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed007ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed007.Validity
open Papers.RationalityTen
cert_checked_4 00512 512 544 32
cert_checked_4 00544 544 556 12
theorem part_001 : FiniteChecks.Interval test 512 556 :=
  (FiniteChecks.interval_append test 512 544 556
  checked_00512
  checked_00544)
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed007.Validity
