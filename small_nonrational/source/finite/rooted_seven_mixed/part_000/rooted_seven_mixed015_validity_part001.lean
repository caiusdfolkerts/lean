module
prelude
public import RootedSevenMixed015ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed015.Validity
open Papers.RationalityTen
theorem checked_00512 : FiniteChecks.Interval test 512 521 :=
  FiniteChecks.interval_of_check test 512 9 (by decide +kernel)
theorem part_001 : FiniteChecks.Interval test 512 521 :=
  checked_00512
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed015.Validity
