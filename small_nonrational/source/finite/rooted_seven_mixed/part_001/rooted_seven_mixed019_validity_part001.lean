module
prelude
public import RootedSevenMixed019ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed019.Validity
open Papers.RationalityTen
theorem checked_00512 : FiniteChecks.Interval test 512 544 :=
  FiniteChecks.interval_of_check test 512 32 (by decide +kernel)
theorem checked_00544 : FiniteChecks.Interval test 544 556 :=
  FiniteChecks.interval_of_check test 544 12 (by decide +kernel)
theorem part_001 : FiniteChecks.Interval test 512 556 :=
  (FiniteChecks.interval_append test 512 544 556
  checked_00512
  checked_00544)
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed019.Validity
