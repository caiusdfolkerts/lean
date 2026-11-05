module
prelude
public import RootedSevenMixed010ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed010.Validity
open Papers.RationalityTen
theorem checked_00000 : FiniteChecks.Interval test 0 32 :=
  FiniteChecks.interval_of_check test 0 32 (by decide +kernel)
theorem checked_00032 : FiniteChecks.Interval test 32 64 :=
  FiniteChecks.interval_of_check test 32 32 (by decide +kernel)
theorem checked_00064 : FiniteChecks.Interval test 64 96 :=
  FiniteChecks.interval_of_check test 64 32 (by decide +kernel)
theorem checked_00096 : FiniteChecks.Interval test 96 128 :=
  FiniteChecks.interval_of_check test 96 32 (by decide +kernel)
theorem checked_00128 : FiniteChecks.Interval test 128 160 :=
  FiniteChecks.interval_of_check test 128 32 (by decide +kernel)
theorem checked_00160 : FiniteChecks.Interval test 160 192 :=
  FiniteChecks.interval_of_check test 160 32 (by decide +kernel)
theorem checked_00192 : FiniteChecks.Interval test 192 224 :=
  FiniteChecks.interval_of_check test 192 32 (by decide +kernel)
theorem checked_00224 : FiniteChecks.Interval test 224 256 :=
  FiniteChecks.interval_of_check test 224 32 (by decide +kernel)
theorem checked_00256 : FiniteChecks.Interval test 256 288 :=
  FiniteChecks.interval_of_check test 256 32 (by decide +kernel)
theorem checked_00288 : FiniteChecks.Interval test 288 320 :=
  FiniteChecks.interval_of_check test 288 32 (by decide +kernel)
theorem checked_00320 : FiniteChecks.Interval test 320 352 :=
  FiniteChecks.interval_of_check test 320 32 (by decide +kernel)
theorem checked_00352 : FiniteChecks.Interval test 352 384 :=
  FiniteChecks.interval_of_check test 352 32 (by decide +kernel)
theorem checked_00384 : FiniteChecks.Interval test 384 416 :=
  FiniteChecks.interval_of_check test 384 32 (by decide +kernel)
theorem checked_00416 : FiniteChecks.Interval test 416 430 :=
  FiniteChecks.interval_of_check test 416 14 (by decide +kernel)
theorem part_000 : FiniteChecks.Interval test 0 430 :=
  (FiniteChecks.interval_append test 0 224 430
  (FiniteChecks.interval_append test 0 96 224
  (FiniteChecks.interval_append test 0 32 96
  checked_00000
  (FiniteChecks.interval_append test 32 64 96
  checked_00032
  checked_00064))
  (FiniteChecks.interval_append test 96 160 224
  (FiniteChecks.interval_append test 96 128 160
  checked_00096
  checked_00128)
  (FiniteChecks.interval_append test 160 192 224
  checked_00160
  checked_00192)))
  (FiniteChecks.interval_append test 224 320 430
  (FiniteChecks.interval_append test 224 256 320
  checked_00224
  (FiniteChecks.interval_append test 256 288 320
  checked_00256
  checked_00288))
  (FiniteChecks.interval_append test 320 384 430
  (FiniteChecks.interval_append test 320 352 384
  checked_00320
  checked_00352)
  (FiniteChecks.interval_append test 384 416 430
  checked_00384
  checked_00416))))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed010.Validity
