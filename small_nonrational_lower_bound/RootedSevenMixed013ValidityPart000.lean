module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed013ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenMixed013.Validity
open Papers.RationalityTen
cert_checked_4 00000 0 32 32
cert_checked_4 00032 32 64 32
cert_checked_4 00064 64 96 32
cert_checked_4 00096 96 128 32
cert_checked_4 00128 128 160 32
cert_checked_4 00160 160 192 32
cert_checked_4 00192 192 224 32
cert_checked_4 00224 224 256 32
cert_checked_4 00256 256 288 32
cert_checked_4 00288 288 320 32
cert_checked_4 00320 320 352 32
cert_checked_4 00352 352 384 32
cert_checked_4 00384 384 416 32
cert_checked_4 00416 416 448 32
cert_checked_4 00448 448 466 18
theorem part_000 : FiniteChecks.Interval test 0 466 :=
  (FiniteChecks.interval_append test 0 224 466
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
  (FiniteChecks.interval_append test 224 352 466
  (FiniteChecks.interval_append test 224 288 352
  (FiniteChecks.interval_append test 224 256 288
  checked_00224
  checked_00256)
  (FiniteChecks.interval_append test 288 320 352
  checked_00288
  checked_00320))
  (FiniteChecks.interval_append test 352 416 466
  (FiniteChecks.interval_append test 352 384 416
  checked_00352
  checked_00384)
  (FiniteChecks.interval_append test 416 448 466
  checked_00416
  checked_00448))))
end Papers.RationalityTen.FacetUniverses.RootedSevenMixed013.Validity
