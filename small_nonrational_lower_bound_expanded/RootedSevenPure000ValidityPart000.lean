module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public import RootedSevenPure000ValidityTest

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure000.Validity
open Papers.RationalityTen
cert_checked_6 00000 0 32 32
cert_checked_6 00032 32 64 32
cert_checked_6 00064 64 96 32
cert_checked_6 00096 96 128 32
cert_checked_6 00128 128 160 32
cert_checked_6 00160 160 192 32
cert_checked_6 00192 192 224 32
cert_checked_6 00224 224 256 32
cert_checked_6 00256 256 288 32
cert_checked_6 00288 288 320 32
cert_checked_6 00320 320 352 32
cert_checked_6 00352 352 384 32
cert_checked_6 00384 384 416 32
cert_checked_6 00416 416 448 32
cert_checked_6 00448 448 480 32
cert_checked_6 00480 480 512 32
theorem part_000 : FiniteChecks.Interval test 0 512 :=
  (FiniteChecks.interval_append test 0 256 512
  (FiniteChecks.interval_append test 0 128 256
  (FiniteChecks.interval_append test 0 64 128
  (FiniteChecks.interval_append test 0 32 64
  checked_00000
  checked_00032)
  (FiniteChecks.interval_append test 64 96 128
  checked_00064
  checked_00096))
  (FiniteChecks.interval_append test 128 192 256
  (FiniteChecks.interval_append test 128 160 192
  checked_00128
  checked_00160)
  (FiniteChecks.interval_append test 192 224 256
  checked_00192
  checked_00224)))
  (FiniteChecks.interval_append test 256 384 512
  (FiniteChecks.interval_append test 256 320 384
  (FiniteChecks.interval_append test 256 288 320
  checked_00256
  checked_00288)
  (FiniteChecks.interval_append test 320 352 384
  checked_00320
  checked_00352))
  (FiniteChecks.interval_append test 384 448 512
  (FiniteChecks.interval_append test 384 416 448
  checked_00384
  checked_00416)
  (FiniteChecks.interval_append test 448 480 512
  checked_00448
  checked_00480))))
end Papers.RationalityTen.FacetUniverses.RootedSevenPure000.Validity
