module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_008192 : Interval inverseTest 8192 8320 :=
  interval_of_check inverseTest 8192 128 (by decide +kernel)

theorem inverse_008320 : Interval inverseTest 8320 8448 :=
  interval_of_check inverseTest 8320 128 (by decide +kernel)

theorem inverse_008448 : Interval inverseTest 8448 8576 :=
  interval_of_check inverseTest 8448 128 (by decide +kernel)

theorem inverse_008576 : Interval inverseTest 8576 8704 :=
  interval_of_check inverseTest 8576 128 (by decide +kernel)

theorem inverse_008704 : Interval inverseTest 8704 8832 :=
  interval_of_check inverseTest 8704 128 (by decide +kernel)

theorem inverse_008832 : Interval inverseTest 8832 8960 :=
  interval_of_check inverseTest 8832 128 (by decide +kernel)

theorem inverse_008960 : Interval inverseTest 8960 9088 :=
  interval_of_check inverseTest 8960 128 (by decide +kernel)

theorem inverse_009088 : Interval inverseTest 9088 9216 :=
  interval_of_check inverseTest 9088 128 (by decide +kernel)

theorem inverse_009216 : Interval inverseTest 9216 9344 :=
  interval_of_check inverseTest 9216 128 (by decide +kernel)

theorem inverse_009344 : Interval inverseTest 9344 9472 :=
  interval_of_check inverseTest 9344 128 (by decide +kernel)

theorem inverse_009472 : Interval inverseTest 9472 9600 :=
  interval_of_check inverseTest 9472 128 (by decide +kernel)

theorem inverse_009600 : Interval inverseTest 9600 9728 :=
  interval_of_check inverseTest 9600 128 (by decide +kernel)

theorem inverse_009728 : Interval inverseTest 9728 9856 :=
  interval_of_check inverseTest 9728 128 (by decide +kernel)

theorem inverse_009856 : Interval inverseTest 9856 9984 :=
  interval_of_check inverseTest 9856 128 (by decide +kernel)

theorem inverse_009984 : Interval inverseTest 9984 10112 :=
  interval_of_check inverseTest 9984 128 (by decide +kernel)

theorem inverse_010112 : Interval inverseTest 10112 10240 :=
  interval_of_check inverseTest 10112 128 (by decide +kernel)

theorem inverse_join_008192_008448 : Interval inverseTest 8192 8448 :=
  interval_append inverseTest 8192 8320 8448 inverse_008192 inverse_008320

theorem inverse_join_008448_008704 : Interval inverseTest 8448 8704 :=
  interval_append inverseTest 8448 8576 8704 inverse_008448 inverse_008576

theorem inverse_join_008192_008704 : Interval inverseTest 8192 8704 :=
  interval_append inverseTest 8192 8448 8704 inverse_join_008192_008448 inverse_join_008448_008704

theorem inverse_join_008704_008960 : Interval inverseTest 8704 8960 :=
  interval_append inverseTest 8704 8832 8960 inverse_008704 inverse_008832

theorem inverse_join_008960_009216 : Interval inverseTest 8960 9216 :=
  interval_append inverseTest 8960 9088 9216 inverse_008960 inverse_009088

theorem inverse_join_008704_009216 : Interval inverseTest 8704 9216 :=
  interval_append inverseTest 8704 8960 9216 inverse_join_008704_008960 inverse_join_008960_009216

theorem inverse_join_008192_009216 : Interval inverseTest 8192 9216 :=
  interval_append inverseTest 8192 8704 9216 inverse_join_008192_008704 inverse_join_008704_009216

theorem inverse_join_009216_009472 : Interval inverseTest 9216 9472 :=
  interval_append inverseTest 9216 9344 9472 inverse_009216 inverse_009344

theorem inverse_join_009472_009728 : Interval inverseTest 9472 9728 :=
  interval_append inverseTest 9472 9600 9728 inverse_009472 inverse_009600

theorem inverse_join_009216_009728 : Interval inverseTest 9216 9728 :=
  interval_append inverseTest 9216 9472 9728 inverse_join_009216_009472 inverse_join_009472_009728

theorem inverse_join_009728_009984 : Interval inverseTest 9728 9984 :=
  interval_append inverseTest 9728 9856 9984 inverse_009728 inverse_009856

theorem inverse_join_009984_010240 : Interval inverseTest 9984 10240 :=
  interval_append inverseTest 9984 10112 10240 inverse_009984 inverse_010112

theorem inverse_join_009728_010240 : Interval inverseTest 9728 10240 :=
  interval_append inverseTest 9728 9984 10240 inverse_join_009728_009984 inverse_join_009984_010240

theorem inverse_join_009216_010240 : Interval inverseTest 9216 10240 :=
  interval_append inverseTest 9216 9728 10240 inverse_join_009216_009728 inverse_join_009728_010240

theorem inverse_join_008192_010240 : Interval inverseTest 8192 10240 :=
  interval_append inverseTest 8192 9216 10240 inverse_join_008192_009216 inverse_join_009216_010240

theorem inverse_part_004 : Interval inverseTest 8192 10240 := inverse_join_008192_010240
end Papers.RationalityTen.FullSix0FacetEmbedding
