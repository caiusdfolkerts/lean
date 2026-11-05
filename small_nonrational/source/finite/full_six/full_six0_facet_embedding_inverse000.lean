module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_000000 : Interval inverseTest 0 128 :=
  interval_of_check inverseTest 0 128 (by decide +kernel)

theorem inverse_000128 : Interval inverseTest 128 256 :=
  interval_of_check inverseTest 128 128 (by decide +kernel)

theorem inverse_000256 : Interval inverseTest 256 384 :=
  interval_of_check inverseTest 256 128 (by decide +kernel)

theorem inverse_000384 : Interval inverseTest 384 512 :=
  interval_of_check inverseTest 384 128 (by decide +kernel)

theorem inverse_000512 : Interval inverseTest 512 640 :=
  interval_of_check inverseTest 512 128 (by decide +kernel)

theorem inverse_000640 : Interval inverseTest 640 768 :=
  interval_of_check inverseTest 640 128 (by decide +kernel)

theorem inverse_000768 : Interval inverseTest 768 896 :=
  interval_of_check inverseTest 768 128 (by decide +kernel)

theorem inverse_000896 : Interval inverseTest 896 1024 :=
  interval_of_check inverseTest 896 128 (by decide +kernel)

theorem inverse_001024 : Interval inverseTest 1024 1152 :=
  interval_of_check inverseTest 1024 128 (by decide +kernel)

theorem inverse_001152 : Interval inverseTest 1152 1280 :=
  interval_of_check inverseTest 1152 128 (by decide +kernel)

theorem inverse_001280 : Interval inverseTest 1280 1408 :=
  interval_of_check inverseTest 1280 128 (by decide +kernel)

theorem inverse_001408 : Interval inverseTest 1408 1536 :=
  interval_of_check inverseTest 1408 128 (by decide +kernel)

theorem inverse_001536 : Interval inverseTest 1536 1664 :=
  interval_of_check inverseTest 1536 128 (by decide +kernel)

theorem inverse_001664 : Interval inverseTest 1664 1792 :=
  interval_of_check inverseTest 1664 128 (by decide +kernel)

theorem inverse_001792 : Interval inverseTest 1792 1920 :=
  interval_of_check inverseTest 1792 128 (by decide +kernel)

theorem inverse_001920 : Interval inverseTest 1920 2048 :=
  interval_of_check inverseTest 1920 128 (by decide +kernel)

theorem inverse_join_000000_000256 : Interval inverseTest 0 256 :=
  interval_append inverseTest 0 128 256 inverse_000000 inverse_000128

theorem inverse_join_000256_000512 : Interval inverseTest 256 512 :=
  interval_append inverseTest 256 384 512 inverse_000256 inverse_000384

theorem inverse_join_000000_000512 : Interval inverseTest 0 512 :=
  interval_append inverseTest 0 256 512 inverse_join_000000_000256 inverse_join_000256_000512

theorem inverse_join_000512_000768 : Interval inverseTest 512 768 :=
  interval_append inverseTest 512 640 768 inverse_000512 inverse_000640

theorem inverse_join_000768_001024 : Interval inverseTest 768 1024 :=
  interval_append inverseTest 768 896 1024 inverse_000768 inverse_000896

theorem inverse_join_000512_001024 : Interval inverseTest 512 1024 :=
  interval_append inverseTest 512 768 1024 inverse_join_000512_000768 inverse_join_000768_001024

theorem inverse_join_000000_001024 : Interval inverseTest 0 1024 :=
  interval_append inverseTest 0 512 1024 inverse_join_000000_000512 inverse_join_000512_001024

theorem inverse_join_001024_001280 : Interval inverseTest 1024 1280 :=
  interval_append inverseTest 1024 1152 1280 inverse_001024 inverse_001152

theorem inverse_join_001280_001536 : Interval inverseTest 1280 1536 :=
  interval_append inverseTest 1280 1408 1536 inverse_001280 inverse_001408

theorem inverse_join_001024_001536 : Interval inverseTest 1024 1536 :=
  interval_append inverseTest 1024 1280 1536 inverse_join_001024_001280 inverse_join_001280_001536

theorem inverse_join_001536_001792 : Interval inverseTest 1536 1792 :=
  interval_append inverseTest 1536 1664 1792 inverse_001536 inverse_001664

theorem inverse_join_001792_002048 : Interval inverseTest 1792 2048 :=
  interval_append inverseTest 1792 1920 2048 inverse_001792 inverse_001920

theorem inverse_join_001536_002048 : Interval inverseTest 1536 2048 :=
  interval_append inverseTest 1536 1792 2048 inverse_join_001536_001792 inverse_join_001792_002048

theorem inverse_join_001024_002048 : Interval inverseTest 1024 2048 :=
  interval_append inverseTest 1024 1536 2048 inverse_join_001024_001536 inverse_join_001536_002048

theorem inverse_join_000000_002048 : Interval inverseTest 0 2048 :=
  interval_append inverseTest 0 1024 2048 inverse_join_000000_001024 inverse_join_001024_002048

theorem inverse_part_000 : Interval inverseTest 0 2048 := inverse_join_000000_002048
end Papers.RationalityTen.FullSix0FacetEmbedding
