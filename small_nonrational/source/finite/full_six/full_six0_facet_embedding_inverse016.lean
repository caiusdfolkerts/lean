module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_032768 : Interval inverseTest 32768 32896 :=
  interval_of_check inverseTest 32768 128 (by decide +kernel)

theorem inverse_032896 : Interval inverseTest 32896 33024 :=
  interval_of_check inverseTest 32896 128 (by decide +kernel)

theorem inverse_033024 : Interval inverseTest 33024 33152 :=
  interval_of_check inverseTest 33024 128 (by decide +kernel)

theorem inverse_033152 : Interval inverseTest 33152 33280 :=
  interval_of_check inverseTest 33152 128 (by decide +kernel)

theorem inverse_033280 : Interval inverseTest 33280 33408 :=
  interval_of_check inverseTest 33280 128 (by decide +kernel)

theorem inverse_033408 : Interval inverseTest 33408 33536 :=
  interval_of_check inverseTest 33408 128 (by decide +kernel)

theorem inverse_033536 : Interval inverseTest 33536 33664 :=
  interval_of_check inverseTest 33536 128 (by decide +kernel)

theorem inverse_033664 : Interval inverseTest 33664 33792 :=
  interval_of_check inverseTest 33664 128 (by decide +kernel)

theorem inverse_033792 : Interval inverseTest 33792 33920 :=
  interval_of_check inverseTest 33792 128 (by decide +kernel)

theorem inverse_033920 : Interval inverseTest 33920 34048 :=
  interval_of_check inverseTest 33920 128 (by decide +kernel)

theorem inverse_034048 : Interval inverseTest 34048 34176 :=
  interval_of_check inverseTest 34048 128 (by decide +kernel)

theorem inverse_034176 : Interval inverseTest 34176 34304 :=
  interval_of_check inverseTest 34176 128 (by decide +kernel)

theorem inverse_034304 : Interval inverseTest 34304 34432 :=
  interval_of_check inverseTest 34304 128 (by decide +kernel)

theorem inverse_034432 : Interval inverseTest 34432 34560 :=
  interval_of_check inverseTest 34432 128 (by decide +kernel)

theorem inverse_034560 : Interval inverseTest 34560 34688 :=
  interval_of_check inverseTest 34560 128 (by decide +kernel)

theorem inverse_034688 : Interval inverseTest 34688 34816 :=
  interval_of_check inverseTest 34688 128 (by decide +kernel)

theorem inverse_join_032768_033024 : Interval inverseTest 32768 33024 :=
  interval_append inverseTest 32768 32896 33024 inverse_032768 inverse_032896

theorem inverse_join_033024_033280 : Interval inverseTest 33024 33280 :=
  interval_append inverseTest 33024 33152 33280 inverse_033024 inverse_033152

theorem inverse_join_032768_033280 : Interval inverseTest 32768 33280 :=
  interval_append inverseTest 32768 33024 33280 inverse_join_032768_033024 inverse_join_033024_033280

theorem inverse_join_033280_033536 : Interval inverseTest 33280 33536 :=
  interval_append inverseTest 33280 33408 33536 inverse_033280 inverse_033408

theorem inverse_join_033536_033792 : Interval inverseTest 33536 33792 :=
  interval_append inverseTest 33536 33664 33792 inverse_033536 inverse_033664

theorem inverse_join_033280_033792 : Interval inverseTest 33280 33792 :=
  interval_append inverseTest 33280 33536 33792 inverse_join_033280_033536 inverse_join_033536_033792

theorem inverse_join_032768_033792 : Interval inverseTest 32768 33792 :=
  interval_append inverseTest 32768 33280 33792 inverse_join_032768_033280 inverse_join_033280_033792

theorem inverse_join_033792_034048 : Interval inverseTest 33792 34048 :=
  interval_append inverseTest 33792 33920 34048 inverse_033792 inverse_033920

theorem inverse_join_034048_034304 : Interval inverseTest 34048 34304 :=
  interval_append inverseTest 34048 34176 34304 inverse_034048 inverse_034176

theorem inverse_join_033792_034304 : Interval inverseTest 33792 34304 :=
  interval_append inverseTest 33792 34048 34304 inverse_join_033792_034048 inverse_join_034048_034304

theorem inverse_join_034304_034560 : Interval inverseTest 34304 34560 :=
  interval_append inverseTest 34304 34432 34560 inverse_034304 inverse_034432

theorem inverse_join_034560_034816 : Interval inverseTest 34560 34816 :=
  interval_append inverseTest 34560 34688 34816 inverse_034560 inverse_034688

theorem inverse_join_034304_034816 : Interval inverseTest 34304 34816 :=
  interval_append inverseTest 34304 34560 34816 inverse_join_034304_034560 inverse_join_034560_034816

theorem inverse_join_033792_034816 : Interval inverseTest 33792 34816 :=
  interval_append inverseTest 33792 34304 34816 inverse_join_033792_034304 inverse_join_034304_034816

theorem inverse_join_032768_034816 : Interval inverseTest 32768 34816 :=
  interval_append inverseTest 32768 33792 34816 inverse_join_032768_033792 inverse_join_033792_034816

theorem inverse_part_016 : Interval inverseTest 32768 34816 := inverse_join_032768_034816
end Papers.RationalityTen.FullSix0FacetEmbedding
