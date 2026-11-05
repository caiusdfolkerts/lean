module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_028672 : Interval inverseTest 28672 28800 :=
  interval_of_check inverseTest 28672 128 (by decide +kernel)

theorem inverse_028800 : Interval inverseTest 28800 28928 :=
  interval_of_check inverseTest 28800 128 (by decide +kernel)

theorem inverse_028928 : Interval inverseTest 28928 29056 :=
  interval_of_check inverseTest 28928 128 (by decide +kernel)

theorem inverse_029056 : Interval inverseTest 29056 29184 :=
  interval_of_check inverseTest 29056 128 (by decide +kernel)

theorem inverse_029184 : Interval inverseTest 29184 29312 :=
  interval_of_check inverseTest 29184 128 (by decide +kernel)

theorem inverse_029312 : Interval inverseTest 29312 29440 :=
  interval_of_check inverseTest 29312 128 (by decide +kernel)

theorem inverse_029440 : Interval inverseTest 29440 29568 :=
  interval_of_check inverseTest 29440 128 (by decide +kernel)

theorem inverse_029568 : Interval inverseTest 29568 29696 :=
  interval_of_check inverseTest 29568 128 (by decide +kernel)

theorem inverse_029696 : Interval inverseTest 29696 29824 :=
  interval_of_check inverseTest 29696 128 (by decide +kernel)

theorem inverse_029824 : Interval inverseTest 29824 29952 :=
  interval_of_check inverseTest 29824 128 (by decide +kernel)

theorem inverse_029952 : Interval inverseTest 29952 30080 :=
  interval_of_check inverseTest 29952 128 (by decide +kernel)

theorem inverse_030080 : Interval inverseTest 30080 30208 :=
  interval_of_check inverseTest 30080 128 (by decide +kernel)

theorem inverse_030208 : Interval inverseTest 30208 30336 :=
  interval_of_check inverseTest 30208 128 (by decide +kernel)

theorem inverse_030336 : Interval inverseTest 30336 30464 :=
  interval_of_check inverseTest 30336 128 (by decide +kernel)

theorem inverse_030464 : Interval inverseTest 30464 30592 :=
  interval_of_check inverseTest 30464 128 (by decide +kernel)

theorem inverse_030592 : Interval inverseTest 30592 30720 :=
  interval_of_check inverseTest 30592 128 (by decide +kernel)

theorem inverse_join_028672_028928 : Interval inverseTest 28672 28928 :=
  interval_append inverseTest 28672 28800 28928 inverse_028672 inverse_028800

theorem inverse_join_028928_029184 : Interval inverseTest 28928 29184 :=
  interval_append inverseTest 28928 29056 29184 inverse_028928 inverse_029056

theorem inverse_join_028672_029184 : Interval inverseTest 28672 29184 :=
  interval_append inverseTest 28672 28928 29184 inverse_join_028672_028928 inverse_join_028928_029184

theorem inverse_join_029184_029440 : Interval inverseTest 29184 29440 :=
  interval_append inverseTest 29184 29312 29440 inverse_029184 inverse_029312

theorem inverse_join_029440_029696 : Interval inverseTest 29440 29696 :=
  interval_append inverseTest 29440 29568 29696 inverse_029440 inverse_029568

theorem inverse_join_029184_029696 : Interval inverseTest 29184 29696 :=
  interval_append inverseTest 29184 29440 29696 inverse_join_029184_029440 inverse_join_029440_029696

theorem inverse_join_028672_029696 : Interval inverseTest 28672 29696 :=
  interval_append inverseTest 28672 29184 29696 inverse_join_028672_029184 inverse_join_029184_029696

theorem inverse_join_029696_029952 : Interval inverseTest 29696 29952 :=
  interval_append inverseTest 29696 29824 29952 inverse_029696 inverse_029824

theorem inverse_join_029952_030208 : Interval inverseTest 29952 30208 :=
  interval_append inverseTest 29952 30080 30208 inverse_029952 inverse_030080

theorem inverse_join_029696_030208 : Interval inverseTest 29696 30208 :=
  interval_append inverseTest 29696 29952 30208 inverse_join_029696_029952 inverse_join_029952_030208

theorem inverse_join_030208_030464 : Interval inverseTest 30208 30464 :=
  interval_append inverseTest 30208 30336 30464 inverse_030208 inverse_030336

theorem inverse_join_030464_030720 : Interval inverseTest 30464 30720 :=
  interval_append inverseTest 30464 30592 30720 inverse_030464 inverse_030592

theorem inverse_join_030208_030720 : Interval inverseTest 30208 30720 :=
  interval_append inverseTest 30208 30464 30720 inverse_join_030208_030464 inverse_join_030464_030720

theorem inverse_join_029696_030720 : Interval inverseTest 29696 30720 :=
  interval_append inverseTest 29696 30208 30720 inverse_join_029696_030208 inverse_join_030208_030720

theorem inverse_join_028672_030720 : Interval inverseTest 28672 30720 :=
  interval_append inverseTest 28672 29696 30720 inverse_join_028672_029696 inverse_join_029696_030720

theorem inverse_part_014 : Interval inverseTest 28672 30720 := inverse_join_028672_030720
end Papers.RationalityTen.FullSix0FacetEmbedding
