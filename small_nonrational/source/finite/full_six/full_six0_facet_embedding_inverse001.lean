module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_002048 : Interval inverseTest 2048 2176 :=
  interval_of_check inverseTest 2048 128 (by decide +kernel)

theorem inverse_002176 : Interval inverseTest 2176 2304 :=
  interval_of_check inverseTest 2176 128 (by decide +kernel)

theorem inverse_002304 : Interval inverseTest 2304 2432 :=
  interval_of_check inverseTest 2304 128 (by decide +kernel)

theorem inverse_002432 : Interval inverseTest 2432 2560 :=
  interval_of_check inverseTest 2432 128 (by decide +kernel)

theorem inverse_002560 : Interval inverseTest 2560 2688 :=
  interval_of_check inverseTest 2560 128 (by decide +kernel)

theorem inverse_002688 : Interval inverseTest 2688 2816 :=
  interval_of_check inverseTest 2688 128 (by decide +kernel)

theorem inverse_002816 : Interval inverseTest 2816 2944 :=
  interval_of_check inverseTest 2816 128 (by decide +kernel)

theorem inverse_002944 : Interval inverseTest 2944 3072 :=
  interval_of_check inverseTest 2944 128 (by decide +kernel)

theorem inverse_003072 : Interval inverseTest 3072 3200 :=
  interval_of_check inverseTest 3072 128 (by decide +kernel)

theorem inverse_003200 : Interval inverseTest 3200 3328 :=
  interval_of_check inverseTest 3200 128 (by decide +kernel)

theorem inverse_003328 : Interval inverseTest 3328 3456 :=
  interval_of_check inverseTest 3328 128 (by decide +kernel)

theorem inverse_003456 : Interval inverseTest 3456 3584 :=
  interval_of_check inverseTest 3456 128 (by decide +kernel)

theorem inverse_003584 : Interval inverseTest 3584 3712 :=
  interval_of_check inverseTest 3584 128 (by decide +kernel)

theorem inverse_003712 : Interval inverseTest 3712 3840 :=
  interval_of_check inverseTest 3712 128 (by decide +kernel)

theorem inverse_003840 : Interval inverseTest 3840 3968 :=
  interval_of_check inverseTest 3840 128 (by decide +kernel)

theorem inverse_003968 : Interval inverseTest 3968 4096 :=
  interval_of_check inverseTest 3968 128 (by decide +kernel)

theorem inverse_join_002048_002304 : Interval inverseTest 2048 2304 :=
  interval_append inverseTest 2048 2176 2304 inverse_002048 inverse_002176

theorem inverse_join_002304_002560 : Interval inverseTest 2304 2560 :=
  interval_append inverseTest 2304 2432 2560 inverse_002304 inverse_002432

theorem inverse_join_002048_002560 : Interval inverseTest 2048 2560 :=
  interval_append inverseTest 2048 2304 2560 inverse_join_002048_002304 inverse_join_002304_002560

theorem inverse_join_002560_002816 : Interval inverseTest 2560 2816 :=
  interval_append inverseTest 2560 2688 2816 inverse_002560 inverse_002688

theorem inverse_join_002816_003072 : Interval inverseTest 2816 3072 :=
  interval_append inverseTest 2816 2944 3072 inverse_002816 inverse_002944

theorem inverse_join_002560_003072 : Interval inverseTest 2560 3072 :=
  interval_append inverseTest 2560 2816 3072 inverse_join_002560_002816 inverse_join_002816_003072

theorem inverse_join_002048_003072 : Interval inverseTest 2048 3072 :=
  interval_append inverseTest 2048 2560 3072 inverse_join_002048_002560 inverse_join_002560_003072

theorem inverse_join_003072_003328 : Interval inverseTest 3072 3328 :=
  interval_append inverseTest 3072 3200 3328 inverse_003072 inverse_003200

theorem inverse_join_003328_003584 : Interval inverseTest 3328 3584 :=
  interval_append inverseTest 3328 3456 3584 inverse_003328 inverse_003456

theorem inverse_join_003072_003584 : Interval inverseTest 3072 3584 :=
  interval_append inverseTest 3072 3328 3584 inverse_join_003072_003328 inverse_join_003328_003584

theorem inverse_join_003584_003840 : Interval inverseTest 3584 3840 :=
  interval_append inverseTest 3584 3712 3840 inverse_003584 inverse_003712

theorem inverse_join_003840_004096 : Interval inverseTest 3840 4096 :=
  interval_append inverseTest 3840 3968 4096 inverse_003840 inverse_003968

theorem inverse_join_003584_004096 : Interval inverseTest 3584 4096 :=
  interval_append inverseTest 3584 3840 4096 inverse_join_003584_003840 inverse_join_003840_004096

theorem inverse_join_003072_004096 : Interval inverseTest 3072 4096 :=
  interval_append inverseTest 3072 3584 4096 inverse_join_003072_003584 inverse_join_003584_004096

theorem inverse_join_002048_004096 : Interval inverseTest 2048 4096 :=
  interval_append inverseTest 2048 3072 4096 inverse_join_002048_003072 inverse_join_003072_004096

theorem inverse_part_001 : Interval inverseTest 2048 4096 := inverse_join_002048_004096
end Papers.RationalityTen.FullSix0FacetEmbedding
