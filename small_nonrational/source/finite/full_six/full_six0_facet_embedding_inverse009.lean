module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_018432 : Interval inverseTest 18432 18560 :=
  interval_of_check inverseTest 18432 128 (by decide +kernel)

theorem inverse_018560 : Interval inverseTest 18560 18688 :=
  interval_of_check inverseTest 18560 128 (by decide +kernel)

theorem inverse_018688 : Interval inverseTest 18688 18816 :=
  interval_of_check inverseTest 18688 128 (by decide +kernel)

theorem inverse_018816 : Interval inverseTest 18816 18944 :=
  interval_of_check inverseTest 18816 128 (by decide +kernel)

theorem inverse_018944 : Interval inverseTest 18944 19072 :=
  interval_of_check inverseTest 18944 128 (by decide +kernel)

theorem inverse_019072 : Interval inverseTest 19072 19200 :=
  interval_of_check inverseTest 19072 128 (by decide +kernel)

theorem inverse_019200 : Interval inverseTest 19200 19328 :=
  interval_of_check inverseTest 19200 128 (by decide +kernel)

theorem inverse_019328 : Interval inverseTest 19328 19456 :=
  interval_of_check inverseTest 19328 128 (by decide +kernel)

theorem inverse_019456 : Interval inverseTest 19456 19584 :=
  interval_of_check inverseTest 19456 128 (by decide +kernel)

theorem inverse_019584 : Interval inverseTest 19584 19712 :=
  interval_of_check inverseTest 19584 128 (by decide +kernel)

theorem inverse_019712 : Interval inverseTest 19712 19840 :=
  interval_of_check inverseTest 19712 128 (by decide +kernel)

theorem inverse_019840 : Interval inverseTest 19840 19968 :=
  interval_of_check inverseTest 19840 128 (by decide +kernel)

theorem inverse_019968 : Interval inverseTest 19968 20096 :=
  interval_of_check inverseTest 19968 128 (by decide +kernel)

theorem inverse_020096 : Interval inverseTest 20096 20224 :=
  interval_of_check inverseTest 20096 128 (by decide +kernel)

theorem inverse_020224 : Interval inverseTest 20224 20352 :=
  interval_of_check inverseTest 20224 128 (by decide +kernel)

theorem inverse_020352 : Interval inverseTest 20352 20480 :=
  interval_of_check inverseTest 20352 128 (by decide +kernel)

theorem inverse_join_018432_018688 : Interval inverseTest 18432 18688 :=
  interval_append inverseTest 18432 18560 18688 inverse_018432 inverse_018560

theorem inverse_join_018688_018944 : Interval inverseTest 18688 18944 :=
  interval_append inverseTest 18688 18816 18944 inverse_018688 inverse_018816

theorem inverse_join_018432_018944 : Interval inverseTest 18432 18944 :=
  interval_append inverseTest 18432 18688 18944 inverse_join_018432_018688 inverse_join_018688_018944

theorem inverse_join_018944_019200 : Interval inverseTest 18944 19200 :=
  interval_append inverseTest 18944 19072 19200 inverse_018944 inverse_019072

theorem inverse_join_019200_019456 : Interval inverseTest 19200 19456 :=
  interval_append inverseTest 19200 19328 19456 inverse_019200 inverse_019328

theorem inverse_join_018944_019456 : Interval inverseTest 18944 19456 :=
  interval_append inverseTest 18944 19200 19456 inverse_join_018944_019200 inverse_join_019200_019456

theorem inverse_join_018432_019456 : Interval inverseTest 18432 19456 :=
  interval_append inverseTest 18432 18944 19456 inverse_join_018432_018944 inverse_join_018944_019456

theorem inverse_join_019456_019712 : Interval inverseTest 19456 19712 :=
  interval_append inverseTest 19456 19584 19712 inverse_019456 inverse_019584

theorem inverse_join_019712_019968 : Interval inverseTest 19712 19968 :=
  interval_append inverseTest 19712 19840 19968 inverse_019712 inverse_019840

theorem inverse_join_019456_019968 : Interval inverseTest 19456 19968 :=
  interval_append inverseTest 19456 19712 19968 inverse_join_019456_019712 inverse_join_019712_019968

theorem inverse_join_019968_020224 : Interval inverseTest 19968 20224 :=
  interval_append inverseTest 19968 20096 20224 inverse_019968 inverse_020096

theorem inverse_join_020224_020480 : Interval inverseTest 20224 20480 :=
  interval_append inverseTest 20224 20352 20480 inverse_020224 inverse_020352

theorem inverse_join_019968_020480 : Interval inverseTest 19968 20480 :=
  interval_append inverseTest 19968 20224 20480 inverse_join_019968_020224 inverse_join_020224_020480

theorem inverse_join_019456_020480 : Interval inverseTest 19456 20480 :=
  interval_append inverseTest 19456 19968 20480 inverse_join_019456_019968 inverse_join_019968_020480

theorem inverse_join_018432_020480 : Interval inverseTest 18432 20480 :=
  interval_append inverseTest 18432 19456 20480 inverse_join_018432_019456 inverse_join_019456_020480

theorem inverse_part_009 : Interval inverseTest 18432 20480 := inverse_join_018432_020480
end Papers.RationalityTen.FullSix0FacetEmbedding
