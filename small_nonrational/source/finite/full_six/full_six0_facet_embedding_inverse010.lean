module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_020480 : Interval inverseTest 20480 20608 :=
  interval_of_check inverseTest 20480 128 (by decide +kernel)

theorem inverse_020608 : Interval inverseTest 20608 20736 :=
  interval_of_check inverseTest 20608 128 (by decide +kernel)

theorem inverse_020736 : Interval inverseTest 20736 20864 :=
  interval_of_check inverseTest 20736 128 (by decide +kernel)

theorem inverse_020864 : Interval inverseTest 20864 20992 :=
  interval_of_check inverseTest 20864 128 (by decide +kernel)

theorem inverse_020992 : Interval inverseTest 20992 21120 :=
  interval_of_check inverseTest 20992 128 (by decide +kernel)

theorem inverse_021120 : Interval inverseTest 21120 21248 :=
  interval_of_check inverseTest 21120 128 (by decide +kernel)

theorem inverse_021248 : Interval inverseTest 21248 21376 :=
  interval_of_check inverseTest 21248 128 (by decide +kernel)

theorem inverse_021376 : Interval inverseTest 21376 21504 :=
  interval_of_check inverseTest 21376 128 (by decide +kernel)

theorem inverse_021504 : Interval inverseTest 21504 21632 :=
  interval_of_check inverseTest 21504 128 (by decide +kernel)

theorem inverse_021632 : Interval inverseTest 21632 21760 :=
  interval_of_check inverseTest 21632 128 (by decide +kernel)

theorem inverse_021760 : Interval inverseTest 21760 21888 :=
  interval_of_check inverseTest 21760 128 (by decide +kernel)

theorem inverse_021888 : Interval inverseTest 21888 22016 :=
  interval_of_check inverseTest 21888 128 (by decide +kernel)

theorem inverse_022016 : Interval inverseTest 22016 22144 :=
  interval_of_check inverseTest 22016 128 (by decide +kernel)

theorem inverse_022144 : Interval inverseTest 22144 22272 :=
  interval_of_check inverseTest 22144 128 (by decide +kernel)

theorem inverse_022272 : Interval inverseTest 22272 22400 :=
  interval_of_check inverseTest 22272 128 (by decide +kernel)

theorem inverse_022400 : Interval inverseTest 22400 22528 :=
  interval_of_check inverseTest 22400 128 (by decide +kernel)

theorem inverse_join_020480_020736 : Interval inverseTest 20480 20736 :=
  interval_append inverseTest 20480 20608 20736 inverse_020480 inverse_020608

theorem inverse_join_020736_020992 : Interval inverseTest 20736 20992 :=
  interval_append inverseTest 20736 20864 20992 inverse_020736 inverse_020864

theorem inverse_join_020480_020992 : Interval inverseTest 20480 20992 :=
  interval_append inverseTest 20480 20736 20992 inverse_join_020480_020736 inverse_join_020736_020992

theorem inverse_join_020992_021248 : Interval inverseTest 20992 21248 :=
  interval_append inverseTest 20992 21120 21248 inverse_020992 inverse_021120

theorem inverse_join_021248_021504 : Interval inverseTest 21248 21504 :=
  interval_append inverseTest 21248 21376 21504 inverse_021248 inverse_021376

theorem inverse_join_020992_021504 : Interval inverseTest 20992 21504 :=
  interval_append inverseTest 20992 21248 21504 inverse_join_020992_021248 inverse_join_021248_021504

theorem inverse_join_020480_021504 : Interval inverseTest 20480 21504 :=
  interval_append inverseTest 20480 20992 21504 inverse_join_020480_020992 inverse_join_020992_021504

theorem inverse_join_021504_021760 : Interval inverseTest 21504 21760 :=
  interval_append inverseTest 21504 21632 21760 inverse_021504 inverse_021632

theorem inverse_join_021760_022016 : Interval inverseTest 21760 22016 :=
  interval_append inverseTest 21760 21888 22016 inverse_021760 inverse_021888

theorem inverse_join_021504_022016 : Interval inverseTest 21504 22016 :=
  interval_append inverseTest 21504 21760 22016 inverse_join_021504_021760 inverse_join_021760_022016

theorem inverse_join_022016_022272 : Interval inverseTest 22016 22272 :=
  interval_append inverseTest 22016 22144 22272 inverse_022016 inverse_022144

theorem inverse_join_022272_022528 : Interval inverseTest 22272 22528 :=
  interval_append inverseTest 22272 22400 22528 inverse_022272 inverse_022400

theorem inverse_join_022016_022528 : Interval inverseTest 22016 22528 :=
  interval_append inverseTest 22016 22272 22528 inverse_join_022016_022272 inverse_join_022272_022528

theorem inverse_join_021504_022528 : Interval inverseTest 21504 22528 :=
  interval_append inverseTest 21504 22016 22528 inverse_join_021504_022016 inverse_join_022016_022528

theorem inverse_join_020480_022528 : Interval inverseTest 20480 22528 :=
  interval_append inverseTest 20480 21504 22528 inverse_join_020480_021504 inverse_join_021504_022528

theorem inverse_part_010 : Interval inverseTest 20480 22528 := inverse_join_020480_022528
end Papers.RationalityTen.FullSix0FacetEmbedding
