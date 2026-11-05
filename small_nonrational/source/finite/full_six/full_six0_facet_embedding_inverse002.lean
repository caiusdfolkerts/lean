module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_004096 : Interval inverseTest 4096 4224 :=
  interval_of_check inverseTest 4096 128 (by decide +kernel)

theorem inverse_004224 : Interval inverseTest 4224 4352 :=
  interval_of_check inverseTest 4224 128 (by decide +kernel)

theorem inverse_004352 : Interval inverseTest 4352 4480 :=
  interval_of_check inverseTest 4352 128 (by decide +kernel)

theorem inverse_004480 : Interval inverseTest 4480 4608 :=
  interval_of_check inverseTest 4480 128 (by decide +kernel)

theorem inverse_004608 : Interval inverseTest 4608 4736 :=
  interval_of_check inverseTest 4608 128 (by decide +kernel)

theorem inverse_004736 : Interval inverseTest 4736 4864 :=
  interval_of_check inverseTest 4736 128 (by decide +kernel)

theorem inverse_004864 : Interval inverseTest 4864 4992 :=
  interval_of_check inverseTest 4864 128 (by decide +kernel)

theorem inverse_004992 : Interval inverseTest 4992 5120 :=
  interval_of_check inverseTest 4992 128 (by decide +kernel)

theorem inverse_005120 : Interval inverseTest 5120 5248 :=
  interval_of_check inverseTest 5120 128 (by decide +kernel)

theorem inverse_005248 : Interval inverseTest 5248 5376 :=
  interval_of_check inverseTest 5248 128 (by decide +kernel)

theorem inverse_005376 : Interval inverseTest 5376 5504 :=
  interval_of_check inverseTest 5376 128 (by decide +kernel)

theorem inverse_005504 : Interval inverseTest 5504 5632 :=
  interval_of_check inverseTest 5504 128 (by decide +kernel)

theorem inverse_005632 : Interval inverseTest 5632 5760 :=
  interval_of_check inverseTest 5632 128 (by decide +kernel)

theorem inverse_005760 : Interval inverseTest 5760 5888 :=
  interval_of_check inverseTest 5760 128 (by decide +kernel)

theorem inverse_005888 : Interval inverseTest 5888 6016 :=
  interval_of_check inverseTest 5888 128 (by decide +kernel)

theorem inverse_006016 : Interval inverseTest 6016 6144 :=
  interval_of_check inverseTest 6016 128 (by decide +kernel)

theorem inverse_join_004096_004352 : Interval inverseTest 4096 4352 :=
  interval_append inverseTest 4096 4224 4352 inverse_004096 inverse_004224

theorem inverse_join_004352_004608 : Interval inverseTest 4352 4608 :=
  interval_append inverseTest 4352 4480 4608 inverse_004352 inverse_004480

theorem inverse_join_004096_004608 : Interval inverseTest 4096 4608 :=
  interval_append inverseTest 4096 4352 4608 inverse_join_004096_004352 inverse_join_004352_004608

theorem inverse_join_004608_004864 : Interval inverseTest 4608 4864 :=
  interval_append inverseTest 4608 4736 4864 inverse_004608 inverse_004736

theorem inverse_join_004864_005120 : Interval inverseTest 4864 5120 :=
  interval_append inverseTest 4864 4992 5120 inverse_004864 inverse_004992

theorem inverse_join_004608_005120 : Interval inverseTest 4608 5120 :=
  interval_append inverseTest 4608 4864 5120 inverse_join_004608_004864 inverse_join_004864_005120

theorem inverse_join_004096_005120 : Interval inverseTest 4096 5120 :=
  interval_append inverseTest 4096 4608 5120 inverse_join_004096_004608 inverse_join_004608_005120

theorem inverse_join_005120_005376 : Interval inverseTest 5120 5376 :=
  interval_append inverseTest 5120 5248 5376 inverse_005120 inverse_005248

theorem inverse_join_005376_005632 : Interval inverseTest 5376 5632 :=
  interval_append inverseTest 5376 5504 5632 inverse_005376 inverse_005504

theorem inverse_join_005120_005632 : Interval inverseTest 5120 5632 :=
  interval_append inverseTest 5120 5376 5632 inverse_join_005120_005376 inverse_join_005376_005632

theorem inverse_join_005632_005888 : Interval inverseTest 5632 5888 :=
  interval_append inverseTest 5632 5760 5888 inverse_005632 inverse_005760

theorem inverse_join_005888_006144 : Interval inverseTest 5888 6144 :=
  interval_append inverseTest 5888 6016 6144 inverse_005888 inverse_006016

theorem inverse_join_005632_006144 : Interval inverseTest 5632 6144 :=
  interval_append inverseTest 5632 5888 6144 inverse_join_005632_005888 inverse_join_005888_006144

theorem inverse_join_005120_006144 : Interval inverseTest 5120 6144 :=
  interval_append inverseTest 5120 5632 6144 inverse_join_005120_005632 inverse_join_005632_006144

theorem inverse_join_004096_006144 : Interval inverseTest 4096 6144 :=
  interval_append inverseTest 4096 5120 6144 inverse_join_004096_005120 inverse_join_005120_006144

theorem inverse_part_002 : Interval inverseTest 4096 6144 := inverse_join_004096_006144
end Papers.RationalityTen.FullSix0FacetEmbedding
