module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_036864 : Interval inverseTest 36864 36992 :=
  interval_of_check inverseTest 36864 128 (by decide +kernel)

theorem inverse_036992 : Interval inverseTest 36992 37120 :=
  interval_of_check inverseTest 36992 128 (by decide +kernel)

theorem inverse_037120 : Interval inverseTest 37120 37248 :=
  interval_of_check inverseTest 37120 128 (by decide +kernel)

theorem inverse_037248 : Interval inverseTest 37248 37376 :=
  interval_of_check inverseTest 37248 128 (by decide +kernel)

theorem inverse_037376 : Interval inverseTest 37376 37504 :=
  interval_of_check inverseTest 37376 128 (by decide +kernel)

theorem inverse_037504 : Interval inverseTest 37504 37632 :=
  interval_of_check inverseTest 37504 128 (by decide +kernel)

theorem inverse_037632 : Interval inverseTest 37632 37760 :=
  interval_of_check inverseTest 37632 128 (by decide +kernel)

theorem inverse_037760 : Interval inverseTest 37760 37800 :=
  interval_of_check inverseTest 37760 40 (by decide +kernel)

theorem inverse_join_036864_037120 : Interval inverseTest 36864 37120 :=
  interval_append inverseTest 36864 36992 37120 inverse_036864 inverse_036992

theorem inverse_join_037120_037376 : Interval inverseTest 37120 37376 :=
  interval_append inverseTest 37120 37248 37376 inverse_037120 inverse_037248

theorem inverse_join_036864_037376 : Interval inverseTest 36864 37376 :=
  interval_append inverseTest 36864 37120 37376 inverse_join_036864_037120 inverse_join_037120_037376

theorem inverse_join_037376_037632 : Interval inverseTest 37376 37632 :=
  interval_append inverseTest 37376 37504 37632 inverse_037376 inverse_037504

theorem inverse_join_037632_037800 : Interval inverseTest 37632 37800 :=
  interval_append inverseTest 37632 37760 37800 inverse_037632 inverse_037760

theorem inverse_join_037376_037800 : Interval inverseTest 37376 37800 :=
  interval_append inverseTest 37376 37632 37800 inverse_join_037376_037632 inverse_join_037632_037800

theorem inverse_join_036864_037800 : Interval inverseTest 36864 37800 :=
  interval_append inverseTest 36864 37376 37800 inverse_join_036864_037376 inverse_join_037376_037800

theorem inverse_part_018 : Interval inverseTest 36864 37800 := inverse_join_036864_037800
end Papers.RationalityTen.FullSix0FacetEmbedding
