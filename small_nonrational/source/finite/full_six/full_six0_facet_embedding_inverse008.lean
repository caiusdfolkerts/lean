module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_016384 : Interval inverseTest 16384 16512 :=
  interval_of_check inverseTest 16384 128 (by decide +kernel)

theorem inverse_016512 : Interval inverseTest 16512 16640 :=
  interval_of_check inverseTest 16512 128 (by decide +kernel)

theorem inverse_016640 : Interval inverseTest 16640 16768 :=
  interval_of_check inverseTest 16640 128 (by decide +kernel)

theorem inverse_016768 : Interval inverseTest 16768 16896 :=
  interval_of_check inverseTest 16768 128 (by decide +kernel)

theorem inverse_016896 : Interval inverseTest 16896 17024 :=
  interval_of_check inverseTest 16896 128 (by decide +kernel)

theorem inverse_017024 : Interval inverseTest 17024 17152 :=
  interval_of_check inverseTest 17024 128 (by decide +kernel)

theorem inverse_017152 : Interval inverseTest 17152 17280 :=
  interval_of_check inverseTest 17152 128 (by decide +kernel)

theorem inverse_017280 : Interval inverseTest 17280 17408 :=
  interval_of_check inverseTest 17280 128 (by decide +kernel)

theorem inverse_017408 : Interval inverseTest 17408 17536 :=
  interval_of_check inverseTest 17408 128 (by decide +kernel)

theorem inverse_017536 : Interval inverseTest 17536 17664 :=
  interval_of_check inverseTest 17536 128 (by decide +kernel)

theorem inverse_017664 : Interval inverseTest 17664 17792 :=
  interval_of_check inverseTest 17664 128 (by decide +kernel)

theorem inverse_017792 : Interval inverseTest 17792 17920 :=
  interval_of_check inverseTest 17792 128 (by decide +kernel)

theorem inverse_017920 : Interval inverseTest 17920 18048 :=
  interval_of_check inverseTest 17920 128 (by decide +kernel)

theorem inverse_018048 : Interval inverseTest 18048 18176 :=
  interval_of_check inverseTest 18048 128 (by decide +kernel)

theorem inverse_018176 : Interval inverseTest 18176 18304 :=
  interval_of_check inverseTest 18176 128 (by decide +kernel)

theorem inverse_018304 : Interval inverseTest 18304 18432 :=
  interval_of_check inverseTest 18304 128 (by decide +kernel)

theorem inverse_join_016384_016640 : Interval inverseTest 16384 16640 :=
  interval_append inverseTest 16384 16512 16640 inverse_016384 inverse_016512

theorem inverse_join_016640_016896 : Interval inverseTest 16640 16896 :=
  interval_append inverseTest 16640 16768 16896 inverse_016640 inverse_016768

theorem inverse_join_016384_016896 : Interval inverseTest 16384 16896 :=
  interval_append inverseTest 16384 16640 16896 inverse_join_016384_016640 inverse_join_016640_016896

theorem inverse_join_016896_017152 : Interval inverseTest 16896 17152 :=
  interval_append inverseTest 16896 17024 17152 inverse_016896 inverse_017024

theorem inverse_join_017152_017408 : Interval inverseTest 17152 17408 :=
  interval_append inverseTest 17152 17280 17408 inverse_017152 inverse_017280

theorem inverse_join_016896_017408 : Interval inverseTest 16896 17408 :=
  interval_append inverseTest 16896 17152 17408 inverse_join_016896_017152 inverse_join_017152_017408

theorem inverse_join_016384_017408 : Interval inverseTest 16384 17408 :=
  interval_append inverseTest 16384 16896 17408 inverse_join_016384_016896 inverse_join_016896_017408

theorem inverse_join_017408_017664 : Interval inverseTest 17408 17664 :=
  interval_append inverseTest 17408 17536 17664 inverse_017408 inverse_017536

theorem inverse_join_017664_017920 : Interval inverseTest 17664 17920 :=
  interval_append inverseTest 17664 17792 17920 inverse_017664 inverse_017792

theorem inverse_join_017408_017920 : Interval inverseTest 17408 17920 :=
  interval_append inverseTest 17408 17664 17920 inverse_join_017408_017664 inverse_join_017664_017920

theorem inverse_join_017920_018176 : Interval inverseTest 17920 18176 :=
  interval_append inverseTest 17920 18048 18176 inverse_017920 inverse_018048

theorem inverse_join_018176_018432 : Interval inverseTest 18176 18432 :=
  interval_append inverseTest 18176 18304 18432 inverse_018176 inverse_018304

theorem inverse_join_017920_018432 : Interval inverseTest 17920 18432 :=
  interval_append inverseTest 17920 18176 18432 inverse_join_017920_018176 inverse_join_018176_018432

theorem inverse_join_017408_018432 : Interval inverseTest 17408 18432 :=
  interval_append inverseTest 17408 17920 18432 inverse_join_017408_017920 inverse_join_017920_018432

theorem inverse_join_016384_018432 : Interval inverseTest 16384 18432 :=
  interval_append inverseTest 16384 17408 18432 inverse_join_016384_017408 inverse_join_017408_018432

theorem inverse_part_008 : Interval inverseTest 16384 18432 := inverse_join_016384_018432
end Papers.RationalityTen.FullSix0FacetEmbedding
