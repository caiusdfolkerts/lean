module
prelude
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

theorem inverse_012288 : Interval inverseTest 12288 12416 :=
  interval_of_check inverseTest 12288 128 (by decide +kernel)

theorem inverse_012416 : Interval inverseTest 12416 12544 :=
  interval_of_check inverseTest 12416 128 (by decide +kernel)

theorem inverse_012544 : Interval inverseTest 12544 12672 :=
  interval_of_check inverseTest 12544 128 (by decide +kernel)

theorem inverse_012672 : Interval inverseTest 12672 12800 :=
  interval_of_check inverseTest 12672 128 (by decide +kernel)

theorem inverse_012800 : Interval inverseTest 12800 12928 :=
  interval_of_check inverseTest 12800 128 (by decide +kernel)

theorem inverse_012928 : Interval inverseTest 12928 13056 :=
  interval_of_check inverseTest 12928 128 (by decide +kernel)

theorem inverse_013056 : Interval inverseTest 13056 13184 :=
  interval_of_check inverseTest 13056 128 (by decide +kernel)

theorem inverse_013184 : Interval inverseTest 13184 13312 :=
  interval_of_check inverseTest 13184 128 (by decide +kernel)

theorem inverse_013312 : Interval inverseTest 13312 13440 :=
  interval_of_check inverseTest 13312 128 (by decide +kernel)

theorem inverse_013440 : Interval inverseTest 13440 13568 :=
  interval_of_check inverseTest 13440 128 (by decide +kernel)

theorem inverse_013568 : Interval inverseTest 13568 13696 :=
  interval_of_check inverseTest 13568 128 (by decide +kernel)

theorem inverse_013696 : Interval inverseTest 13696 13824 :=
  interval_of_check inverseTest 13696 128 (by decide +kernel)

theorem inverse_013824 : Interval inverseTest 13824 13952 :=
  interval_of_check inverseTest 13824 128 (by decide +kernel)

theorem inverse_013952 : Interval inverseTest 13952 14080 :=
  interval_of_check inverseTest 13952 128 (by decide +kernel)

theorem inverse_014080 : Interval inverseTest 14080 14208 :=
  interval_of_check inverseTest 14080 128 (by decide +kernel)

theorem inverse_014208 : Interval inverseTest 14208 14336 :=
  interval_of_check inverseTest 14208 128 (by decide +kernel)

theorem inverse_join_012288_012544 : Interval inverseTest 12288 12544 :=
  interval_append inverseTest 12288 12416 12544 inverse_012288 inverse_012416

theorem inverse_join_012544_012800 : Interval inverseTest 12544 12800 :=
  interval_append inverseTest 12544 12672 12800 inverse_012544 inverse_012672

theorem inverse_join_012288_012800 : Interval inverseTest 12288 12800 :=
  interval_append inverseTest 12288 12544 12800 inverse_join_012288_012544 inverse_join_012544_012800

theorem inverse_join_012800_013056 : Interval inverseTest 12800 13056 :=
  interval_append inverseTest 12800 12928 13056 inverse_012800 inverse_012928

theorem inverse_join_013056_013312 : Interval inverseTest 13056 13312 :=
  interval_append inverseTest 13056 13184 13312 inverse_013056 inverse_013184

theorem inverse_join_012800_013312 : Interval inverseTest 12800 13312 :=
  interval_append inverseTest 12800 13056 13312 inverse_join_012800_013056 inverse_join_013056_013312

theorem inverse_join_012288_013312 : Interval inverseTest 12288 13312 :=
  interval_append inverseTest 12288 12800 13312 inverse_join_012288_012800 inverse_join_012800_013312

theorem inverse_join_013312_013568 : Interval inverseTest 13312 13568 :=
  interval_append inverseTest 13312 13440 13568 inverse_013312 inverse_013440

theorem inverse_join_013568_013824 : Interval inverseTest 13568 13824 :=
  interval_append inverseTest 13568 13696 13824 inverse_013568 inverse_013696

theorem inverse_join_013312_013824 : Interval inverseTest 13312 13824 :=
  interval_append inverseTest 13312 13568 13824 inverse_join_013312_013568 inverse_join_013568_013824

theorem inverse_join_013824_014080 : Interval inverseTest 13824 14080 :=
  interval_append inverseTest 13824 13952 14080 inverse_013824 inverse_013952

theorem inverse_join_014080_014336 : Interval inverseTest 14080 14336 :=
  interval_append inverseTest 14080 14208 14336 inverse_014080 inverse_014208

theorem inverse_join_013824_014336 : Interval inverseTest 13824 14336 :=
  interval_append inverseTest 13824 14080 14336 inverse_join_013824_014080 inverse_join_014080_014336

theorem inverse_join_013312_014336 : Interval inverseTest 13312 14336 :=
  interval_append inverseTest 13312 13824 14336 inverse_join_013312_013824 inverse_join_013824_014336

theorem inverse_join_012288_014336 : Interval inverseTest 12288 14336 :=
  interval_append inverseTest 12288 13312 14336 inverse_join_012288_013312 inverse_join_013312_014336

theorem inverse_part_006 : Interval inverseTest 12288 14336 := inverse_join_012288_014336
end Papers.RationalityTen.FullSix0FacetEmbedding
