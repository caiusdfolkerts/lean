module
prelude
public import PolygonN7DAGTests

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

theorem candidates_checked_00000 : FiniteChecks.Interval candidateTest 0 8 :=
  FiniteChecks.interval_of_check candidateTest 0 8 (by decide +kernel)

theorem candidates_checked_00008 : FiniteChecks.Interval candidateTest 8 16 :=
  FiniteChecks.interval_of_check candidateTest 8 8 (by decide +kernel)

theorem candidates_checked_00016 : FiniteChecks.Interval candidateTest 16 24 :=
  FiniteChecks.interval_of_check candidateTest 16 8 (by decide +kernel)

theorem candidates_checked_00024 : FiniteChecks.Interval candidateTest 24 32 :=
  FiniteChecks.interval_of_check candidateTest 24 8 (by decide +kernel)

theorem candidates_checked_00032 : FiniteChecks.Interval candidateTest 32 40 :=
  FiniteChecks.interval_of_check candidateTest 32 8 (by decide +kernel)

theorem candidates_checked_00040 : FiniteChecks.Interval candidateTest 40 48 :=
  FiniteChecks.interval_of_check candidateTest 40 8 (by decide +kernel)

theorem candidates_checked_00048 : FiniteChecks.Interval candidateTest 48 56 :=
  FiniteChecks.interval_of_check candidateTest 48 8 (by decide +kernel)

theorem candidates_checked_00056 : FiniteChecks.Interval candidateTest 56 64 :=
  FiniteChecks.interval_of_check candidateTest 56 8 (by decide +kernel)

theorem candidates_checked_00064 : FiniteChecks.Interval candidateTest 64 72 :=
  FiniteChecks.interval_of_check candidateTest 64 8 (by decide +kernel)

theorem candidates_checked_00072 : FiniteChecks.Interval candidateTest 72 80 :=
  FiniteChecks.interval_of_check candidateTest 72 8 (by decide +kernel)

theorem candidates_checked_00080 : FiniteChecks.Interval candidateTest 80 88 :=
  FiniteChecks.interval_of_check candidateTest 80 8 (by decide +kernel)

theorem candidates_checked_00088 : FiniteChecks.Interval candidateTest 88 96 :=
  FiniteChecks.interval_of_check candidateTest 88 8 (by decide +kernel)

theorem candidates_checked_00096 : FiniteChecks.Interval candidateTest 96 104 :=
  FiniteChecks.interval_of_check candidateTest 96 8 (by decide +kernel)

theorem candidates_checked_00104 : FiniteChecks.Interval candidateTest 104 112 :=
  FiniteChecks.interval_of_check candidateTest 104 8 (by decide +kernel)

theorem candidates_checked_00112 : FiniteChecks.Interval candidateTest 112 120 :=
  FiniteChecks.interval_of_check candidateTest 112 8 (by decide +kernel)

theorem candidates_checked_00120 : FiniteChecks.Interval candidateTest 120 128 :=
  FiniteChecks.interval_of_check candidateTest 120 8 (by decide +kernel)

theorem candidates_checked_00128 : FiniteChecks.Interval candidateTest 128 136 :=
  FiniteChecks.interval_of_check candidateTest 128 8 (by decide +kernel)

theorem candidates_checked_00136 : FiniteChecks.Interval candidateTest 136 144 :=
  FiniteChecks.interval_of_check candidateTest 136 8 (by decide +kernel)

theorem candidates_checked_00144 : FiniteChecks.Interval candidateTest 144 152 :=
  FiniteChecks.interval_of_check candidateTest 144 8 (by decide +kernel)

theorem candidates_checked_00152 : FiniteChecks.Interval candidateTest 152 160 :=
  FiniteChecks.interval_of_check candidateTest 152 8 (by decide +kernel)

theorem candidates_checked_00160 : FiniteChecks.Interval candidateTest 160 168 :=
  FiniteChecks.interval_of_check candidateTest 160 8 (by decide +kernel)

theorem candidates_checked_00168 : FiniteChecks.Interval candidateTest 168 176 :=
  FiniteChecks.interval_of_check candidateTest 168 8 (by decide +kernel)

theorem candidates_checked_00176 : FiniteChecks.Interval candidateTest 176 184 :=
  FiniteChecks.interval_of_check candidateTest 176 8 (by decide +kernel)

theorem candidates_checked_00184 : FiniteChecks.Interval candidateTest 184 192 :=
  FiniteChecks.interval_of_check candidateTest 184 8 (by decide +kernel)

theorem candidates_checked_00192 : FiniteChecks.Interval candidateTest 192 200 :=
  FiniteChecks.interval_of_check candidateTest 192 8 (by decide +kernel)

theorem candidates_checked_00200 : FiniteChecks.Interval candidateTest 200 208 :=
  FiniteChecks.interval_of_check candidateTest 200 8 (by decide +kernel)

theorem candidates_checked_00208 : FiniteChecks.Interval candidateTest 208 216 :=
  FiniteChecks.interval_of_check candidateTest 208 8 (by decide +kernel)

theorem candidates_checked_00216 : FiniteChecks.Interval candidateTest 216 224 :=
  FiniteChecks.interval_of_check candidateTest 216 8 (by decide +kernel)

theorem candidates_checked_00224 : FiniteChecks.Interval candidateTest 224 232 :=
  FiniteChecks.interval_of_check candidateTest 224 8 (by decide +kernel)

theorem candidates_checked_00232 : FiniteChecks.Interval candidateTest 232 240 :=
  FiniteChecks.interval_of_check candidateTest 232 8 (by decide +kernel)

theorem candidates_checked_00240 : FiniteChecks.Interval candidateTest 240 248 :=
  FiniteChecks.interval_of_check candidateTest 240 8 (by decide +kernel)

theorem candidates_checked_00248 : FiniteChecks.Interval candidateTest 248 256 :=
  FiniteChecks.interval_of_check candidateTest 248 8 (by decide +kernel)

theorem candidates_checked_00256 : FiniteChecks.Interval candidateTest 256 264 :=
  FiniteChecks.interval_of_check candidateTest 256 8 (by decide +kernel)

theorem candidates_checked_00264 : FiniteChecks.Interval candidateTest 264 272 :=
  FiniteChecks.interval_of_check candidateTest 264 8 (by decide +kernel)

theorem candidates_checked_00272 : FiniteChecks.Interval candidateTest 272 280 :=
  FiniteChecks.interval_of_check candidateTest 272 8 (by decide +kernel)

theorem candidates_checked_00280 : FiniteChecks.Interval candidateTest 280 288 :=
  FiniteChecks.interval_of_check candidateTest 280 8 (by decide +kernel)

theorem candidates_checked_00288 : FiniteChecks.Interval candidateTest 288 290 :=
  FiniteChecks.interval_of_check candidateTest 288 2 (by decide +kernel)

theorem candidates_checked_join_00000_00016 : FiniteChecks.Interval candidateTest 0 16 :=
  FiniteChecks.interval_append candidateTest 0 8 16 candidates_checked_00000 candidates_checked_00008

theorem candidates_checked_join_00016_00032 : FiniteChecks.Interval candidateTest 16 32 :=
  FiniteChecks.interval_append candidateTest 16 24 32 candidates_checked_00016 candidates_checked_00024

theorem candidates_checked_join_00000_00032 : FiniteChecks.Interval candidateTest 0 32 :=
  FiniteChecks.interval_append candidateTest 0 16 32 candidates_checked_join_00000_00016 candidates_checked_join_00016_00032

theorem candidates_checked_join_00032_00048 : FiniteChecks.Interval candidateTest 32 48 :=
  FiniteChecks.interval_append candidateTest 32 40 48 candidates_checked_00032 candidates_checked_00040

theorem candidates_checked_join_00056_00072 : FiniteChecks.Interval candidateTest 56 72 :=
  FiniteChecks.interval_append candidateTest 56 64 72 candidates_checked_00056 candidates_checked_00064

theorem candidates_checked_join_00048_00072 : FiniteChecks.Interval candidateTest 48 72 :=
  FiniteChecks.interval_append candidateTest 48 56 72 candidates_checked_00048 candidates_checked_join_00056_00072

theorem candidates_checked_join_00032_00072 : FiniteChecks.Interval candidateTest 32 72 :=
  FiniteChecks.interval_append candidateTest 32 48 72 candidates_checked_join_00032_00048 candidates_checked_join_00048_00072

theorem candidates_checked_join_00000_00072 : FiniteChecks.Interval candidateTest 0 72 :=
  FiniteChecks.interval_append candidateTest 0 32 72 candidates_checked_join_00000_00032 candidates_checked_join_00032_00072

theorem candidates_checked_join_00072_00088 : FiniteChecks.Interval candidateTest 72 88 :=
  FiniteChecks.interval_append candidateTest 72 80 88 candidates_checked_00072 candidates_checked_00080

theorem candidates_checked_join_00088_00104 : FiniteChecks.Interval candidateTest 88 104 :=
  FiniteChecks.interval_append candidateTest 88 96 104 candidates_checked_00088 candidates_checked_00096

theorem candidates_checked_join_00072_00104 : FiniteChecks.Interval candidateTest 72 104 :=
  FiniteChecks.interval_append candidateTest 72 88 104 candidates_checked_join_00072_00088 candidates_checked_join_00088_00104

theorem candidates_checked_join_00104_00120 : FiniteChecks.Interval candidateTest 104 120 :=
  FiniteChecks.interval_append candidateTest 104 112 120 candidates_checked_00104 candidates_checked_00112

theorem candidates_checked_join_00128_00144 : FiniteChecks.Interval candidateTest 128 144 :=
  FiniteChecks.interval_append candidateTest 128 136 144 candidates_checked_00128 candidates_checked_00136

theorem candidates_checked_join_00120_00144 : FiniteChecks.Interval candidateTest 120 144 :=
  FiniteChecks.interval_append candidateTest 120 128 144 candidates_checked_00120 candidates_checked_join_00128_00144

theorem candidates_checked_join_00104_00144 : FiniteChecks.Interval candidateTest 104 144 :=
  FiniteChecks.interval_append candidateTest 104 120 144 candidates_checked_join_00104_00120 candidates_checked_join_00120_00144

theorem candidates_checked_join_00072_00144 : FiniteChecks.Interval candidateTest 72 144 :=
  FiniteChecks.interval_append candidateTest 72 104 144 candidates_checked_join_00072_00104 candidates_checked_join_00104_00144

theorem candidates_checked_join_00000_00144 : FiniteChecks.Interval candidateTest 0 144 :=
  FiniteChecks.interval_append candidateTest 0 72 144 candidates_checked_join_00000_00072 candidates_checked_join_00072_00144

theorem candidates_checked_join_00144_00160 : FiniteChecks.Interval candidateTest 144 160 :=
  FiniteChecks.interval_append candidateTest 144 152 160 candidates_checked_00144 candidates_checked_00152

theorem candidates_checked_join_00160_00176 : FiniteChecks.Interval candidateTest 160 176 :=
  FiniteChecks.interval_append candidateTest 160 168 176 candidates_checked_00160 candidates_checked_00168

theorem candidates_checked_join_00144_00176 : FiniteChecks.Interval candidateTest 144 176 :=
  FiniteChecks.interval_append candidateTest 144 160 176 candidates_checked_join_00144_00160 candidates_checked_join_00160_00176

theorem candidates_checked_join_00176_00192 : FiniteChecks.Interval candidateTest 176 192 :=
  FiniteChecks.interval_append candidateTest 176 184 192 candidates_checked_00176 candidates_checked_00184

theorem candidates_checked_join_00200_00216 : FiniteChecks.Interval candidateTest 200 216 :=
  FiniteChecks.interval_append candidateTest 200 208 216 candidates_checked_00200 candidates_checked_00208

theorem candidates_checked_join_00192_00216 : FiniteChecks.Interval candidateTest 192 216 :=
  FiniteChecks.interval_append candidateTest 192 200 216 candidates_checked_00192 candidates_checked_join_00200_00216

theorem candidates_checked_join_00176_00216 : FiniteChecks.Interval candidateTest 176 216 :=
  FiniteChecks.interval_append candidateTest 176 192 216 candidates_checked_join_00176_00192 candidates_checked_join_00192_00216

theorem candidates_checked_join_00144_00216 : FiniteChecks.Interval candidateTest 144 216 :=
  FiniteChecks.interval_append candidateTest 144 176 216 candidates_checked_join_00144_00176 candidates_checked_join_00176_00216

theorem candidates_checked_join_00216_00232 : FiniteChecks.Interval candidateTest 216 232 :=
  FiniteChecks.interval_append candidateTest 216 224 232 candidates_checked_00216 candidates_checked_00224

theorem candidates_checked_join_00240_00256 : FiniteChecks.Interval candidateTest 240 256 :=
  FiniteChecks.interval_append candidateTest 240 248 256 candidates_checked_00240 candidates_checked_00248

theorem candidates_checked_join_00232_00256 : FiniteChecks.Interval candidateTest 232 256 :=
  FiniteChecks.interval_append candidateTest 232 240 256 candidates_checked_00232 candidates_checked_join_00240_00256

theorem candidates_checked_join_00216_00256 : FiniteChecks.Interval candidateTest 216 256 :=
  FiniteChecks.interval_append candidateTest 216 232 256 candidates_checked_join_00216_00232 candidates_checked_join_00232_00256

theorem candidates_checked_join_00256_00272 : FiniteChecks.Interval candidateTest 256 272 :=
  FiniteChecks.interval_append candidateTest 256 264 272 candidates_checked_00256 candidates_checked_00264

theorem candidates_checked_join_00280_00290 : FiniteChecks.Interval candidateTest 280 290 :=
  FiniteChecks.interval_append candidateTest 280 288 290 candidates_checked_00280 candidates_checked_00288

theorem candidates_checked_join_00272_00290 : FiniteChecks.Interval candidateTest 272 290 :=
  FiniteChecks.interval_append candidateTest 272 280 290 candidates_checked_00272 candidates_checked_join_00280_00290

theorem candidates_checked_join_00256_00290 : FiniteChecks.Interval candidateTest 256 290 :=
  FiniteChecks.interval_append candidateTest 256 272 290 candidates_checked_join_00256_00272 candidates_checked_join_00272_00290

theorem candidates_checked_join_00216_00290 : FiniteChecks.Interval candidateTest 216 290 :=
  FiniteChecks.interval_append candidateTest 216 256 290 candidates_checked_join_00216_00256 candidates_checked_join_00256_00290

theorem candidates_checked_join_00144_00290 : FiniteChecks.Interval candidateTest 144 290 :=
  FiniteChecks.interval_append candidateTest 144 216 290 candidates_checked_join_00144_00216 candidates_checked_join_00216_00290

theorem candidates_checked_join_00000_00290 : FiniteChecks.Interval candidateTest 0 290 :=
  FiniteChecks.interval_append candidateTest 0 144 290 candidates_checked_join_00000_00144 candidates_checked_join_00144_00290

end Papers.RationalityTen.PolygonGrowth.N7
