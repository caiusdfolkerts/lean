module
prelude
public meta import LowerSchemas.FinitePolygonN
public import PolygonN7DAGTests

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

cert_candidates_checked 00000 0 8 8
cert_candidates_checked 00008 8 16 8
cert_candidates_checked 00016 16 24 8
cert_candidates_checked 00024 24 32 8
cert_candidates_checked 00032 32 40 8
cert_candidates_checked 00040 40 48 8
cert_candidates_checked 00048 48 56 8
cert_candidates_checked 00056 56 64 8
cert_candidates_checked 00064 64 72 8
cert_candidates_checked 00072 72 80 8
cert_candidates_checked 00080 80 88 8
cert_candidates_checked 00088 88 96 8
cert_candidates_checked 00096 96 104 8
cert_candidates_checked 00104 104 112 8
cert_candidates_checked 00112 112 120 8
cert_candidates_checked 00120 120 128 8
cert_candidates_checked 00128 128 136 8
cert_candidates_checked 00136 136 144 8
cert_candidates_checked 00144 144 152 8
cert_candidates_checked 00152 152 160 8
cert_candidates_checked 00160 160 168 8
cert_candidates_checked 00168 168 176 8
cert_candidates_checked 00176 176 184 8
cert_candidates_checked 00184 184 192 8
cert_candidates_checked 00192 192 200 8
cert_candidates_checked 00200 200 208 8
cert_candidates_checked 00208 208 216 8
cert_candidates_checked 00216 216 224 8
cert_candidates_checked 00224 224 232 8
cert_candidates_checked 00232 232 240 8
cert_candidates_checked 00240 240 248 8
cert_candidates_checked 00248 248 256 8
cert_candidates_checked 00256 256 264 8
cert_candidates_checked 00264 264 272 8
cert_candidates_checked 00272 272 280 8
cert_candidates_checked 00280 280 288 8
cert_candidates_checked 00288 288 290 2
cert_candidates_checked_join_2 00000 00016 0 16 8 00008
cert_candidates_checked_join_2 00016 00032 16 32 24 00024
cert_candidates_checked_join 00000 00032 0 32 16 00016
cert_candidates_checked_join_2 00032 00048 32 48 40 00040
cert_candidates_checked_join_2 00056 00072 56 72 64 00064
theorem candidates_checked_join_00048_00072 : FiniteChecks.Interval candidateTest 48 72 :=
  FiniteChecks.interval_append candidateTest 48 56 72 candidates_checked_00048 candidates_checked_join_00056_00072

cert_candidates_checked_join 00032 00072 32 72 48 00048
cert_candidates_checked_join 00000 00072 0 72 32 00032
cert_candidates_checked_join_2 00072 00088 72 88 80 00080
cert_candidates_checked_join_2 00088 00104 88 104 96 00096
cert_candidates_checked_join 00072 00104 72 104 88 00088
cert_candidates_checked_join_2 00104 00120 104 120 112 00112
cert_candidates_checked_join_2 00128 00144 128 144 136 00136
theorem candidates_checked_join_00120_00144 : FiniteChecks.Interval candidateTest 120 144 :=
  FiniteChecks.interval_append candidateTest 120 128 144 candidates_checked_00120 candidates_checked_join_00128_00144

cert_candidates_checked_join 00104 00144 104 144 120 00120
cert_candidates_checked_join 00072 00144 72 144 104 00104
cert_candidates_checked_join 00000 00144 0 144 72 00072
cert_candidates_checked_join_2 00144 00160 144 160 152 00152
cert_candidates_checked_join_2 00160 00176 160 176 168 00168
cert_candidates_checked_join 00144 00176 144 176 160 00160
cert_candidates_checked_join_2 00176 00192 176 192 184 00184
cert_candidates_checked_join_2 00200 00216 200 216 208 00208
theorem candidates_checked_join_00192_00216 : FiniteChecks.Interval candidateTest 192 216 :=
  FiniteChecks.interval_append candidateTest 192 200 216 candidates_checked_00192 candidates_checked_join_00200_00216

cert_candidates_checked_join 00176 00216 176 216 192 00192
cert_candidates_checked_join 00144 00216 144 216 176 00176
cert_candidates_checked_join_2 00216 00232 216 232 224 00224
cert_candidates_checked_join_2 00240 00256 240 256 248 00248
theorem candidates_checked_join_00232_00256 : FiniteChecks.Interval candidateTest 232 256 :=
  FiniteChecks.interval_append candidateTest 232 240 256 candidates_checked_00232 candidates_checked_join_00240_00256

cert_candidates_checked_join 00216 00256 216 256 232 00232
cert_candidates_checked_join_2 00256 00272 256 272 264 00264
cert_candidates_checked_join_2 00280 00290 280 290 288 00288
theorem candidates_checked_join_00272_00290 : FiniteChecks.Interval candidateTest 272 290 :=
  FiniteChecks.interval_append candidateTest 272 280 290 candidates_checked_00272 candidates_checked_join_00280_00290

cert_candidates_checked_join 00256 00290 256 290 272 00272
cert_candidates_checked_join 00216 00290 216 290 256 00256
cert_candidates_checked_join 00144 00290 144 290 216 00216
cert_candidates_checked_join 00000 00290 0 290 144 00144
end Papers.RationalityTen.PolygonGrowth.N7
