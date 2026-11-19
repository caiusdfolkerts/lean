module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_ridge_data 00000 0 8 8
cert_ridge_data 00008 8 16 8
cert_ridge_data 00016 16 24 8
cert_ridge_data 00024 24 32 8
cert_ridge_data 00032 32 40 8
cert_ridge_data 00040 40 48 8
cert_ridge_data 00048 48 56 8
cert_ridge_data 00056 56 64 8
cert_ridge_data 00064 64 72 8
cert_ridge_data 00072 72 80 8
cert_ridge_data 00080 80 88 8
cert_ridge_data 00088 88 96 8
cert_ridge_data 00096 96 104 8
cert_ridge_data 00104 104 112 8
cert_ridge_data 00112 112 120 8
cert_ridge_data 00120 120 128 8
cert_ridge_data 00128 128 136 8
cert_ridge_data 00136 136 144 8
cert_ridge_data 00144 144 152 8
cert_ridge_data 00152 152 160 8
cert_ridge_data 00160 160 168 8
cert_ridge_data 00168 168 176 8
cert_ridge_data 00176 176 184 8
cert_ridge_data 00184 184 192 8
cert_ridge_data 00192 192 200 8
cert_ridge_data 00200 200 208 8
cert_ridge_data 00208 208 216 8
cert_ridge_data 00216 216 224 8
cert_ridge_data 00224 224 232 8
cert_ridge_data 00232 232 240 8
cert_ridge_data 00240 240 248 8
cert_ridge_data 00248 248 256 8
cert_ridge_data 00256 256 264 8
cert_ridge_data 00264 264 272 8
cert_ridge_data 00272 272 280 8
cert_ridge_data 00280 280 288 8
cert_ridge_data 00288 288 290 2
cert_ridge_data_join 00000 00016 0 16 8 00008
cert_ridge_data_join 00016 00032 16 32 24 00024
cert_ridge_data_join_2 00000 00032 0 32 16 00016
cert_ridge_data_join 00032 00048 32 48 40 00040
cert_ridge_data_join 00056 00072 56 72 64 00064
theorem ridge_data_join_00048_00072 : FiniteChecks.Interval ridgeDataTest 48 72 :=
  FiniteChecks.interval_append ridgeDataTest 48 56 72 ridge_data_00048 ridge_data_join_00056_00072

cert_ridge_data_join_2 00032 00072 32 72 48 00048
cert_ridge_data_join_2 00000 00072 0 72 32 00032
cert_ridge_data_join 00072 00088 72 88 80 00080
cert_ridge_data_join 00088 00104 88 104 96 00096
cert_ridge_data_join_2 00072 00104 72 104 88 00088
cert_ridge_data_join 00104 00120 104 120 112 00112
cert_ridge_data_join 00128 00144 128 144 136 00136
theorem ridge_data_join_00120_00144 : FiniteChecks.Interval ridgeDataTest 120 144 :=
  FiniteChecks.interval_append ridgeDataTest 120 128 144 ridge_data_00120 ridge_data_join_00128_00144

cert_ridge_data_join_2 00104 00144 104 144 120 00120
cert_ridge_data_join_2 00072 00144 72 144 104 00104
cert_ridge_data_join_2 00000 00144 0 144 72 00072
cert_ridge_data_join 00144 00160 144 160 152 00152
cert_ridge_data_join 00160 00176 160 176 168 00168
cert_ridge_data_join_2 00144 00176 144 176 160 00160
cert_ridge_data_join 00176 00192 176 192 184 00184
cert_ridge_data_join 00200 00216 200 216 208 00208
theorem ridge_data_join_00192_00216 : FiniteChecks.Interval ridgeDataTest 192 216 :=
  FiniteChecks.interval_append ridgeDataTest 192 200 216 ridge_data_00192 ridge_data_join_00200_00216

cert_ridge_data_join_2 00176 00216 176 216 192 00192
cert_ridge_data_join_2 00144 00216 144 216 176 00176
cert_ridge_data_join 00216 00232 216 232 224 00224
theorem ridge_data_join_00240_00256 : FiniteChecks.Interval ridgeDataTest 240 256 :=
  FiniteChecks.interval_append ridgeDataTest 240 248 256 ridge_data_00240 ridge_data_00248


end Papers.RationalityTen.ConcretePolygonClassification.N7
