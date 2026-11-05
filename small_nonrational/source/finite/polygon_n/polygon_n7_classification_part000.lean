module

public import PolygonN7ClassificationData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem ridge_data_00000 : FiniteChecks.Interval ridgeDataTest 0 8 :=
  FiniteChecks.interval_of_check ridgeDataTest 0 8 (by decide +kernel)

theorem ridge_data_00008 : FiniteChecks.Interval ridgeDataTest 8 16 :=
  FiniteChecks.interval_of_check ridgeDataTest 8 8 (by decide +kernel)

theorem ridge_data_00016 : FiniteChecks.Interval ridgeDataTest 16 24 :=
  FiniteChecks.interval_of_check ridgeDataTest 16 8 (by decide +kernel)

theorem ridge_data_00024 : FiniteChecks.Interval ridgeDataTest 24 32 :=
  FiniteChecks.interval_of_check ridgeDataTest 24 8 (by decide +kernel)

theorem ridge_data_00032 : FiniteChecks.Interval ridgeDataTest 32 40 :=
  FiniteChecks.interval_of_check ridgeDataTest 32 8 (by decide +kernel)

theorem ridge_data_00040 : FiniteChecks.Interval ridgeDataTest 40 48 :=
  FiniteChecks.interval_of_check ridgeDataTest 40 8 (by decide +kernel)

theorem ridge_data_00048 : FiniteChecks.Interval ridgeDataTest 48 56 :=
  FiniteChecks.interval_of_check ridgeDataTest 48 8 (by decide +kernel)

theorem ridge_data_00056 : FiniteChecks.Interval ridgeDataTest 56 64 :=
  FiniteChecks.interval_of_check ridgeDataTest 56 8 (by decide +kernel)

theorem ridge_data_00064 : FiniteChecks.Interval ridgeDataTest 64 72 :=
  FiniteChecks.interval_of_check ridgeDataTest 64 8 (by decide +kernel)

theorem ridge_data_00072 : FiniteChecks.Interval ridgeDataTest 72 80 :=
  FiniteChecks.interval_of_check ridgeDataTest 72 8 (by decide +kernel)

theorem ridge_data_00080 : FiniteChecks.Interval ridgeDataTest 80 88 :=
  FiniteChecks.interval_of_check ridgeDataTest 80 8 (by decide +kernel)

theorem ridge_data_00088 : FiniteChecks.Interval ridgeDataTest 88 96 :=
  FiniteChecks.interval_of_check ridgeDataTest 88 8 (by decide +kernel)

theorem ridge_data_00096 : FiniteChecks.Interval ridgeDataTest 96 104 :=
  FiniteChecks.interval_of_check ridgeDataTest 96 8 (by decide +kernel)

theorem ridge_data_00104 : FiniteChecks.Interval ridgeDataTest 104 112 :=
  FiniteChecks.interval_of_check ridgeDataTest 104 8 (by decide +kernel)

theorem ridge_data_00112 : FiniteChecks.Interval ridgeDataTest 112 120 :=
  FiniteChecks.interval_of_check ridgeDataTest 112 8 (by decide +kernel)

theorem ridge_data_00120 : FiniteChecks.Interval ridgeDataTest 120 128 :=
  FiniteChecks.interval_of_check ridgeDataTest 120 8 (by decide +kernel)

theorem ridge_data_00128 : FiniteChecks.Interval ridgeDataTest 128 136 :=
  FiniteChecks.interval_of_check ridgeDataTest 128 8 (by decide +kernel)

theorem ridge_data_00136 : FiniteChecks.Interval ridgeDataTest 136 144 :=
  FiniteChecks.interval_of_check ridgeDataTest 136 8 (by decide +kernel)

theorem ridge_data_00144 : FiniteChecks.Interval ridgeDataTest 144 152 :=
  FiniteChecks.interval_of_check ridgeDataTest 144 8 (by decide +kernel)

theorem ridge_data_00152 : FiniteChecks.Interval ridgeDataTest 152 160 :=
  FiniteChecks.interval_of_check ridgeDataTest 152 8 (by decide +kernel)

theorem ridge_data_00160 : FiniteChecks.Interval ridgeDataTest 160 168 :=
  FiniteChecks.interval_of_check ridgeDataTest 160 8 (by decide +kernel)

theorem ridge_data_00168 : FiniteChecks.Interval ridgeDataTest 168 176 :=
  FiniteChecks.interval_of_check ridgeDataTest 168 8 (by decide +kernel)

theorem ridge_data_00176 : FiniteChecks.Interval ridgeDataTest 176 184 :=
  FiniteChecks.interval_of_check ridgeDataTest 176 8 (by decide +kernel)

theorem ridge_data_00184 : FiniteChecks.Interval ridgeDataTest 184 192 :=
  FiniteChecks.interval_of_check ridgeDataTest 184 8 (by decide +kernel)

theorem ridge_data_00192 : FiniteChecks.Interval ridgeDataTest 192 200 :=
  FiniteChecks.interval_of_check ridgeDataTest 192 8 (by decide +kernel)

theorem ridge_data_00200 : FiniteChecks.Interval ridgeDataTest 200 208 :=
  FiniteChecks.interval_of_check ridgeDataTest 200 8 (by decide +kernel)

theorem ridge_data_00208 : FiniteChecks.Interval ridgeDataTest 208 216 :=
  FiniteChecks.interval_of_check ridgeDataTest 208 8 (by decide +kernel)

theorem ridge_data_00216 : FiniteChecks.Interval ridgeDataTest 216 224 :=
  FiniteChecks.interval_of_check ridgeDataTest 216 8 (by decide +kernel)

theorem ridge_data_00224 : FiniteChecks.Interval ridgeDataTest 224 232 :=
  FiniteChecks.interval_of_check ridgeDataTest 224 8 (by decide +kernel)

theorem ridge_data_00232 : FiniteChecks.Interval ridgeDataTest 232 240 :=
  FiniteChecks.interval_of_check ridgeDataTest 232 8 (by decide +kernel)

theorem ridge_data_00240 : FiniteChecks.Interval ridgeDataTest 240 248 :=
  FiniteChecks.interval_of_check ridgeDataTest 240 8 (by decide +kernel)

theorem ridge_data_00248 : FiniteChecks.Interval ridgeDataTest 248 256 :=
  FiniteChecks.interval_of_check ridgeDataTest 248 8 (by decide +kernel)

theorem ridge_data_00256 : FiniteChecks.Interval ridgeDataTest 256 264 :=
  FiniteChecks.interval_of_check ridgeDataTest 256 8 (by decide +kernel)

theorem ridge_data_00264 : FiniteChecks.Interval ridgeDataTest 264 272 :=
  FiniteChecks.interval_of_check ridgeDataTest 264 8 (by decide +kernel)

theorem ridge_data_00272 : FiniteChecks.Interval ridgeDataTest 272 280 :=
  FiniteChecks.interval_of_check ridgeDataTest 272 8 (by decide +kernel)

theorem ridge_data_00280 : FiniteChecks.Interval ridgeDataTest 280 288 :=
  FiniteChecks.interval_of_check ridgeDataTest 280 8 (by decide +kernel)

theorem ridge_data_00288 : FiniteChecks.Interval ridgeDataTest 288 290 :=
  FiniteChecks.interval_of_check ridgeDataTest 288 2 (by decide +kernel)

theorem ridge_data_join_00000_00016 : FiniteChecks.Interval ridgeDataTest 0 16 :=
  FiniteChecks.interval_append ridgeDataTest 0 8 16 ridge_data_00000 ridge_data_00008

theorem ridge_data_join_00016_00032 : FiniteChecks.Interval ridgeDataTest 16 32 :=
  FiniteChecks.interval_append ridgeDataTest 16 24 32 ridge_data_00016 ridge_data_00024

theorem ridge_data_join_00000_00032 : FiniteChecks.Interval ridgeDataTest 0 32 :=
  FiniteChecks.interval_append ridgeDataTest 0 16 32 ridge_data_join_00000_00016 ridge_data_join_00016_00032

theorem ridge_data_join_00032_00048 : FiniteChecks.Interval ridgeDataTest 32 48 :=
  FiniteChecks.interval_append ridgeDataTest 32 40 48 ridge_data_00032 ridge_data_00040

theorem ridge_data_join_00056_00072 : FiniteChecks.Interval ridgeDataTest 56 72 :=
  FiniteChecks.interval_append ridgeDataTest 56 64 72 ridge_data_00056 ridge_data_00064

theorem ridge_data_join_00048_00072 : FiniteChecks.Interval ridgeDataTest 48 72 :=
  FiniteChecks.interval_append ridgeDataTest 48 56 72 ridge_data_00048 ridge_data_join_00056_00072

theorem ridge_data_join_00032_00072 : FiniteChecks.Interval ridgeDataTest 32 72 :=
  FiniteChecks.interval_append ridgeDataTest 32 48 72 ridge_data_join_00032_00048 ridge_data_join_00048_00072

theorem ridge_data_join_00000_00072 : FiniteChecks.Interval ridgeDataTest 0 72 :=
  FiniteChecks.interval_append ridgeDataTest 0 32 72 ridge_data_join_00000_00032 ridge_data_join_00032_00072

theorem ridge_data_join_00072_00088 : FiniteChecks.Interval ridgeDataTest 72 88 :=
  FiniteChecks.interval_append ridgeDataTest 72 80 88 ridge_data_00072 ridge_data_00080

theorem ridge_data_join_00088_00104 : FiniteChecks.Interval ridgeDataTest 88 104 :=
  FiniteChecks.interval_append ridgeDataTest 88 96 104 ridge_data_00088 ridge_data_00096

theorem ridge_data_join_00072_00104 : FiniteChecks.Interval ridgeDataTest 72 104 :=
  FiniteChecks.interval_append ridgeDataTest 72 88 104 ridge_data_join_00072_00088 ridge_data_join_00088_00104

theorem ridge_data_join_00104_00120 : FiniteChecks.Interval ridgeDataTest 104 120 :=
  FiniteChecks.interval_append ridgeDataTest 104 112 120 ridge_data_00104 ridge_data_00112

theorem ridge_data_join_00128_00144 : FiniteChecks.Interval ridgeDataTest 128 144 :=
  FiniteChecks.interval_append ridgeDataTest 128 136 144 ridge_data_00128 ridge_data_00136

theorem ridge_data_join_00120_00144 : FiniteChecks.Interval ridgeDataTest 120 144 :=
  FiniteChecks.interval_append ridgeDataTest 120 128 144 ridge_data_00120 ridge_data_join_00128_00144

theorem ridge_data_join_00104_00144 : FiniteChecks.Interval ridgeDataTest 104 144 :=
  FiniteChecks.interval_append ridgeDataTest 104 120 144 ridge_data_join_00104_00120 ridge_data_join_00120_00144

theorem ridge_data_join_00072_00144 : FiniteChecks.Interval ridgeDataTest 72 144 :=
  FiniteChecks.interval_append ridgeDataTest 72 104 144 ridge_data_join_00072_00104 ridge_data_join_00104_00144

theorem ridge_data_join_00000_00144 : FiniteChecks.Interval ridgeDataTest 0 144 :=
  FiniteChecks.interval_append ridgeDataTest 0 72 144 ridge_data_join_00000_00072 ridge_data_join_00072_00144

theorem ridge_data_join_00144_00160 : FiniteChecks.Interval ridgeDataTest 144 160 :=
  FiniteChecks.interval_append ridgeDataTest 144 152 160 ridge_data_00144 ridge_data_00152

theorem ridge_data_join_00160_00176 : FiniteChecks.Interval ridgeDataTest 160 176 :=
  FiniteChecks.interval_append ridgeDataTest 160 168 176 ridge_data_00160 ridge_data_00168

theorem ridge_data_join_00144_00176 : FiniteChecks.Interval ridgeDataTest 144 176 :=
  FiniteChecks.interval_append ridgeDataTest 144 160 176 ridge_data_join_00144_00160 ridge_data_join_00160_00176

theorem ridge_data_join_00176_00192 : FiniteChecks.Interval ridgeDataTest 176 192 :=
  FiniteChecks.interval_append ridgeDataTest 176 184 192 ridge_data_00176 ridge_data_00184

theorem ridge_data_join_00200_00216 : FiniteChecks.Interval ridgeDataTest 200 216 :=
  FiniteChecks.interval_append ridgeDataTest 200 208 216 ridge_data_00200 ridge_data_00208

theorem ridge_data_join_00192_00216 : FiniteChecks.Interval ridgeDataTest 192 216 :=
  FiniteChecks.interval_append ridgeDataTest 192 200 216 ridge_data_00192 ridge_data_join_00200_00216

theorem ridge_data_join_00176_00216 : FiniteChecks.Interval ridgeDataTest 176 216 :=
  FiniteChecks.interval_append ridgeDataTest 176 192 216 ridge_data_join_00176_00192 ridge_data_join_00192_00216

theorem ridge_data_join_00144_00216 : FiniteChecks.Interval ridgeDataTest 144 216 :=
  FiniteChecks.interval_append ridgeDataTest 144 176 216 ridge_data_join_00144_00176 ridge_data_join_00176_00216

theorem ridge_data_join_00216_00232 : FiniteChecks.Interval ridgeDataTest 216 232 :=
  FiniteChecks.interval_append ridgeDataTest 216 224 232 ridge_data_00216 ridge_data_00224

theorem ridge_data_join_00240_00256 : FiniteChecks.Interval ridgeDataTest 240 256 :=
  FiniteChecks.interval_append ridgeDataTest 240 248 256 ridge_data_00240 ridge_data_00248


end Papers.RationalityTen.ConcretePolygonClassification.N7
