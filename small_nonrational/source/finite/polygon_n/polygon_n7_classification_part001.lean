module

public import PolygonN7ClassificationPart000

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem ridge_data_join_00232_00256 : FiniteChecks.Interval ridgeDataTest 232 256 :=
  FiniteChecks.interval_append ridgeDataTest 232 240 256 ridge_data_00232 ridge_data_join_00240_00256

theorem ridge_data_join_00216_00256 : FiniteChecks.Interval ridgeDataTest 216 256 :=
  FiniteChecks.interval_append ridgeDataTest 216 232 256 ridge_data_join_00216_00232 ridge_data_join_00232_00256

theorem ridge_data_join_00256_00272 : FiniteChecks.Interval ridgeDataTest 256 272 :=
  FiniteChecks.interval_append ridgeDataTest 256 264 272 ridge_data_00256 ridge_data_00264

theorem ridge_data_join_00280_00290 : FiniteChecks.Interval ridgeDataTest 280 290 :=
  FiniteChecks.interval_append ridgeDataTest 280 288 290 ridge_data_00280 ridge_data_00288

theorem ridge_data_join_00272_00290 : FiniteChecks.Interval ridgeDataTest 272 290 :=
  FiniteChecks.interval_append ridgeDataTest 272 280 290 ridge_data_00272 ridge_data_join_00280_00290

theorem ridge_data_join_00256_00290 : FiniteChecks.Interval ridgeDataTest 256 290 :=
  FiniteChecks.interval_append ridgeDataTest 256 272 290 ridge_data_join_00256_00272 ridge_data_join_00272_00290

theorem ridge_data_join_00216_00290 : FiniteChecks.Interval ridgeDataTest 216 290 :=
  FiniteChecks.interval_append ridgeDataTest 216 256 290 ridge_data_join_00216_00256 ridge_data_join_00256_00290

theorem ridge_data_join_00144_00290 : FiniteChecks.Interval ridgeDataTest 144 290 :=
  FiniteChecks.interval_append ridgeDataTest 144 216 290 ridge_data_join_00144_00216 ridge_data_join_00216_00290

theorem ridge_data_join_00000_00290 : FiniteChecks.Interval ridgeDataTest 0 290 :=
  FiniteChecks.interval_append ridgeDataTest 0 144 290 ridge_data_join_00000_00144 ridge_data_join_00144_00290

theorem compatibility_data_00000 : FiniteChecks.Interval compatibilityTest 0 8 :=
  FiniteChecks.interval_of_check compatibilityTest 0 8 (by decide +kernel)

theorem compatibility_data_00008 : FiniteChecks.Interval compatibilityTest 8 16 :=
  FiniteChecks.interval_of_check compatibilityTest 8 8 (by decide +kernel)

theorem compatibility_data_00016 : FiniteChecks.Interval compatibilityTest 16 24 :=
  FiniteChecks.interval_of_check compatibilityTest 16 8 (by decide +kernel)

theorem compatibility_data_00024 : FiniteChecks.Interval compatibilityTest 24 32 :=
  FiniteChecks.interval_of_check compatibilityTest 24 8 (by decide +kernel)

theorem compatibility_data_00032 : FiniteChecks.Interval compatibilityTest 32 40 :=
  FiniteChecks.interval_of_check compatibilityTest 32 8 (by decide +kernel)

theorem compatibility_data_00040 : FiniteChecks.Interval compatibilityTest 40 48 :=
  FiniteChecks.interval_of_check compatibilityTest 40 8 (by decide +kernel)

theorem compatibility_data_00048 : FiniteChecks.Interval compatibilityTest 48 56 :=
  FiniteChecks.interval_of_check compatibilityTest 48 8 (by decide +kernel)

theorem compatibility_data_00056 : FiniteChecks.Interval compatibilityTest 56 64 :=
  FiniteChecks.interval_of_check compatibilityTest 56 8 (by decide +kernel)

theorem compatibility_data_00064 : FiniteChecks.Interval compatibilityTest 64 72 :=
  FiniteChecks.interval_of_check compatibilityTest 64 8 (by decide +kernel)

theorem compatibility_data_00072 : FiniteChecks.Interval compatibilityTest 72 80 :=
  FiniteChecks.interval_of_check compatibilityTest 72 8 (by decide +kernel)

theorem compatibility_data_00080 : FiniteChecks.Interval compatibilityTest 80 88 :=
  FiniteChecks.interval_of_check compatibilityTest 80 8 (by decide +kernel)

theorem compatibility_data_00088 : FiniteChecks.Interval compatibilityTest 88 96 :=
  FiniteChecks.interval_of_check compatibilityTest 88 8 (by decide +kernel)

theorem compatibility_data_00096 : FiniteChecks.Interval compatibilityTest 96 104 :=
  FiniteChecks.interval_of_check compatibilityTest 96 8 (by decide +kernel)

theorem compatibility_data_00104 : FiniteChecks.Interval compatibilityTest 104 112 :=
  FiniteChecks.interval_of_check compatibilityTest 104 8 (by decide +kernel)

theorem compatibility_data_00112 : FiniteChecks.Interval compatibilityTest 112 120 :=
  FiniteChecks.interval_of_check compatibilityTest 112 8 (by decide +kernel)

theorem compatibility_data_00120 : FiniteChecks.Interval compatibilityTest 120 128 :=
  FiniteChecks.interval_of_check compatibilityTest 120 8 (by decide +kernel)

theorem compatibility_data_00128 : FiniteChecks.Interval compatibilityTest 128 136 :=
  FiniteChecks.interval_of_check compatibilityTest 128 8 (by decide +kernel)

theorem compatibility_data_00136 : FiniteChecks.Interval compatibilityTest 136 144 :=
  FiniteChecks.interval_of_check compatibilityTest 136 8 (by decide +kernel)

theorem compatibility_data_00144 : FiniteChecks.Interval compatibilityTest 144 152 :=
  FiniteChecks.interval_of_check compatibilityTest 144 8 (by decide +kernel)

theorem compatibility_data_00152 : FiniteChecks.Interval compatibilityTest 152 160 :=
  FiniteChecks.interval_of_check compatibilityTest 152 8 (by decide +kernel)

theorem compatibility_data_00160 : FiniteChecks.Interval compatibilityTest 160 168 :=
  FiniteChecks.interval_of_check compatibilityTest 160 8 (by decide +kernel)

theorem compatibility_data_00168 : FiniteChecks.Interval compatibilityTest 168 176 :=
  FiniteChecks.interval_of_check compatibilityTest 168 8 (by decide +kernel)

theorem compatibility_data_00176 : FiniteChecks.Interval compatibilityTest 176 184 :=
  FiniteChecks.interval_of_check compatibilityTest 176 8 (by decide +kernel)

theorem compatibility_data_00184 : FiniteChecks.Interval compatibilityTest 184 192 :=
  FiniteChecks.interval_of_check compatibilityTest 184 8 (by decide +kernel)

theorem compatibility_data_00192 : FiniteChecks.Interval compatibilityTest 192 200 :=
  FiniteChecks.interval_of_check compatibilityTest 192 8 (by decide +kernel)

theorem compatibility_data_00200 : FiniteChecks.Interval compatibilityTest 200 208 :=
  FiniteChecks.interval_of_check compatibilityTest 200 8 (by decide +kernel)

theorem compatibility_data_00208 : FiniteChecks.Interval compatibilityTest 208 216 :=
  FiniteChecks.interval_of_check compatibilityTest 208 8 (by decide +kernel)

theorem compatibility_data_00216 : FiniteChecks.Interval compatibilityTest 216 224 :=
  FiniteChecks.interval_of_check compatibilityTest 216 8 (by decide +kernel)

theorem compatibility_data_00224 : FiniteChecks.Interval compatibilityTest 224 232 :=
  FiniteChecks.interval_of_check compatibilityTest 224 8 (by decide +kernel)

theorem compatibility_data_00232 : FiniteChecks.Interval compatibilityTest 232 240 :=
  FiniteChecks.interval_of_check compatibilityTest 232 8 (by decide +kernel)

theorem compatibility_data_00240 : FiniteChecks.Interval compatibilityTest 240 248 :=
  FiniteChecks.interval_of_check compatibilityTest 240 8 (by decide +kernel)

theorem compatibility_data_00248 : FiniteChecks.Interval compatibilityTest 248 256 :=
  FiniteChecks.interval_of_check compatibilityTest 248 8 (by decide +kernel)

theorem compatibility_data_00256 : FiniteChecks.Interval compatibilityTest 256 264 :=
  FiniteChecks.interval_of_check compatibilityTest 256 8 (by decide +kernel)

theorem compatibility_data_00264 : FiniteChecks.Interval compatibilityTest 264 272 :=
  FiniteChecks.interval_of_check compatibilityTest 264 8 (by decide +kernel)

theorem compatibility_data_00272 : FiniteChecks.Interval compatibilityTest 272 280 :=
  FiniteChecks.interval_of_check compatibilityTest 272 8 (by decide +kernel)

theorem compatibility_data_00280 : FiniteChecks.Interval compatibilityTest 280 288 :=
  FiniteChecks.interval_of_check compatibilityTest 280 8 (by decide +kernel)

theorem compatibility_data_00288 : FiniteChecks.Interval compatibilityTest 288 290 :=
  FiniteChecks.interval_of_check compatibilityTest 288 2 (by decide +kernel)

theorem compatibility_data_join_00000_00016 : FiniteChecks.Interval compatibilityTest 0 16 :=
  FiniteChecks.interval_append compatibilityTest 0 8 16 compatibility_data_00000 compatibility_data_00008

theorem compatibility_data_join_00016_00032 : FiniteChecks.Interval compatibilityTest 16 32 :=
  FiniteChecks.interval_append compatibilityTest 16 24 32 compatibility_data_00016 compatibility_data_00024

theorem compatibility_data_join_00000_00032 : FiniteChecks.Interval compatibilityTest 0 32 :=
  FiniteChecks.interval_append compatibilityTest 0 16 32 compatibility_data_join_00000_00016 compatibility_data_join_00016_00032

theorem compatibility_data_join_00032_00048 : FiniteChecks.Interval compatibilityTest 32 48 :=
  FiniteChecks.interval_append compatibilityTest 32 40 48 compatibility_data_00032 compatibility_data_00040

theorem compatibility_data_join_00056_00072 : FiniteChecks.Interval compatibilityTest 56 72 :=
  FiniteChecks.interval_append compatibilityTest 56 64 72 compatibility_data_00056 compatibility_data_00064

theorem compatibility_data_join_00048_00072 : FiniteChecks.Interval compatibilityTest 48 72 :=
  FiniteChecks.interval_append compatibilityTest 48 56 72 compatibility_data_00048 compatibility_data_join_00056_00072

theorem compatibility_data_join_00032_00072 : FiniteChecks.Interval compatibilityTest 32 72 :=
  FiniteChecks.interval_append compatibilityTest 32 48 72 compatibility_data_join_00032_00048 compatibility_data_join_00048_00072

theorem compatibility_data_join_00000_00072 : FiniteChecks.Interval compatibilityTest 0 72 :=
  FiniteChecks.interval_append compatibilityTest 0 32 72 compatibility_data_join_00000_00032 compatibility_data_join_00032_00072

theorem compatibility_data_join_00072_00088 : FiniteChecks.Interval compatibilityTest 72 88 :=
  FiniteChecks.interval_append compatibilityTest 72 80 88 compatibility_data_00072 compatibility_data_00080

theorem compatibility_data_join_00088_00104 : FiniteChecks.Interval compatibilityTest 88 104 :=
  FiniteChecks.interval_append compatibilityTest 88 96 104 compatibility_data_00088 compatibility_data_00096

theorem compatibility_data_join_00072_00104 : FiniteChecks.Interval compatibilityTest 72 104 :=
  FiniteChecks.interval_append compatibilityTest 72 88 104 compatibility_data_join_00072_00088 compatibility_data_join_00088_00104

theorem compatibility_data_join_00104_00120 : FiniteChecks.Interval compatibilityTest 104 120 :=
  FiniteChecks.interval_append compatibilityTest 104 112 120 compatibility_data_00104 compatibility_data_00112

theorem compatibility_data_join_00128_00144 : FiniteChecks.Interval compatibilityTest 128 144 :=
  FiniteChecks.interval_append compatibilityTest 128 136 144 compatibility_data_00128 compatibility_data_00136

theorem compatibility_data_join_00120_00144 : FiniteChecks.Interval compatibilityTest 120 144 :=
  FiniteChecks.interval_append compatibilityTest 120 128 144 compatibility_data_00120 compatibility_data_join_00128_00144

theorem compatibility_data_join_00104_00144 : FiniteChecks.Interval compatibilityTest 104 144 :=
  FiniteChecks.interval_append compatibilityTest 104 120 144 compatibility_data_join_00104_00120 compatibility_data_join_00120_00144

theorem compatibility_data_join_00072_00144 : FiniteChecks.Interval compatibilityTest 72 144 :=
  FiniteChecks.interval_append compatibilityTest 72 104 144 compatibility_data_join_00072_00104 compatibility_data_join_00104_00144

theorem compatibility_data_join_00000_00144 : FiniteChecks.Interval compatibilityTest 0 144 :=
  FiniteChecks.interval_append compatibilityTest 0 72 144 compatibility_data_join_00000_00072 compatibility_data_join_00072_00144

theorem compatibility_data_join_00144_00160 : FiniteChecks.Interval compatibilityTest 144 160 :=
  FiniteChecks.interval_append compatibilityTest 144 152 160 compatibility_data_00144 compatibility_data_00152


end Papers.RationalityTen.ConcretePolygonClassification.N7
