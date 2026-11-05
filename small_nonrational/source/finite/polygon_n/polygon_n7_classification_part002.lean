module

public import PolygonN7ClassificationPart001

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

theorem compatibility_data_join_00160_00176 : FiniteChecks.Interval compatibilityTest 160 176 :=
  FiniteChecks.interval_append compatibilityTest 160 168 176 compatibility_data_00160 compatibility_data_00168

theorem compatibility_data_join_00144_00176 : FiniteChecks.Interval compatibilityTest 144 176 :=
  FiniteChecks.interval_append compatibilityTest 144 160 176 compatibility_data_join_00144_00160 compatibility_data_join_00160_00176

theorem compatibility_data_join_00176_00192 : FiniteChecks.Interval compatibilityTest 176 192 :=
  FiniteChecks.interval_append compatibilityTest 176 184 192 compatibility_data_00176 compatibility_data_00184

theorem compatibility_data_join_00200_00216 : FiniteChecks.Interval compatibilityTest 200 216 :=
  FiniteChecks.interval_append compatibilityTest 200 208 216 compatibility_data_00200 compatibility_data_00208

theorem compatibility_data_join_00192_00216 : FiniteChecks.Interval compatibilityTest 192 216 :=
  FiniteChecks.interval_append compatibilityTest 192 200 216 compatibility_data_00192 compatibility_data_join_00200_00216

theorem compatibility_data_join_00176_00216 : FiniteChecks.Interval compatibilityTest 176 216 :=
  FiniteChecks.interval_append compatibilityTest 176 192 216 compatibility_data_join_00176_00192 compatibility_data_join_00192_00216

theorem compatibility_data_join_00144_00216 : FiniteChecks.Interval compatibilityTest 144 216 :=
  FiniteChecks.interval_append compatibilityTest 144 176 216 compatibility_data_join_00144_00176 compatibility_data_join_00176_00216

theorem compatibility_data_join_00216_00232 : FiniteChecks.Interval compatibilityTest 216 232 :=
  FiniteChecks.interval_append compatibilityTest 216 224 232 compatibility_data_00216 compatibility_data_00224

theorem compatibility_data_join_00240_00256 : FiniteChecks.Interval compatibilityTest 240 256 :=
  FiniteChecks.interval_append compatibilityTest 240 248 256 compatibility_data_00240 compatibility_data_00248

theorem compatibility_data_join_00232_00256 : FiniteChecks.Interval compatibilityTest 232 256 :=
  FiniteChecks.interval_append compatibilityTest 232 240 256 compatibility_data_00232 compatibility_data_join_00240_00256

theorem compatibility_data_join_00216_00256 : FiniteChecks.Interval compatibilityTest 216 256 :=
  FiniteChecks.interval_append compatibilityTest 216 232 256 compatibility_data_join_00216_00232 compatibility_data_join_00232_00256

theorem compatibility_data_join_00256_00272 : FiniteChecks.Interval compatibilityTest 256 272 :=
  FiniteChecks.interval_append compatibilityTest 256 264 272 compatibility_data_00256 compatibility_data_00264

theorem compatibility_data_join_00280_00290 : FiniteChecks.Interval compatibilityTest 280 290 :=
  FiniteChecks.interval_append compatibilityTest 280 288 290 compatibility_data_00280 compatibility_data_00288

theorem compatibility_data_join_00272_00290 : FiniteChecks.Interval compatibilityTest 272 290 :=
  FiniteChecks.interval_append compatibilityTest 272 280 290 compatibility_data_00272 compatibility_data_join_00280_00290

theorem compatibility_data_join_00256_00290 : FiniteChecks.Interval compatibilityTest 256 290 :=
  FiniteChecks.interval_append compatibilityTest 256 272 290 compatibility_data_join_00256_00272 compatibility_data_join_00272_00290

theorem compatibility_data_join_00216_00290 : FiniteChecks.Interval compatibilityTest 216 290 :=
  FiniteChecks.interval_append compatibilityTest 216 256 290 compatibility_data_join_00216_00256 compatibility_data_join_00256_00290

theorem compatibility_data_join_00144_00290 : FiniteChecks.Interval compatibilityTest 144 290 :=
  FiniteChecks.interval_append compatibilityTest 144 216 290 compatibility_data_join_00144_00216 compatibility_data_join_00216_00290

theorem compatibility_data_join_00000_00290 : FiniteChecks.Interval compatibilityTest 0 290 :=
  FiniteChecks.interval_append compatibilityTest 0 144 290 compatibility_data_join_00000_00144 compatibility_data_join_00144_00290

theorem terminal_data_00000 : FiniteChecks.Interval terminalTest 0 8 :=
  FiniteChecks.interval_of_check terminalTest 0 8 (by decide +kernel)

theorem terminal_data_00008 : FiniteChecks.Interval terminalTest 8 16 :=
  FiniteChecks.interval_of_check terminalTest 8 8 (by decide +kernel)

theorem terminal_data_00016 : FiniteChecks.Interval terminalTest 16 24 :=
  FiniteChecks.interval_of_check terminalTest 16 8 (by decide +kernel)

theorem terminal_data_00024 : FiniteChecks.Interval terminalTest 24 32 :=
  FiniteChecks.interval_of_check terminalTest 24 8 (by decide +kernel)

theorem terminal_data_00032 : FiniteChecks.Interval terminalTest 32 40 :=
  FiniteChecks.interval_of_check terminalTest 32 8 (by decide +kernel)

theorem terminal_data_00040 : FiniteChecks.Interval terminalTest 40 48 :=
  FiniteChecks.interval_of_check terminalTest 40 8 (by decide +kernel)

theorem terminal_data_00048 : FiniteChecks.Interval terminalTest 48 56 :=
  FiniteChecks.interval_of_check terminalTest 48 8 (by decide +kernel)

theorem terminal_data_00056 : FiniteChecks.Interval terminalTest 56 64 :=
  FiniteChecks.interval_of_check terminalTest 56 8 (by decide +kernel)

theorem terminal_data_00064 : FiniteChecks.Interval terminalTest 64 72 :=
  FiniteChecks.interval_of_check terminalTest 64 8 (by decide +kernel)

theorem terminal_data_00072 : FiniteChecks.Interval terminalTest 72 80 :=
  FiniteChecks.interval_of_check terminalTest 72 8 (by decide +kernel)

theorem terminal_data_00080 : FiniteChecks.Interval terminalTest 80 88 :=
  FiniteChecks.interval_of_check terminalTest 80 8 (by decide +kernel)

theorem terminal_data_00088 : FiniteChecks.Interval terminalTest 88 96 :=
  FiniteChecks.interval_of_check terminalTest 88 8 (by decide +kernel)

theorem terminal_data_00096 : FiniteChecks.Interval terminalTest 96 104 :=
  FiniteChecks.interval_of_check terminalTest 96 8 (by decide +kernel)

theorem terminal_data_00104 : FiniteChecks.Interval terminalTest 104 112 :=
  FiniteChecks.interval_of_check terminalTest 104 8 (by decide +kernel)

theorem terminal_data_00112 : FiniteChecks.Interval terminalTest 112 120 :=
  FiniteChecks.interval_of_check terminalTest 112 8 (by decide +kernel)

theorem terminal_data_00120 : FiniteChecks.Interval terminalTest 120 128 :=
  FiniteChecks.interval_of_check terminalTest 120 8 (by decide +kernel)

theorem terminal_data_00128 : FiniteChecks.Interval terminalTest 128 136 :=
  FiniteChecks.interval_of_check terminalTest 128 8 (by decide +kernel)

theorem terminal_data_00136 : FiniteChecks.Interval terminalTest 136 144 :=
  FiniteChecks.interval_of_check terminalTest 136 8 (by decide +kernel)

theorem terminal_data_00144 : FiniteChecks.Interval terminalTest 144 152 :=
  FiniteChecks.interval_of_check terminalTest 144 8 (by decide +kernel)

theorem terminal_data_00152 : FiniteChecks.Interval terminalTest 152 160 :=
  FiniteChecks.interval_of_check terminalTest 152 8 (by decide +kernel)

theorem terminal_data_00160 : FiniteChecks.Interval terminalTest 160 168 :=
  FiniteChecks.interval_of_check terminalTest 160 8 (by decide +kernel)

theorem terminal_data_00168 : FiniteChecks.Interval terminalTest 168 176 :=
  FiniteChecks.interval_of_check terminalTest 168 8 (by decide +kernel)

theorem terminal_data_00176 : FiniteChecks.Interval terminalTest 176 184 :=
  FiniteChecks.interval_of_check terminalTest 176 8 (by decide +kernel)

theorem terminal_data_00184 : FiniteChecks.Interval terminalTest 184 192 :=
  FiniteChecks.interval_of_check terminalTest 184 8 (by decide +kernel)

theorem terminal_data_00192 : FiniteChecks.Interval terminalTest 192 200 :=
  FiniteChecks.interval_of_check terminalTest 192 8 (by decide +kernel)

theorem terminal_data_00200 : FiniteChecks.Interval terminalTest 200 208 :=
  FiniteChecks.interval_of_check terminalTest 200 8 (by decide +kernel)

theorem terminal_data_00208 : FiniteChecks.Interval terminalTest 208 216 :=
  FiniteChecks.interval_of_check terminalTest 208 8 (by decide +kernel)

theorem terminal_data_00216 : FiniteChecks.Interval terminalTest 216 224 :=
  FiniteChecks.interval_of_check terminalTest 216 8 (by decide +kernel)

theorem terminal_data_00224 : FiniteChecks.Interval terminalTest 224 232 :=
  FiniteChecks.interval_of_check terminalTest 224 8 (by decide +kernel)

theorem terminal_data_00232 : FiniteChecks.Interval terminalTest 232 240 :=
  FiniteChecks.interval_of_check terminalTest 232 8 (by decide +kernel)

theorem terminal_data_00240 : FiniteChecks.Interval terminalTest 240 248 :=
  FiniteChecks.interval_of_check terminalTest 240 8 (by decide +kernel)

theorem terminal_data_00248 : FiniteChecks.Interval terminalTest 248 256 :=
  FiniteChecks.interval_of_check terminalTest 248 8 (by decide +kernel)

theorem terminal_data_00256 : FiniteChecks.Interval terminalTest 256 264 :=
  FiniteChecks.interval_of_check terminalTest 256 8 (by decide +kernel)

theorem terminal_data_00264 : FiniteChecks.Interval terminalTest 264 272 :=
  FiniteChecks.interval_of_check terminalTest 264 8 (by decide +kernel)

theorem terminal_data_00272 : FiniteChecks.Interval terminalTest 272 280 :=
  FiniteChecks.interval_of_check terminalTest 272 8 (by decide +kernel)

theorem terminal_data_00280 : FiniteChecks.Interval terminalTest 280 288 :=
  FiniteChecks.interval_of_check terminalTest 280 8 (by decide +kernel)

theorem terminal_data_00288 : FiniteChecks.Interval terminalTest 288 296 :=
  FiniteChecks.interval_of_check terminalTest 288 8 (by decide +kernel)

theorem terminal_data_00296 : FiniteChecks.Interval terminalTest 296 304 :=
  FiniteChecks.interval_of_check terminalTest 296 8 (by decide +kernel)

theorem terminal_data_00304 : FiniteChecks.Interval terminalTest 304 312 :=
  FiniteChecks.interval_of_check terminalTest 304 8 (by decide +kernel)

theorem terminal_data_00312 : FiniteChecks.Interval terminalTest 312 320 :=
  FiniteChecks.interval_of_check terminalTest 312 8 (by decide +kernel)

theorem terminal_data_00320 : FiniteChecks.Interval terminalTest 320 328 :=
  FiniteChecks.interval_of_check terminalTest 320 8 (by decide +kernel)

theorem terminal_data_00328 : FiniteChecks.Interval terminalTest 328 336 :=
  FiniteChecks.interval_of_check terminalTest 328 8 (by decide +kernel)

theorem terminal_data_00336 : FiniteChecks.Interval terminalTest 336 344 :=
  FiniteChecks.interval_of_check terminalTest 336 8 (by decide +kernel)

theorem terminal_data_00344 : FiniteChecks.Interval terminalTest 344 352 :=
  FiniteChecks.interval_of_check terminalTest 344 8 (by decide +kernel)

theorem terminal_data_00352 : FiniteChecks.Interval terminalTest 352 360 :=
  FiniteChecks.interval_of_check terminalTest 352 8 (by decide +kernel)

theorem terminal_data_00360 : FiniteChecks.Interval terminalTest 360 368 :=
  FiniteChecks.interval_of_check terminalTest 360 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
