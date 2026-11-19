module

public meta import LowerSchemas.FinitePolygonN
public import PolygonN7ClassificationPart001

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Papers.RationalityTen.ConcretePolygonClassification.N7
open Papers.RationalityTen PolygonBoundaryCatalogue BoundarySearch PolygonDAGSemantics
open GrowthDAG SparseGrowthDAG GrowthPruning

cert_compatibility_data_join_2 00160 00176 160 176 168 00168
cert_compatibility_data_join 00144 00176 144 176 160 00160
cert_compatibility_data_join_2 00176 00192 176 192 184 00184
cert_compatibility_data_join_2 00200 00216 200 216 208 00208
theorem compatibility_data_join_00192_00216 : FiniteChecks.Interval compatibilityTest 192 216 :=
  FiniteChecks.interval_append compatibilityTest 192 200 216 compatibility_data_00192 compatibility_data_join_00200_00216

cert_compatibility_data_join 00176 00216 176 216 192 00192
cert_compatibility_data_join 00144 00216 144 216 176 00176
cert_compatibility_data_join_2 00216 00232 216 232 224 00224
cert_compatibility_data_join_2 00240 00256 240 256 248 00248
theorem compatibility_data_join_00232_00256 : FiniteChecks.Interval compatibilityTest 232 256 :=
  FiniteChecks.interval_append compatibilityTest 232 240 256 compatibility_data_00232 compatibility_data_join_00240_00256

cert_compatibility_data_join 00216 00256 216 256 232 00232
cert_compatibility_data_join_2 00256 00272 256 272 264 00264
cert_compatibility_data_join_2 00280 00290 280 290 288 00288
theorem compatibility_data_join_00272_00290 : FiniteChecks.Interval compatibilityTest 272 290 :=
  FiniteChecks.interval_append compatibilityTest 272 280 290 compatibility_data_00272 compatibility_data_join_00280_00290

cert_compatibility_data_join 00256 00290 256 290 272 00272
cert_compatibility_data_join 00216 00290 216 290 256 00256
cert_compatibility_data_join 00144 00290 144 290 216 00216
cert_compatibility_data_join 00000 00290 0 290 144 00144
cert_terminal_data 00000 0 8 8
cert_terminal_data 00008 8 16 8
cert_terminal_data 00016 16 24 8
cert_terminal_data 00024 24 32 8
cert_terminal_data 00032 32 40 8
cert_terminal_data 00040 40 48 8
cert_terminal_data 00048 48 56 8
cert_terminal_data 00056 56 64 8
cert_terminal_data 00064 64 72 8
cert_terminal_data 00072 72 80 8
cert_terminal_data 00080 80 88 8
cert_terminal_data 00088 88 96 8
cert_terminal_data 00096 96 104 8
cert_terminal_data 00104 104 112 8
cert_terminal_data 00112 112 120 8
cert_terminal_data 00120 120 128 8
cert_terminal_data 00128 128 136 8
cert_terminal_data 00136 136 144 8
cert_terminal_data 00144 144 152 8
cert_terminal_data 00152 152 160 8
cert_terminal_data 00160 160 168 8
cert_terminal_data 00168 168 176 8
cert_terminal_data 00176 176 184 8
cert_terminal_data 00184 184 192 8
cert_terminal_data 00192 192 200 8
cert_terminal_data 00200 200 208 8
cert_terminal_data 00208 208 216 8
cert_terminal_data 00216 216 224 8
cert_terminal_data 00224 224 232 8
cert_terminal_data 00232 232 240 8
cert_terminal_data 00240 240 248 8
cert_terminal_data 00248 248 256 8
cert_terminal_data 00256 256 264 8
cert_terminal_data 00264 264 272 8
cert_terminal_data 00272 272 280 8
cert_terminal_data 00280 280 288 8
cert_terminal_data 00288 288 296 8
cert_terminal_data 00296 296 304 8
cert_terminal_data 00304 304 312 8
cert_terminal_data 00312 312 320 8
cert_terminal_data 00320 320 328 8
cert_terminal_data 00328 328 336 8
cert_terminal_data 00336 336 344 8
cert_terminal_data 00344 344 352 8
cert_terminal_data 00352 352 360 8
theorem terminal_data_00360 : FiniteChecks.Interval terminalTest 360 368 :=
  FiniteChecks.interval_of_check terminalTest 360 8 (by decide +kernel)


end Papers.RationalityTen.ConcretePolygonClassification.N7
