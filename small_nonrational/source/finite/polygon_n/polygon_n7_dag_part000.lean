module
prelude
public import PolygonN7DAGTests

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

theorem nodes_part000_00000 : FiniteChecks.Interval nodeTest 0 8 :=
  FiniteChecks.interval_of_check nodeTest 0 8 (by decide +kernel)

theorem nodes_part000_00008 : FiniteChecks.Interval nodeTest 8 16 :=
  FiniteChecks.interval_of_check nodeTest 8 8 (by decide +kernel)

theorem nodes_part000_00016 : FiniteChecks.Interval nodeTest 16 24 :=
  FiniteChecks.interval_of_check nodeTest 16 8 (by decide +kernel)

theorem nodes_part000_00024 : FiniteChecks.Interval nodeTest 24 32 :=
  FiniteChecks.interval_of_check nodeTest 24 8 (by decide +kernel)

theorem nodes_part000_00032 : FiniteChecks.Interval nodeTest 32 40 :=
  FiniteChecks.interval_of_check nodeTest 32 8 (by decide +kernel)

theorem nodes_part000_00040 : FiniteChecks.Interval nodeTest 40 48 :=
  FiniteChecks.interval_of_check nodeTest 40 8 (by decide +kernel)

theorem nodes_part000_00048 : FiniteChecks.Interval nodeTest 48 56 :=
  FiniteChecks.interval_of_check nodeTest 48 8 (by decide +kernel)

theorem nodes_part000_00056 : FiniteChecks.Interval nodeTest 56 64 :=
  FiniteChecks.interval_of_check nodeTest 56 8 (by decide +kernel)

theorem nodes_part000_00064 : FiniteChecks.Interval nodeTest 64 72 :=
  FiniteChecks.interval_of_check nodeTest 64 8 (by decide +kernel)

theorem nodes_part000_00072 : FiniteChecks.Interval nodeTest 72 80 :=
  FiniteChecks.interval_of_check nodeTest 72 8 (by decide +kernel)

theorem nodes_part000_00080 : FiniteChecks.Interval nodeTest 80 88 :=
  FiniteChecks.interval_of_check nodeTest 80 8 (by decide +kernel)

theorem nodes_part000_00088 : FiniteChecks.Interval nodeTest 88 96 :=
  FiniteChecks.interval_of_check nodeTest 88 8 (by decide +kernel)

theorem nodes_part000_00096 : FiniteChecks.Interval nodeTest 96 104 :=
  FiniteChecks.interval_of_check nodeTest 96 8 (by decide +kernel)

theorem nodes_part000_00104 : FiniteChecks.Interval nodeTest 104 112 :=
  FiniteChecks.interval_of_check nodeTest 104 8 (by decide +kernel)

theorem nodes_part000_00112 : FiniteChecks.Interval nodeTest 112 120 :=
  FiniteChecks.interval_of_check nodeTest 112 8 (by decide +kernel)

theorem nodes_part000_00120 : FiniteChecks.Interval nodeTest 120 128 :=
  FiniteChecks.interval_of_check nodeTest 120 8 (by decide +kernel)

theorem nodes_part000_00128 : FiniteChecks.Interval nodeTest 128 136 :=
  FiniteChecks.interval_of_check nodeTest 128 8 (by decide +kernel)

theorem nodes_part000_00136 : FiniteChecks.Interval nodeTest 136 144 :=
  FiniteChecks.interval_of_check nodeTest 136 8 (by decide +kernel)

theorem nodes_part000_00144 : FiniteChecks.Interval nodeTest 144 152 :=
  FiniteChecks.interval_of_check nodeTest 144 8 (by decide +kernel)

theorem nodes_part000_00152 : FiniteChecks.Interval nodeTest 152 160 :=
  FiniteChecks.interval_of_check nodeTest 152 8 (by decide +kernel)

theorem nodes_part000_00160 : FiniteChecks.Interval nodeTest 160 168 :=
  FiniteChecks.interval_of_check nodeTest 160 8 (by decide +kernel)

theorem nodes_part000_00168 : FiniteChecks.Interval nodeTest 168 176 :=
  FiniteChecks.interval_of_check nodeTest 168 8 (by decide +kernel)

theorem nodes_part000_00176 : FiniteChecks.Interval nodeTest 176 184 :=
  FiniteChecks.interval_of_check nodeTest 176 8 (by decide +kernel)

theorem nodes_part000_00184 : FiniteChecks.Interval nodeTest 184 192 :=
  FiniteChecks.interval_of_check nodeTest 184 8 (by decide +kernel)

theorem nodes_part000_00192 : FiniteChecks.Interval nodeTest 192 200 :=
  FiniteChecks.interval_of_check nodeTest 192 8 (by decide +kernel)

theorem nodes_part000_00200 : FiniteChecks.Interval nodeTest 200 208 :=
  FiniteChecks.interval_of_check nodeTest 200 8 (by decide +kernel)

theorem nodes_part000_00208 : FiniteChecks.Interval nodeTest 208 216 :=
  FiniteChecks.interval_of_check nodeTest 208 8 (by decide +kernel)

theorem nodes_part000_00216 : FiniteChecks.Interval nodeTest 216 224 :=
  FiniteChecks.interval_of_check nodeTest 216 8 (by decide +kernel)

theorem nodes_part000_00224 : FiniteChecks.Interval nodeTest 224 232 :=
  FiniteChecks.interval_of_check nodeTest 224 8 (by decide +kernel)

theorem nodes_part000_00232 : FiniteChecks.Interval nodeTest 232 240 :=
  FiniteChecks.interval_of_check nodeTest 232 8 (by decide +kernel)

theorem nodes_part000_00240 : FiniteChecks.Interval nodeTest 240 248 :=
  FiniteChecks.interval_of_check nodeTest 240 8 (by decide +kernel)

theorem nodes_part000_00248 : FiniteChecks.Interval nodeTest 248 256 :=
  FiniteChecks.interval_of_check nodeTest 248 8 (by decide +kernel)

theorem nodes_part000_join_00000_00016 : FiniteChecks.Interval nodeTest 0 16 :=
  FiniteChecks.interval_append nodeTest 0 8 16 nodes_part000_00000 nodes_part000_00008

theorem nodes_part000_join_00016_00032 : FiniteChecks.Interval nodeTest 16 32 :=
  FiniteChecks.interval_append nodeTest 16 24 32 nodes_part000_00016 nodes_part000_00024

theorem nodes_part000_join_00000_00032 : FiniteChecks.Interval nodeTest 0 32 :=
  FiniteChecks.interval_append nodeTest 0 16 32 nodes_part000_join_00000_00016 nodes_part000_join_00016_00032

theorem nodes_part000_join_00032_00048 : FiniteChecks.Interval nodeTest 32 48 :=
  FiniteChecks.interval_append nodeTest 32 40 48 nodes_part000_00032 nodes_part000_00040

theorem nodes_part000_join_00048_00064 : FiniteChecks.Interval nodeTest 48 64 :=
  FiniteChecks.interval_append nodeTest 48 56 64 nodes_part000_00048 nodes_part000_00056

theorem nodes_part000_join_00032_00064 : FiniteChecks.Interval nodeTest 32 64 :=
  FiniteChecks.interval_append nodeTest 32 48 64 nodes_part000_join_00032_00048 nodes_part000_join_00048_00064

theorem nodes_part000_join_00000_00064 : FiniteChecks.Interval nodeTest 0 64 :=
  FiniteChecks.interval_append nodeTest 0 32 64 nodes_part000_join_00000_00032 nodes_part000_join_00032_00064

theorem nodes_part000_join_00064_00080 : FiniteChecks.Interval nodeTest 64 80 :=
  FiniteChecks.interval_append nodeTest 64 72 80 nodes_part000_00064 nodes_part000_00072

theorem nodes_part000_join_00080_00096 : FiniteChecks.Interval nodeTest 80 96 :=
  FiniteChecks.interval_append nodeTest 80 88 96 nodes_part000_00080 nodes_part000_00088

theorem nodes_part000_join_00064_00096 : FiniteChecks.Interval nodeTest 64 96 :=
  FiniteChecks.interval_append nodeTest 64 80 96 nodes_part000_join_00064_00080 nodes_part000_join_00080_00096

theorem nodes_part000_join_00096_00112 : FiniteChecks.Interval nodeTest 96 112 :=
  FiniteChecks.interval_append nodeTest 96 104 112 nodes_part000_00096 nodes_part000_00104

theorem nodes_part000_join_00112_00128 : FiniteChecks.Interval nodeTest 112 128 :=
  FiniteChecks.interval_append nodeTest 112 120 128 nodes_part000_00112 nodes_part000_00120

theorem nodes_part000_join_00096_00128 : FiniteChecks.Interval nodeTest 96 128 :=
  FiniteChecks.interval_append nodeTest 96 112 128 nodes_part000_join_00096_00112 nodes_part000_join_00112_00128

theorem nodes_part000_join_00064_00128 : FiniteChecks.Interval nodeTest 64 128 :=
  FiniteChecks.interval_append nodeTest 64 96 128 nodes_part000_join_00064_00096 nodes_part000_join_00096_00128

theorem nodes_part000_join_00000_00128 : FiniteChecks.Interval nodeTest 0 128 :=
  FiniteChecks.interval_append nodeTest 0 64 128 nodes_part000_join_00000_00064 nodes_part000_join_00064_00128

theorem nodes_part000_join_00128_00144 : FiniteChecks.Interval nodeTest 128 144 :=
  FiniteChecks.interval_append nodeTest 128 136 144 nodes_part000_00128 nodes_part000_00136

theorem nodes_part000_join_00144_00160 : FiniteChecks.Interval nodeTest 144 160 :=
  FiniteChecks.interval_append nodeTest 144 152 160 nodes_part000_00144 nodes_part000_00152

theorem nodes_part000_join_00128_00160 : FiniteChecks.Interval nodeTest 128 160 :=
  FiniteChecks.interval_append nodeTest 128 144 160 nodes_part000_join_00128_00144 nodes_part000_join_00144_00160

theorem nodes_part000_join_00160_00176 : FiniteChecks.Interval nodeTest 160 176 :=
  FiniteChecks.interval_append nodeTest 160 168 176 nodes_part000_00160 nodes_part000_00168

theorem nodes_part000_join_00176_00192 : FiniteChecks.Interval nodeTest 176 192 :=
  FiniteChecks.interval_append nodeTest 176 184 192 nodes_part000_00176 nodes_part000_00184

theorem nodes_part000_join_00160_00192 : FiniteChecks.Interval nodeTest 160 192 :=
  FiniteChecks.interval_append nodeTest 160 176 192 nodes_part000_join_00160_00176 nodes_part000_join_00176_00192

theorem nodes_part000_join_00128_00192 : FiniteChecks.Interval nodeTest 128 192 :=
  FiniteChecks.interval_append nodeTest 128 160 192 nodes_part000_join_00128_00160 nodes_part000_join_00160_00192

theorem nodes_part000_join_00192_00208 : FiniteChecks.Interval nodeTest 192 208 :=
  FiniteChecks.interval_append nodeTest 192 200 208 nodes_part000_00192 nodes_part000_00200

theorem nodes_part000_join_00208_00224 : FiniteChecks.Interval nodeTest 208 224 :=
  FiniteChecks.interval_append nodeTest 208 216 224 nodes_part000_00208 nodes_part000_00216

theorem nodes_part000_join_00192_00224 : FiniteChecks.Interval nodeTest 192 224 :=
  FiniteChecks.interval_append nodeTest 192 208 224 nodes_part000_join_00192_00208 nodes_part000_join_00208_00224

theorem nodes_part000_join_00224_00240 : FiniteChecks.Interval nodeTest 224 240 :=
  FiniteChecks.interval_append nodeTest 224 232 240 nodes_part000_00224 nodes_part000_00232

theorem nodes_part000_join_00240_00256 : FiniteChecks.Interval nodeTest 240 256 :=
  FiniteChecks.interval_append nodeTest 240 248 256 nodes_part000_00240 nodes_part000_00248

theorem nodes_part000_join_00224_00256 : FiniteChecks.Interval nodeTest 224 256 :=
  FiniteChecks.interval_append nodeTest 224 240 256 nodes_part000_join_00224_00240 nodes_part000_join_00240_00256

theorem nodes_part000_join_00192_00256 : FiniteChecks.Interval nodeTest 192 256 :=
  FiniteChecks.interval_append nodeTest 192 224 256 nodes_part000_join_00192_00224 nodes_part000_join_00224_00256

theorem nodes_part000_join_00128_00256 : FiniteChecks.Interval nodeTest 128 256 :=
  FiniteChecks.interval_append nodeTest 128 192 256 nodes_part000_join_00128_00192 nodes_part000_join_00192_00256

theorem nodes_part000_join_00000_00256 : FiniteChecks.Interval nodeTest 0 256 :=
  FiniteChecks.interval_append nodeTest 0 128 256 nodes_part000_join_00000_00128 nodes_part000_join_00128_00256

end Papers.RationalityTen.PolygonGrowth.N7
