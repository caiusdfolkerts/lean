module
prelude
public meta import LowerSchemas.FinitePolygonN
public import PolygonN7DAGTests

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PolygonGrowth.N7
open Papers.RationalityTen GrowthDAG SparseGrowthDAG GrowthPruning FiniteChecks

cert_nodes_part 000 00000 0 8 8
cert_nodes_part 000 00008 8 16 8
cert_nodes_part 000 00016 16 24 8
cert_nodes_part 000 00024 24 32 8
cert_nodes_part 000 00032 32 40 8
cert_nodes_part 000 00040 40 48 8
cert_nodes_part 000 00048 48 56 8
cert_nodes_part 000 00056 56 64 8
cert_nodes_part 000 00064 64 72 8
cert_nodes_part 000 00072 72 80 8
cert_nodes_part 000 00080 80 88 8
cert_nodes_part 000 00088 88 96 8
cert_nodes_part 000 00096 96 104 8
cert_nodes_part 000 00104 104 112 8
cert_nodes_part 000 00112 112 120 8
cert_nodes_part 000 00120 120 128 8
cert_nodes_part 000 00128 128 136 8
cert_nodes_part 000 00136 136 144 8
cert_nodes_part 000 00144 144 152 8
cert_nodes_part 000 00152 152 160 8
cert_nodes_part 000 00160 160 168 8
cert_nodes_part 000 00168 168 176 8
cert_nodes_part 000 00176 176 184 8
cert_nodes_part 000 00184 184 192 8
cert_nodes_part 000 00192 192 200 8
cert_nodes_part 000 00200 200 208 8
cert_nodes_part 000 00208 208 216 8
cert_nodes_part 000 00216 216 224 8
cert_nodes_part 000 00224 224 232 8
cert_nodes_part 000 00232 232 240 8
cert_nodes_part 000 00240 240 248 8
cert_nodes_part 000 00248 248 256 8
cert_nodes_part_join_2 000 00000 00016 0 16 8 00008
cert_nodes_part_join_2 000 00016 00032 16 32 24 00024
cert_nodes_part_join 000 00000 00032 0 32 16 00016
cert_nodes_part_join_2 000 00032 00048 32 48 40 00040
cert_nodes_part_join_2 000 00048 00064 48 64 56 00056
cert_nodes_part_join 000 00032 00064 32 64 48 00048
cert_nodes_part_join 000 00000 00064 0 64 32 00032
cert_nodes_part_join_2 000 00064 00080 64 80 72 00072
cert_nodes_part_join_2 000 00080 00096 80 96 88 00088
cert_nodes_part_join 000 00064 00096 64 96 80 00080
cert_nodes_part_join_2 000 00096 00112 96 112 104 00104
cert_nodes_part_join_2 000 00112 00128 112 128 120 00120
cert_nodes_part_join 000 00096 00128 96 128 112 00112
cert_nodes_part_join 000 00064 00128 64 128 96 00096
cert_nodes_part_join 000 00000 00128 0 128 64 00064
cert_nodes_part_join_2 000 00128 00144 128 144 136 00136
cert_nodes_part_join_2 000 00144 00160 144 160 152 00152
cert_nodes_part_join 000 00128 00160 128 160 144 00144
cert_nodes_part_join_2 000 00160 00176 160 176 168 00168
cert_nodes_part_join_2 000 00176 00192 176 192 184 00184
cert_nodes_part_join 000 00160 00192 160 192 176 00176
cert_nodes_part_join 000 00128 00192 128 192 160 00160
cert_nodes_part_join_2 000 00192 00208 192 208 200 00200
cert_nodes_part_join_2 000 00208 00224 208 224 216 00216
cert_nodes_part_join 000 00192 00224 192 224 208 00208
cert_nodes_part_join_2 000 00224 00240 224 240 232 00232
cert_nodes_part_join_2 000 00240 00256 240 256 248 00248
cert_nodes_part_join 000 00224 00256 224 256 240 00240
cert_nodes_part_join 000 00192 00256 192 256 224 00224
cert_nodes_part_join 000 00128 00256 128 256 192 00192
cert_nodes_part_join 000 00000 00256 0 256 128 00128
end Papers.RationalityTen.PolygonGrowth.N7
