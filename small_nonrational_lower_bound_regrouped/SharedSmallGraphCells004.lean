module
prelude
public import SharedSmallGraphData

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cells_004_b1024 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1024 1032 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1024 8 (by decide +kernel)

theorem cells_004_b1032 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1032 1040 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1032 8 (by decide +kernel)

theorem cells_004_b1040 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1040 1048 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1040 8 (by decide +kernel)

theorem cells_004_b1048 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1048 1056 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1048 8 (by decide +kernel)

theorem cells_004_b1056 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1056 1064 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1056 8 (by decide +kernel)

theorem cells_004_b1064 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1064 1072 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1064 8 (by decide +kernel)

theorem cells_004_b1072 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1072 1080 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1072 8 (by decide +kernel)

theorem cells_004_b1080 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1080 1088 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1080 8 (by decide +kernel)

theorem cells_004_b1088 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1088 1096 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1088 8 (by decide +kernel)

theorem cells_004_b1096 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1096 1104 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1096 8 (by decide +kernel)

theorem cells_004_b1104 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1104 1112 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1104 8 (by decide +kernel)

theorem cells_004_b1112 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1112 1120 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1112 8 (by decide +kernel)

theorem cells_004_b1120 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1120 1128 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1120 8 (by decide +kernel)

theorem cells_004_b1128 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1128 1136 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1128 8 (by decide +kernel)

theorem cells_004_b1136 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1136 1144 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1136 8 (by decide +kernel)

theorem cells_004_b1144 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1144 1152 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1144 8 (by decide +kernel)

theorem cells_004_b1152 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1152 1160 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1152 8 (by decide +kernel)

theorem cells_004_b1160 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1160 1168 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1160 8 (by decide +kernel)

theorem cells_004_b1168 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1168 1176 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1168 8 (by decide +kernel)

theorem cells_004_b1176 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1176 1184 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1176 8 (by decide +kernel)

theorem cells_004_b1184 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1184 1192 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1184 8 (by decide +kernel)

theorem cells_004_b1192 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1192 1200 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1192 8 (by decide +kernel)

theorem cells_004_b1200 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1200 1208 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1200 8 (by decide +kernel)

theorem cells_004_b1208 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1208 1216 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1208 8 (by decide +kernel)

theorem cells_004_b1216 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1216 1224 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1216 8 (by decide +kernel)

theorem cells_004_b1224 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1224 1232 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1224 8 (by decide +kernel)

theorem cells_004_b1232 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1232 1240 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1232 8 (by decide +kernel)

theorem cells_004_b1240 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1240 1248 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1240 8 (by decide +kernel)

theorem cells_004_b1248 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1248 1256 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1248 8 (by decide +kernel)

theorem cells_004_b1256 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1256 1264 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1256 8 (by decide +kernel)

theorem cells_004_b1264 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1264 1272 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1264 8 (by decide +kernel)

theorem cells_004_b1272 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1272 1280 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1272 8 (by decide +kernel)

theorem cells_004 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1024 1280 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1024 1152 1280
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1024 1088 1152
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1024 1056 1088
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1024 1040 1056
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1024 1032 1040
 cells_004_b1024
 cells_004_b1032)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1040 1048 1056
 cells_004_b1040
 cells_004_b1048))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1056 1072 1088
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1056 1064 1072
 cells_004_b1056
 cells_004_b1064)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1072 1080 1088
 cells_004_b1072
 cells_004_b1080)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1088 1120 1152
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1088 1104 1120
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1088 1096 1104
 cells_004_b1088
 cells_004_b1096)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1104 1112 1120
 cells_004_b1104
 cells_004_b1112))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1120 1136 1152
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1120 1128 1136
 cells_004_b1120
 cells_004_b1128)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1136 1144 1152
 cells_004_b1136
 cells_004_b1144))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1152 1216 1280
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1152 1184 1216
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1152 1168 1184
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1152 1160 1168
 cells_004_b1152
 cells_004_b1160)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1168 1176 1184
 cells_004_b1168
 cells_004_b1176))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1184 1200 1216
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1184 1192 1200
 cells_004_b1184
 cells_004_b1192)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1200 1208 1216
 cells_004_b1200
 cells_004_b1208)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1216 1248 1280
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1216 1232 1248
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1216 1224 1232
 cells_004_b1216
 cells_004_b1224)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1232 1240 1248
 cells_004_b1232
 cells_004_b1240))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1248 1264 1280
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1248 1256 1264
 cells_004_b1248
 cells_004_b1256)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1264 1272 1280
 cells_004_b1264
 cells_004_b1272)))))
end Papers.RationalityTen.SharedSmallGraph
