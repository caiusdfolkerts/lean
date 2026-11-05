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
theorem cells_020_b5120 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5120 5128 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5120 8 (by decide +kernel)

theorem cells_020_b5128 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5128 5136 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5128 8 (by decide +kernel)

theorem cells_020_b5136 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5136 5144 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5136 8 (by decide +kernel)

theorem cells_020_b5144 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5144 5152 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5144 8 (by decide +kernel)

theorem cells_020_b5152 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5152 5160 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5152 8 (by decide +kernel)

theorem cells_020_b5160 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5160 5168 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5160 8 (by decide +kernel)

theorem cells_020_b5168 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5168 5176 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5168 8 (by decide +kernel)

theorem cells_020_b5176 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5176 5184 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5176 8 (by decide +kernel)

theorem cells_020_b5184 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5184 5192 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5184 8 (by decide +kernel)

theorem cells_020_b5192 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5192 5200 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5192 8 (by decide +kernel)

theorem cells_020_b5200 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5200 5208 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5200 8 (by decide +kernel)

theorem cells_020_b5208 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5208 5216 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5208 8 (by decide +kernel)

theorem cells_020_b5216 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5216 5224 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5216 8 (by decide +kernel)

theorem cells_020_b5224 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5224 5232 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5224 8 (by decide +kernel)

theorem cells_020_b5232 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5232 5240 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5232 8 (by decide +kernel)

theorem cells_020_b5240 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5240 5248 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5240 8 (by decide +kernel)

theorem cells_020_b5248 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5248 5256 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5248 8 (by decide +kernel)

theorem cells_020_b5256 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5256 5264 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5256 8 (by decide +kernel)

theorem cells_020_b5264 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5264 5272 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5264 8 (by decide +kernel)

theorem cells_020_b5272 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5272 5280 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5272 8 (by decide +kernel)

theorem cells_020_b5280 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5280 5288 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5280 8 (by decide +kernel)

theorem cells_020_b5288 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5288 5296 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5288 8 (by decide +kernel)

theorem cells_020_b5296 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5296 5304 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5296 8 (by decide +kernel)

theorem cells_020_b5304 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5304 5312 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5304 8 (by decide +kernel)

theorem cells_020_b5312 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5312 5320 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5312 8 (by decide +kernel)

theorem cells_020_b5320 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5320 5328 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5320 8 (by decide +kernel)

theorem cells_020_b5328 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5328 5336 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5328 8 (by decide +kernel)

theorem cells_020_b5336 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5336 5344 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5336 8 (by decide +kernel)

theorem cells_020_b5344 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5344 5352 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5344 8 (by decide +kernel)

theorem cells_020_b5352 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5352 5360 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5352 8 (by decide +kernel)

theorem cells_020_b5360 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5360 5368 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5360 8 (by decide +kernel)

theorem cells_020_b5368 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5368 5376 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5368 8 (by decide +kernel)

theorem cells_020 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5120 5376 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5120 5248 5376
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5120 5184 5248
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5120 5152 5184
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5120 5136 5152
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5120 5128 5136
 cells_020_b5120
 cells_020_b5128)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5136 5144 5152
 cells_020_b5136
 cells_020_b5144))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5152 5168 5184
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5152 5160 5168
 cells_020_b5152
 cells_020_b5160)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5168 5176 5184
 cells_020_b5168
 cells_020_b5176)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5184 5216 5248
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5184 5200 5216
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5184 5192 5200
 cells_020_b5184
 cells_020_b5192)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5200 5208 5216
 cells_020_b5200
 cells_020_b5208))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5216 5232 5248
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5216 5224 5232
 cells_020_b5216
 cells_020_b5224)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5232 5240 5248
 cells_020_b5232
 cells_020_b5240))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5248 5312 5376
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5248 5280 5312
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5248 5264 5280
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5248 5256 5264
 cells_020_b5248
 cells_020_b5256)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5264 5272 5280
 cells_020_b5264
 cells_020_b5272))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5280 5296 5312
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5280 5288 5296
 cells_020_b5280
 cells_020_b5288)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5296 5304 5312
 cells_020_b5296
 cells_020_b5304)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5312 5344 5376
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5312 5328 5344
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5312 5320 5328
 cells_020_b5312
 cells_020_b5320)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5328 5336 5344
 cells_020_b5328
 cells_020_b5336))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5344 5360 5376
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5344 5352 5360
 cells_020_b5344
 cells_020_b5352)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5360 5368 5376
 cells_020_b5360
 cells_020_b5368)))))
end Papers.RationalityTen.SharedSmallGraph
