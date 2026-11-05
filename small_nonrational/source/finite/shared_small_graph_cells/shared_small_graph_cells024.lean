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
theorem cells_024_b6144 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6144 6152 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6144 8 (by decide +kernel)

theorem cells_024_b6152 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6152 6160 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6152 8 (by decide +kernel)

theorem cells_024_b6160 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6160 6168 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6160 8 (by decide +kernel)

theorem cells_024_b6168 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6168 6176 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6168 8 (by decide +kernel)

theorem cells_024_b6176 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6176 6184 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6176 8 (by decide +kernel)

theorem cells_024_b6184 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6184 6192 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6184 8 (by decide +kernel)

theorem cells_024_b6192 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6192 6200 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6192 8 (by decide +kernel)

theorem cells_024_b6200 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6200 6208 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6200 8 (by decide +kernel)

theorem cells_024_b6208 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6208 6216 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6208 8 (by decide +kernel)

theorem cells_024_b6216 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6216 6224 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6216 8 (by decide +kernel)

theorem cells_024_b6224 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6224 6232 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6224 8 (by decide +kernel)

theorem cells_024_b6232 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6232 6240 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6232 8 (by decide +kernel)

theorem cells_024_b6240 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6240 6248 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6240 8 (by decide +kernel)

theorem cells_024_b6248 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6248 6256 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6248 8 (by decide +kernel)

theorem cells_024_b6256 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6256 6264 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6256 8 (by decide +kernel)

theorem cells_024_b6264 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6264 6272 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6264 8 (by decide +kernel)

theorem cells_024_b6272 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6272 6280 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6272 8 (by decide +kernel)

theorem cells_024_b6280 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6280 6288 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6280 8 (by decide +kernel)

theorem cells_024_b6288 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6288 6296 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6288 8 (by decide +kernel)

theorem cells_024_b6296 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6296 6304 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6296 8 (by decide +kernel)

theorem cells_024_b6304 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6304 6312 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6304 8 (by decide +kernel)

theorem cells_024_b6312 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6312 6320 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6312 8 (by decide +kernel)

theorem cells_024_b6320 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6320 6328 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6320 8 (by decide +kernel)

theorem cells_024_b6328 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6328 6336 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6328 8 (by decide +kernel)

theorem cells_024_b6336 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6336 6344 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6336 8 (by decide +kernel)

theorem cells_024_b6344 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6344 6352 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6344 8 (by decide +kernel)

theorem cells_024_b6352 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6352 6360 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6352 8 (by decide +kernel)

theorem cells_024_b6360 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6360 6368 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6360 8 (by decide +kernel)

theorem cells_024_b6368 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6368 6376 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6368 8 (by decide +kernel)

theorem cells_024_b6376 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6376 6384 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6376 8 (by decide +kernel)

theorem cells_024_b6384 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6384 6392 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6384 8 (by decide +kernel)

theorem cells_024_b6392 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6392 6400 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6392 8 (by decide +kernel)

theorem cells_024 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6144 6400 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6144 6272 6400
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6144 6208 6272
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6144 6176 6208
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6144 6160 6176
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6144 6152 6160
 cells_024_b6144
 cells_024_b6152)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6160 6168 6176
 cells_024_b6160
 cells_024_b6168))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6176 6192 6208
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6176 6184 6192
 cells_024_b6176
 cells_024_b6184)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6192 6200 6208
 cells_024_b6192
 cells_024_b6200)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6208 6240 6272
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6208 6224 6240
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6208 6216 6224
 cells_024_b6208
 cells_024_b6216)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6224 6232 6240
 cells_024_b6224
 cells_024_b6232))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6240 6256 6272
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6240 6248 6256
 cells_024_b6240
 cells_024_b6248)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6256 6264 6272
 cells_024_b6256
 cells_024_b6264))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6272 6336 6400
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6272 6304 6336
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6272 6288 6304
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6272 6280 6288
 cells_024_b6272
 cells_024_b6280)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6288 6296 6304
 cells_024_b6288
 cells_024_b6296))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6304 6320 6336
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6304 6312 6320
 cells_024_b6304
 cells_024_b6312)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6320 6328 6336
 cells_024_b6320
 cells_024_b6328)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6336 6368 6400
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6336 6352 6368
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6336 6344 6352
 cells_024_b6336
 cells_024_b6344)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6352 6360 6368
 cells_024_b6352
 cells_024_b6360))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6368 6384 6400
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6368 6376 6384
 cells_024_b6368
 cells_024_b6376)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6384 6392 6400
 cells_024_b6384
 cells_024_b6392)))))
end Papers.RationalityTen.SharedSmallGraph
