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
theorem cells_025_b6400 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6400 6408 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6400 8 (by decide +kernel)

theorem cells_025_b6408 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6408 6416 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6408 8 (by decide +kernel)

theorem cells_025_b6416 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6416 6424 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6416 8 (by decide +kernel)

theorem cells_025_b6424 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6424 6432 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6424 8 (by decide +kernel)

theorem cells_025_b6432 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6432 6440 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6432 8 (by decide +kernel)

theorem cells_025_b6440 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6440 6448 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6440 8 (by decide +kernel)

theorem cells_025_b6448 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6448 6456 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6448 8 (by decide +kernel)

theorem cells_025_b6456 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6456 6464 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6456 8 (by decide +kernel)

theorem cells_025_b6464 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6464 6472 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6464 8 (by decide +kernel)

theorem cells_025_b6472 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6472 6480 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6472 8 (by decide +kernel)

theorem cells_025_b6480 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6480 6488 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6480 8 (by decide +kernel)

theorem cells_025_b6488 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6488 6496 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6488 8 (by decide +kernel)

theorem cells_025_b6496 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6496 6504 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6496 8 (by decide +kernel)

theorem cells_025_b6504 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6504 6510 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6504 6 (by decide +kernel)

theorem cells_025 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6400 6510 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6400 6456 6510
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6400 6424 6456
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6400 6408 6424
 cells_025_b6400
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6408 6416 6424
 cells_025_b6408
 cells_025_b6416))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6424 6440 6456
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6424 6432 6440
 cells_025_b6424
 cells_025_b6432)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6440 6448 6456
 cells_025_b6440
 cells_025_b6448)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6456 6480 6510
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6456 6464 6480
 cells_025_b6456
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6464 6472 6480
 cells_025_b6464
 cells_025_b6472))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6480 6496 6510
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6480 6488 6496
 cells_025_b6480
 cells_025_b6488)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6496 6504 6510
 cells_025_b6496
 cells_025_b6504))))
end Papers.RationalityTen.SharedSmallGraph
