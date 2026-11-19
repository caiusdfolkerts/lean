module
prelude
public import SharedSmallGraphCells000
public import SharedSmallGraphCells001
public import SharedSmallGraphCells002
public import SharedSmallGraphCells003
public import SharedSmallGraphCells004
public import SharedSmallGraphCells005
public import SharedSmallGraphCells006
public import SharedSmallGraphCells007
public import SharedSmallGraphCells008
public import SharedSmallGraphCells009
public import SharedSmallGraphCells010
public import SharedSmallGraphCells011
public import SharedSmallGraphCells012
public import SharedSmallGraphCells013
public import SharedSmallGraphCells014
public import SharedSmallGraphCells015
public import SharedSmallGraphCells016
public import SharedSmallGraphCells017
public import SharedSmallGraphCells018
public import SharedSmallGraphCells019
public import SharedSmallGraphCells020
public import SharedSmallGraphCells021
public import SharedSmallGraphCells022
public import SharedSmallGraphCells023
public import SharedSmallGraphCells024
public import SharedSmallGraphCells025

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cells_checked : ∀ i, cellCheck i = true :=
  fin_of_interval cellCheck
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 0 3328 6510
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 0 1536 3328
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 0 768 1536
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 0 256 768
 cells_000
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 256 512 768
 cells_001
 cells_002))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 768 1024 1536
 cells_003
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1024 1280 1536
 cells_004
 cells_005)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1536 2304 3328
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1536 1792 2304
 cells_006
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1792 2048 2304
 cells_007
 cells_008))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2304 2816 3328
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2304 2560 2816
 cells_009
 cells_010)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2816 3072 3328
 cells_011
 cells_012))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 4864 6510
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 4096 4864
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 3584 4096
 cells_013
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3584 3840 4096
 cells_014
 cells_015))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4096 4352 4864
 cells_016
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4352 4608 4864
 cells_017
 cells_018)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4864 5632 6510
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4864 5120 5632
 cells_019
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5120 5376 5632
 cells_020
 cells_021))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5632 6144 6510
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5632 5888 6144
 cells_022
 cells_023)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6144 6400 6510
 cells_024
 cells_025)))))
end Papers.RationalityTen.SharedSmallGraph
