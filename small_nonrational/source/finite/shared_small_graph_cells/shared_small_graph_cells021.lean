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
theorem cells_021_b5376 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5376 5384 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5376 8 (by decide +kernel)

theorem cells_021_b5384 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5384 5392 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5384 8 (by decide +kernel)

theorem cells_021_b5392 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5392 5400 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5392 8 (by decide +kernel)

theorem cells_021_b5400 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5400 5408 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5400 8 (by decide +kernel)

theorem cells_021_b5408 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5408 5416 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5408 8 (by decide +kernel)

theorem cells_021_b5416 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5416 5424 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5416 8 (by decide +kernel)

theorem cells_021_b5424 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5424 5432 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5424 8 (by decide +kernel)

theorem cells_021_b5432 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5432 5440 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5432 8 (by decide +kernel)

theorem cells_021_b5440 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5440 5448 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5440 8 (by decide +kernel)

theorem cells_021_b5448 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5448 5456 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5448 8 (by decide +kernel)

theorem cells_021_b5456 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5456 5464 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5456 8 (by decide +kernel)

theorem cells_021_b5464 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5464 5472 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5464 8 (by decide +kernel)

theorem cells_021_b5472 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5472 5480 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5472 8 (by decide +kernel)

theorem cells_021_b5480 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5480 5488 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5480 8 (by decide +kernel)

theorem cells_021_b5488 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5488 5496 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5488 8 (by decide +kernel)

theorem cells_021_b5496 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5496 5504 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5496 8 (by decide +kernel)

theorem cells_021_b5504 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5504 5512 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5504 8 (by decide +kernel)

theorem cells_021_b5512 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5512 5520 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5512 8 (by decide +kernel)

theorem cells_021_b5520 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5520 5528 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5520 8 (by decide +kernel)

theorem cells_021_b5528 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5528 5536 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5528 8 (by decide +kernel)

theorem cells_021_b5536 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5536 5544 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5536 8 (by decide +kernel)

theorem cells_021_b5544 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5544 5552 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5544 8 (by decide +kernel)

theorem cells_021_b5552 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5552 5560 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5552 8 (by decide +kernel)

theorem cells_021_b5560 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5560 5568 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5560 8 (by decide +kernel)

theorem cells_021_b5568 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5568 5576 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5568 8 (by decide +kernel)

theorem cells_021_b5576 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5576 5584 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5576 8 (by decide +kernel)

theorem cells_021_b5584 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5584 5592 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5584 8 (by decide +kernel)

theorem cells_021_b5592 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5592 5600 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5592 8 (by decide +kernel)

theorem cells_021_b5600 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5600 5608 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5600 8 (by decide +kernel)

theorem cells_021_b5608 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5608 5616 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5608 8 (by decide +kernel)

theorem cells_021_b5616 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5616 5624 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5616 8 (by decide +kernel)

theorem cells_021_b5624 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5624 5632 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5624 8 (by decide +kernel)

theorem cells_021 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5376 5632 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5376 5504 5632
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5376 5440 5504
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5376 5408 5440
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5376 5392 5408
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5376 5384 5392
 cells_021_b5376
 cells_021_b5384)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5392 5400 5408
 cells_021_b5392
 cells_021_b5400))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5408 5424 5440
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5408 5416 5424
 cells_021_b5408
 cells_021_b5416)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5424 5432 5440
 cells_021_b5424
 cells_021_b5432)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5440 5472 5504
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5440 5456 5472
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5440 5448 5456
 cells_021_b5440
 cells_021_b5448)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5456 5464 5472
 cells_021_b5456
 cells_021_b5464))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5472 5488 5504
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5472 5480 5488
 cells_021_b5472
 cells_021_b5480)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5488 5496 5504
 cells_021_b5488
 cells_021_b5496))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5504 5568 5632
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5504 5536 5568
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5504 5520 5536
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5504 5512 5520
 cells_021_b5504
 cells_021_b5512)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5520 5528 5536
 cells_021_b5520
 cells_021_b5528))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5536 5552 5568
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5536 5544 5552
 cells_021_b5536
 cells_021_b5544)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5552 5560 5568
 cells_021_b5552
 cells_021_b5560)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5568 5600 5632
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5568 5584 5600
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5568 5576 5584
 cells_021_b5568
 cells_021_b5576)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5584 5592 5600
 cells_021_b5584
 cells_021_b5592))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5600 5616 5632
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5600 5608 5616
 cells_021_b5600
 cells_021_b5608)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5616 5624 5632
 cells_021_b5616
 cells_021_b5624)))))
end Papers.RationalityTen.SharedSmallGraph
