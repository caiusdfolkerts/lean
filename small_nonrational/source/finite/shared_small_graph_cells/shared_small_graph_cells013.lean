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
theorem cells_013_b3328 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 3336 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 8 (by decide +kernel)

theorem cells_013_b3336 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3336 3344 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3336 8 (by decide +kernel)

theorem cells_013_b3344 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3344 3352 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3344 8 (by decide +kernel)

theorem cells_013_b3352 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3352 3360 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3352 8 (by decide +kernel)

theorem cells_013_b3360 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3360 3368 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3360 8 (by decide +kernel)

theorem cells_013_b3368 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3368 3376 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3368 8 (by decide +kernel)

theorem cells_013_b3376 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3376 3384 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3376 8 (by decide +kernel)

theorem cells_013_b3384 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3384 3392 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3384 8 (by decide +kernel)

theorem cells_013_b3392 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3392 3400 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3392 8 (by decide +kernel)

theorem cells_013_b3400 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3400 3408 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3400 8 (by decide +kernel)

theorem cells_013_b3408 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3408 3416 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3408 8 (by decide +kernel)

theorem cells_013_b3416 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3416 3424 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3416 8 (by decide +kernel)

theorem cells_013_b3424 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3424 3432 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3424 8 (by decide +kernel)

theorem cells_013_b3432 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3432 3440 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3432 8 (by decide +kernel)

theorem cells_013_b3440 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3440 3448 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3440 8 (by decide +kernel)

theorem cells_013_b3448 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3448 3456 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3448 8 (by decide +kernel)

theorem cells_013_b3456 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3456 3464 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3456 8 (by decide +kernel)

theorem cells_013_b3464 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3464 3472 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3464 8 (by decide +kernel)

theorem cells_013_b3472 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3472 3480 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3472 8 (by decide +kernel)

theorem cells_013_b3480 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3480 3488 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3480 8 (by decide +kernel)

theorem cells_013_b3488 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3488 3496 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3488 8 (by decide +kernel)

theorem cells_013_b3496 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3496 3504 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3496 8 (by decide +kernel)

theorem cells_013_b3504 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3504 3512 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3504 8 (by decide +kernel)

theorem cells_013_b3512 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3512 3520 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3512 8 (by decide +kernel)

theorem cells_013_b3520 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3520 3528 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3520 8 (by decide +kernel)

theorem cells_013_b3528 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3528 3536 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3528 8 (by decide +kernel)

theorem cells_013_b3536 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3536 3544 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3536 8 (by decide +kernel)

theorem cells_013_b3544 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3544 3552 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3544 8 (by decide +kernel)

theorem cells_013_b3552 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3552 3560 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3552 8 (by decide +kernel)

theorem cells_013_b3560 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3560 3568 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3560 8 (by decide +kernel)

theorem cells_013_b3568 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3568 3576 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3568 8 (by decide +kernel)

theorem cells_013_b3576 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3576 3584 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3576 8 (by decide +kernel)

theorem cells_013 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 3584 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 3456 3584
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 3392 3456
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 3360 3392
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 3344 3360
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3328 3336 3344
 cells_013_b3328
 cells_013_b3336)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3344 3352 3360
 cells_013_b3344
 cells_013_b3352))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3360 3376 3392
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3360 3368 3376
 cells_013_b3360
 cells_013_b3368)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3376 3384 3392
 cells_013_b3376
 cells_013_b3384)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3392 3424 3456
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3392 3408 3424
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3392 3400 3408
 cells_013_b3392
 cells_013_b3400)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3408 3416 3424
 cells_013_b3408
 cells_013_b3416))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3424 3440 3456
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3424 3432 3440
 cells_013_b3424
 cells_013_b3432)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3440 3448 3456
 cells_013_b3440
 cells_013_b3448))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3456 3520 3584
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3456 3488 3520
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3456 3472 3488
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3456 3464 3472
 cells_013_b3456
 cells_013_b3464)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3472 3480 3488
 cells_013_b3472
 cells_013_b3480))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3488 3504 3520
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3488 3496 3504
 cells_013_b3488
 cells_013_b3496)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3504 3512 3520
 cells_013_b3504
 cells_013_b3512)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3520 3552 3584
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3520 3536 3552
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3520 3528 3536
 cells_013_b3520
 cells_013_b3528)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3536 3544 3552
 cells_013_b3536
 cells_013_b3544))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3552 3568 3584
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3552 3560 3568
 cells_013_b3552
 cells_013_b3560)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3568 3576 3584
 cells_013_b3568
 cells_013_b3576)))))
end Papers.RationalityTen.SharedSmallGraph
