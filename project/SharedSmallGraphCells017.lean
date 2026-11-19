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
theorem cells_017_b4352 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4352 4360 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4352 8 (by decide +kernel)

theorem cells_017_b4360 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4360 4368 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4360 8 (by decide +kernel)

theorem cells_017_b4368 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4368 4376 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4368 8 (by decide +kernel)

theorem cells_017_b4376 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4376 4384 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4376 8 (by decide +kernel)

theorem cells_017_b4384 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4384 4392 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4384 8 (by decide +kernel)

theorem cells_017_b4392 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4392 4400 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4392 8 (by decide +kernel)

theorem cells_017_b4400 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4400 4408 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4400 8 (by decide +kernel)

theorem cells_017_b4408 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4408 4416 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4408 8 (by decide +kernel)

theorem cells_017_b4416 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4416 4424 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4416 8 (by decide +kernel)

theorem cells_017_b4424 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4424 4432 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4424 8 (by decide +kernel)

theorem cells_017_b4432 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4432 4440 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4432 8 (by decide +kernel)

theorem cells_017_b4440 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4440 4448 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4440 8 (by decide +kernel)

theorem cells_017_b4448 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4448 4456 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4448 8 (by decide +kernel)

theorem cells_017_b4456 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4456 4464 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4456 8 (by decide +kernel)

theorem cells_017_b4464 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4464 4472 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4464 8 (by decide +kernel)

theorem cells_017_b4472 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4472 4480 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4472 8 (by decide +kernel)

theorem cells_017_b4480 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4480 4488 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4480 8 (by decide +kernel)

theorem cells_017_b4488 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4488 4496 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4488 8 (by decide +kernel)

theorem cells_017_b4496 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4496 4504 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4496 8 (by decide +kernel)

theorem cells_017_b4504 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4504 4512 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4504 8 (by decide +kernel)

theorem cells_017_b4512 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4512 4520 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4512 8 (by decide +kernel)

theorem cells_017_b4520 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4520 4528 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4520 8 (by decide +kernel)

theorem cells_017_b4528 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4528 4536 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4528 8 (by decide +kernel)

theorem cells_017_b4536 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4536 4544 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4536 8 (by decide +kernel)

theorem cells_017_b4544 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4544 4552 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4544 8 (by decide +kernel)

theorem cells_017_b4552 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4552 4560 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4552 8 (by decide +kernel)

theorem cells_017_b4560 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4560 4568 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4560 8 (by decide +kernel)

theorem cells_017_b4568 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4568 4576 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4568 8 (by decide +kernel)

theorem cells_017_b4576 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4576 4584 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4576 8 (by decide +kernel)

theorem cells_017_b4584 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4584 4592 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4584 8 (by decide +kernel)

theorem cells_017_b4592 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4592 4600 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4592 8 (by decide +kernel)

theorem cells_017_b4600 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4600 4608 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4600 8 (by decide +kernel)

theorem cells_017 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4352 4608 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4352 4480 4608
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4352 4416 4480
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4352 4384 4416
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4352 4368 4384
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4352 4360 4368
 cells_017_b4352
 cells_017_b4360)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4368 4376 4384
 cells_017_b4368
 cells_017_b4376))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4384 4400 4416
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4384 4392 4400
 cells_017_b4384
 cells_017_b4392)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4400 4408 4416
 cells_017_b4400
 cells_017_b4408)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4416 4448 4480
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4416 4432 4448
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4416 4424 4432
 cells_017_b4416
 cells_017_b4424)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4432 4440 4448
 cells_017_b4432
 cells_017_b4440))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4448 4464 4480
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4448 4456 4464
 cells_017_b4448
 cells_017_b4456)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4464 4472 4480
 cells_017_b4464
 cells_017_b4472))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4480 4544 4608
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4480 4512 4544
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4480 4496 4512
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4480 4488 4496
 cells_017_b4480
 cells_017_b4488)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4496 4504 4512
 cells_017_b4496
 cells_017_b4504))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4512 4528 4544
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4512 4520 4528
 cells_017_b4512
 cells_017_b4520)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4528 4536 4544
 cells_017_b4528
 cells_017_b4536)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4544 4576 4608
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4544 4560 4576
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4544 4552 4560
 cells_017_b4544
 cells_017_b4552)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4560 4568 4576
 cells_017_b4560
 cells_017_b4568))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4576 4592 4608
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4576 4584 4592
 cells_017_b4576
 cells_017_b4584)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4592 4600 4608
 cells_017_b4592
 cells_017_b4600)))))
end Papers.RationalityTen.SharedSmallGraph
