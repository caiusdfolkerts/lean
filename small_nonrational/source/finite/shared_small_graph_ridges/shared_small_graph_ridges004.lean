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
theorem ridges_004_b512 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 512 516 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 512 4 (by decide +kernel)

theorem ridges_004_b516 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 516 520 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 516 4 (by decide +kernel)

theorem ridges_004_b520 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 520 524 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 520 4 (by decide +kernel)

theorem ridges_004_b524 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 524 528 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 524 4 (by decide +kernel)

theorem ridges_004_b528 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 528 532 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 528 4 (by decide +kernel)

theorem ridges_004_b532 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 532 536 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 532 4 (by decide +kernel)

theorem ridges_004_b536 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 536 540 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 536 4 (by decide +kernel)

theorem ridges_004_b540 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 540 544 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 540 4 (by decide +kernel)

theorem ridges_004_b544 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 544 548 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 544 4 (by decide +kernel)

theorem ridges_004_b548 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 548 552 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 548 4 (by decide +kernel)

theorem ridges_004_b552 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 552 556 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 552 4 (by decide +kernel)

theorem ridges_004_b556 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 556 560 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 556 4 (by decide +kernel)

theorem ridges_004_b560 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 560 564 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 560 4 (by decide +kernel)

theorem ridges_004_b564 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 564 568 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 564 4 (by decide +kernel)

theorem ridges_004_b568 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 568 572 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 568 4 (by decide +kernel)

theorem ridges_004_b572 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 572 576 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 572 4 (by decide +kernel)

theorem ridges_004_b576 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 576 580 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 576 4 (by decide +kernel)

theorem ridges_004_b580 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 580 584 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 580 4 (by decide +kernel)

theorem ridges_004_b584 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 584 588 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 584 4 (by decide +kernel)

theorem ridges_004_b588 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 588 592 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 588 4 (by decide +kernel)

theorem ridges_004_b592 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 592 596 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 592 4 (by decide +kernel)

theorem ridges_004_b596 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 596 600 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 596 4 (by decide +kernel)

theorem ridges_004_b600 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 600 604 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 600 4 (by decide +kernel)

theorem ridges_004_b604 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 604 608 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 604 4 (by decide +kernel)

theorem ridges_004_b608 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 608 612 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 608 4 (by decide +kernel)

theorem ridges_004_b612 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 612 616 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 612 4 (by decide +kernel)

theorem ridges_004_b616 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 616 620 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 616 4 (by decide +kernel)

theorem ridges_004_b620 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 620 624 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 620 4 (by decide +kernel)

theorem ridges_004_b624 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 624 628 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 624 4 (by decide +kernel)

theorem ridges_004_b628 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 628 632 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 628 4 (by decide +kernel)

theorem ridges_004_b632 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 632 636 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 632 4 (by decide +kernel)

theorem ridges_004_b636 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 636 640 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 636 4 (by decide +kernel)

theorem ridges_004 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 512 640 :=
  (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 512 576 640
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 512 544 576
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 512 528 544
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 512 520 528
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 512 516 520
 ridges_004_b512
 ridges_004_b516)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 520 524 528
 ridges_004_b520
 ridges_004_b524))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 528 536 544
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 528 532 536
 ridges_004_b528
 ridges_004_b532)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 536 540 544
 ridges_004_b536
 ridges_004_b540)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 544 560 576
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 544 552 560
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 544 548 552
 ridges_004_b544
 ridges_004_b548)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 552 556 560
 ridges_004_b552
 ridges_004_b556))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 560 568 576
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 560 564 568
 ridges_004_b560
 ridges_004_b564)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 568 572 576
 ridges_004_b568
 ridges_004_b572))))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 576 608 640
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 576 592 608
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 576 584 592
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 576 580 584
 ridges_004_b576
 ridges_004_b580)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 584 588 592
 ridges_004_b584
 ridges_004_b588))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 592 600 608
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 592 596 600
 ridges_004_b592
 ridges_004_b596)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 600 604 608
 ridges_004_b600
 ridges_004_b604)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 608 624 640
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 608 616 624
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 608 612 616
 ridges_004_b608
 ridges_004_b612)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 616 620 624
 ridges_004_b616
 ridges_004_b620))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 624 632 640
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 624 628 632
 ridges_004_b624
 ridges_004_b628)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 632 636 640
 ridges_004_b632
 ridges_004_b636)))))
end Papers.RationalityTen.SharedSmallGraph
