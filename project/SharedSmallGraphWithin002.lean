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
theorem within_002_b512 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 512 520 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 512 8 (by decide +kernel)

theorem within_002_b520 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 520 528 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 520 8 (by decide +kernel)

theorem within_002_b528 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 528 536 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 528 8 (by decide +kernel)

theorem within_002_b536 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 536 544 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 536 8 (by decide +kernel)

theorem within_002_b544 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 544 552 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 544 8 (by decide +kernel)

theorem within_002_b552 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 552 560 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 552 8 (by decide +kernel)

theorem within_002_b560 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 560 568 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 560 8 (by decide +kernel)

theorem within_002_b568 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 568 576 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 568 8 (by decide +kernel)

theorem within_002_b576 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 576 584 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 576 8 (by decide +kernel)

theorem within_002_b584 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 584 592 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 584 8 (by decide +kernel)

theorem within_002_b592 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 592 600 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 592 8 (by decide +kernel)

theorem within_002_b600 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 600 608 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 600 8 (by decide +kernel)

theorem within_002_b608 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 608 616 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 608 8 (by decide +kernel)

theorem within_002_b616 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 616 624 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 616 8 (by decide +kernel)

theorem within_002_b624 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 624 632 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 624 8 (by decide +kernel)

theorem within_002_b632 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 632 640 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 632 8 (by decide +kernel)

theorem within_002_b640 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 640 648 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 640 8 (by decide +kernel)

theorem within_002_b648 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 648 656 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 648 8 (by decide +kernel)

theorem within_002_b656 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 656 664 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 656 8 (by decide +kernel)

theorem within_002_b664 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 664 672 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 664 8 (by decide +kernel)

theorem within_002_b672 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 672 680 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 672 8 (by decide +kernel)

theorem within_002_b680 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 680 688 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 680 8 (by decide +kernel)

theorem within_002_b688 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 688 696 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 688 8 (by decide +kernel)

theorem within_002_b696 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 696 704 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 696 8 (by decide +kernel)

theorem within_002_b704 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 704 712 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 704 8 (by decide +kernel)

theorem within_002_b712 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 712 720 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 712 8 (by decide +kernel)

theorem within_002_b720 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 720 728 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 720 8 (by decide +kernel)

theorem within_002_b728 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 728 736 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 728 8 (by decide +kernel)

theorem within_002_b736 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 736 744 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 736 8 (by decide +kernel)

theorem within_002_b744 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 744 752 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 744 8 (by decide +kernel)

theorem within_002_b752 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 752 760 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 752 8 (by decide +kernel)

theorem within_002_b760 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 760 768 :=
  interval_of_check (fun i => withinCheck (Fin.ofNat 1024 i)) 760 8 (by decide +kernel)

theorem within_002 : Interval (fun i => withinCheck (Fin.ofNat 1024 i)) 512 768 :=
  (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 512 640 768
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 512 576 640
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 512 544 576
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 512 528 544
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 512 520 528
 within_002_b512
 within_002_b520)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 528 536 544
 within_002_b528
 within_002_b536))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 544 560 576
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 544 552 560
 within_002_b544
 within_002_b552)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 560 568 576
 within_002_b560
 within_002_b568)))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 576 608 640
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 576 592 608
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 576 584 592
 within_002_b576
 within_002_b584)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 592 600 608
 within_002_b592
 within_002_b600))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 608 624 640
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 608 616 624
 within_002_b608
 within_002_b616)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 624 632 640
 within_002_b624
 within_002_b632))))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 640 704 768
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 640 672 704
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 640 656 672
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 640 648 656
 within_002_b640
 within_002_b648)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 656 664 672
 within_002_b656
 within_002_b664))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 672 688 704
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 672 680 688
 within_002_b672
 within_002_b680)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 688 696 704
 within_002_b688
 within_002_b696)))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 704 736 768
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 704 720 736
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 704 712 720
 within_002_b704
 within_002_b712)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 720 728 736
 within_002_b720
 within_002_b728))
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 736 752 768
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 736 744 752
 within_002_b736
 within_002_b744)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 752 760 768
 within_002_b752
 within_002_b760)))))
end Papers.RationalityTen.SharedSmallGraph
