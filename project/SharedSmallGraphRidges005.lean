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
theorem ridges_005_b640 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 640 644 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 640 4 (by decide +kernel)

theorem ridges_005_b644 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 644 648 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 644 4 (by decide +kernel)

theorem ridges_005_b648 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 648 652 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 648 4 (by decide +kernel)

theorem ridges_005_b652 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 652 656 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 652 4 (by decide +kernel)

theorem ridges_005_b656 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 656 660 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 656 4 (by decide +kernel)

theorem ridges_005_b660 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 660 664 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 660 4 (by decide +kernel)

theorem ridges_005_b664 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 664 668 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 664 4 (by decide +kernel)

theorem ridges_005_b668 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 668 672 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 668 4 (by decide +kernel)

theorem ridges_005_b672 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 672 676 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 672 4 (by decide +kernel)

theorem ridges_005_b676 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 676 680 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 676 4 (by decide +kernel)

theorem ridges_005_b680 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 680 684 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 680 4 (by decide +kernel)

theorem ridges_005_b684 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 684 688 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 684 4 (by decide +kernel)

theorem ridges_005_b688 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 688 692 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 688 4 (by decide +kernel)

theorem ridges_005_b692 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 692 696 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 692 4 (by decide +kernel)

theorem ridges_005_b696 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 696 700 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 696 4 (by decide +kernel)

theorem ridges_005_b700 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 700 704 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 700 4 (by decide +kernel)

theorem ridges_005_b704 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 704 708 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 704 4 (by decide +kernel)

theorem ridges_005_b708 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 708 712 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 708 4 (by decide +kernel)

theorem ridges_005_b712 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 712 716 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 712 4 (by decide +kernel)

theorem ridges_005_b716 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 716 720 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 716 4 (by decide +kernel)

theorem ridges_005_b720 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 720 724 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 720 4 (by decide +kernel)

theorem ridges_005_b724 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 724 728 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 724 4 (by decide +kernel)

theorem ridges_005_b728 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 728 732 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 728 4 (by decide +kernel)

theorem ridges_005_b732 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 732 736 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 732 4 (by decide +kernel)

theorem ridges_005_b736 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 736 740 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 736 4 (by decide +kernel)

theorem ridges_005_b740 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 740 744 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 740 4 (by decide +kernel)

theorem ridges_005_b744 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 744 748 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 744 4 (by decide +kernel)

theorem ridges_005_b748 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 748 752 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 748 4 (by decide +kernel)

theorem ridges_005_b752 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 752 756 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 752 4 (by decide +kernel)

theorem ridges_005_b756 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 756 760 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 756 4 (by decide +kernel)

theorem ridges_005_b760 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 760 764 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 760 4 (by decide +kernel)

theorem ridges_005_b764 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 764 768 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 764 4 (by decide +kernel)

theorem ridges_005 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 640 768 :=
  (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 640 704 768
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 640 672 704
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 640 656 672
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 640 648 656
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 640 644 648
 ridges_005_b640
 ridges_005_b644)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 648 652 656
 ridges_005_b648
 ridges_005_b652))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 656 664 672
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 656 660 664
 ridges_005_b656
 ridges_005_b660)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 664 668 672
 ridges_005_b664
 ridges_005_b668)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 672 688 704
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 672 680 688
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 672 676 680
 ridges_005_b672
 ridges_005_b676)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 680 684 688
 ridges_005_b680
 ridges_005_b684))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 688 696 704
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 688 692 696
 ridges_005_b688
 ridges_005_b692)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 696 700 704
 ridges_005_b696
 ridges_005_b700))))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 704 736 768
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 704 720 736
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 704 712 720
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 704 708 712
 ridges_005_b704
 ridges_005_b708)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 712 716 720
 ridges_005_b712
 ridges_005_b716))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 720 728 736
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 720 724 728
 ridges_005_b720
 ridges_005_b724)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 728 732 736
 ridges_005_b728
 ridges_005_b732)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 736 752 768
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 736 744 752
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 736 740 744
 ridges_005_b736
 ridges_005_b740)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 744 748 752
 ridges_005_b744
 ridges_005_b748))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 752 760 768
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 752 756 760
 ridges_005_b752
 ridges_005_b756)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 760 764 768
 ridges_005_b760
 ridges_005_b764)))))
end Papers.RationalityTen.SharedSmallGraph
