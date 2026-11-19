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
theorem cells_010_b2560 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2560 2568 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2560 8 (by decide +kernel)

theorem cells_010_b2568 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2568 2576 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2568 8 (by decide +kernel)

theorem cells_010_b2576 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2576 2584 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2576 8 (by decide +kernel)

theorem cells_010_b2584 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2584 2592 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2584 8 (by decide +kernel)

theorem cells_010_b2592 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2592 2600 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2592 8 (by decide +kernel)

theorem cells_010_b2600 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2600 2608 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2600 8 (by decide +kernel)

theorem cells_010_b2608 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2608 2616 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2608 8 (by decide +kernel)

theorem cells_010_b2616 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2616 2624 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2616 8 (by decide +kernel)

theorem cells_010_b2624 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2624 2632 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2624 8 (by decide +kernel)

theorem cells_010_b2632 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2632 2640 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2632 8 (by decide +kernel)

theorem cells_010_b2640 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2640 2648 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2640 8 (by decide +kernel)

theorem cells_010_b2648 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2648 2656 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2648 8 (by decide +kernel)

theorem cells_010_b2656 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2656 2664 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2656 8 (by decide +kernel)

theorem cells_010_b2664 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2664 2672 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2664 8 (by decide +kernel)

theorem cells_010_b2672 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2672 2680 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2672 8 (by decide +kernel)

theorem cells_010_b2680 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2680 2688 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2680 8 (by decide +kernel)

theorem cells_010_b2688 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2688 2696 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2688 8 (by decide +kernel)

theorem cells_010_b2696 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2696 2704 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2696 8 (by decide +kernel)

theorem cells_010_b2704 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2704 2712 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2704 8 (by decide +kernel)

theorem cells_010_b2712 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2712 2720 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2712 8 (by decide +kernel)

theorem cells_010_b2720 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2720 2728 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2720 8 (by decide +kernel)

theorem cells_010_b2728 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2728 2736 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2728 8 (by decide +kernel)

theorem cells_010_b2736 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2736 2744 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2736 8 (by decide +kernel)

theorem cells_010_b2744 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2744 2752 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2744 8 (by decide +kernel)

theorem cells_010_b2752 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2752 2760 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2752 8 (by decide +kernel)

theorem cells_010_b2760 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2760 2768 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2760 8 (by decide +kernel)

theorem cells_010_b2768 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2768 2776 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2768 8 (by decide +kernel)

theorem cells_010_b2776 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2776 2784 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2776 8 (by decide +kernel)

theorem cells_010_b2784 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2784 2792 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2784 8 (by decide +kernel)

theorem cells_010_b2792 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2792 2800 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2792 8 (by decide +kernel)

theorem cells_010_b2800 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2800 2808 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2800 8 (by decide +kernel)

theorem cells_010_b2808 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2808 2816 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2808 8 (by decide +kernel)

theorem cells_010 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2560 2816 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2560 2688 2816
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2560 2624 2688
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2560 2592 2624
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2560 2576 2592
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2560 2568 2576
 cells_010_b2560
 cells_010_b2568)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2576 2584 2592
 cells_010_b2576
 cells_010_b2584))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2592 2608 2624
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2592 2600 2608
 cells_010_b2592
 cells_010_b2600)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2608 2616 2624
 cells_010_b2608
 cells_010_b2616)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2624 2656 2688
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2624 2640 2656
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2624 2632 2640
 cells_010_b2624
 cells_010_b2632)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2640 2648 2656
 cells_010_b2640
 cells_010_b2648))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2656 2672 2688
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2656 2664 2672
 cells_010_b2656
 cells_010_b2664)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2672 2680 2688
 cells_010_b2672
 cells_010_b2680))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2688 2752 2816
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2688 2720 2752
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2688 2704 2720
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2688 2696 2704
 cells_010_b2688
 cells_010_b2696)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2704 2712 2720
 cells_010_b2704
 cells_010_b2712))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2720 2736 2752
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2720 2728 2736
 cells_010_b2720
 cells_010_b2728)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2736 2744 2752
 cells_010_b2736
 cells_010_b2744)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2752 2784 2816
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2752 2768 2784
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2752 2760 2768
 cells_010_b2752
 cells_010_b2760)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2768 2776 2784
 cells_010_b2768
 cells_010_b2776))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2784 2800 2816
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2784 2792 2800
 cells_010_b2784
 cells_010_b2792)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2800 2808 2816
 cells_010_b2800
 cells_010_b2808)))))
end Papers.RationalityTen.SharedSmallGraph
