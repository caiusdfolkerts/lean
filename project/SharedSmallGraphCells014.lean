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
theorem cells_014_b3584 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3584 3592 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3584 8 (by decide +kernel)

theorem cells_014_b3592 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3592 3600 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3592 8 (by decide +kernel)

theorem cells_014_b3600 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3600 3608 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3600 8 (by decide +kernel)

theorem cells_014_b3608 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3608 3616 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3608 8 (by decide +kernel)

theorem cells_014_b3616 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3616 3624 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3616 8 (by decide +kernel)

theorem cells_014_b3624 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3624 3632 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3624 8 (by decide +kernel)

theorem cells_014_b3632 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3632 3640 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3632 8 (by decide +kernel)

theorem cells_014_b3640 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3640 3648 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3640 8 (by decide +kernel)

theorem cells_014_b3648 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3648 3656 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3648 8 (by decide +kernel)

theorem cells_014_b3656 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3656 3664 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3656 8 (by decide +kernel)

theorem cells_014_b3664 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3664 3672 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3664 8 (by decide +kernel)

theorem cells_014_b3672 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3672 3680 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3672 8 (by decide +kernel)

theorem cells_014_b3680 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3680 3688 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3680 8 (by decide +kernel)

theorem cells_014_b3688 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3688 3696 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3688 8 (by decide +kernel)

theorem cells_014_b3696 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3696 3704 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3696 8 (by decide +kernel)

theorem cells_014_b3704 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3704 3712 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3704 8 (by decide +kernel)

theorem cells_014_b3712 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3712 3720 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3712 8 (by decide +kernel)

theorem cells_014_b3720 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3720 3728 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3720 8 (by decide +kernel)

theorem cells_014_b3728 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3728 3736 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3728 8 (by decide +kernel)

theorem cells_014_b3736 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3736 3744 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3736 8 (by decide +kernel)

theorem cells_014_b3744 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3744 3752 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3744 8 (by decide +kernel)

theorem cells_014_b3752 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3752 3760 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3752 8 (by decide +kernel)

theorem cells_014_b3760 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3760 3768 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3760 8 (by decide +kernel)

theorem cells_014_b3768 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3768 3776 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3768 8 (by decide +kernel)

theorem cells_014_b3776 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3776 3784 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3776 8 (by decide +kernel)

theorem cells_014_b3784 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3784 3792 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3784 8 (by decide +kernel)

theorem cells_014_b3792 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3792 3800 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3792 8 (by decide +kernel)

theorem cells_014_b3800 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3800 3808 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3800 8 (by decide +kernel)

theorem cells_014_b3808 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3808 3816 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3808 8 (by decide +kernel)

theorem cells_014_b3816 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3816 3824 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3816 8 (by decide +kernel)

theorem cells_014_b3824 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3824 3832 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3824 8 (by decide +kernel)

theorem cells_014_b3832 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3832 3840 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3832 8 (by decide +kernel)

theorem cells_014 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3584 3840 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3584 3712 3840
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3584 3648 3712
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3584 3616 3648
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3584 3600 3616
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3584 3592 3600
 cells_014_b3584
 cells_014_b3592)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3600 3608 3616
 cells_014_b3600
 cells_014_b3608))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3616 3632 3648
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3616 3624 3632
 cells_014_b3616
 cells_014_b3624)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3632 3640 3648
 cells_014_b3632
 cells_014_b3640)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3648 3680 3712
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3648 3664 3680
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3648 3656 3664
 cells_014_b3648
 cells_014_b3656)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3664 3672 3680
 cells_014_b3664
 cells_014_b3672))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3680 3696 3712
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3680 3688 3696
 cells_014_b3680
 cells_014_b3688)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3696 3704 3712
 cells_014_b3696
 cells_014_b3704))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3712 3776 3840
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3712 3744 3776
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3712 3728 3744
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3712 3720 3728
 cells_014_b3712
 cells_014_b3720)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3728 3736 3744
 cells_014_b3728
 cells_014_b3736))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3744 3760 3776
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3744 3752 3760
 cells_014_b3744
 cells_014_b3752)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3760 3768 3776
 cells_014_b3760
 cells_014_b3768)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3776 3808 3840
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3776 3792 3808
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3776 3784 3792
 cells_014_b3776
 cells_014_b3784)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3792 3800 3808
 cells_014_b3792
 cells_014_b3800))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3808 3824 3840
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3808 3816 3824
 cells_014_b3808
 cells_014_b3816)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3824 3832 3840
 cells_014_b3824
 cells_014_b3832)))))
end Papers.RationalityTen.SharedSmallGraph
