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
theorem cells_022_b5632 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5632 5640 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5632 8 (by decide +kernel)

theorem cells_022_b5640 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5640 5648 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5640 8 (by decide +kernel)

theorem cells_022_b5648 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5648 5656 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5648 8 (by decide +kernel)

theorem cells_022_b5656 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5656 5664 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5656 8 (by decide +kernel)

theorem cells_022_b5664 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5664 5672 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5664 8 (by decide +kernel)

theorem cells_022_b5672 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5672 5680 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5672 8 (by decide +kernel)

theorem cells_022_b5680 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5680 5688 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5680 8 (by decide +kernel)

theorem cells_022_b5688 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5688 5696 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5688 8 (by decide +kernel)

theorem cells_022_b5696 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5696 5704 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5696 8 (by decide +kernel)

theorem cells_022_b5704 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5704 5712 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5704 8 (by decide +kernel)

theorem cells_022_b5712 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5712 5720 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5712 8 (by decide +kernel)

theorem cells_022_b5720 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5720 5728 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5720 8 (by decide +kernel)

theorem cells_022_b5728 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5728 5736 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5728 8 (by decide +kernel)

theorem cells_022_b5736 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5736 5744 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5736 8 (by decide +kernel)

theorem cells_022_b5744 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5744 5752 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5744 8 (by decide +kernel)

theorem cells_022_b5752 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5752 5760 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5752 8 (by decide +kernel)

theorem cells_022_b5760 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5760 5768 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5760 8 (by decide +kernel)

theorem cells_022_b5768 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5768 5776 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5768 8 (by decide +kernel)

theorem cells_022_b5776 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5776 5784 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5776 8 (by decide +kernel)

theorem cells_022_b5784 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5784 5792 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5784 8 (by decide +kernel)

theorem cells_022_b5792 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5792 5800 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5792 8 (by decide +kernel)

theorem cells_022_b5800 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5800 5808 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5800 8 (by decide +kernel)

theorem cells_022_b5808 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5808 5816 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5808 8 (by decide +kernel)

theorem cells_022_b5816 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5816 5824 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5816 8 (by decide +kernel)

theorem cells_022_b5824 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5824 5832 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5824 8 (by decide +kernel)

theorem cells_022_b5832 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5832 5840 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5832 8 (by decide +kernel)

theorem cells_022_b5840 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5840 5848 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5840 8 (by decide +kernel)

theorem cells_022_b5848 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5848 5856 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5848 8 (by decide +kernel)

theorem cells_022_b5856 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5856 5864 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5856 8 (by decide +kernel)

theorem cells_022_b5864 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5864 5872 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5864 8 (by decide +kernel)

theorem cells_022_b5872 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5872 5880 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5872 8 (by decide +kernel)

theorem cells_022_b5880 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5880 5888 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5880 8 (by decide +kernel)

theorem cells_022 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5632 5888 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5632 5760 5888
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5632 5696 5760
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5632 5664 5696
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5632 5648 5664
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5632 5640 5648
 cells_022_b5632
 cells_022_b5640)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5648 5656 5664
 cells_022_b5648
 cells_022_b5656))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5664 5680 5696
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5664 5672 5680
 cells_022_b5664
 cells_022_b5672)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5680 5688 5696
 cells_022_b5680
 cells_022_b5688)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5696 5728 5760
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5696 5712 5728
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5696 5704 5712
 cells_022_b5696
 cells_022_b5704)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5712 5720 5728
 cells_022_b5712
 cells_022_b5720))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5728 5744 5760
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5728 5736 5744
 cells_022_b5728
 cells_022_b5736)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5744 5752 5760
 cells_022_b5744
 cells_022_b5752))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5760 5824 5888
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5760 5792 5824
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5760 5776 5792
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5760 5768 5776
 cells_022_b5760
 cells_022_b5768)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5776 5784 5792
 cells_022_b5776
 cells_022_b5784))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5792 5808 5824
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5792 5800 5808
 cells_022_b5792
 cells_022_b5800)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5808 5816 5824
 cells_022_b5808
 cells_022_b5816)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5824 5856 5888
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5824 5840 5856
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5824 5832 5840
 cells_022_b5824
 cells_022_b5832)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5840 5848 5856
 cells_022_b5840
 cells_022_b5848))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5856 5872 5888
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5856 5864 5872
 cells_022_b5856
 cells_022_b5864)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5872 5880 5888
 cells_022_b5872
 cells_022_b5880)))))
end Papers.RationalityTen.SharedSmallGraph
