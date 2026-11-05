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
theorem cells_018_b4608 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4608 4616 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4608 8 (by decide +kernel)

theorem cells_018_b4616 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4616 4624 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4616 8 (by decide +kernel)

theorem cells_018_b4624 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4624 4632 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4624 8 (by decide +kernel)

theorem cells_018_b4632 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4632 4640 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4632 8 (by decide +kernel)

theorem cells_018_b4640 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4640 4648 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4640 8 (by decide +kernel)

theorem cells_018_b4648 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4648 4656 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4648 8 (by decide +kernel)

theorem cells_018_b4656 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4656 4664 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4656 8 (by decide +kernel)

theorem cells_018_b4664 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4664 4672 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4664 8 (by decide +kernel)

theorem cells_018_b4672 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4672 4680 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4672 8 (by decide +kernel)

theorem cells_018_b4680 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4680 4688 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4680 8 (by decide +kernel)

theorem cells_018_b4688 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4688 4696 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4688 8 (by decide +kernel)

theorem cells_018_b4696 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4696 4704 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4696 8 (by decide +kernel)

theorem cells_018_b4704 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4704 4712 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4704 8 (by decide +kernel)

theorem cells_018_b4712 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4712 4720 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4712 8 (by decide +kernel)

theorem cells_018_b4720 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4720 4728 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4720 8 (by decide +kernel)

theorem cells_018_b4728 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4728 4736 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4728 8 (by decide +kernel)

theorem cells_018_b4736 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4736 4744 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4736 8 (by decide +kernel)

theorem cells_018_b4744 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4744 4752 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4744 8 (by decide +kernel)

theorem cells_018_b4752 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4752 4760 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4752 8 (by decide +kernel)

theorem cells_018_b4760 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4760 4768 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4760 8 (by decide +kernel)

theorem cells_018_b4768 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4768 4776 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4768 8 (by decide +kernel)

theorem cells_018_b4776 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4776 4784 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4776 8 (by decide +kernel)

theorem cells_018_b4784 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4784 4792 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4784 8 (by decide +kernel)

theorem cells_018_b4792 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4792 4800 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4792 8 (by decide +kernel)

theorem cells_018_b4800 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4800 4808 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4800 8 (by decide +kernel)

theorem cells_018_b4808 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4808 4816 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4808 8 (by decide +kernel)

theorem cells_018_b4816 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4816 4824 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4816 8 (by decide +kernel)

theorem cells_018_b4824 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4824 4832 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4824 8 (by decide +kernel)

theorem cells_018_b4832 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4832 4840 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4832 8 (by decide +kernel)

theorem cells_018_b4840 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4840 4848 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4840 8 (by decide +kernel)

theorem cells_018_b4848 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4848 4856 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4848 8 (by decide +kernel)

theorem cells_018_b4856 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4856 4864 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4856 8 (by decide +kernel)

theorem cells_018 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4608 4864 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4608 4736 4864
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4608 4672 4736
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4608 4640 4672
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4608 4624 4640
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4608 4616 4624
 cells_018_b4608
 cells_018_b4616)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4624 4632 4640
 cells_018_b4624
 cells_018_b4632))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4640 4656 4672
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4640 4648 4656
 cells_018_b4640
 cells_018_b4648)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4656 4664 4672
 cells_018_b4656
 cells_018_b4664)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4672 4704 4736
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4672 4688 4704
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4672 4680 4688
 cells_018_b4672
 cells_018_b4680)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4688 4696 4704
 cells_018_b4688
 cells_018_b4696))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4704 4720 4736
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4704 4712 4720
 cells_018_b4704
 cells_018_b4712)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4720 4728 4736
 cells_018_b4720
 cells_018_b4728))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4736 4800 4864
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4736 4768 4800
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4736 4752 4768
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4736 4744 4752
 cells_018_b4736
 cells_018_b4744)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4752 4760 4768
 cells_018_b4752
 cells_018_b4760))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4768 4784 4800
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4768 4776 4784
 cells_018_b4768
 cells_018_b4776)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4784 4792 4800
 cells_018_b4784
 cells_018_b4792)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4800 4832 4864
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4800 4816 4832
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4800 4808 4816
 cells_018_b4800
 cells_018_b4808)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4816 4824 4832
 cells_018_b4816
 cells_018_b4824))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4832 4848 4864
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4832 4840 4848
 cells_018_b4832
 cells_018_b4840)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4848 4856 4864
 cells_018_b4848
 cells_018_b4856)))))
end Papers.RationalityTen.SharedSmallGraph
