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
theorem cells_003_b768 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 768 776 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 768 8 (by decide +kernel)

theorem cells_003_b776 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 776 784 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 776 8 (by decide +kernel)

theorem cells_003_b784 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 784 792 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 784 8 (by decide +kernel)

theorem cells_003_b792 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 792 800 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 792 8 (by decide +kernel)

theorem cells_003_b800 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 800 808 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 800 8 (by decide +kernel)

theorem cells_003_b808 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 808 816 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 808 8 (by decide +kernel)

theorem cells_003_b816 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 816 824 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 816 8 (by decide +kernel)

theorem cells_003_b824 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 824 832 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 824 8 (by decide +kernel)

theorem cells_003_b832 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 832 840 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 832 8 (by decide +kernel)

theorem cells_003_b840 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 840 848 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 840 8 (by decide +kernel)

theorem cells_003_b848 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 848 856 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 848 8 (by decide +kernel)

theorem cells_003_b856 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 856 864 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 856 8 (by decide +kernel)

theorem cells_003_b864 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 864 872 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 864 8 (by decide +kernel)

theorem cells_003_b872 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 872 880 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 872 8 (by decide +kernel)

theorem cells_003_b880 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 880 888 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 880 8 (by decide +kernel)

theorem cells_003_b888 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 888 896 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 888 8 (by decide +kernel)

theorem cells_003_b896 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 896 904 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 896 8 (by decide +kernel)

theorem cells_003_b904 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 904 912 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 904 8 (by decide +kernel)

theorem cells_003_b912 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 912 920 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 912 8 (by decide +kernel)

theorem cells_003_b920 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 920 928 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 920 8 (by decide +kernel)

theorem cells_003_b928 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 928 936 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 928 8 (by decide +kernel)

theorem cells_003_b936 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 936 944 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 936 8 (by decide +kernel)

theorem cells_003_b944 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 944 952 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 944 8 (by decide +kernel)

theorem cells_003_b952 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 952 960 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 952 8 (by decide +kernel)

theorem cells_003_b960 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 960 968 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 960 8 (by decide +kernel)

theorem cells_003_b968 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 968 976 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 968 8 (by decide +kernel)

theorem cells_003_b976 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 976 984 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 976 8 (by decide +kernel)

theorem cells_003_b984 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 984 992 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 984 8 (by decide +kernel)

theorem cells_003_b992 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 992 1000 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 992 8 (by decide +kernel)

theorem cells_003_b1000 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1000 1008 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1000 8 (by decide +kernel)

theorem cells_003_b1008 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1008 1016 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1008 8 (by decide +kernel)

theorem cells_003_b1016 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 1016 1024 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 1016 8 (by decide +kernel)

theorem cells_003 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 768 1024 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 768 896 1024
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 768 832 896
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 768 800 832
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 768 784 800
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 768 776 784
 cells_003_b768
 cells_003_b776)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 784 792 800
 cells_003_b784
 cells_003_b792))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 800 816 832
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 800 808 816
 cells_003_b800
 cells_003_b808)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 816 824 832
 cells_003_b816
 cells_003_b824)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 832 864 896
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 832 848 864
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 832 840 848
 cells_003_b832
 cells_003_b840)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 848 856 864
 cells_003_b848
 cells_003_b856))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 864 880 896
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 864 872 880
 cells_003_b864
 cells_003_b872)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 880 888 896
 cells_003_b880
 cells_003_b888))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 896 960 1024
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 896 928 960
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 896 912 928
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 896 904 912
 cells_003_b896
 cells_003_b904)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 912 920 928
 cells_003_b912
 cells_003_b920))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 928 944 960
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 928 936 944
 cells_003_b928
 cells_003_b936)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 944 952 960
 cells_003_b944
 cells_003_b952)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 960 992 1024
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 960 976 992
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 960 968 976
 cells_003_b960
 cells_003_b968)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 976 984 992
 cells_003_b976
 cells_003_b984))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 992 1008 1024
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 992 1000 1008
 cells_003_b992
 cells_003_b1000)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 1008 1016 1024
 cells_003_b1008
 cells_003_b1016)))))
end Papers.RationalityTen.SharedSmallGraph
