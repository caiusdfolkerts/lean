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
theorem cells_023_b5888 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5888 5896 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5888 8 (by decide +kernel)

theorem cells_023_b5896 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5896 5904 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5896 8 (by decide +kernel)

theorem cells_023_b5904 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5904 5912 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5904 8 (by decide +kernel)

theorem cells_023_b5912 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5912 5920 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5912 8 (by decide +kernel)

theorem cells_023_b5920 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5920 5928 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5920 8 (by decide +kernel)

theorem cells_023_b5928 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5928 5936 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5928 8 (by decide +kernel)

theorem cells_023_b5936 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5936 5944 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5936 8 (by decide +kernel)

theorem cells_023_b5944 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5944 5952 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5944 8 (by decide +kernel)

theorem cells_023_b5952 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5952 5960 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5952 8 (by decide +kernel)

theorem cells_023_b5960 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5960 5968 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5960 8 (by decide +kernel)

theorem cells_023_b5968 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5968 5976 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5968 8 (by decide +kernel)

theorem cells_023_b5976 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5976 5984 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5976 8 (by decide +kernel)

theorem cells_023_b5984 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5984 5992 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5984 8 (by decide +kernel)

theorem cells_023_b5992 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5992 6000 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5992 8 (by decide +kernel)

theorem cells_023_b6000 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6000 6008 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6000 8 (by decide +kernel)

theorem cells_023_b6008 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6008 6016 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6008 8 (by decide +kernel)

theorem cells_023_b6016 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6016 6024 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6016 8 (by decide +kernel)

theorem cells_023_b6024 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6024 6032 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6024 8 (by decide +kernel)

theorem cells_023_b6032 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6032 6040 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6032 8 (by decide +kernel)

theorem cells_023_b6040 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6040 6048 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6040 8 (by decide +kernel)

theorem cells_023_b6048 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6048 6056 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6048 8 (by decide +kernel)

theorem cells_023_b6056 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6056 6064 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6056 8 (by decide +kernel)

theorem cells_023_b6064 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6064 6072 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6064 8 (by decide +kernel)

theorem cells_023_b6072 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6072 6080 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6072 8 (by decide +kernel)

theorem cells_023_b6080 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6080 6088 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6080 8 (by decide +kernel)

theorem cells_023_b6088 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6088 6096 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6088 8 (by decide +kernel)

theorem cells_023_b6096 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6096 6104 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6096 8 (by decide +kernel)

theorem cells_023_b6104 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6104 6112 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6104 8 (by decide +kernel)

theorem cells_023_b6112 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6112 6120 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6112 8 (by decide +kernel)

theorem cells_023_b6120 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6120 6128 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6120 8 (by decide +kernel)

theorem cells_023_b6128 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6128 6136 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6128 8 (by decide +kernel)

theorem cells_023_b6136 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 6136 6144 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 6136 8 (by decide +kernel)

theorem cells_023 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5888 6144 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5888 6016 6144
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5888 5952 6016
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5888 5920 5952
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5888 5904 5920
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5888 5896 5904
 cells_023_b5888
 cells_023_b5896)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5904 5912 5920
 cells_023_b5904
 cells_023_b5912))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5920 5936 5952
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5920 5928 5936
 cells_023_b5920
 cells_023_b5928)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5936 5944 5952
 cells_023_b5936
 cells_023_b5944)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5952 5984 6016
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5952 5968 5984
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5952 5960 5968
 cells_023_b5952
 cells_023_b5960)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5968 5976 5984
 cells_023_b5968
 cells_023_b5976))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5984 6000 6016
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5984 5992 6000
 cells_023_b5984
 cells_023_b5992)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6000 6008 6016
 cells_023_b6000
 cells_023_b6008))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6016 6080 6144
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6016 6048 6080
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6016 6032 6048
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6016 6024 6032
 cells_023_b6016
 cells_023_b6024)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6032 6040 6048
 cells_023_b6032
 cells_023_b6040))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6048 6064 6080
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6048 6056 6064
 cells_023_b6048
 cells_023_b6056)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6064 6072 6080
 cells_023_b6064
 cells_023_b6072)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6080 6112 6144
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6080 6096 6112
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6080 6088 6096
 cells_023_b6080
 cells_023_b6088)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6096 6104 6112
 cells_023_b6096
 cells_023_b6104))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6112 6128 6144
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6112 6120 6128
 cells_023_b6112
 cells_023_b6120)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 6128 6136 6144
 cells_023_b6128
 cells_023_b6136)))))
end Papers.RationalityTen.SharedSmallGraph
