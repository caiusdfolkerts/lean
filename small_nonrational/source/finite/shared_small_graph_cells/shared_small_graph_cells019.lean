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
theorem cells_019_b4864 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4864 4872 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4864 8 (by decide +kernel)

theorem cells_019_b4872 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4872 4880 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4872 8 (by decide +kernel)

theorem cells_019_b4880 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4880 4888 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4880 8 (by decide +kernel)

theorem cells_019_b4888 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4888 4896 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4888 8 (by decide +kernel)

theorem cells_019_b4896 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4896 4904 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4896 8 (by decide +kernel)

theorem cells_019_b4904 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4904 4912 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4904 8 (by decide +kernel)

theorem cells_019_b4912 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4912 4920 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4912 8 (by decide +kernel)

theorem cells_019_b4920 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4920 4928 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4920 8 (by decide +kernel)

theorem cells_019_b4928 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4928 4936 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4928 8 (by decide +kernel)

theorem cells_019_b4936 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4936 4944 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4936 8 (by decide +kernel)

theorem cells_019_b4944 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4944 4952 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4944 8 (by decide +kernel)

theorem cells_019_b4952 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4952 4960 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4952 8 (by decide +kernel)

theorem cells_019_b4960 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4960 4968 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4960 8 (by decide +kernel)

theorem cells_019_b4968 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4968 4976 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4968 8 (by decide +kernel)

theorem cells_019_b4976 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4976 4984 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4976 8 (by decide +kernel)

theorem cells_019_b4984 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4984 4992 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4984 8 (by decide +kernel)

theorem cells_019_b4992 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4992 5000 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 4992 8 (by decide +kernel)

theorem cells_019_b5000 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5000 5008 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5000 8 (by decide +kernel)

theorem cells_019_b5008 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5008 5016 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5008 8 (by decide +kernel)

theorem cells_019_b5016 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5016 5024 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5016 8 (by decide +kernel)

theorem cells_019_b5024 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5024 5032 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5024 8 (by decide +kernel)

theorem cells_019_b5032 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5032 5040 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5032 8 (by decide +kernel)

theorem cells_019_b5040 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5040 5048 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5040 8 (by decide +kernel)

theorem cells_019_b5048 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5048 5056 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5048 8 (by decide +kernel)

theorem cells_019_b5056 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5056 5064 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5056 8 (by decide +kernel)

theorem cells_019_b5064 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5064 5072 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5064 8 (by decide +kernel)

theorem cells_019_b5072 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5072 5080 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5072 8 (by decide +kernel)

theorem cells_019_b5080 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5080 5088 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5080 8 (by decide +kernel)

theorem cells_019_b5088 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5088 5096 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5088 8 (by decide +kernel)

theorem cells_019_b5096 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5096 5104 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5096 8 (by decide +kernel)

theorem cells_019_b5104 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5104 5112 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5104 8 (by decide +kernel)

theorem cells_019_b5112 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 5112 5120 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 5112 8 (by decide +kernel)

theorem cells_019 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 4864 5120 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4864 4992 5120
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4864 4928 4992
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4864 4896 4928
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4864 4880 4896
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4864 4872 4880
 cells_019_b4864
 cells_019_b4872)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4880 4888 4896
 cells_019_b4880
 cells_019_b4888))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4896 4912 4928
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4896 4904 4912
 cells_019_b4896
 cells_019_b4904)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4912 4920 4928
 cells_019_b4912
 cells_019_b4920)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4928 4960 4992
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4928 4944 4960
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4928 4936 4944
 cells_019_b4928
 cells_019_b4936)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4944 4952 4960
 cells_019_b4944
 cells_019_b4952))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4960 4976 4992
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4960 4968 4976
 cells_019_b4960
 cells_019_b4968)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4976 4984 4992
 cells_019_b4976
 cells_019_b4984))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4992 5056 5120
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4992 5024 5056
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4992 5008 5024
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 4992 5000 5008
 cells_019_b4992
 cells_019_b5000)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5008 5016 5024
 cells_019_b5008
 cells_019_b5016))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5024 5040 5056
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5024 5032 5040
 cells_019_b5024
 cells_019_b5032)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5040 5048 5056
 cells_019_b5040
 cells_019_b5048)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5056 5088 5120
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5056 5072 5088
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5056 5064 5072
 cells_019_b5056
 cells_019_b5064)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5072 5080 5088
 cells_019_b5072
 cells_019_b5080))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5088 5104 5120
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5088 5096 5104
 cells_019_b5088
 cells_019_b5096)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 5104 5112 5120
 cells_019_b5104
 cells_019_b5112)))))
end Papers.RationalityTen.SharedSmallGraph
