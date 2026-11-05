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
theorem cells_011_b2816 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2816 2824 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2816 8 (by decide +kernel)

theorem cells_011_b2824 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2824 2832 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2824 8 (by decide +kernel)

theorem cells_011_b2832 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2832 2840 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2832 8 (by decide +kernel)

theorem cells_011_b2840 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2840 2848 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2840 8 (by decide +kernel)

theorem cells_011_b2848 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2848 2856 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2848 8 (by decide +kernel)

theorem cells_011_b2856 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2856 2864 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2856 8 (by decide +kernel)

theorem cells_011_b2864 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2864 2872 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2864 8 (by decide +kernel)

theorem cells_011_b2872 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2872 2880 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2872 8 (by decide +kernel)

theorem cells_011_b2880 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2880 2888 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2880 8 (by decide +kernel)

theorem cells_011_b2888 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2888 2896 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2888 8 (by decide +kernel)

theorem cells_011_b2896 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2896 2904 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2896 8 (by decide +kernel)

theorem cells_011_b2904 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2904 2912 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2904 8 (by decide +kernel)

theorem cells_011_b2912 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2912 2920 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2912 8 (by decide +kernel)

theorem cells_011_b2920 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2920 2928 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2920 8 (by decide +kernel)

theorem cells_011_b2928 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2928 2936 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2928 8 (by decide +kernel)

theorem cells_011_b2936 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2936 2944 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2936 8 (by decide +kernel)

theorem cells_011_b2944 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2944 2952 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2944 8 (by decide +kernel)

theorem cells_011_b2952 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2952 2960 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2952 8 (by decide +kernel)

theorem cells_011_b2960 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2960 2968 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2960 8 (by decide +kernel)

theorem cells_011_b2968 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2968 2976 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2968 8 (by decide +kernel)

theorem cells_011_b2976 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2976 2984 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2976 8 (by decide +kernel)

theorem cells_011_b2984 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2984 2992 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2984 8 (by decide +kernel)

theorem cells_011_b2992 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2992 3000 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 2992 8 (by decide +kernel)

theorem cells_011_b3000 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3000 3008 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3000 8 (by decide +kernel)

theorem cells_011_b3008 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3008 3016 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3008 8 (by decide +kernel)

theorem cells_011_b3016 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3016 3024 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3016 8 (by decide +kernel)

theorem cells_011_b3024 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3024 3032 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3024 8 (by decide +kernel)

theorem cells_011_b3032 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3032 3040 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3032 8 (by decide +kernel)

theorem cells_011_b3040 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3040 3048 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3040 8 (by decide +kernel)

theorem cells_011_b3048 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3048 3056 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3048 8 (by decide +kernel)

theorem cells_011_b3056 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3056 3064 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3056 8 (by decide +kernel)

theorem cells_011_b3064 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 3064 3072 :=
  interval_of_check (fun i => cellCheck (Fin.ofNat cellCount i)) 3064 8 (by decide +kernel)

theorem cells_011 : Interval (fun i => cellCheck (Fin.ofNat cellCount i)) 2816 3072 :=
  (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2816 2944 3072
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2816 2880 2944
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2816 2848 2880
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2816 2832 2848
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2816 2824 2832
 cells_011_b2816
 cells_011_b2824)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2832 2840 2848
 cells_011_b2832
 cells_011_b2840))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2848 2864 2880
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2848 2856 2864
 cells_011_b2848
 cells_011_b2856)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2864 2872 2880
 cells_011_b2864
 cells_011_b2872)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2880 2912 2944
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2880 2896 2912
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2880 2888 2896
 cells_011_b2880
 cells_011_b2888)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2896 2904 2912
 cells_011_b2896
 cells_011_b2904))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2912 2928 2944
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2912 2920 2928
 cells_011_b2912
 cells_011_b2920)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2928 2936 2944
 cells_011_b2928
 cells_011_b2936))))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2944 3008 3072
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2944 2976 3008
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2944 2960 2976
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2944 2952 2960
 cells_011_b2944
 cells_011_b2952)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2960 2968 2976
 cells_011_b2960
 cells_011_b2968))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2976 2992 3008
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2976 2984 2992
 cells_011_b2976
 cells_011_b2984)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 2992 3000 3008
 cells_011_b2992
 cells_011_b3000)))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3008 3040 3072
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3008 3024 3040
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3008 3016 3024
 cells_011_b3008
 cells_011_b3016)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3024 3032 3040
 cells_011_b3024
 cells_011_b3032))
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3040 3056 3072
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3040 3048 3056
 cells_011_b3040
 cells_011_b3048)
 (interval_append (fun i => cellCheck (Fin.ofNat cellCount i)) 3056 3064 3072
 cells_011_b3056
 cells_011_b3064)))))
end Papers.RationalityTen.SharedSmallGraph
