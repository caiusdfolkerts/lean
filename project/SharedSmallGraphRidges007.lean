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
theorem ridges_007_b896 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 896 900 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 896 4 (by decide +kernel)

theorem ridges_007_b900 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 900 904 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 900 4 (by decide +kernel)

theorem ridges_007_b904 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 904 908 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 904 4 (by decide +kernel)

theorem ridges_007_b908 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 908 912 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 908 4 (by decide +kernel)

theorem ridges_007_b912 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 912 916 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 912 4 (by decide +kernel)

theorem ridges_007_b916 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 916 920 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 916 4 (by decide +kernel)

theorem ridges_007_b920 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 920 924 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 920 4 (by decide +kernel)

theorem ridges_007_b924 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 924 928 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 924 4 (by decide +kernel)

theorem ridges_007_b928 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 928 932 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 928 4 (by decide +kernel)

theorem ridges_007_b932 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 932 936 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 932 4 (by decide +kernel)

theorem ridges_007_b936 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 936 940 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 936 4 (by decide +kernel)

theorem ridges_007_b940 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 940 944 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 940 4 (by decide +kernel)

theorem ridges_007_b944 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 944 948 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 944 4 (by decide +kernel)

theorem ridges_007_b948 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 948 952 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 948 4 (by decide +kernel)

theorem ridges_007_b952 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 952 956 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 952 4 (by decide +kernel)

theorem ridges_007_b956 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 956 960 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 956 4 (by decide +kernel)

theorem ridges_007_b960 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 960 964 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 960 4 (by decide +kernel)

theorem ridges_007_b964 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 964 968 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 964 4 (by decide +kernel)

theorem ridges_007_b968 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 968 972 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 968 4 (by decide +kernel)

theorem ridges_007_b972 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 972 976 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 972 4 (by decide +kernel)

theorem ridges_007_b976 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 976 980 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 976 4 (by decide +kernel)

theorem ridges_007_b980 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 980 984 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 980 4 (by decide +kernel)

theorem ridges_007_b984 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 984 988 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 984 4 (by decide +kernel)

theorem ridges_007_b988 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 988 992 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 988 4 (by decide +kernel)

theorem ridges_007_b992 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 992 996 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 992 4 (by decide +kernel)

theorem ridges_007_b996 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 996 1000 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 996 4 (by decide +kernel)

theorem ridges_007_b1000 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 1000 1004 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 1000 4 (by decide +kernel)

theorem ridges_007_b1004 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 1004 1008 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 1004 4 (by decide +kernel)

theorem ridges_007_b1008 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 1008 1012 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 1008 4 (by decide +kernel)

theorem ridges_007_b1012 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 1012 1016 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 1012 4 (by decide +kernel)

theorem ridges_007_b1016 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 1016 1020 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 1016 4 (by decide +kernel)

theorem ridges_007_b1020 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 1020 1024 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 1020 4 (by decide +kernel)

theorem ridges_007 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 896 1024 :=
  (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 896 960 1024
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 896 928 960
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 896 912 928
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 896 904 912
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 896 900 904
 ridges_007_b896
 ridges_007_b900)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 904 908 912
 ridges_007_b904
 ridges_007_b908))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 912 920 928
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 912 916 920
 ridges_007_b912
 ridges_007_b916)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 920 924 928
 ridges_007_b920
 ridges_007_b924)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 928 944 960
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 928 936 944
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 928 932 936
 ridges_007_b928
 ridges_007_b932)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 936 940 944
 ridges_007_b936
 ridges_007_b940))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 944 952 960
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 944 948 952
 ridges_007_b944
 ridges_007_b948)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 952 956 960
 ridges_007_b952
 ridges_007_b956))))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 960 992 1024
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 960 976 992
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 960 968 976
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 960 964 968
 ridges_007_b960
 ridges_007_b964)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 968 972 976
 ridges_007_b968
 ridges_007_b972))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 976 984 992
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 976 980 984
 ridges_007_b976
 ridges_007_b980)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 984 988 992
 ridges_007_b984
 ridges_007_b988)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 992 1008 1024
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 992 1000 1008
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 992 996 1000
 ridges_007_b992
 ridges_007_b996)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 1000 1004 1008
 ridges_007_b1000
 ridges_007_b1004))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 1008 1016 1024
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 1008 1012 1016
 ridges_007_b1008
 ridges_007_b1012)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 1016 1020 1024
 ridges_007_b1016
 ridges_007_b1020)))))
end Papers.RationalityTen.SharedSmallGraph
