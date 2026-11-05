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
theorem ridges_000_b0 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 4 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 4 (by decide +kernel)

theorem ridges_000_b4 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 4 8 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 4 4 (by decide +kernel)

theorem ridges_000_b8 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 8 12 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 8 4 (by decide +kernel)

theorem ridges_000_b12 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 12 16 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 12 4 (by decide +kernel)

theorem ridges_000_b16 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 16 20 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 16 4 (by decide +kernel)

theorem ridges_000_b20 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 20 24 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 20 4 (by decide +kernel)

theorem ridges_000_b24 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 24 28 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 24 4 (by decide +kernel)

theorem ridges_000_b28 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 28 32 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 28 4 (by decide +kernel)

theorem ridges_000_b32 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 32 36 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 32 4 (by decide +kernel)

theorem ridges_000_b36 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 36 40 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 36 4 (by decide +kernel)

theorem ridges_000_b40 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 40 44 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 40 4 (by decide +kernel)

theorem ridges_000_b44 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 44 48 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 44 4 (by decide +kernel)

theorem ridges_000_b48 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 48 52 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 48 4 (by decide +kernel)

theorem ridges_000_b52 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 52 56 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 52 4 (by decide +kernel)

theorem ridges_000_b56 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 56 60 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 56 4 (by decide +kernel)

theorem ridges_000_b60 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 60 64 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 60 4 (by decide +kernel)

theorem ridges_000_b64 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 64 68 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 64 4 (by decide +kernel)

theorem ridges_000_b68 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 68 72 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 68 4 (by decide +kernel)

theorem ridges_000_b72 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 72 76 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 72 4 (by decide +kernel)

theorem ridges_000_b76 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 76 80 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 76 4 (by decide +kernel)

theorem ridges_000_b80 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 80 84 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 80 4 (by decide +kernel)

theorem ridges_000_b84 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 84 88 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 84 4 (by decide +kernel)

theorem ridges_000_b88 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 88 92 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 88 4 (by decide +kernel)

theorem ridges_000_b92 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 92 96 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 92 4 (by decide +kernel)

theorem ridges_000_b96 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 96 100 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 96 4 (by decide +kernel)

theorem ridges_000_b100 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 100 104 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 100 4 (by decide +kernel)

theorem ridges_000_b104 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 104 108 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 104 4 (by decide +kernel)

theorem ridges_000_b108 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 108 112 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 108 4 (by decide +kernel)

theorem ridges_000_b112 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 112 116 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 112 4 (by decide +kernel)

theorem ridges_000_b116 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 116 120 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 116 4 (by decide +kernel)

theorem ridges_000_b120 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 120 124 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 120 4 (by decide +kernel)

theorem ridges_000_b124 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 124 128 :=
  interval_of_check (fun i => candidateCheck (Fin.ofNat 1024 i)) 124 4 (by decide +kernel)

theorem ridges_000 : Interval (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 128 :=
  (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 64 128
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 32 64
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 16 32
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 8 16
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 4 8
 ridges_000_b0
 ridges_000_b4)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 8 12 16
 ridges_000_b8
 ridges_000_b12))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 16 24 32
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 16 20 24
 ridges_000_b16
 ridges_000_b20)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 24 28 32
 ridges_000_b24
 ridges_000_b28)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 32 48 64
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 32 40 48
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 32 36 40
 ridges_000_b32
 ridges_000_b36)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 40 44 48
 ridges_000_b40
 ridges_000_b44))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 48 56 64
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 48 52 56
 ridges_000_b48
 ridges_000_b52)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 56 60 64
 ridges_000_b56
 ridges_000_b60))))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 64 96 128
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 64 80 96
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 64 72 80
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 64 68 72
 ridges_000_b64
 ridges_000_b68)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 72 76 80
 ridges_000_b72
 ridges_000_b76))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 80 88 96
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 80 84 88
 ridges_000_b80
 ridges_000_b84)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 88 92 96
 ridges_000_b88
 ridges_000_b92)))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 96 112 128
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 96 104 112
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 96 100 104
 ridges_000_b96
 ridges_000_b100)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 104 108 112
 ridges_000_b104
 ridges_000_b108))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 112 120 128
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 112 116 120
 ridges_000_b112
 ridges_000_b116)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 120 124 128
 ridges_000_b120
 ridges_000_b124)))))
end Papers.RationalityTen.SharedSmallGraph
