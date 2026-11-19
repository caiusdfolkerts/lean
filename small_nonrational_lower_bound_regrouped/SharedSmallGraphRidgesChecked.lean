module
prelude
public import SharedSmallGraphRidges000
public import SharedSmallGraphRidges001
public import SharedSmallGraphRidges002
public import SharedSmallGraphRidges003
public import SharedSmallGraphRidges004
public import SharedSmallGraphRidges005
public import SharedSmallGraphRidges006
public import SharedSmallGraphRidges007

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem ridges_checked : ∀ i, candidateCheck i = true :=
  fin_of_interval candidateCheck
  (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 512 1024
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 256 512
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 0 128 256
 ridges_000
 ridges_001)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 256 384 512
 ridges_002
 ridges_003))
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 512 768 1024
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 512 640 768
 ridges_004
 ridges_005)
 (interval_append (fun i => candidateCheck (Fin.ofNat 1024 i)) 768 896 1024
 ridges_006
 ridges_007)))
end Papers.RationalityTen.SharedSmallGraph
