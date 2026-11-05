module
prelude
public import SharedSmallGraphWithin000
public import SharedSmallGraphWithin001
public import SharedSmallGraphWithin002
public import SharedSmallGraphWithin003

@[expose] public section
namespace Papers.RationalityTen.SharedSmallGraph
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming GrowthBitsets
open BatchedGrowthPruning GraphGrowthConstraints FiniteChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem within_checked : ∀ i, withinCheck i = true :=
  fin_of_interval withinCheck
  (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 0 512 1024
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 0 256 512
 within_000
 within_001)
 (interval_append (fun i => withinCheck (Fin.ofNat 1024 i)) 512 768 1024
 within_002
 within_003))
end Papers.RationalityTen.SharedSmallGraph
