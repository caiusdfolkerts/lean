module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0743Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 448
cert_leafTestAt_block_2 448 0 1
cert_leafTestAt_block_2 448 1 2
cert_leafTestAt_block_2 448 2 3
theorem leafTestAt448_complete : Interval leafTestAt448 0 3 :=
  (interval_append leafTestAt448 0 1 3
  leafTestAt448_block_0
  (interval_append leafTestAt448 1 2 3
  leafTestAt448_block_1
  leafTestAt448_block_2))
cert_leafInterval 448 451
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
