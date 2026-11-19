module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0319Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 64
cert_leafTestAt_block_2 64 0 1
cert_leafTestAt_block_2 64 1 2
cert_leafTestAt_block_2 64 2 3
cert_leafTestAt_block_2 64 3 4
cert_leafTestAt_block_2 64 4 5
theorem leafTestAt64_complete : Interval leafTestAt64 0 5 :=
  (interval_append leafTestAt64 0 2 5
  (interval_append leafTestAt64 0 1 2
  leafTestAt64_block_0
  leafTestAt64_block_1)
  (interval_append leafTestAt64 2 3 5
  leafTestAt64_block_2
  (interval_append leafTestAt64 3 4 5
  leafTestAt64_block_3
  leafTestAt64_block_4)))
cert_leafInterval 64 69
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
