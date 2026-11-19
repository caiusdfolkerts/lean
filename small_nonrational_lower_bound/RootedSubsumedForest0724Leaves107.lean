module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 3424
cert_leafTestAt_block_2 3424 0 1
cert_leafTestAt_block_2 3424 1 2
cert_leafTestAt_block_2 3424 2 3
cert_leafTestAt_block_2 3424 3 4
theorem leafTestAt3424_complete : Interval leafTestAt3424 0 4 :=
  (interval_append leafTestAt3424 0 2 4
  (interval_append leafTestAt3424 0 1 2
  leafTestAt3424_block_0
  leafTestAt3424_block_1)
  (interval_append leafTestAt3424 2 3 4
  leafTestAt3424_block_2
  leafTestAt3424_block_3))
cert_leafInterval 3424 3428
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
