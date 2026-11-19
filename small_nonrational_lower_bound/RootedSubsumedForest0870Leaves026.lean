module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0870Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 832
cert_leafTestAt_block_2 832 0 1
cert_leafTestAt_block_2 832 1 2
cert_leafTestAt_block_2 832 2 3
theorem leafTestAt832_complete : Interval leafTestAt832 0 3 :=
  (interval_append leafTestAt832 0 1 3
  leafTestAt832_block_0
  (interval_append leafTestAt832 1 2 3
  leafTestAt832_block_1
  leafTestAt832_block_2))
cert_leafInterval 832 835
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
