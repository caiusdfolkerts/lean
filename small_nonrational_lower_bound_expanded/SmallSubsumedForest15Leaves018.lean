module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest15Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt_2 576
cert_leafTestAt_block_3 576 0 1
cert_leafTestAt_block_3 576 1 2
theorem leafTestAt576_complete : Interval leafTestAt576 0 2 :=
  (interval_append leafTestAt576 0 1 2
  leafTestAt576_block_0
  leafTestAt576_block_1)
cert_leafInterval_2 576 578
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
