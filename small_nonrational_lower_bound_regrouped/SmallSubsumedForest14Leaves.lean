module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest14Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest14
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTest_block_4 0 1
theorem leafTest_complete : Interval leafTest 0 1 :=
  leafTest_block_0
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest14
