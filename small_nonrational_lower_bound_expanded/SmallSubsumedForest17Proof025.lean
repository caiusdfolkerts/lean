module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest17Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 16000
cert_test_block_4 16000 0 0 16 16
cert_test_block_4 16000 1 16 19 3
theorem test16000_complete : Interval test16000 0 19 :=
  (interval_append test16000 0 16 19
  test16000_block_0
  test16000_block_1)
cert_nodeInterval_4 16000 16019
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
