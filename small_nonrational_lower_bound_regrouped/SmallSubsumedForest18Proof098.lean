module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest18Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 62720
cert_test_block_4 62720 0 0 16 16
cert_test_block_4 62720 1 16 32 16
cert_test_block_4 62720 2 32 48 16
cert_test_block_4 62720 3 48 49 1
theorem test62720_complete : Interval test62720 0 49 :=
  (interval_append test62720 0 32 49
  (interval_append test62720 0 16 32
  test62720_block_0
  test62720_block_1)
  (interval_append test62720 32 48 49
  test62720_block_2
  test62720_block_3))
cert_nodeInterval_4 62720 62769
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
