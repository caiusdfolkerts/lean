module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest22Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest22
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 1920
cert_test_block_4 1920 0 0 16 16
cert_test_block_4 1920 1 16 32 16
cert_test_block_4 1920 2 32 48 16
cert_test_block_4 1920 3 48 64 16
cert_test_block_4 1920 4 64 69 5
theorem test1920_complete : Interval test1920 0 69 :=
  (interval_append test1920 0 32 69
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 69
  test1920_block_2
  (interval_append test1920 48 64 69
  test1920_block_3
  test1920_block_4)))
cert_nodeInterval_4 1920 1989
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest22
