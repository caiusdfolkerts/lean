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
cert_test_13 79360
cert_test_block_4 79360 0 0 16 16
cert_test_block_4 79360 1 16 32 16
cert_test_block_4 79360 2 32 48 16
cert_test_block_4 79360 3 48 57 9
theorem test79360_complete : Interval test79360 0 57 :=
  (interval_append test79360 0 32 57
  (interval_append test79360 0 16 32
  test79360_block_0
  test79360_block_1)
  (interval_append test79360 32 48 57
  test79360_block_2
  test79360_block_3))
cert_nodeInterval_4 79360 79417
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
