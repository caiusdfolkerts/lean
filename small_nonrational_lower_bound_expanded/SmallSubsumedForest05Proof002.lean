module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest05Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 1280
cert_test_block_4 1280 0 0 16 16
cert_test_block_4 1280 1 16 32 16
cert_test_block_4 1280 2 32 48 16
cert_test_block_4 1280 3 48 64 16
cert_test_block_4 1280 4 64 80 16
cert_test_block_4 1280 5 80 96 16
cert_test_block_4 1280 6 96 112 16
cert_test_block_4 1280 7 112 124 12
theorem test1280_complete : Interval test1280 0 124 :=
  (interval_append test1280 0 64 124
  (interval_append test1280 0 32 64
  (interval_append test1280 0 16 32
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 32 48 64
  test1280_block_2
  test1280_block_3))
  (interval_append test1280 64 96 124
  (interval_append test1280 64 80 96
  test1280_block_4
  test1280_block_5)
  (interval_append test1280 96 112 124
  test1280_block_6
  test1280_block_7)))
cert_nodeInterval_4 1280 1404
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest05
