module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0070Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0070
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 1280
cert_test_block_2 1280 0 0 32 32
cert_test_block_2 1280 1 32 64 32
cert_test_block_2 1280 2 64 96 32
cert_test_block_2 1280 3 96 128 32
cert_test_block_2 1280 4 128 160 32
cert_test_block_2 1280 5 160 192 32
cert_test_block_2 1280 6 192 224 32
cert_test_block_2 1280 7 224 256 32
cert_test_block_2 1280 8 256 288 32
cert_test_block_2 1280 9 288 314 26
theorem test1280_complete : Interval test1280 0 314 :=
  (interval_append test1280 0 160 314
  (interval_append test1280 0 64 160
  (interval_append test1280 0 32 64
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 64 96 160
  test1280_block_2
  (interval_append test1280 96 128 160
  test1280_block_3
  test1280_block_4)))
  (interval_append test1280 160 224 314
  (interval_append test1280 160 192 224
  test1280_block_5
  test1280_block_6)
  (interval_append test1280 224 256 314
  test1280_block_7
  (interval_append test1280 256 288 314
  test1280_block_8
  test1280_block_9))))
cert_nodeInterval_2 1280 1594
end Papers.RationalityTen.RootedForests.RootedRawForest0070
