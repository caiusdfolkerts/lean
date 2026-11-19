module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0098Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0098
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 1920
cert_test_block_2 1920 0 0 32 32
cert_test_block_2 1920 1 32 64 32
cert_test_block_2 1920 2 64 96 32
cert_test_block_2 1920 3 96 128 32
cert_test_block_2 1920 4 128 160 32
cert_test_block_2 1920 5 160 192 32
cert_test_block_2 1920 6 192 224 32
cert_test_block_2 1920 7 224 256 32
cert_test_block_2 1920 8 256 288 32
cert_test_block_2 1920 9 288 289 1
theorem test1920_complete : Interval test1920 0 289 :=
  (interval_append test1920 0 160 289
  (interval_append test1920 0 64 160
  (interval_append test1920 0 32 64
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 64 96 160
  test1920_block_2
  (interval_append test1920 96 128 160
  test1920_block_3
  test1920_block_4)))
  (interval_append test1920 160 224 289
  (interval_append test1920 160 192 224
  test1920_block_5
  test1920_block_6)
  (interval_append test1920 224 256 289
  test1920_block_7
  (interval_append test1920 256 288 289
  test1920_block_8
  test1920_block_9))))
cert_nodeInterval_2 1920 2209
end Papers.RationalityTen.RootedForests.RootedRawForest0098
