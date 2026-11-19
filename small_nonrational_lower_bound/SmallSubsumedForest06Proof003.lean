module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest06Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 1920
cert_test_block_4 1920 0 0 16 16
cert_test_block_4 1920 1 16 32 16
cert_test_block_4 1920 2 32 48 16
cert_test_block_4 1920 3 48 64 16
cert_test_block_4 1920 4 64 80 16
cert_test_block_4 1920 5 80 96 16
cert_test_block_4 1920 6 96 112 16
cert_test_block_4 1920 7 112 128 16
cert_test_block_4 1920 8 128 144 16
cert_test_block_4 1920 9 144 160 16
cert_test_block_4 1920 10 160 176 16
cert_test_block_4 1920 11 176 192 16
cert_test_block_4 1920 12 192 208 16
cert_test_block_4 1920 13 208 224 16
cert_test_block_4 1920 14 224 227 3
theorem test1920_complete : Interval test1920 0 227 :=
  (interval_append test1920 0 112 227
  (interval_append test1920 0 48 112
  (interval_append test1920 0 16 48
  test1920_block_0
  (interval_append test1920 16 32 48
  test1920_block_1
  test1920_block_2))
  (interval_append test1920 48 80 112
  (interval_append test1920 48 64 80
  test1920_block_3
  test1920_block_4)
  (interval_append test1920 80 96 112
  test1920_block_5
  test1920_block_6)))
  (interval_append test1920 112 176 227
  (interval_append test1920 112 144 176
  (interval_append test1920 112 128 144
  test1920_block_7
  test1920_block_8)
  (interval_append test1920 144 160 176
  test1920_block_9
  test1920_block_10))
  (interval_append test1920 176 208 227
  (interval_append test1920 176 192 208
  test1920_block_11
  test1920_block_12)
  (interval_append test1920 208 224 227
  test1920_block_13
  test1920_block_14))))
cert_nodeInterval_4 1920 2147
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest06
