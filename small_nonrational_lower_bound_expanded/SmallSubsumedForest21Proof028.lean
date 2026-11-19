module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest21Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest21
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 17920
cert_test_block_4 17920 0 0 16 16
cert_test_block_4 17920 1 16 32 16
cert_test_block_4 17920 2 32 48 16
cert_test_block_4 17920 3 48 64 16
cert_test_block_4 17920 4 64 80 16
cert_test_block_4 17920 5 80 96 16
cert_test_block_4 17920 6 96 112 16
cert_test_block_4 17920 7 112 128 16
cert_test_block_4 17920 8 128 144 16
cert_test_block_4 17920 9 144 160 16
cert_test_block_4 17920 10 160 176 16
cert_test_block_4 17920 11 176 192 16
cert_test_block_4 17920 12 192 208 16
cert_test_block_4 17920 13 208 224 16
cert_test_block_4 17920 14 224 234 10
theorem test17920_complete : Interval test17920 0 234 :=
  (interval_append test17920 0 112 234
  (interval_append test17920 0 48 112
  (interval_append test17920 0 16 48
  test17920_block_0
  (interval_append test17920 16 32 48
  test17920_block_1
  test17920_block_2))
  (interval_append test17920 48 80 112
  (interval_append test17920 48 64 80
  test17920_block_3
  test17920_block_4)
  (interval_append test17920 80 96 112
  test17920_block_5
  test17920_block_6)))
  (interval_append test17920 112 176 234
  (interval_append test17920 112 144 176
  (interval_append test17920 112 128 144
  test17920_block_7
  test17920_block_8)
  (interval_append test17920 144 160 176
  test17920_block_9
  test17920_block_10))
  (interval_append test17920 176 208 234
  (interval_append test17920 176 192 208
  test17920_block_11
  test17920_block_12)
  (interval_append test17920 208 224 234
  test17920_block_13
  test17920_block_14))))
cert_nodeInterval_4 17920 18154
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest21
