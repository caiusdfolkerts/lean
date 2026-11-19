module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest13Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest13
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
cert_test_block_4 1920 14 224 240 16
cert_test_block_4 1920 15 240 256 16
cert_test_block_4 1920 16 256 272 16
cert_test_block_4 1920 17 272 288 16
cert_test_block_4 1920 18 288 295 7
theorem test1920_complete : Interval test1920 0 295 :=
  (interval_append test1920 0 144 295
  (interval_append test1920 0 64 144
  (interval_append test1920 0 32 64
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 64
  test1920_block_2
  test1920_block_3))
  (interval_append test1920 64 96 144
  (interval_append test1920 64 80 96
  test1920_block_4
  test1920_block_5)
  (interval_append test1920 96 112 144
  test1920_block_6
  (interval_append test1920 112 128 144
  test1920_block_7
  test1920_block_8))))
  (interval_append test1920 144 224 295
  (interval_append test1920 144 176 224
  (interval_append test1920 144 160 176
  test1920_block_9
  test1920_block_10)
  (interval_append test1920 176 192 224
  test1920_block_11
  (interval_append test1920 192 208 224
  test1920_block_12
  test1920_block_13)))
  (interval_append test1920 224 256 295
  (interval_append test1920 224 240 256
  test1920_block_14
  test1920_block_15)
  (interval_append test1920 256 272 295
  test1920_block_16
  (interval_append test1920 272 288 295
  test1920_block_17
  test1920_block_18)))))
cert_nodeInterval_4 1920 2215
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest13
