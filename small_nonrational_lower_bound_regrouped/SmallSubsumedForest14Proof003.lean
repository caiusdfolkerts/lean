module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest14Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest14
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
cert_test_block_4 1920 18 288 304 16
cert_test_block_4 1920 19 304 320 16
cert_test_block_4 1920 20 320 336 16
cert_test_block_4 1920 21 336 340 4
theorem test1920_complete : Interval test1920 0 340 :=
  (interval_append test1920 0 176 340
  (interval_append test1920 0 80 176
  (interval_append test1920 0 32 80
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 80
  test1920_block_2
  (interval_append test1920 48 64 80
  test1920_block_3
  test1920_block_4)))
  (interval_append test1920 80 128 176
  (interval_append test1920 80 96 128
  test1920_block_5
  (interval_append test1920 96 112 128
  test1920_block_6
  test1920_block_7))
  (interval_append test1920 128 144 176
  test1920_block_8
  (interval_append test1920 144 160 176
  test1920_block_9
  test1920_block_10))))
  (interval_append test1920 176 256 340
  (interval_append test1920 176 208 256
  (interval_append test1920 176 192 208
  test1920_block_11
  test1920_block_12)
  (interval_append test1920 208 224 256
  test1920_block_13
  (interval_append test1920 224 240 256
  test1920_block_14
  test1920_block_15)))
  (interval_append test1920 256 304 340
  (interval_append test1920 256 272 304
  test1920_block_16
  (interval_append test1920 272 288 304
  test1920_block_17
  test1920_block_18))
  (interval_append test1920 304 320 340
  test1920_block_19
  (interval_append test1920 320 336 340
  test1920_block_20
  test1920_block_21)))))
cert_nodeInterval_4 1920 2260
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest14
