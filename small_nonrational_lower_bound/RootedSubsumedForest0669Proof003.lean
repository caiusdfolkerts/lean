module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0669Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0669
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 1920
cert_test_block_3 1920 0 0 16 16
cert_test_block_3 1920 1 16 32 16
cert_test_block_3 1920 2 32 48 16
cert_test_block_3 1920 3 48 64 16
cert_test_block_3 1920 4 64 80 16
cert_test_block_3 1920 5 80 96 16
cert_test_block_3 1920 6 96 112 16
cert_test_block_3 1920 7 112 128 16
cert_test_block_3 1920 8 128 144 16
cert_test_block_3 1920 9 144 160 16
cert_test_block_3 1920 10 160 176 16
cert_test_block_3 1920 11 176 192 16
cert_test_block_3 1920 12 192 208 16
cert_test_block_3 1920 13 208 224 16
cert_test_block_3 1920 14 224 240 16
cert_test_block_3 1920 15 240 256 16
cert_test_block_3 1920 16 256 272 16
cert_test_block_3 1920 17 272 288 16
cert_test_block_3 1920 18 288 304 16
cert_test_block_3 1920 19 304 320 16
cert_test_block_3 1920 20 320 336 16
cert_test_block_3 1920 21 336 352 16
cert_test_block_3 1920 22 352 358 6
theorem test1920_complete : Interval test1920 0 358 :=
  (interval_append test1920 0 176 358
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
  (interval_append test1920 176 272 358
  (interval_append test1920 176 224 272
  (interval_append test1920 176 192 224
  test1920_block_11
  (interval_append test1920 192 208 224
  test1920_block_12
  test1920_block_13))
  (interval_append test1920 224 240 272
  test1920_block_14
  (interval_append test1920 240 256 272
  test1920_block_15
  test1920_block_16)))
  (interval_append test1920 272 320 358
  (interval_append test1920 272 288 320
  test1920_block_17
  (interval_append test1920 288 304 320
  test1920_block_18
  test1920_block_19))
  (interval_append test1920 320 336 358
  test1920_block_20
  (interval_append test1920 336 352 358
  test1920_block_21
  test1920_block_22)))))
cert_nodeInterval_3 1920 2278
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0669
