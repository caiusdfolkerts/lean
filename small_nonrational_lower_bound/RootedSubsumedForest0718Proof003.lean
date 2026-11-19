module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0718Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0718
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
cert_test_block_3 1920 22 352 368 16
cert_test_block_3 1920 23 368 384 16
cert_test_block_3 1920 24 384 400 16
cert_test_block_3 1920 25 400 416 16
cert_test_block_3 1920 26 416 423 7
theorem test1920_complete : Interval test1920 0 423 :=
  (interval_append test1920 0 208 423
  (interval_append test1920 0 96 208
  (interval_append test1920 0 48 96
  (interval_append test1920 0 16 48
  test1920_block_0
  (interval_append test1920 16 32 48
  test1920_block_1
  test1920_block_2))
  (interval_append test1920 48 64 96
  test1920_block_3
  (interval_append test1920 64 80 96
  test1920_block_4
  test1920_block_5)))
  (interval_append test1920 96 144 208
  (interval_append test1920 96 112 144
  test1920_block_6
  (interval_append test1920 112 128 144
  test1920_block_7
  test1920_block_8))
  (interval_append test1920 144 176 208
  (interval_append test1920 144 160 176
  test1920_block_9
  test1920_block_10)
  (interval_append test1920 176 192 208
  test1920_block_11
  test1920_block_12))))
  (interval_append test1920 208 320 423
  (interval_append test1920 208 256 320
  (interval_append test1920 208 224 256
  test1920_block_13
  (interval_append test1920 224 240 256
  test1920_block_14
  test1920_block_15))
  (interval_append test1920 256 288 320
  (interval_append test1920 256 272 288
  test1920_block_16
  test1920_block_17)
  (interval_append test1920 288 304 320
  test1920_block_18
  test1920_block_19)))
  (interval_append test1920 320 368 423
  (interval_append test1920 320 336 368
  test1920_block_20
  (interval_append test1920 336 352 368
  test1920_block_21
  test1920_block_22))
  (interval_append test1920 368 400 423
  (interval_append test1920 368 384 400
  test1920_block_23
  test1920_block_24)
  (interval_append test1920 400 416 423
  test1920_block_25
  test1920_block_26)))))
cert_nodeInterval_3 1920 2343
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0718
