module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0309Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0309
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 5120
cert_test_block_3 5120 0 0 16 16
cert_test_block_3 5120 1 16 32 16
cert_test_block_3 5120 2 32 48 16
cert_test_block_3 5120 3 48 64 16
cert_test_block_3 5120 4 64 80 16
cert_test_block_3 5120 5 80 96 16
cert_test_block_3 5120 6 96 112 16
cert_test_block_3 5120 7 112 128 16
cert_test_block_3 5120 8 128 144 16
cert_test_block_3 5120 9 144 160 16
cert_test_block_3 5120 10 160 176 16
cert_test_block_3 5120 11 176 192 16
cert_test_block_3 5120 12 192 208 16
cert_test_block_3 5120 13 208 224 16
cert_test_block_3 5120 14 224 240 16
cert_test_block_3 5120 15 240 256 16
cert_test_block_3 5120 16 256 272 16
cert_test_block_3 5120 17 272 288 16
cert_test_block_3 5120 18 288 304 16
cert_test_block_3 5120 19 304 320 16
cert_test_block_3 5120 20 320 336 16
cert_test_block_3 5120 21 336 352 16
cert_test_block_3 5120 22 352 368 16
cert_test_block_3 5120 23 368 384 16
cert_test_block_3 5120 24 384 400 16
cert_test_block_3 5120 25 400 416 16
cert_test_block_3 5120 26 416 432 16
cert_test_block_3 5120 27 432 448 16
cert_test_block_3 5120 28 448 457 9
theorem test5120_complete : Interval test5120 0 457 :=
  (interval_append test5120 0 224 457
  (interval_append test5120 0 112 224
  (interval_append test5120 0 48 112
  (interval_append test5120 0 16 48
  test5120_block_0
  (interval_append test5120 16 32 48
  test5120_block_1
  test5120_block_2))
  (interval_append test5120 48 80 112
  (interval_append test5120 48 64 80
  test5120_block_3
  test5120_block_4)
  (interval_append test5120 80 96 112
  test5120_block_5
  test5120_block_6)))
  (interval_append test5120 112 160 224
  (interval_append test5120 112 128 160
  test5120_block_7
  (interval_append test5120 128 144 160
  test5120_block_8
  test5120_block_9))
  (interval_append test5120 160 192 224
  (interval_append test5120 160 176 192
  test5120_block_10
  test5120_block_11)
  (interval_append test5120 192 208 224
  test5120_block_12
  test5120_block_13))))
  (interval_append test5120 224 336 457
  (interval_append test5120 224 272 336
  (interval_append test5120 224 240 272
  test5120_block_14
  (interval_append test5120 240 256 272
  test5120_block_15
  test5120_block_16))
  (interval_append test5120 272 304 336
  (interval_append test5120 272 288 304
  test5120_block_17
  test5120_block_18)
  (interval_append test5120 304 320 336
  test5120_block_19
  test5120_block_20)))
  (interval_append test5120 336 400 457
  (interval_append test5120 336 368 400
  (interval_append test5120 336 352 368
  test5120_block_21
  test5120_block_22)
  (interval_append test5120 368 384 400
  test5120_block_23
  test5120_block_24))
  (interval_append test5120 400 432 457
  (interval_append test5120 400 416 432
  test5120_block_25
  test5120_block_26)
  (interval_append test5120 432 448 457
  test5120_block_27
  test5120_block_28)))))
cert_nodeInterval_3 5120 5577
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0309
