module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0267Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0267
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 0
cert_test_block_3 0 0 0 16 16
cert_test_block_3 0 1 16 32 16
cert_test_block_3 0 2 32 48 16
cert_test_block_3 0 3 48 64 16
cert_test_block_3 0 4 64 80 16
cert_test_block_3 0 5 80 96 16
cert_test_block_3 0 6 96 112 16
cert_test_block_3 0 7 112 128 16
cert_test_block_3 0 8 128 144 16
cert_test_block_3 0 9 144 160 16
cert_test_block_3 0 10 160 176 16
cert_test_block_3 0 11 176 192 16
cert_test_block_3 0 12 192 208 16
cert_test_block_3 0 13 208 224 16
cert_test_block_3 0 14 224 240 16
cert_test_block_3 0 15 240 256 16
cert_test_block_3 0 16 256 272 16
cert_test_block_3 0 17 272 288 16
cert_test_block_3 0 18 288 304 16
cert_test_block_3 0 19 304 320 16
cert_test_block_3 0 20 320 336 16
cert_test_block_3 0 21 336 352 16
cert_test_block_3 0 22 352 368 16
cert_test_block_3 0 23 368 384 16
cert_test_block_3 0 24 384 400 16
cert_test_block_3 0 25 400 416 16
cert_test_block_3 0 26 416 432 16
cert_test_block_3 0 27 432 448 16
cert_test_block_3 0 28 448 464 16
cert_test_block_3 0 29 464 480 16
cert_test_block_3 0 30 480 496 16
theorem test0_complete : Interval test0 0 496 :=
  (interval_append test0 0 240 496
  (interval_append test0 0 112 240
  (interval_append test0 0 48 112
  (interval_append test0 0 16 48
  test0_block_0
  (interval_append test0 16 32 48
  test0_block_1
  test0_block_2))
  (interval_append test0 48 80 112
  (interval_append test0 48 64 80
  test0_block_3
  test0_block_4)
  (interval_append test0 80 96 112
  test0_block_5
  test0_block_6)))
  (interval_append test0 112 176 240
  (interval_append test0 112 144 176
  (interval_append test0 112 128 144
  test0_block_7
  test0_block_8)
  (interval_append test0 144 160 176
  test0_block_9
  test0_block_10))
  (interval_append test0 176 208 240
  (interval_append test0 176 192 208
  test0_block_11
  test0_block_12)
  (interval_append test0 208 224 240
  test0_block_13
  test0_block_14))))
  (interval_append test0 240 368 496
  (interval_append test0 240 304 368
  (interval_append test0 240 272 304
  (interval_append test0 240 256 272
  test0_block_15
  test0_block_16)
  (interval_append test0 272 288 304
  test0_block_17
  test0_block_18))
  (interval_append test0 304 336 368
  (interval_append test0 304 320 336
  test0_block_19
  test0_block_20)
  (interval_append test0 336 352 368
  test0_block_21
  test0_block_22)))
  (interval_append test0 368 432 496
  (interval_append test0 368 400 432
  (interval_append test0 368 384 400
  test0_block_23
  test0_block_24)
  (interval_append test0 400 416 432
  test0_block_25
  test0_block_26))
  (interval_append test0 432 464 496
  (interval_append test0 432 448 464
  test0_block_27
  test0_block_28)
  (interval_append test0 464 480 496
  test0_block_29
  test0_block_30)))))
cert_nodeInterval_3 0 496
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0267
