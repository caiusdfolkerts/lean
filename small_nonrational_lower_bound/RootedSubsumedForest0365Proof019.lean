module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0365Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 12160
cert_test_block_3 12160 0 0 16 16
cert_test_block_3 12160 1 16 32 16
cert_test_block_3 12160 2 32 48 16
cert_test_block_3 12160 3 48 64 16
cert_test_block_3 12160 4 64 80 16
cert_test_block_3 12160 5 80 96 16
cert_test_block_3 12160 6 96 112 16
cert_test_block_3 12160 7 112 128 16
cert_test_block_3 12160 8 128 144 16
cert_test_block_3 12160 9 144 160 16
cert_test_block_3 12160 10 160 176 16
cert_test_block_3 12160 11 176 192 16
cert_test_block_3 12160 12 192 208 16
cert_test_block_3 12160 13 208 224 16
cert_test_block_3 12160 14 224 240 16
cert_test_block_3 12160 15 240 256 16
cert_test_block_3 12160 16 256 272 16
cert_test_block_3 12160 17 272 288 16
cert_test_block_3 12160 18 288 304 16
cert_test_block_3 12160 19 304 320 16
cert_test_block_3 12160 20 320 336 16
cert_test_block_3 12160 21 336 352 16
cert_test_block_3 12160 22 352 368 16
cert_test_block_3 12160 23 368 384 16
cert_test_block_3 12160 24 384 400 16
cert_test_block_3 12160 25 400 416 16
cert_test_block_3 12160 26 416 432 16
cert_test_block_3 12160 27 432 448 16
cert_test_block_3 12160 28 448 464 16
cert_test_block_3 12160 29 464 480 16
cert_test_block_3 12160 30 480 496 16
cert_test_block_3 12160 31 496 512 16
cert_test_block_3 12160 32 512 528 16
cert_test_block_3 12160 33 528 544 16
cert_test_block_3 12160 34 544 560 16
cert_test_block_3 12160 35 560 576 16
cert_test_block_3 12160 36 576 592 16
cert_test_block_3 12160 37 592 607 15
theorem test12160_complete : Interval test12160 0 607 :=
  (interval_append test12160 0 304 607
  (interval_append test12160 0 144 304
  (interval_append test12160 0 64 144
  (interval_append test12160 0 32 64
  (interval_append test12160 0 16 32
  test12160_block_0
  test12160_block_1)
  (interval_append test12160 32 48 64
  test12160_block_2
  test12160_block_3))
  (interval_append test12160 64 96 144
  (interval_append test12160 64 80 96
  test12160_block_4
  test12160_block_5)
  (interval_append test12160 96 112 144
  test12160_block_6
  (interval_append test12160 112 128 144
  test12160_block_7
  test12160_block_8))))
  (interval_append test12160 144 224 304
  (interval_append test12160 144 176 224
  (interval_append test12160 144 160 176
  test12160_block_9
  test12160_block_10)
  (interval_append test12160 176 192 224
  test12160_block_11
  (interval_append test12160 192 208 224
  test12160_block_12
  test12160_block_13)))
  (interval_append test12160 224 256 304
  (interval_append test12160 224 240 256
  test12160_block_14
  test12160_block_15)
  (interval_append test12160 256 272 304
  test12160_block_16
  (interval_append test12160 272 288 304
  test12160_block_17
  test12160_block_18)))))
  (interval_append test12160 304 448 607
  (interval_append test12160 304 368 448
  (interval_append test12160 304 336 368
  (interval_append test12160 304 320 336
  test12160_block_19
  test12160_block_20)
  (interval_append test12160 336 352 368
  test12160_block_21
  test12160_block_22))
  (interval_append test12160 368 400 448
  (interval_append test12160 368 384 400
  test12160_block_23
  test12160_block_24)
  (interval_append test12160 400 416 448
  test12160_block_25
  (interval_append test12160 416 432 448
  test12160_block_26
  test12160_block_27))))
  (interval_append test12160 448 528 607
  (interval_append test12160 448 480 528
  (interval_append test12160 448 464 480
  test12160_block_28
  test12160_block_29)
  (interval_append test12160 480 496 528
  test12160_block_30
  (interval_append test12160 496 512 528
  test12160_block_31
  test12160_block_32)))
  (interval_append test12160 528 560 607
  (interval_append test12160 528 544 560
  test12160_block_33
  test12160_block_34)
  (interval_append test12160 560 576 607
  test12160_block_35
  (interval_append test12160 576 592 607
  test12160_block_36
  test12160_block_37))))))
cert_nodeInterval_3 12160 12767
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
