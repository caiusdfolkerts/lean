module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0865Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0865
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
cert_test_block_3 5120 28 448 464 16
cert_test_block_3 5120 29 464 480 16
cert_test_block_3 5120 30 480 496 16
cert_test_block_3 5120 31 496 512 16
cert_test_block_3 5120 32 512 528 16
cert_test_block_3 5120 33 528 544 16
cert_test_block_3 5120 34 544 560 16
cert_test_block_3 5120 35 560 576 16
cert_test_block_3 5120 36 576 592 16
cert_test_block_3 5120 37 592 593 1
theorem test5120_complete : Interval test5120 0 593 :=
  (interval_append test5120 0 304 593
  (interval_append test5120 0 144 304
  (interval_append test5120 0 64 144
  (interval_append test5120 0 32 64
  (interval_append test5120 0 16 32
  test5120_block_0
  test5120_block_1)
  (interval_append test5120 32 48 64
  test5120_block_2
  test5120_block_3))
  (interval_append test5120 64 96 144
  (interval_append test5120 64 80 96
  test5120_block_4
  test5120_block_5)
  (interval_append test5120 96 112 144
  test5120_block_6
  (interval_append test5120 112 128 144
  test5120_block_7
  test5120_block_8))))
  (interval_append test5120 144 224 304
  (interval_append test5120 144 176 224
  (interval_append test5120 144 160 176
  test5120_block_9
  test5120_block_10)
  (interval_append test5120 176 192 224
  test5120_block_11
  (interval_append test5120 192 208 224
  test5120_block_12
  test5120_block_13)))
  (interval_append test5120 224 256 304
  (interval_append test5120 224 240 256
  test5120_block_14
  test5120_block_15)
  (interval_append test5120 256 272 304
  test5120_block_16
  (interval_append test5120 272 288 304
  test5120_block_17
  test5120_block_18)))))
  (interval_append test5120 304 448 593
  (interval_append test5120 304 368 448
  (interval_append test5120 304 336 368
  (interval_append test5120 304 320 336
  test5120_block_19
  test5120_block_20)
  (interval_append test5120 336 352 368
  test5120_block_21
  test5120_block_22))
  (interval_append test5120 368 400 448
  (interval_append test5120 368 384 400
  test5120_block_23
  test5120_block_24)
  (interval_append test5120 400 416 448
  test5120_block_25
  (interval_append test5120 416 432 448
  test5120_block_26
  test5120_block_27))))
  (interval_append test5120 448 528 593
  (interval_append test5120 448 480 528
  (interval_append test5120 448 464 480
  test5120_block_28
  test5120_block_29)
  (interval_append test5120 480 496 528
  test5120_block_30
  (interval_append test5120 496 512 528
  test5120_block_31
  test5120_block_32)))
  (interval_append test5120 528 560 593
  (interval_append test5120 528 544 560
  test5120_block_33
  test5120_block_34)
  (interval_append test5120 560 576 593
  test5120_block_35
  (interval_append test5120 576 592 593
  test5120_block_36
  test5120_block_37))))))
cert_nodeInterval_3 5120 5713
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0865
