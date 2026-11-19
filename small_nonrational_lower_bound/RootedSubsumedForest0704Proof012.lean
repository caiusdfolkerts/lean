module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0704Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0704
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 7680
cert_test_block_3 7680 0 0 16 16
cert_test_block_3 7680 1 16 32 16
cert_test_block_3 7680 2 32 48 16
cert_test_block_3 7680 3 48 64 16
cert_test_block_3 7680 4 64 80 16
cert_test_block_3 7680 5 80 96 16
cert_test_block_3 7680 6 96 112 16
cert_test_block_3 7680 7 112 128 16
cert_test_block_3 7680 8 128 144 16
cert_test_block_3 7680 9 144 160 16
cert_test_block_3 7680 10 160 176 16
cert_test_block_3 7680 11 176 192 16
cert_test_block_3 7680 12 192 208 16
cert_test_block_3 7680 13 208 224 16
cert_test_block_3 7680 14 224 240 16
cert_test_block_3 7680 15 240 256 16
cert_test_block_3 7680 16 256 272 16
cert_test_block_3 7680 17 272 288 16
cert_test_block_3 7680 18 288 304 16
cert_test_block_3 7680 19 304 320 16
cert_test_block_3 7680 20 320 336 16
cert_test_block_3 7680 21 336 352 16
cert_test_block_3 7680 22 352 368 16
cert_test_block_3 7680 23 368 384 16
cert_test_block_3 7680 24 384 400 16
cert_test_block_3 7680 25 400 416 16
cert_test_block_3 7680 26 416 432 16
cert_test_block_3 7680 27 432 448 16
cert_test_block_3 7680 28 448 464 16
cert_test_block_3 7680 29 464 480 16
cert_test_block_3 7680 30 480 496 16
cert_test_block_3 7680 31 496 512 16
cert_test_block_3 7680 32 512 528 16
cert_test_block_3 7680 33 528 544 16
cert_test_block_3 7680 34 544 560 16
cert_test_block_3 7680 35 560 576 16
cert_test_block_3 7680 36 576 592 16
cert_test_block_3 7680 37 592 600 8
theorem test7680_complete : Interval test7680 0 600 :=
  (interval_append test7680 0 304 600
  (interval_append test7680 0 144 304
  (interval_append test7680 0 64 144
  (interval_append test7680 0 32 64
  (interval_append test7680 0 16 32
  test7680_block_0
  test7680_block_1)
  (interval_append test7680 32 48 64
  test7680_block_2
  test7680_block_3))
  (interval_append test7680 64 96 144
  (interval_append test7680 64 80 96
  test7680_block_4
  test7680_block_5)
  (interval_append test7680 96 112 144
  test7680_block_6
  (interval_append test7680 112 128 144
  test7680_block_7
  test7680_block_8))))
  (interval_append test7680 144 224 304
  (interval_append test7680 144 176 224
  (interval_append test7680 144 160 176
  test7680_block_9
  test7680_block_10)
  (interval_append test7680 176 192 224
  test7680_block_11
  (interval_append test7680 192 208 224
  test7680_block_12
  test7680_block_13)))
  (interval_append test7680 224 256 304
  (interval_append test7680 224 240 256
  test7680_block_14
  test7680_block_15)
  (interval_append test7680 256 272 304
  test7680_block_16
  (interval_append test7680 272 288 304
  test7680_block_17
  test7680_block_18)))))
  (interval_append test7680 304 448 600
  (interval_append test7680 304 368 448
  (interval_append test7680 304 336 368
  (interval_append test7680 304 320 336
  test7680_block_19
  test7680_block_20)
  (interval_append test7680 336 352 368
  test7680_block_21
  test7680_block_22))
  (interval_append test7680 368 400 448
  (interval_append test7680 368 384 400
  test7680_block_23
  test7680_block_24)
  (interval_append test7680 400 416 448
  test7680_block_25
  (interval_append test7680 416 432 448
  test7680_block_26
  test7680_block_27))))
  (interval_append test7680 448 528 600
  (interval_append test7680 448 480 528
  (interval_append test7680 448 464 480
  test7680_block_28
  test7680_block_29)
  (interval_append test7680 480 496 528
  test7680_block_30
  (interval_append test7680 496 512 528
  test7680_block_31
  test7680_block_32)))
  (interval_append test7680 528 560 600
  (interval_append test7680 528 544 560
  test7680_block_33
  test7680_block_34)
  (interval_append test7680 560 576 600
  test7680_block_35
  (interval_append test7680 576 592 600
  test7680_block_36
  test7680_block_37))))))
cert_nodeInterval_3 7680 8280
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0704
