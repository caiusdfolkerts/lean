module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0281Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0281
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 640
cert_test_block_3 640 0 0 16 16
cert_test_block_3 640 1 16 32 16
cert_test_block_3 640 2 32 48 16
cert_test_block_3 640 3 48 64 16
cert_test_block_3 640 4 64 80 16
cert_test_block_3 640 5 80 96 16
cert_test_block_3 640 6 96 112 16
cert_test_block_3 640 7 112 128 16
cert_test_block_3 640 8 128 144 16
cert_test_block_3 640 9 144 160 16
cert_test_block_3 640 10 160 176 16
cert_test_block_3 640 11 176 192 16
cert_test_block_3 640 12 192 208 16
cert_test_block_3 640 13 208 224 16
cert_test_block_3 640 14 224 240 16
cert_test_block_3 640 15 240 256 16
cert_test_block_3 640 16 256 272 16
cert_test_block_3 640 17 272 288 16
cert_test_block_3 640 18 288 304 16
cert_test_block_3 640 19 304 320 16
cert_test_block_3 640 20 320 336 16
cert_test_block_3 640 21 336 352 16
cert_test_block_3 640 22 352 368 16
cert_test_block_3 640 23 368 384 16
cert_test_block_3 640 24 384 400 16
cert_test_block_3 640 25 400 416 16
cert_test_block_3 640 26 416 432 16
cert_test_block_3 640 27 432 448 16
cert_test_block_3 640 28 448 464 16
cert_test_block_3 640 29 464 480 16
cert_test_block_3 640 30 480 496 16
cert_test_block_3 640 31 496 512 16
cert_test_block_3 640 32 512 528 16
cert_test_block_3 640 33 528 544 16
cert_test_block_3 640 34 544 560 16
cert_test_block_3 640 35 560 576 16
cert_test_block_3 640 36 576 592 16
cert_test_block_3 640 37 592 602 10
theorem test640_complete : Interval test640 0 602 :=
  (interval_append test640 0 304 602
  (interval_append test640 0 144 304
  (interval_append test640 0 64 144
  (interval_append test640 0 32 64
  (interval_append test640 0 16 32
  test640_block_0
  test640_block_1)
  (interval_append test640 32 48 64
  test640_block_2
  test640_block_3))
  (interval_append test640 64 96 144
  (interval_append test640 64 80 96
  test640_block_4
  test640_block_5)
  (interval_append test640 96 112 144
  test640_block_6
  (interval_append test640 112 128 144
  test640_block_7
  test640_block_8))))
  (interval_append test640 144 224 304
  (interval_append test640 144 176 224
  (interval_append test640 144 160 176
  test640_block_9
  test640_block_10)
  (interval_append test640 176 192 224
  test640_block_11
  (interval_append test640 192 208 224
  test640_block_12
  test640_block_13)))
  (interval_append test640 224 256 304
  (interval_append test640 224 240 256
  test640_block_14
  test640_block_15)
  (interval_append test640 256 272 304
  test640_block_16
  (interval_append test640 272 288 304
  test640_block_17
  test640_block_18)))))
  (interval_append test640 304 448 602
  (interval_append test640 304 368 448
  (interval_append test640 304 336 368
  (interval_append test640 304 320 336
  test640_block_19
  test640_block_20)
  (interval_append test640 336 352 368
  test640_block_21
  test640_block_22))
  (interval_append test640 368 400 448
  (interval_append test640 368 384 400
  test640_block_23
  test640_block_24)
  (interval_append test640 400 416 448
  test640_block_25
  (interval_append test640 416 432 448
  test640_block_26
  test640_block_27))))
  (interval_append test640 448 528 602
  (interval_append test640 448 480 528
  (interval_append test640 448 464 480
  test640_block_28
  test640_block_29)
  (interval_append test640 480 496 528
  test640_block_30
  (interval_append test640 496 512 528
  test640_block_31
  test640_block_32)))
  (interval_append test640 528 560 602
  (interval_append test640 528 544 560
  test640_block_33
  test640_block_34)
  (interval_append test640 560 576 602
  test640_block_35
  (interval_append test640 576 592 602
  test640_block_36
  test640_block_37))))))
cert_nodeInterval_3 640 1242
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0281
