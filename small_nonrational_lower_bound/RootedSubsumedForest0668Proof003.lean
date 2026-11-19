module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0668Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0668
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
cert_test_block_3 1920 26 416 432 16
cert_test_block_3 1920 27 432 448 16
cert_test_block_3 1920 28 448 464 16
cert_test_block_3 1920 29 464 480 16
cert_test_block_3 1920 30 480 496 16
cert_test_block_3 1920 31 496 512 16
cert_test_block_3 1920 32 512 528 16
cert_test_block_3 1920 33 528 544 16
cert_test_block_3 1920 34 544 560 16
cert_test_block_3 1920 35 560 576 16
cert_test_block_3 1920 36 576 592 16
cert_test_block_3 1920 37 592 593 1
theorem test1920_complete : Interval test1920 0 593 :=
  (interval_append test1920 0 304 593
  (interval_append test1920 0 144 304
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
  (interval_append test1920 144 224 304
  (interval_append test1920 144 176 224
  (interval_append test1920 144 160 176
  test1920_block_9
  test1920_block_10)
  (interval_append test1920 176 192 224
  test1920_block_11
  (interval_append test1920 192 208 224
  test1920_block_12
  test1920_block_13)))
  (interval_append test1920 224 256 304
  (interval_append test1920 224 240 256
  test1920_block_14
  test1920_block_15)
  (interval_append test1920 256 272 304
  test1920_block_16
  (interval_append test1920 272 288 304
  test1920_block_17
  test1920_block_18)))))
  (interval_append test1920 304 448 593
  (interval_append test1920 304 368 448
  (interval_append test1920 304 336 368
  (interval_append test1920 304 320 336
  test1920_block_19
  test1920_block_20)
  (interval_append test1920 336 352 368
  test1920_block_21
  test1920_block_22))
  (interval_append test1920 368 400 448
  (interval_append test1920 368 384 400
  test1920_block_23
  test1920_block_24)
  (interval_append test1920 400 416 448
  test1920_block_25
  (interval_append test1920 416 432 448
  test1920_block_26
  test1920_block_27))))
  (interval_append test1920 448 528 593
  (interval_append test1920 448 480 528
  (interval_append test1920 448 464 480
  test1920_block_28
  test1920_block_29)
  (interval_append test1920 480 496 528
  test1920_block_30
  (interval_append test1920 496 512 528
  test1920_block_31
  test1920_block_32)))
  (interval_append test1920 528 560 593
  (interval_append test1920 528 544 560
  test1920_block_33
  test1920_block_34)
  (interval_append test1920 560 576 593
  test1920_block_35
  (interval_append test1920 576 592 593
  test1920_block_36
  test1920_block_37))))))
cert_nodeInterval_3 1920 2513
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0668
