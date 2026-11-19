module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0275Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0275
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 2560
cert_test_block_3 2560 0 0 16 16
cert_test_block_3 2560 1 16 32 16
cert_test_block_3 2560 2 32 48 16
cert_test_block_3 2560 3 48 64 16
cert_test_block_3 2560 4 64 80 16
cert_test_block_3 2560 5 80 96 16
cert_test_block_3 2560 6 96 112 16
cert_test_block_3 2560 7 112 128 16
cert_test_block_3 2560 8 128 144 16
cert_test_block_3 2560 9 144 160 16
cert_test_block_3 2560 10 160 176 16
cert_test_block_3 2560 11 176 192 16
cert_test_block_3 2560 12 192 208 16
cert_test_block_3 2560 13 208 224 16
cert_test_block_3 2560 14 224 240 16
cert_test_block_3 2560 15 240 256 16
cert_test_block_3 2560 16 256 272 16
cert_test_block_3 2560 17 272 288 16
cert_test_block_3 2560 18 288 304 16
cert_test_block_3 2560 19 304 320 16
cert_test_block_3 2560 20 320 336 16
cert_test_block_3 2560 21 336 352 16
cert_test_block_3 2560 22 352 368 16
cert_test_block_3 2560 23 368 384 16
cert_test_block_3 2560 24 384 400 16
cert_test_block_3 2560 25 400 416 16
cert_test_block_3 2560 26 416 432 16
cert_test_block_3 2560 27 432 448 16
cert_test_block_3 2560 28 448 464 16
cert_test_block_3 2560 29 464 480 16
cert_test_block_3 2560 30 480 496 16
cert_test_block_3 2560 31 496 512 16
cert_test_block_3 2560 32 512 528 16
cert_test_block_3 2560 33 528 544 16
cert_test_block_3 2560 34 544 560 16
cert_test_block_3 2560 35 560 576 16
cert_test_block_3 2560 36 576 592 16
cert_test_block_3 2560 37 592 599 7
theorem test2560_complete : Interval test2560 0 599 :=
  (interval_append test2560 0 304 599
  (interval_append test2560 0 144 304
  (interval_append test2560 0 64 144
  (interval_append test2560 0 32 64
  (interval_append test2560 0 16 32
  test2560_block_0
  test2560_block_1)
  (interval_append test2560 32 48 64
  test2560_block_2
  test2560_block_3))
  (interval_append test2560 64 96 144
  (interval_append test2560 64 80 96
  test2560_block_4
  test2560_block_5)
  (interval_append test2560 96 112 144
  test2560_block_6
  (interval_append test2560 112 128 144
  test2560_block_7
  test2560_block_8))))
  (interval_append test2560 144 224 304
  (interval_append test2560 144 176 224
  (interval_append test2560 144 160 176
  test2560_block_9
  test2560_block_10)
  (interval_append test2560 176 192 224
  test2560_block_11
  (interval_append test2560 192 208 224
  test2560_block_12
  test2560_block_13)))
  (interval_append test2560 224 256 304
  (interval_append test2560 224 240 256
  test2560_block_14
  test2560_block_15)
  (interval_append test2560 256 272 304
  test2560_block_16
  (interval_append test2560 272 288 304
  test2560_block_17
  test2560_block_18)))))
  (interval_append test2560 304 448 599
  (interval_append test2560 304 368 448
  (interval_append test2560 304 336 368
  (interval_append test2560 304 320 336
  test2560_block_19
  test2560_block_20)
  (interval_append test2560 336 352 368
  test2560_block_21
  test2560_block_22))
  (interval_append test2560 368 400 448
  (interval_append test2560 368 384 400
  test2560_block_23
  test2560_block_24)
  (interval_append test2560 400 416 448
  test2560_block_25
  (interval_append test2560 416 432 448
  test2560_block_26
  test2560_block_27))))
  (interval_append test2560 448 528 599
  (interval_append test2560 448 480 528
  (interval_append test2560 448 464 480
  test2560_block_28
  test2560_block_29)
  (interval_append test2560 480 496 528
  test2560_block_30
  (interval_append test2560 496 512 528
  test2560_block_31
  test2560_block_32)))
  (interval_append test2560 528 560 599
  (interval_append test2560 528 544 560
  test2560_block_33
  test2560_block_34)
  (interval_append test2560 560 576 599
  test2560_block_35
  (interval_append test2560 576 592 599
  test2560_block_36
  test2560_block_37))))))
cert_nodeInterval_3 2560 3159
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0275
