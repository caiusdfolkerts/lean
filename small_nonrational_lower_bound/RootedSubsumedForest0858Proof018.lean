module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0858Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 11520
cert_test_block_3 11520 0 0 16 16
cert_test_block_3 11520 1 16 32 16
cert_test_block_3 11520 2 32 48 16
cert_test_block_3 11520 3 48 64 16
cert_test_block_3 11520 4 64 80 16
cert_test_block_3 11520 5 80 96 16
cert_test_block_3 11520 6 96 112 16
cert_test_block_3 11520 7 112 128 16
cert_test_block_3 11520 8 128 144 16
cert_test_block_3 11520 9 144 160 16
cert_test_block_3 11520 10 160 176 16
cert_test_block_3 11520 11 176 192 16
cert_test_block_3 11520 12 192 208 16
cert_test_block_3 11520 13 208 224 16
cert_test_block_3 11520 14 224 240 16
cert_test_block_3 11520 15 240 256 16
cert_test_block_3 11520 16 256 272 16
cert_test_block_3 11520 17 272 288 16
cert_test_block_3 11520 18 288 304 16
cert_test_block_3 11520 19 304 320 16
cert_test_block_3 11520 20 320 336 16
cert_test_block_3 11520 21 336 352 16
cert_test_block_3 11520 22 352 368 16
cert_test_block_3 11520 23 368 384 16
cert_test_block_3 11520 24 384 400 16
cert_test_block_3 11520 25 400 416 16
cert_test_block_3 11520 26 416 432 16
cert_test_block_3 11520 27 432 448 16
cert_test_block_3 11520 28 448 464 16
cert_test_block_3 11520 29 464 480 16
cert_test_block_3 11520 30 480 496 16
cert_test_block_3 11520 31 496 512 16
cert_test_block_3 11520 32 512 528 16
cert_test_block_3 11520 33 528 544 16
cert_test_block_3 11520 34 544 560 16
cert_test_block_3 11520 35 560 576 16
cert_test_block_3 11520 36 576 592 16
cert_test_block_3 11520 37 592 608 16
cert_test_block_3 11520 38 608 617 9
theorem test11520_complete : Interval test11520 0 617 :=
  (interval_append test11520 0 304 617
  (interval_append test11520 0 144 304
  (interval_append test11520 0 64 144
  (interval_append test11520 0 32 64
  (interval_append test11520 0 16 32
  test11520_block_0
  test11520_block_1)
  (interval_append test11520 32 48 64
  test11520_block_2
  test11520_block_3))
  (interval_append test11520 64 96 144
  (interval_append test11520 64 80 96
  test11520_block_4
  test11520_block_5)
  (interval_append test11520 96 112 144
  test11520_block_6
  (interval_append test11520 112 128 144
  test11520_block_7
  test11520_block_8))))
  (interval_append test11520 144 224 304
  (interval_append test11520 144 176 224
  (interval_append test11520 144 160 176
  test11520_block_9
  test11520_block_10)
  (interval_append test11520 176 192 224
  test11520_block_11
  (interval_append test11520 192 208 224
  test11520_block_12
  test11520_block_13)))
  (interval_append test11520 224 256 304
  (interval_append test11520 224 240 256
  test11520_block_14
  test11520_block_15)
  (interval_append test11520 256 272 304
  test11520_block_16
  (interval_append test11520 272 288 304
  test11520_block_17
  test11520_block_18)))))
  (interval_append test11520 304 464 617
  (interval_append test11520 304 384 464
  (interval_append test11520 304 336 384
  (interval_append test11520 304 320 336
  test11520_block_19
  test11520_block_20)
  (interval_append test11520 336 352 384
  test11520_block_21
  (interval_append test11520 352 368 384
  test11520_block_22
  test11520_block_23)))
  (interval_append test11520 384 416 464
  (interval_append test11520 384 400 416
  test11520_block_24
  test11520_block_25)
  (interval_append test11520 416 432 464
  test11520_block_26
  (interval_append test11520 432 448 464
  test11520_block_27
  test11520_block_28))))
  (interval_append test11520 464 544 617
  (interval_append test11520 464 496 544
  (interval_append test11520 464 480 496
  test11520_block_29
  test11520_block_30)
  (interval_append test11520 496 512 544
  test11520_block_31
  (interval_append test11520 512 528 544
  test11520_block_32
  test11520_block_33)))
  (interval_append test11520 544 576 617
  (interval_append test11520 544 560 576
  test11520_block_34
  test11520_block_35)
  (interval_append test11520 576 592 617
  test11520_block_36
  (interval_append test11520 592 608 617
  test11520_block_37
  test11520_block_38))))))
cert_nodeInterval_3 11520 12137
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0858
