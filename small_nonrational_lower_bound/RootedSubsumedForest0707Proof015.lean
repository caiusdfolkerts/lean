module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0707Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 9600
cert_test_block_3 9600 0 0 16 16
cert_test_block_3 9600 1 16 32 16
cert_test_block_3 9600 2 32 48 16
cert_test_block_3 9600 3 48 64 16
cert_test_block_3 9600 4 64 80 16
cert_test_block_3 9600 5 80 96 16
cert_test_block_3 9600 6 96 112 16
cert_test_block_3 9600 7 112 128 16
cert_test_block_3 9600 8 128 144 16
cert_test_block_3 9600 9 144 160 16
cert_test_block_3 9600 10 160 176 16
cert_test_block_3 9600 11 176 192 16
cert_test_block_3 9600 12 192 208 16
cert_test_block_3 9600 13 208 224 16
cert_test_block_3 9600 14 224 240 16
cert_test_block_3 9600 15 240 256 16
cert_test_block_3 9600 16 256 272 16
cert_test_block_3 9600 17 272 288 16
cert_test_block_3 9600 18 288 304 16
cert_test_block_3 9600 19 304 320 16
cert_test_block_3 9600 20 320 336 16
cert_test_block_3 9600 21 336 352 16
cert_test_block_3 9600 22 352 368 16
cert_test_block_3 9600 23 368 384 16
cert_test_block_3 9600 24 384 400 16
cert_test_block_3 9600 25 400 416 16
cert_test_block_3 9600 26 416 432 16
cert_test_block_3 9600 27 432 448 16
cert_test_block_3 9600 28 448 464 16
cert_test_block_3 9600 29 464 480 16
cert_test_block_3 9600 30 480 496 16
cert_test_block_3 9600 31 496 512 16
cert_test_block_3 9600 32 512 528 16
cert_test_block_3 9600 33 528 544 16
cert_test_block_3 9600 34 544 560 16
cert_test_block_3 9600 35 560 576 16
cert_test_block_3 9600 36 576 592 16
cert_test_block_3 9600 37 592 608 16
cert_test_block_3 9600 38 608 623 15
theorem test9600_complete : Interval test9600 0 623 :=
  (interval_append test9600 0 304 623
  (interval_append test9600 0 144 304
  (interval_append test9600 0 64 144
  (interval_append test9600 0 32 64
  (interval_append test9600 0 16 32
  test9600_block_0
  test9600_block_1)
  (interval_append test9600 32 48 64
  test9600_block_2
  test9600_block_3))
  (interval_append test9600 64 96 144
  (interval_append test9600 64 80 96
  test9600_block_4
  test9600_block_5)
  (interval_append test9600 96 112 144
  test9600_block_6
  (interval_append test9600 112 128 144
  test9600_block_7
  test9600_block_8))))
  (interval_append test9600 144 224 304
  (interval_append test9600 144 176 224
  (interval_append test9600 144 160 176
  test9600_block_9
  test9600_block_10)
  (interval_append test9600 176 192 224
  test9600_block_11
  (interval_append test9600 192 208 224
  test9600_block_12
  test9600_block_13)))
  (interval_append test9600 224 256 304
  (interval_append test9600 224 240 256
  test9600_block_14
  test9600_block_15)
  (interval_append test9600 256 272 304
  test9600_block_16
  (interval_append test9600 272 288 304
  test9600_block_17
  test9600_block_18)))))
  (interval_append test9600 304 464 623
  (interval_append test9600 304 384 464
  (interval_append test9600 304 336 384
  (interval_append test9600 304 320 336
  test9600_block_19
  test9600_block_20)
  (interval_append test9600 336 352 384
  test9600_block_21
  (interval_append test9600 352 368 384
  test9600_block_22
  test9600_block_23)))
  (interval_append test9600 384 416 464
  (interval_append test9600 384 400 416
  test9600_block_24
  test9600_block_25)
  (interval_append test9600 416 432 464
  test9600_block_26
  (interval_append test9600 432 448 464
  test9600_block_27
  test9600_block_28))))
  (interval_append test9600 464 544 623
  (interval_append test9600 464 496 544
  (interval_append test9600 464 480 496
  test9600_block_29
  test9600_block_30)
  (interval_append test9600 496 512 544
  test9600_block_31
  (interval_append test9600 512 528 544
  test9600_block_32
  test9600_block_33)))
  (interval_append test9600 544 576 623
  (interval_append test9600 544 560 576
  test9600_block_34
  test9600_block_35)
  (interval_append test9600 576 592 623
  test9600_block_36
  (interval_append test9600 592 608 623
  test9600_block_37
  test9600_block_38))))))
cert_nodeInterval_3 9600 10223
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
