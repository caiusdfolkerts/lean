module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0182Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0182
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
cert_test_block_3 0 31 496 512 16
cert_test_block_3 0 32 512 528 16
cert_test_block_3 0 33 528 544 16
cert_test_block_3 0 34 544 547 3
theorem test0_complete : Interval test0 0 547 :=
  (interval_append test0 0 272 547
  (interval_append test0 0 128 272
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 128
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 128
  test0_block_6
  test0_block_7)))
  (interval_append test0 128 192 272
  (interval_append test0 128 160 192
  (interval_append test0 128 144 160
  test0_block_8
  test0_block_9)
  (interval_append test0 160 176 192
  test0_block_10
  test0_block_11))
  (interval_append test0 192 224 272
  (interval_append test0 192 208 224
  test0_block_12
  test0_block_13)
  (interval_append test0 224 240 272
  test0_block_14
  (interval_append test0 240 256 272
  test0_block_15
  test0_block_16)))))
  (interval_append test0 272 416 547
  (interval_append test0 272 336 416
  (interval_append test0 272 304 336
  (interval_append test0 272 288 304
  test0_block_17
  test0_block_18)
  (interval_append test0 304 320 336
  test0_block_19
  test0_block_20))
  (interval_append test0 336 368 416
  (interval_append test0 336 352 368
  test0_block_21
  test0_block_22)
  (interval_append test0 368 384 416
  test0_block_23
  (interval_append test0 384 400 416
  test0_block_24
  test0_block_25))))
  (interval_append test0 416 480 547
  (interval_append test0 416 448 480
  (interval_append test0 416 432 448
  test0_block_26
  test0_block_27)
  (interval_append test0 448 464 480
  test0_block_28
  test0_block_29))
  (interval_append test0 480 512 547
  (interval_append test0 480 496 512
  test0_block_30
  test0_block_31)
  (interval_append test0 512 528 547
  test0_block_32
  (interval_append test0 528 544 547
  test0_block_33
  test0_block_34))))))
cert_nodeInterval_3 0 547
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0182
