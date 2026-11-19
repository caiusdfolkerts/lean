module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0695Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 19200
cert_test_block_3 19200 0 0 16 16
cert_test_block_3 19200 1 16 32 16
cert_test_block_3 19200 2 32 48 16
cert_test_block_3 19200 3 48 64 16
cert_test_block_3 19200 4 64 80 16
cert_test_block_3 19200 5 80 96 16
cert_test_block_3 19200 6 96 112 16
cert_test_block_3 19200 7 112 128 16
cert_test_block_3 19200 8 128 144 16
cert_test_block_3 19200 9 144 160 16
cert_test_block_3 19200 10 160 176 16
cert_test_block_3 19200 11 176 192 16
cert_test_block_3 19200 12 192 208 16
cert_test_block_3 19200 13 208 224 16
cert_test_block_3 19200 14 224 240 16
cert_test_block_3 19200 15 240 256 16
cert_test_block_3 19200 16 256 272 16
cert_test_block_3 19200 17 272 288 16
cert_test_block_3 19200 18 288 304 16
cert_test_block_3 19200 19 304 320 16
cert_test_block_3 19200 20 320 336 16
cert_test_block_3 19200 21 336 352 16
cert_test_block_3 19200 22 352 368 16
cert_test_block_3 19200 23 368 384 16
cert_test_block_3 19200 24 384 400 16
cert_test_block_3 19200 25 400 416 16
cert_test_block_3 19200 26 416 432 16
cert_test_block_3 19200 27 432 448 16
cert_test_block_3 19200 28 448 464 16
cert_test_block_3 19200 29 464 480 16
cert_test_block_3 19200 30 480 496 16
cert_test_block_3 19200 31 496 512 16
cert_test_block_3 19200 32 512 528 16
cert_test_block_3 19200 33 528 544 16
cert_test_block_3 19200 34 544 555 11
theorem test19200_complete : Interval test19200 0 555 :=
  (interval_append test19200 0 272 555
  (interval_append test19200 0 128 272
  (interval_append test19200 0 64 128
  (interval_append test19200 0 32 64
  (interval_append test19200 0 16 32
  test19200_block_0
  test19200_block_1)
  (interval_append test19200 32 48 64
  test19200_block_2
  test19200_block_3))
  (interval_append test19200 64 96 128
  (interval_append test19200 64 80 96
  test19200_block_4
  test19200_block_5)
  (interval_append test19200 96 112 128
  test19200_block_6
  test19200_block_7)))
  (interval_append test19200 128 192 272
  (interval_append test19200 128 160 192
  (interval_append test19200 128 144 160
  test19200_block_8
  test19200_block_9)
  (interval_append test19200 160 176 192
  test19200_block_10
  test19200_block_11))
  (interval_append test19200 192 224 272
  (interval_append test19200 192 208 224
  test19200_block_12
  test19200_block_13)
  (interval_append test19200 224 240 272
  test19200_block_14
  (interval_append test19200 240 256 272
  test19200_block_15
  test19200_block_16)))))
  (interval_append test19200 272 416 555
  (interval_append test19200 272 336 416
  (interval_append test19200 272 304 336
  (interval_append test19200 272 288 304
  test19200_block_17
  test19200_block_18)
  (interval_append test19200 304 320 336
  test19200_block_19
  test19200_block_20))
  (interval_append test19200 336 368 416
  (interval_append test19200 336 352 368
  test19200_block_21
  test19200_block_22)
  (interval_append test19200 368 384 416
  test19200_block_23
  (interval_append test19200 384 400 416
  test19200_block_24
  test19200_block_25))))
  (interval_append test19200 416 480 555
  (interval_append test19200 416 448 480
  (interval_append test19200 416 432 448
  test19200_block_26
  test19200_block_27)
  (interval_append test19200 448 464 480
  test19200_block_28
  test19200_block_29))
  (interval_append test19200 480 512 555
  (interval_append test19200 480 496 512
  test19200_block_30
  test19200_block_31)
  (interval_append test19200 512 528 555
  test19200_block_32
  (interval_append test19200 528 544 555
  test19200_block_33
  test19200_block_34))))))
cert_nodeInterval_3 19200 19755
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
