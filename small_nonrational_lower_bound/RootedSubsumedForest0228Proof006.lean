module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0228Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0228
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 3840
cert_test_block_3 3840 0 0 16 16
cert_test_block_3 3840 1 16 32 16
cert_test_block_3 3840 2 32 48 16
cert_test_block_3 3840 3 48 64 16
cert_test_block_3 3840 4 64 80 16
cert_test_block_3 3840 5 80 96 16
cert_test_block_3 3840 6 96 112 16
cert_test_block_3 3840 7 112 128 16
cert_test_block_3 3840 8 128 144 16
cert_test_block_3 3840 9 144 160 16
cert_test_block_3 3840 10 160 176 16
cert_test_block_3 3840 11 176 192 16
cert_test_block_3 3840 12 192 208 16
cert_test_block_3 3840 13 208 224 16
cert_test_block_3 3840 14 224 240 16
cert_test_block_3 3840 15 240 256 16
cert_test_block_3 3840 16 256 272 16
cert_test_block_3 3840 17 272 288 16
cert_test_block_3 3840 18 288 304 16
cert_test_block_3 3840 19 304 320 16
cert_test_block_3 3840 20 320 336 16
cert_test_block_3 3840 21 336 352 16
cert_test_block_3 3840 22 352 368 16
cert_test_block_3 3840 23 368 384 16
cert_test_block_3 3840 24 384 400 16
cert_test_block_3 3840 25 400 416 16
cert_test_block_3 3840 26 416 432 16
cert_test_block_3 3840 27 432 448 16
cert_test_block_3 3840 28 448 464 16
cert_test_block_3 3840 29 464 480 16
cert_test_block_3 3840 30 480 496 16
cert_test_block_3 3840 31 496 512 16
cert_test_block_3 3840 32 512 520 8
theorem test3840_complete : Interval test3840 0 520 :=
  (interval_append test3840 0 256 520
  (interval_append test3840 0 128 256
  (interval_append test3840 0 64 128
  (interval_append test3840 0 32 64
  (interval_append test3840 0 16 32
  test3840_block_0
  test3840_block_1)
  (interval_append test3840 32 48 64
  test3840_block_2
  test3840_block_3))
  (interval_append test3840 64 96 128
  (interval_append test3840 64 80 96
  test3840_block_4
  test3840_block_5)
  (interval_append test3840 96 112 128
  test3840_block_6
  test3840_block_7)))
  (interval_append test3840 128 192 256
  (interval_append test3840 128 160 192
  (interval_append test3840 128 144 160
  test3840_block_8
  test3840_block_9)
  (interval_append test3840 160 176 192
  test3840_block_10
  test3840_block_11))
  (interval_append test3840 192 224 256
  (interval_append test3840 192 208 224
  test3840_block_12
  test3840_block_13)
  (interval_append test3840 224 240 256
  test3840_block_14
  test3840_block_15))))
  (interval_append test3840 256 384 520
  (interval_append test3840 256 320 384
  (interval_append test3840 256 288 320
  (interval_append test3840 256 272 288
  test3840_block_16
  test3840_block_17)
  (interval_append test3840 288 304 320
  test3840_block_18
  test3840_block_19))
  (interval_append test3840 320 352 384
  (interval_append test3840 320 336 352
  test3840_block_20
  test3840_block_21)
  (interval_append test3840 352 368 384
  test3840_block_22
  test3840_block_23)))
  (interval_append test3840 384 448 520
  (interval_append test3840 384 416 448
  (interval_append test3840 384 400 416
  test3840_block_24
  test3840_block_25)
  (interval_append test3840 416 432 448
  test3840_block_26
  test3840_block_27))
  (interval_append test3840 448 480 520
  (interval_append test3840 448 464 480
  test3840_block_28
  test3840_block_29)
  (interval_append test3840 480 496 520
  test3840_block_30
  (interval_append test3840 496 512 520
  test3840_block_31
  test3840_block_32))))))
cert_nodeInterval_3 3840 4360
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0228
