module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0331Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0331
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
cert_test_block_3 2560 32 512 522 10
theorem test2560_complete : Interval test2560 0 522 :=
  (interval_append test2560 0 256 522
  (interval_append test2560 0 128 256
  (interval_append test2560 0 64 128
  (interval_append test2560 0 32 64
  (interval_append test2560 0 16 32
  test2560_block_0
  test2560_block_1)
  (interval_append test2560 32 48 64
  test2560_block_2
  test2560_block_3))
  (interval_append test2560 64 96 128
  (interval_append test2560 64 80 96
  test2560_block_4
  test2560_block_5)
  (interval_append test2560 96 112 128
  test2560_block_6
  test2560_block_7)))
  (interval_append test2560 128 192 256
  (interval_append test2560 128 160 192
  (interval_append test2560 128 144 160
  test2560_block_8
  test2560_block_9)
  (interval_append test2560 160 176 192
  test2560_block_10
  test2560_block_11))
  (interval_append test2560 192 224 256
  (interval_append test2560 192 208 224
  test2560_block_12
  test2560_block_13)
  (interval_append test2560 224 240 256
  test2560_block_14
  test2560_block_15))))
  (interval_append test2560 256 384 522
  (interval_append test2560 256 320 384
  (interval_append test2560 256 288 320
  (interval_append test2560 256 272 288
  test2560_block_16
  test2560_block_17)
  (interval_append test2560 288 304 320
  test2560_block_18
  test2560_block_19))
  (interval_append test2560 320 352 384
  (interval_append test2560 320 336 352
  test2560_block_20
  test2560_block_21)
  (interval_append test2560 352 368 384
  test2560_block_22
  test2560_block_23)))
  (interval_append test2560 384 448 522
  (interval_append test2560 384 416 448
  (interval_append test2560 384 400 416
  test2560_block_24
  test2560_block_25)
  (interval_append test2560 416 432 448
  test2560_block_26
  test2560_block_27))
  (interval_append test2560 448 480 522
  (interval_append test2560 448 464 480
  test2560_block_28
  test2560_block_29)
  (interval_append test2560 480 496 522
  test2560_block_30
  (interval_append test2560 496 512 522
  test2560_block_31
  test2560_block_32))))))
cert_nodeInterval_3 2560 3082
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0331
