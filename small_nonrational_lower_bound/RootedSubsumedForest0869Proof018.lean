module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0869Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
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
cert_test_block_3 11520 32 512 521 9
theorem test11520_complete : Interval test11520 0 521 :=
  (interval_append test11520 0 256 521
  (interval_append test11520 0 128 256
  (interval_append test11520 0 64 128
  (interval_append test11520 0 32 64
  (interval_append test11520 0 16 32
  test11520_block_0
  test11520_block_1)
  (interval_append test11520 32 48 64
  test11520_block_2
  test11520_block_3))
  (interval_append test11520 64 96 128
  (interval_append test11520 64 80 96
  test11520_block_4
  test11520_block_5)
  (interval_append test11520 96 112 128
  test11520_block_6
  test11520_block_7)))
  (interval_append test11520 128 192 256
  (interval_append test11520 128 160 192
  (interval_append test11520 128 144 160
  test11520_block_8
  test11520_block_9)
  (interval_append test11520 160 176 192
  test11520_block_10
  test11520_block_11))
  (interval_append test11520 192 224 256
  (interval_append test11520 192 208 224
  test11520_block_12
  test11520_block_13)
  (interval_append test11520 224 240 256
  test11520_block_14
  test11520_block_15))))
  (interval_append test11520 256 384 521
  (interval_append test11520 256 320 384
  (interval_append test11520 256 288 320
  (interval_append test11520 256 272 288
  test11520_block_16
  test11520_block_17)
  (interval_append test11520 288 304 320
  test11520_block_18
  test11520_block_19))
  (interval_append test11520 320 352 384
  (interval_append test11520 320 336 352
  test11520_block_20
  test11520_block_21)
  (interval_append test11520 352 368 384
  test11520_block_22
  test11520_block_23)))
  (interval_append test11520 384 448 521
  (interval_append test11520 384 416 448
  (interval_append test11520 384 400 416
  test11520_block_24
  test11520_block_25)
  (interval_append test11520 416 432 448
  test11520_block_26
  test11520_block_27))
  (interval_append test11520 448 480 521
  (interval_append test11520 448 464 480
  test11520_block_28
  test11520_block_29)
  (interval_append test11520 480 496 521
  test11520_block_30
  (interval_append test11520 496 512 521
  test11520_block_31
  test11520_block_32))))))
cert_nodeInterval_3 11520 12041
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
