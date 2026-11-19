module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0670Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0670
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
cert_test_block_3 0 34 544 560 16
cert_test_block_3 0 35 560 576 16
cert_test_block_3 0 36 576 585 9
theorem test0_complete : Interval test0 0 585 :=
  (interval_append test0 0 288 585
  (interval_append test0 0 144 288
  (interval_append test0 0 64 144
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 144
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 144
  test0_block_6
  (interval_append test0 112 128 144
  test0_block_7
  test0_block_8))))
  (interval_append test0 144 208 288
  (interval_append test0 144 176 208
  (interval_append test0 144 160 176
  test0_block_9
  test0_block_10)
  (interval_append test0 176 192 208
  test0_block_11
  test0_block_12))
  (interval_append test0 208 240 288
  (interval_append test0 208 224 240
  test0_block_13
  test0_block_14)
  (interval_append test0 240 256 288
  test0_block_15
  (interval_append test0 256 272 288
  test0_block_16
  test0_block_17)))))
  (interval_append test0 288 432 585
  (interval_append test0 288 352 432
  (interval_append test0 288 320 352
  (interval_append test0 288 304 320
  test0_block_18
  test0_block_19)
  (interval_append test0 320 336 352
  test0_block_20
  test0_block_21))
  (interval_append test0 352 384 432
  (interval_append test0 352 368 384
  test0_block_22
  test0_block_23)
  (interval_append test0 384 400 432
  test0_block_24
  (interval_append test0 400 416 432
  test0_block_25
  test0_block_26))))
  (interval_append test0 432 512 585
  (interval_append test0 432 464 512
  (interval_append test0 432 448 464
  test0_block_27
  test0_block_28)
  (interval_append test0 464 480 512
  test0_block_29
  (interval_append test0 480 496 512
  test0_block_30
  test0_block_31)))
  (interval_append test0 512 544 585
  (interval_append test0 512 528 544
  test0_block_32
  test0_block_33)
  (interval_append test0 544 560 585
  test0_block_34
  (interval_append test0 560 576 585
  test0_block_35
  test0_block_36))))))
cert_nodeInterval_3 0 585
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0670
