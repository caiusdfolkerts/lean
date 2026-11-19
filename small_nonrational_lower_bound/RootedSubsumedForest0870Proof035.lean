module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0870Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 22400
cert_test_block_3 22400 0 0 16 16
cert_test_block_3 22400 1 16 32 16
cert_test_block_3 22400 2 32 48 16
cert_test_block_3 22400 3 48 64 16
cert_test_block_3 22400 4 64 80 16
cert_test_block_3 22400 5 80 96 16
cert_test_block_3 22400 6 96 112 16
cert_test_block_3 22400 7 112 128 16
cert_test_block_3 22400 8 128 144 16
cert_test_block_3 22400 9 144 160 16
cert_test_block_3 22400 10 160 176 16
cert_test_block_3 22400 11 176 192 16
cert_test_block_3 22400 12 192 208 16
cert_test_block_3 22400 13 208 224 16
cert_test_block_3 22400 14 224 240 16
cert_test_block_3 22400 15 240 256 16
cert_test_block_3 22400 16 256 272 16
cert_test_block_3 22400 17 272 288 16
cert_test_block_3 22400 18 288 304 16
cert_test_block_3 22400 19 304 320 16
cert_test_block_3 22400 20 320 336 16
cert_test_block_3 22400 21 336 352 16
cert_test_block_3 22400 22 352 368 16
cert_test_block_3 22400 23 368 384 16
cert_test_block_3 22400 24 384 400 16
cert_test_block_3 22400 25 400 416 16
cert_test_block_3 22400 26 416 432 16
cert_test_block_3 22400 27 432 448 16
cert_test_block_3 22400 28 448 464 16
cert_test_block_3 22400 29 464 480 16
cert_test_block_3 22400 30 480 496 16
cert_test_block_3 22400 31 496 512 16
cert_test_block_3 22400 32 512 528 16
cert_test_block_3 22400 33 528 544 16
cert_test_block_3 22400 34 544 560 16
cert_test_block_3 22400 35 560 576 16
cert_test_block_3 22400 36 576 583 7
theorem test22400_complete : Interval test22400 0 583 :=
  (interval_append test22400 0 288 583
  (interval_append test22400 0 144 288
  (interval_append test22400 0 64 144
  (interval_append test22400 0 32 64
  (interval_append test22400 0 16 32
  test22400_block_0
  test22400_block_1)
  (interval_append test22400 32 48 64
  test22400_block_2
  test22400_block_3))
  (interval_append test22400 64 96 144
  (interval_append test22400 64 80 96
  test22400_block_4
  test22400_block_5)
  (interval_append test22400 96 112 144
  test22400_block_6
  (interval_append test22400 112 128 144
  test22400_block_7
  test22400_block_8))))
  (interval_append test22400 144 208 288
  (interval_append test22400 144 176 208
  (interval_append test22400 144 160 176
  test22400_block_9
  test22400_block_10)
  (interval_append test22400 176 192 208
  test22400_block_11
  test22400_block_12))
  (interval_append test22400 208 240 288
  (interval_append test22400 208 224 240
  test22400_block_13
  test22400_block_14)
  (interval_append test22400 240 256 288
  test22400_block_15
  (interval_append test22400 256 272 288
  test22400_block_16
  test22400_block_17)))))
  (interval_append test22400 288 432 583
  (interval_append test22400 288 352 432
  (interval_append test22400 288 320 352
  (interval_append test22400 288 304 320
  test22400_block_18
  test22400_block_19)
  (interval_append test22400 320 336 352
  test22400_block_20
  test22400_block_21))
  (interval_append test22400 352 384 432
  (interval_append test22400 352 368 384
  test22400_block_22
  test22400_block_23)
  (interval_append test22400 384 400 432
  test22400_block_24
  (interval_append test22400 400 416 432
  test22400_block_25
  test22400_block_26))))
  (interval_append test22400 432 512 583
  (interval_append test22400 432 464 512
  (interval_append test22400 432 448 464
  test22400_block_27
  test22400_block_28)
  (interval_append test22400 464 480 512
  test22400_block_29
  (interval_append test22400 480 496 512
  test22400_block_30
  test22400_block_31)))
  (interval_append test22400 512 544 583
  (interval_append test22400 512 528 544
  test22400_block_32
  test22400_block_33)
  (interval_append test22400 544 560 583
  test22400_block_34
  (interval_append test22400 560 576 583
  test22400_block_35
  test22400_block_36))))))
cert_nodeInterval_3 22400 22983
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
