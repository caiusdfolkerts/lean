module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0307Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0307
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 10880
cert_test_block_3 10880 0 0 16 16
cert_test_block_3 10880 1 16 32 16
cert_test_block_3 10880 2 32 48 16
cert_test_block_3 10880 3 48 64 16
cert_test_block_3 10880 4 64 80 16
cert_test_block_3 10880 5 80 96 16
cert_test_block_3 10880 6 96 112 16
cert_test_block_3 10880 7 112 128 16
cert_test_block_3 10880 8 128 144 16
cert_test_block_3 10880 9 144 160 16
cert_test_block_3 10880 10 160 176 16
cert_test_block_3 10880 11 176 192 16
cert_test_block_3 10880 12 192 208 16
cert_test_block_3 10880 13 208 224 16
cert_test_block_3 10880 14 224 240 16
cert_test_block_3 10880 15 240 256 16
cert_test_block_3 10880 16 256 272 16
cert_test_block_3 10880 17 272 288 16
cert_test_block_3 10880 18 288 304 16
cert_test_block_3 10880 19 304 320 16
cert_test_block_3 10880 20 320 336 16
cert_test_block_3 10880 21 336 352 16
cert_test_block_3 10880 22 352 368 16
cert_test_block_3 10880 23 368 384 16
cert_test_block_3 10880 24 384 400 16
cert_test_block_3 10880 25 400 416 16
cert_test_block_3 10880 26 416 432 16
cert_test_block_3 10880 27 432 448 16
cert_test_block_3 10880 28 448 464 16
cert_test_block_3 10880 29 464 480 16
cert_test_block_3 10880 30 480 496 16
cert_test_block_3 10880 31 496 512 16
cert_test_block_3 10880 32 512 528 16
cert_test_block_3 10880 33 528 544 16
cert_test_block_3 10880 34 544 560 16
cert_test_block_3 10880 35 560 572 12
theorem test10880_complete : Interval test10880 0 572 :=
  (interval_append test10880 0 288 572
  (interval_append test10880 0 144 288
  (interval_append test10880 0 64 144
  (interval_append test10880 0 32 64
  (interval_append test10880 0 16 32
  test10880_block_0
  test10880_block_1)
  (interval_append test10880 32 48 64
  test10880_block_2
  test10880_block_3))
  (interval_append test10880 64 96 144
  (interval_append test10880 64 80 96
  test10880_block_4
  test10880_block_5)
  (interval_append test10880 96 112 144
  test10880_block_6
  (interval_append test10880 112 128 144
  test10880_block_7
  test10880_block_8))))
  (interval_append test10880 144 208 288
  (interval_append test10880 144 176 208
  (interval_append test10880 144 160 176
  test10880_block_9
  test10880_block_10)
  (interval_append test10880 176 192 208
  test10880_block_11
  test10880_block_12))
  (interval_append test10880 208 240 288
  (interval_append test10880 208 224 240
  test10880_block_13
  test10880_block_14)
  (interval_append test10880 240 256 288
  test10880_block_15
  (interval_append test10880 256 272 288
  test10880_block_16
  test10880_block_17)))))
  (interval_append test10880 288 432 572
  (interval_append test10880 288 352 432
  (interval_append test10880 288 320 352
  (interval_append test10880 288 304 320
  test10880_block_18
  test10880_block_19)
  (interval_append test10880 320 336 352
  test10880_block_20
  test10880_block_21))
  (interval_append test10880 352 384 432
  (interval_append test10880 352 368 384
  test10880_block_22
  test10880_block_23)
  (interval_append test10880 384 400 432
  test10880_block_24
  (interval_append test10880 400 416 432
  test10880_block_25
  test10880_block_26))))
  (interval_append test10880 432 496 572
  (interval_append test10880 432 464 496
  (interval_append test10880 432 448 464
  test10880_block_27
  test10880_block_28)
  (interval_append test10880 464 480 496
  test10880_block_29
  test10880_block_30))
  (interval_append test10880 496 528 572
  (interval_append test10880 496 512 528
  test10880_block_31
  test10880_block_32)
  (interval_append test10880 528 544 572
  test10880_block_33
  (interval_append test10880 544 560 572
  test10880_block_34
  test10880_block_35))))))
cert_nodeInterval_3 10880 11452
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0307
