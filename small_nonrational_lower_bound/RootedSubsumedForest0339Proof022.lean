module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0339Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 14080
cert_test_block_3 14080 0 0 16 16
cert_test_block_3 14080 1 16 32 16
cert_test_block_3 14080 2 32 48 16
cert_test_block_3 14080 3 48 64 16
cert_test_block_3 14080 4 64 80 16
cert_test_block_3 14080 5 80 96 16
cert_test_block_3 14080 6 96 112 16
cert_test_block_3 14080 7 112 128 16
cert_test_block_3 14080 8 128 144 16
cert_test_block_3 14080 9 144 160 16
cert_test_block_3 14080 10 160 176 16
cert_test_block_3 14080 11 176 192 16
cert_test_block_3 14080 12 192 208 16
cert_test_block_3 14080 13 208 224 16
cert_test_block_3 14080 14 224 240 16
cert_test_block_3 14080 15 240 256 16
cert_test_block_3 14080 16 256 272 16
cert_test_block_3 14080 17 272 288 16
cert_test_block_3 14080 18 288 304 16
cert_test_block_3 14080 19 304 320 16
cert_test_block_3 14080 20 320 336 16
cert_test_block_3 14080 21 336 352 16
cert_test_block_3 14080 22 352 368 16
cert_test_block_3 14080 23 368 384 16
cert_test_block_3 14080 24 384 400 16
cert_test_block_3 14080 25 400 416 16
cert_test_block_3 14080 26 416 432 16
cert_test_block_3 14080 27 432 448 16
cert_test_block_3 14080 28 448 464 16
cert_test_block_3 14080 29 464 480 16
cert_test_block_3 14080 30 480 496 16
cert_test_block_3 14080 31 496 512 16
cert_test_block_3 14080 32 512 528 16
cert_test_block_3 14080 33 528 544 16
cert_test_block_3 14080 34 544 560 16
cert_test_block_3 14080 35 560 576 16
cert_test_block_3 14080 36 576 592 16
cert_test_block_3 14080 37 592 608 16
cert_test_block_3 14080 38 608 619 11
theorem test14080_complete : Interval test14080 0 619 :=
  (interval_append test14080 0 304 619
  (interval_append test14080 0 144 304
  (interval_append test14080 0 64 144
  (interval_append test14080 0 32 64
  (interval_append test14080 0 16 32
  test14080_block_0
  test14080_block_1)
  (interval_append test14080 32 48 64
  test14080_block_2
  test14080_block_3))
  (interval_append test14080 64 96 144
  (interval_append test14080 64 80 96
  test14080_block_4
  test14080_block_5)
  (interval_append test14080 96 112 144
  test14080_block_6
  (interval_append test14080 112 128 144
  test14080_block_7
  test14080_block_8))))
  (interval_append test14080 144 224 304
  (interval_append test14080 144 176 224
  (interval_append test14080 144 160 176
  test14080_block_9
  test14080_block_10)
  (interval_append test14080 176 192 224
  test14080_block_11
  (interval_append test14080 192 208 224
  test14080_block_12
  test14080_block_13)))
  (interval_append test14080 224 256 304
  (interval_append test14080 224 240 256
  test14080_block_14
  test14080_block_15)
  (interval_append test14080 256 272 304
  test14080_block_16
  (interval_append test14080 272 288 304
  test14080_block_17
  test14080_block_18)))))
  (interval_append test14080 304 464 619
  (interval_append test14080 304 384 464
  (interval_append test14080 304 336 384
  (interval_append test14080 304 320 336
  test14080_block_19
  test14080_block_20)
  (interval_append test14080 336 352 384
  test14080_block_21
  (interval_append test14080 352 368 384
  test14080_block_22
  test14080_block_23)))
  (interval_append test14080 384 416 464
  (interval_append test14080 384 400 416
  test14080_block_24
  test14080_block_25)
  (interval_append test14080 416 432 464
  test14080_block_26
  (interval_append test14080 432 448 464
  test14080_block_27
  test14080_block_28))))
  (interval_append test14080 464 544 619
  (interval_append test14080 464 496 544
  (interval_append test14080 464 480 496
  test14080_block_29
  test14080_block_30)
  (interval_append test14080 496 512 544
  test14080_block_31
  (interval_append test14080 512 528 544
  test14080_block_32
  test14080_block_33)))
  (interval_append test14080 544 576 619
  (interval_append test14080 544 560 576
  test14080_block_34
  test14080_block_35)
  (interval_append test14080 576 592 619
  test14080_block_36
  (interval_append test14080 592 608 619
  test14080_block_37
  test14080_block_38))))))
cert_nodeInterval_3 14080 14699
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
