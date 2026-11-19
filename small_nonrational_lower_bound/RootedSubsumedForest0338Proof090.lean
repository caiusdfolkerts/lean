module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0338Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 57600
cert_test_block_3 57600 0 0 16 16
cert_test_block_3 57600 1 16 32 16
cert_test_block_3 57600 2 32 48 16
cert_test_block_3 57600 3 48 64 16
cert_test_block_3 57600 4 64 80 16
cert_test_block_3 57600 5 80 96 16
cert_test_block_3 57600 6 96 112 16
cert_test_block_3 57600 7 112 128 16
cert_test_block_3 57600 8 128 144 16
cert_test_block_3 57600 9 144 160 16
cert_test_block_3 57600 10 160 176 16
cert_test_block_3 57600 11 176 192 16
cert_test_block_3 57600 12 192 208 16
cert_test_block_3 57600 13 208 224 16
cert_test_block_3 57600 14 224 240 16
cert_test_block_3 57600 15 240 256 16
cert_test_block_3 57600 16 256 272 16
cert_test_block_3 57600 17 272 288 16
cert_test_block_3 57600 18 288 304 16
cert_test_block_3 57600 19 304 320 16
cert_test_block_3 57600 20 320 336 16
cert_test_block_3 57600 21 336 352 16
cert_test_block_3 57600 22 352 368 16
cert_test_block_3 57600 23 368 384 16
cert_test_block_3 57600 24 384 400 16
cert_test_block_3 57600 25 400 416 16
cert_test_block_3 57600 26 416 432 16
cert_test_block_3 57600 27 432 448 16
cert_test_block_3 57600 28 448 464 16
cert_test_block_3 57600 29 464 480 16
cert_test_block_3 57600 30 480 496 16
cert_test_block_3 57600 31 496 512 16
cert_test_block_3 57600 32 512 528 16
cert_test_block_3 57600 33 528 544 16
cert_test_block_3 57600 34 544 560 16
cert_test_block_3 57600 35 560 576 16
cert_test_block_3 57600 36 576 592 16
cert_test_block_3 57600 37 592 608 16
cert_test_block_3 57600 38 608 609 1
theorem test57600_complete : Interval test57600 0 609 :=
  (interval_append test57600 0 304 609
  (interval_append test57600 0 144 304
  (interval_append test57600 0 64 144
  (interval_append test57600 0 32 64
  (interval_append test57600 0 16 32
  test57600_block_0
  test57600_block_1)
  (interval_append test57600 32 48 64
  test57600_block_2
  test57600_block_3))
  (interval_append test57600 64 96 144
  (interval_append test57600 64 80 96
  test57600_block_4
  test57600_block_5)
  (interval_append test57600 96 112 144
  test57600_block_6
  (interval_append test57600 112 128 144
  test57600_block_7
  test57600_block_8))))
  (interval_append test57600 144 224 304
  (interval_append test57600 144 176 224
  (interval_append test57600 144 160 176
  test57600_block_9
  test57600_block_10)
  (interval_append test57600 176 192 224
  test57600_block_11
  (interval_append test57600 192 208 224
  test57600_block_12
  test57600_block_13)))
  (interval_append test57600 224 256 304
  (interval_append test57600 224 240 256
  test57600_block_14
  test57600_block_15)
  (interval_append test57600 256 272 304
  test57600_block_16
  (interval_append test57600 272 288 304
  test57600_block_17
  test57600_block_18)))))
  (interval_append test57600 304 464 609
  (interval_append test57600 304 384 464
  (interval_append test57600 304 336 384
  (interval_append test57600 304 320 336
  test57600_block_19
  test57600_block_20)
  (interval_append test57600 336 352 384
  test57600_block_21
  (interval_append test57600 352 368 384
  test57600_block_22
  test57600_block_23)))
  (interval_append test57600 384 416 464
  (interval_append test57600 384 400 416
  test57600_block_24
  test57600_block_25)
  (interval_append test57600 416 432 464
  test57600_block_26
  (interval_append test57600 432 448 464
  test57600_block_27
  test57600_block_28))))
  (interval_append test57600 464 544 609
  (interval_append test57600 464 496 544
  (interval_append test57600 464 480 496
  test57600_block_29
  test57600_block_30)
  (interval_append test57600 496 512 544
  test57600_block_31
  (interval_append test57600 512 528 544
  test57600_block_32
  test57600_block_33)))
  (interval_append test57600 544 576 609
  (interval_append test57600 544 560 576
  test57600_block_34
  test57600_block_35)
  (interval_append test57600 576 592 609
  test57600_block_36
  (interval_append test57600 592 608 609
  test57600_block_37
  test57600_block_38))))))
cert_nodeInterval_3 57600 58209
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
