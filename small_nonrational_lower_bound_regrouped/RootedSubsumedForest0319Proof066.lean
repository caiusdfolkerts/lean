module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0319Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 42240
cert_test_block_3 42240 0 0 16 16
cert_test_block_3 42240 1 16 32 16
cert_test_block_3 42240 2 32 48 16
cert_test_block_3 42240 3 48 64 16
cert_test_block_3 42240 4 64 80 16
cert_test_block_3 42240 5 80 96 16
cert_test_block_3 42240 6 96 112 16
cert_test_block_3 42240 7 112 128 16
cert_test_block_3 42240 8 128 144 16
cert_test_block_3 42240 9 144 160 16
cert_test_block_3 42240 10 160 176 16
cert_test_block_3 42240 11 176 192 16
cert_test_block_3 42240 12 192 208 16
cert_test_block_3 42240 13 208 224 16
cert_test_block_3 42240 14 224 240 16
cert_test_block_3 42240 15 240 256 16
cert_test_block_3 42240 16 256 272 16
cert_test_block_3 42240 17 272 288 16
cert_test_block_3 42240 18 288 304 16
cert_test_block_3 42240 19 304 320 16
cert_test_block_3 42240 20 320 336 16
cert_test_block_3 42240 21 336 352 16
cert_test_block_3 42240 22 352 368 16
cert_test_block_3 42240 23 368 384 16
cert_test_block_3 42240 24 384 400 16
cert_test_block_3 42240 25 400 416 16
cert_test_block_3 42240 26 416 432 16
cert_test_block_3 42240 27 432 448 16
cert_test_block_3 42240 28 448 464 16
cert_test_block_3 42240 29 464 467 3
theorem test42240_complete : Interval test42240 0 467 :=
  (interval_append test42240 0 240 467
  (interval_append test42240 0 112 240
  (interval_append test42240 0 48 112
  (interval_append test42240 0 16 48
  test42240_block_0
  (interval_append test42240 16 32 48
  test42240_block_1
  test42240_block_2))
  (interval_append test42240 48 80 112
  (interval_append test42240 48 64 80
  test42240_block_3
  test42240_block_4)
  (interval_append test42240 80 96 112
  test42240_block_5
  test42240_block_6)))
  (interval_append test42240 112 176 240
  (interval_append test42240 112 144 176
  (interval_append test42240 112 128 144
  test42240_block_7
  test42240_block_8)
  (interval_append test42240 144 160 176
  test42240_block_9
  test42240_block_10))
  (interval_append test42240 176 208 240
  (interval_append test42240 176 192 208
  test42240_block_11
  test42240_block_12)
  (interval_append test42240 208 224 240
  test42240_block_13
  test42240_block_14))))
  (interval_append test42240 240 352 467
  (interval_append test42240 240 288 352
  (interval_append test42240 240 256 288
  test42240_block_15
  (interval_append test42240 256 272 288
  test42240_block_16
  test42240_block_17))
  (interval_append test42240 288 320 352
  (interval_append test42240 288 304 320
  test42240_block_18
  test42240_block_19)
  (interval_append test42240 320 336 352
  test42240_block_20
  test42240_block_21)))
  (interval_append test42240 352 416 467
  (interval_append test42240 352 384 416
  (interval_append test42240 352 368 384
  test42240_block_22
  test42240_block_23)
  (interval_append test42240 384 400 416
  test42240_block_24
  test42240_block_25))
  (interval_append test42240 416 448 467
  (interval_append test42240 416 432 448
  test42240_block_26
  test42240_block_27)
  (interval_append test42240 448 464 467
  test42240_block_28
  test42240_block_29)))))
cert_nodeInterval_3 42240 42707
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
