module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0232Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0232
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
theorem test2560_complete : Interval test2560 0 416 :=
  (interval_append test2560 0 208 416
  (interval_append test2560 0 96 208
  (interval_append test2560 0 48 96
  (interval_append test2560 0 16 48
  test2560_block_0
  (interval_append test2560 16 32 48
  test2560_block_1
  test2560_block_2))
  (interval_append test2560 48 64 96
  test2560_block_3
  (interval_append test2560 64 80 96
  test2560_block_4
  test2560_block_5)))
  (interval_append test2560 96 144 208
  (interval_append test2560 96 112 144
  test2560_block_6
  (interval_append test2560 112 128 144
  test2560_block_7
  test2560_block_8))
  (interval_append test2560 144 176 208
  (interval_append test2560 144 160 176
  test2560_block_9
  test2560_block_10)
  (interval_append test2560 176 192 208
  test2560_block_11
  test2560_block_12))))
  (interval_append test2560 208 304 416
  (interval_append test2560 208 256 304
  (interval_append test2560 208 224 256
  test2560_block_13
  (interval_append test2560 224 240 256
  test2560_block_14
  test2560_block_15))
  (interval_append test2560 256 272 304
  test2560_block_16
  (interval_append test2560 272 288 304
  test2560_block_17
  test2560_block_18)))
  (interval_append test2560 304 352 416
  (interval_append test2560 304 320 352
  test2560_block_19
  (interval_append test2560 320 336 352
  test2560_block_20
  test2560_block_21))
  (interval_append test2560 352 384 416
  (interval_append test2560 352 368 384
  test2560_block_22
  test2560_block_23)
  (interval_append test2560 384 400 416
  test2560_block_24
  test2560_block_25)))))
cert_nodeInterval_3 2560 2976
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0232
