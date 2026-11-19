module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0686Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0686
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 640
cert_test_block_3 640 0 0 16 16
cert_test_block_3 640 1 16 32 16
cert_test_block_3 640 2 32 48 16
cert_test_block_3 640 3 48 64 16
cert_test_block_3 640 4 64 80 16
cert_test_block_3 640 5 80 96 16
cert_test_block_3 640 6 96 112 16
cert_test_block_3 640 7 112 128 16
cert_test_block_3 640 8 128 144 16
cert_test_block_3 640 9 144 160 16
cert_test_block_3 640 10 160 176 16
cert_test_block_3 640 11 176 192 16
cert_test_block_3 640 12 192 208 16
cert_test_block_3 640 13 208 224 16
cert_test_block_3 640 14 224 240 16
cert_test_block_3 640 15 240 256 16
cert_test_block_3 640 16 256 272 16
cert_test_block_3 640 17 272 288 16
cert_test_block_3 640 18 288 304 16
cert_test_block_3 640 19 304 320 16
cert_test_block_3 640 20 320 336 16
cert_test_block_3 640 21 336 352 16
cert_test_block_3 640 22 352 368 16
cert_test_block_3 640 23 368 384 16
cert_test_block_3 640 24 384 400 16
cert_test_block_3 640 25 400 416 16
cert_test_block_3 640 26 416 432 16
cert_test_block_3 640 27 432 447 15
theorem test640_complete : Interval test640 0 447 :=
  (interval_append test640 0 224 447
  (interval_append test640 0 112 224
  (interval_append test640 0 48 112
  (interval_append test640 0 16 48
  test640_block_0
  (interval_append test640 16 32 48
  test640_block_1
  test640_block_2))
  (interval_append test640 48 80 112
  (interval_append test640 48 64 80
  test640_block_3
  test640_block_4)
  (interval_append test640 80 96 112
  test640_block_5
  test640_block_6)))
  (interval_append test640 112 160 224
  (interval_append test640 112 128 160
  test640_block_7
  (interval_append test640 128 144 160
  test640_block_8
  test640_block_9))
  (interval_append test640 160 192 224
  (interval_append test640 160 176 192
  test640_block_10
  test640_block_11)
  (interval_append test640 192 208 224
  test640_block_12
  test640_block_13))))
  (interval_append test640 224 336 447
  (interval_append test640 224 272 336
  (interval_append test640 224 240 272
  test640_block_14
  (interval_append test640 240 256 272
  test640_block_15
  test640_block_16))
  (interval_append test640 272 304 336
  (interval_append test640 272 288 304
  test640_block_17
  test640_block_18)
  (interval_append test640 304 320 336
  test640_block_19
  test640_block_20)))
  (interval_append test640 336 384 447
  (interval_append test640 336 352 384
  test640_block_21
  (interval_append test640 352 368 384
  test640_block_22
  test640_block_23))
  (interval_append test640 384 416 447
  (interval_append test640 384 400 416
  test640_block_24
  test640_block_25)
  (interval_append test640 416 432 447
  test640_block_26
  test640_block_27)))))
cert_nodeInterval_3 640 1087
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0686
