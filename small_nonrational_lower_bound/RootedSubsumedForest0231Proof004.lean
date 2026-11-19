module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0231Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0231
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
cert_test_block_3 2560 27 432 434 2
theorem test2560_complete : Interval test2560 0 434 :=
  (interval_append test2560 0 224 434
  (interval_append test2560 0 112 224
  (interval_append test2560 0 48 112
  (interval_append test2560 0 16 48
  test2560_block_0
  (interval_append test2560 16 32 48
  test2560_block_1
  test2560_block_2))
  (interval_append test2560 48 80 112
  (interval_append test2560 48 64 80
  test2560_block_3
  test2560_block_4)
  (interval_append test2560 80 96 112
  test2560_block_5
  test2560_block_6)))
  (interval_append test2560 112 160 224
  (interval_append test2560 112 128 160
  test2560_block_7
  (interval_append test2560 128 144 160
  test2560_block_8
  test2560_block_9))
  (interval_append test2560 160 192 224
  (interval_append test2560 160 176 192
  test2560_block_10
  test2560_block_11)
  (interval_append test2560 192 208 224
  test2560_block_12
  test2560_block_13))))
  (interval_append test2560 224 336 434
  (interval_append test2560 224 272 336
  (interval_append test2560 224 240 272
  test2560_block_14
  (interval_append test2560 240 256 272
  test2560_block_15
  test2560_block_16))
  (interval_append test2560 272 304 336
  (interval_append test2560 272 288 304
  test2560_block_17
  test2560_block_18)
  (interval_append test2560 304 320 336
  test2560_block_19
  test2560_block_20)))
  (interval_append test2560 336 384 434
  (interval_append test2560 336 352 384
  test2560_block_21
  (interval_append test2560 352 368 384
  test2560_block_22
  test2560_block_23))
  (interval_append test2560 384 416 434
  (interval_append test2560 384 400 416
  test2560_block_24
  test2560_block_25)
  (interval_append test2560 416 432 434
  test2560_block_26
  test2560_block_27)))))
cert_nodeInterval_3 2560 2994
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0231
