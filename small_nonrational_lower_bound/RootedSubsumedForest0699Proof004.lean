module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0699Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0699
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
cert_test_block_3 2560 22 352 353 1
theorem test2560_complete : Interval test2560 0 353 :=
  (interval_append test2560 0 176 353
  (interval_append test2560 0 80 176
  (interval_append test2560 0 32 80
  (interval_append test2560 0 16 32
  test2560_block_0
  test2560_block_1)
  (interval_append test2560 32 48 80
  test2560_block_2
  (interval_append test2560 48 64 80
  test2560_block_3
  test2560_block_4)))
  (interval_append test2560 80 128 176
  (interval_append test2560 80 96 128
  test2560_block_5
  (interval_append test2560 96 112 128
  test2560_block_6
  test2560_block_7))
  (interval_append test2560 128 144 176
  test2560_block_8
  (interval_append test2560 144 160 176
  test2560_block_9
  test2560_block_10))))
  (interval_append test2560 176 272 353
  (interval_append test2560 176 224 272
  (interval_append test2560 176 192 224
  test2560_block_11
  (interval_append test2560 192 208 224
  test2560_block_12
  test2560_block_13))
  (interval_append test2560 224 240 272
  test2560_block_14
  (interval_append test2560 240 256 272
  test2560_block_15
  test2560_block_16)))
  (interval_append test2560 272 320 353
  (interval_append test2560 272 288 320
  test2560_block_17
  (interval_append test2560 288 304 320
  test2560_block_18
  test2560_block_19))
  (interval_append test2560 320 336 353
  test2560_block_20
  (interval_append test2560 336 352 353
  test2560_block_21
  test2560_block_22)))))
cert_nodeInterval_3 2560 2913
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0699
