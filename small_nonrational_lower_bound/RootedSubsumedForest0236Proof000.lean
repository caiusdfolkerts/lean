module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0236Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0236
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
theorem test0_complete : Interval test0 0 368 :=
  (interval_append test0 0 176 368
  (interval_append test0 0 80 176
  (interval_append test0 0 32 80
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 80
  test0_block_2
  (interval_append test0 48 64 80
  test0_block_3
  test0_block_4)))
  (interval_append test0 80 128 176
  (interval_append test0 80 96 128
  test0_block_5
  (interval_append test0 96 112 128
  test0_block_6
  test0_block_7))
  (interval_append test0 128 144 176
  test0_block_8
  (interval_append test0 144 160 176
  test0_block_9
  test0_block_10))))
  (interval_append test0 176 272 368
  (interval_append test0 176 224 272
  (interval_append test0 176 192 224
  test0_block_11
  (interval_append test0 192 208 224
  test0_block_12
  test0_block_13))
  (interval_append test0 224 240 272
  test0_block_14
  (interval_append test0 240 256 272
  test0_block_15
  test0_block_16)))
  (interval_append test0 272 320 368
  (interval_append test0 272 288 320
  test0_block_17
  (interval_append test0 288 304 320
  test0_block_18
  test0_block_19))
  (interval_append test0 320 336 368
  test0_block_20
  (interval_append test0 336 352 368
  test0_block_21
  test0_block_22)))))
cert_nodeInterval_3 0 368
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0236
