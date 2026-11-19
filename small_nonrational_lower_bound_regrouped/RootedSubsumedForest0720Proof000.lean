module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0720Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0720
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
cert_test_block_3 0 23 368 384 16
cert_test_block_3 0 24 384 395 11
theorem test0_complete : Interval test0 0 395 :=
  (interval_append test0 0 192 395
  (interval_append test0 0 96 192
  (interval_append test0 0 48 96
  (interval_append test0 0 16 48
  test0_block_0
  (interval_append test0 16 32 48
  test0_block_1
  test0_block_2))
  (interval_append test0 48 64 96
  test0_block_3
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)))
  (interval_append test0 96 144 192
  (interval_append test0 96 112 144
  test0_block_6
  (interval_append test0 112 128 144
  test0_block_7
  test0_block_8))
  (interval_append test0 144 160 192
  test0_block_9
  (interval_append test0 160 176 192
  test0_block_10
  test0_block_11))))
  (interval_append test0 192 288 395
  (interval_append test0 192 240 288
  (interval_append test0 192 208 240
  test0_block_12
  (interval_append test0 208 224 240
  test0_block_13
  test0_block_14))
  (interval_append test0 240 256 288
  test0_block_15
  (interval_append test0 256 272 288
  test0_block_16
  test0_block_17)))
  (interval_append test0 288 336 395
  (interval_append test0 288 304 336
  test0_block_18
  (interval_append test0 304 320 336
  test0_block_19
  test0_block_20))
  (interval_append test0 336 368 395
  (interval_append test0 336 352 368
  test0_block_21
  test0_block_22)
  (interval_append test0 368 384 395
  test0_block_23
  test0_block_24)))))
cert_nodeInterval_3 0 395
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0720
