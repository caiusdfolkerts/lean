module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0868Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 7680
cert_test_block_3 7680 0 0 16 16
cert_test_block_3 7680 1 16 32 16
cert_test_block_3 7680 2 32 48 16
cert_test_block_3 7680 3 48 64 16
cert_test_block_3 7680 4 64 80 16
cert_test_block_3 7680 5 80 96 16
cert_test_block_3 7680 6 96 112 16
cert_test_block_3 7680 7 112 128 16
cert_test_block_3 7680 8 128 144 16
cert_test_block_3 7680 9 144 160 16
cert_test_block_3 7680 10 160 176 16
cert_test_block_3 7680 11 176 192 16
cert_test_block_3 7680 12 192 208 16
cert_test_block_3 7680 13 208 224 16
cert_test_block_3 7680 14 224 240 16
cert_test_block_3 7680 15 240 256 16
cert_test_block_3 7680 16 256 272 16
cert_test_block_3 7680 17 272 288 16
cert_test_block_3 7680 18 288 304 16
cert_test_block_3 7680 19 304 320 16
cert_test_block_3 7680 20 320 336 16
cert_test_block_3 7680 21 336 352 16
cert_test_block_3 7680 22 352 368 16
cert_test_block_3 7680 23 368 377 9
theorem test7680_complete : Interval test7680 0 377 :=
  (interval_append test7680 0 192 377
  (interval_append test7680 0 96 192
  (interval_append test7680 0 48 96
  (interval_append test7680 0 16 48
  test7680_block_0
  (interval_append test7680 16 32 48
  test7680_block_1
  test7680_block_2))
  (interval_append test7680 48 64 96
  test7680_block_3
  (interval_append test7680 64 80 96
  test7680_block_4
  test7680_block_5)))
  (interval_append test7680 96 144 192
  (interval_append test7680 96 112 144
  test7680_block_6
  (interval_append test7680 112 128 144
  test7680_block_7
  test7680_block_8))
  (interval_append test7680 144 160 192
  test7680_block_9
  (interval_append test7680 160 176 192
  test7680_block_10
  test7680_block_11))))
  (interval_append test7680 192 288 377
  (interval_append test7680 192 240 288
  (interval_append test7680 192 208 240
  test7680_block_12
  (interval_append test7680 208 224 240
  test7680_block_13
  test7680_block_14))
  (interval_append test7680 240 256 288
  test7680_block_15
  (interval_append test7680 256 272 288
  test7680_block_16
  test7680_block_17)))
  (interval_append test7680 288 336 377
  (interval_append test7680 288 304 336
  test7680_block_18
  (interval_append test7680 304 320 336
  test7680_block_19
  test7680_block_20))
  (interval_append test7680 336 352 377
  test7680_block_21
  (interval_append test7680 352 368 377
  test7680_block_22
  test7680_block_23)))))
cert_nodeInterval_3 7680 8057
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
