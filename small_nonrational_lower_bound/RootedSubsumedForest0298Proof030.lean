module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0298Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 19200
cert_test_block_3 19200 0 0 16 16
cert_test_block_3 19200 1 16 32 16
cert_test_block_3 19200 2 32 48 16
cert_test_block_3 19200 3 48 64 16
cert_test_block_3 19200 4 64 80 16
cert_test_block_3 19200 5 80 96 16
cert_test_block_3 19200 6 96 112 16
cert_test_block_3 19200 7 112 128 16
cert_test_block_3 19200 8 128 144 16
cert_test_block_3 19200 9 144 160 16
cert_test_block_3 19200 10 160 176 16
cert_test_block_3 19200 11 176 192 16
cert_test_block_3 19200 12 192 208 16
cert_test_block_3 19200 13 208 223 15
theorem test19200_complete : Interval test19200 0 223 :=
  (interval_append test19200 0 112 223
  (interval_append test19200 0 48 112
  (interval_append test19200 0 16 48
  test19200_block_0
  (interval_append test19200 16 32 48
  test19200_block_1
  test19200_block_2))
  (interval_append test19200 48 80 112
  (interval_append test19200 48 64 80
  test19200_block_3
  test19200_block_4)
  (interval_append test19200 80 96 112
  test19200_block_5
  test19200_block_6)))
  (interval_append test19200 112 160 223
  (interval_append test19200 112 128 160
  test19200_block_7
  (interval_append test19200 128 144 160
  test19200_block_8
  test19200_block_9))
  (interval_append test19200 160 192 223
  (interval_append test19200 160 176 192
  test19200_block_10
  test19200_block_11)
  (interval_append test19200 192 208 223
  test19200_block_12
  test19200_block_13))))
cert_nodeInterval_3 19200 19423
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
