module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0698Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0698
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 5120
cert_test_block_3 5120 0 0 16 16
cert_test_block_3 5120 1 16 32 16
cert_test_block_3 5120 2 32 48 16
cert_test_block_3 5120 3 48 64 16
cert_test_block_3 5120 4 64 80 16
cert_test_block_3 5120 5 80 96 16
cert_test_block_3 5120 6 96 112 16
cert_test_block_3 5120 7 112 128 16
cert_test_block_3 5120 8 128 136 8
theorem test5120_complete : Interval test5120 0 136 :=
  (interval_append test5120 0 64 136
  (interval_append test5120 0 32 64
  (interval_append test5120 0 16 32
  test5120_block_0
  test5120_block_1)
  (interval_append test5120 32 48 64
  test5120_block_2
  test5120_block_3))
  (interval_append test5120 64 96 136
  (interval_append test5120 64 80 96
  test5120_block_4
  test5120_block_5)
  (interval_append test5120 96 112 136
  test5120_block_6
  (interval_append test5120 112 128 136
  test5120_block_7
  test5120_block_8))))
cert_nodeInterval_3 5120 5256
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0698
