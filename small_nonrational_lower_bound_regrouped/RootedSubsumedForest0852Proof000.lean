module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0852Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0852
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
cert_test_block_3 0 11 176 191 15
theorem test0_complete : Interval test0 0 191 :=
  (interval_append test0 0 96 191
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
  (interval_append test0 96 144 191
  (interval_append test0 96 112 144
  test0_block_6
  (interval_append test0 112 128 144
  test0_block_7
  test0_block_8))
  (interval_append test0 144 160 191
  test0_block_9
  (interval_append test0 160 176 191
  test0_block_10
  test0_block_11))))
cert_nodeInterval_3 0 191
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0852
