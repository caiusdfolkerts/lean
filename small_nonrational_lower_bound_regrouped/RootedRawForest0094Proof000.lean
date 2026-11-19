module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0094Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0094
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 0
cert_test_block_2 0 0 0 32 32
cert_test_block_2 0 1 32 64 32
cert_test_block_2 0 2 64 96 32
cert_test_block_2 0 3 96 128 32
cert_test_block_2 0 4 128 160 32
cert_test_block_2 0 5 160 172 12
theorem test0_complete : Interval test0 0 172 :=
  (interval_append test0 0 96 172
  (interval_append test0 0 32 96
  test0_block_0
  (interval_append test0 32 64 96
  test0_block_1
  test0_block_2))
  (interval_append test0 96 128 172
  test0_block_3
  (interval_append test0 128 160 172
  test0_block_4
  test0_block_5)))
cert_nodeInterval_2 0 172
end Papers.RationalityTen.RootedForests.RootedRawForest0094
