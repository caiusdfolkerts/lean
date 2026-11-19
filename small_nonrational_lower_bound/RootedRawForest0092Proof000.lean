module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0092Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0092
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 0
cert_test_block_2 0 0 0 32 32
cert_test_block_2 0 1 32 64 32
cert_test_block_2 0 2 64 96 32
cert_test_block_2 0 3 96 128 32
cert_test_block_2 0 4 128 148 20
theorem test0_complete : Interval test0 0 148 :=
  (interval_append test0 0 64 148
  (interval_append test0 0 32 64
  test0_block_0
  test0_block_1)
  (interval_append test0 64 96 148
  test0_block_2
  (interval_append test0 96 128 148
  test0_block_3
  test0_block_4)))
cert_nodeInterval_2 0 148
end Papers.RationalityTen.RootedForests.RootedRawForest0092
