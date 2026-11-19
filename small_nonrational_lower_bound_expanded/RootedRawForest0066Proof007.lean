module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0066Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0066
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 4480
cert_test_block_2 4480 0 0 32 32
cert_test_block_2 4480 1 32 64 32
cert_test_block_2 4480 2 64 96 32
cert_test_block_2 4480 3 96 128 32
cert_test_block_2 4480 4 128 160 32
cert_test_block_2 4480 5 160 192 32
cert_test_block_2 4480 6 192 220 28
theorem test4480_complete : Interval test4480 0 220 :=
  (interval_append test4480 0 96 220
  (interval_append test4480 0 32 96
  test4480_block_0
  (interval_append test4480 32 64 96
  test4480_block_1
  test4480_block_2))
  (interval_append test4480 96 160 220
  (interval_append test4480 96 128 160
  test4480_block_3
  test4480_block_4)
  (interval_append test4480 160 192 220
  test4480_block_5
  test4480_block_6)))
cert_nodeInterval_2 4480 4700
end Papers.RationalityTen.RootedForests.RootedRawForest0066
