module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0091Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0091
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 1920
cert_test_block_2 1920 0 0 32 32
cert_test_block_2 1920 1 32 64 32
cert_test_block_2 1920 2 64 79 15
theorem test1920_complete : Interval test1920 0 79 :=
  (interval_append test1920 0 32 79
  test1920_block_0
  (interval_append test1920 32 64 79
  test1920_block_1
  test1920_block_2))
cert_nodeInterval_2 1920 1999
end Papers.RationalityTen.RootedForests.RootedRawForest0091
