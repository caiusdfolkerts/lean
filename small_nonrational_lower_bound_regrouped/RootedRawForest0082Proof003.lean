module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0082Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0082
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 1920
cert_test_block_2 1920 0 0 32 32
cert_test_block_2 1920 1 32 43 11
theorem test1920_complete : Interval test1920 0 43 :=
  (interval_append test1920 0 32 43
  test1920_block_0
  test1920_block_1)
cert_nodeInterval_2 1920 1963
end Papers.RationalityTen.RootedForests.RootedRawForest0082
