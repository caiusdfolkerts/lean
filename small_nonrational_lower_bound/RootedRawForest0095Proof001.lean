module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0095Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0095
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 640
cert_test_block_2 640 0 0 15 15
theorem test640_complete : Interval test640 0 15 :=
  test640_block_0
cert_nodeInterval_2 640 655
end Papers.RationalityTen.RootedForests.RootedRawForest0095
