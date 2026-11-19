module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0035Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0035
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 1280
cert_test_block_2 1280 0 0 2 2
theorem test1280_complete : Interval test1280 0 2 :=
  test1280_block_0
cert_nodeInterval_2 1280 1282
end Papers.RationalityTen.RootedForests.RootedRawForest0035
