module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0233Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0233
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 1280
cert_test_block_3 1280 0 0 16 16
cert_test_block_3 1280 1 16 26 10
theorem test1280_complete : Interval test1280 0 26 :=
  (interval_append test1280 0 16 26
  test1280_block_0
  test1280_block_1)
cert_nodeInterval_3 1280 1306
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0233
