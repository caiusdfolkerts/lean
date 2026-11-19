module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0706Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0706
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 42880
cert_test_block_3 42880 0 0 16 16
cert_test_block_3 42880 1 16 31 15
theorem test42880_complete : Interval test42880 0 31 :=
  (interval_append test42880 0 16 31
  test42880_block_0
  test42880_block_1)
cert_nodeInterval_3 42880 42911
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0706
