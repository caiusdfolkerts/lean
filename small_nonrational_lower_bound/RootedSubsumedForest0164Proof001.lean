module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0164Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0164
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 640
cert_test_block_3 640 0 0 16 16
cert_test_block_3 640 1 16 32 16
cert_test_block_3 640 2 32 42 10
theorem test640_complete : Interval test640 0 42 :=
  (interval_append test640 0 16 42
  test640_block_0
  (interval_append test640 16 32 42
  test640_block_1
  test640_block_2))
cert_nodeInterval_3 640 682
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0164
