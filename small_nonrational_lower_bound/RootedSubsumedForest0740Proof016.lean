module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0740Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 10240
cert_test_block_3 10240 0 0 16 16
cert_test_block_3 10240 1 16 32 16
cert_test_block_3 10240 2 32 41 9
theorem test10240_complete : Interval test10240 0 41 :=
  (interval_append test10240 0 16 41
  test10240_block_0
  (interval_append test10240 16 32 41
  test10240_block_1
  test10240_block_2))
cert_nodeInterval_3 10240 10281
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
