module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0317Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 8960
cert_test_block_3 8960 0 0 16 16
cert_test_block_3 8960 1 16 32 16
cert_test_block_3 8960 2 32 43 11
theorem test8960_complete : Interval test8960 0 43 :=
  (interval_append test8960 0 16 43
  test8960_block_0
  (interval_append test8960 16 32 43
  test8960_block_1
  test8960_block_2))
cert_nodeInterval_3 8960 9003
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
