module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0355Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 157440
cert_test_block_3 157440 0 0 16 16
cert_test_block_3 157440 1 16 32 16
cert_test_block_3 157440 2 32 48 16
cert_test_block_3 157440 3 48 64 16
cert_test_block_3 157440 4 64 74 10
theorem test157440_complete : Interval test157440 0 74 :=
  (interval_append test157440 0 32 74
  (interval_append test157440 0 16 32
  test157440_block_0
  test157440_block_1)
  (interval_append test157440 32 48 74
  test157440_block_2
  (interval_append test157440 48 64 74
  test157440_block_3
  test157440_block_4)))
cert_nodeInterval_3 157440 157514
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
