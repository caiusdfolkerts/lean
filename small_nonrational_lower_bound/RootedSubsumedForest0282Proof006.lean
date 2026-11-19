module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0282Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0282
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 3840
cert_test_block_3 3840 0 0 16 16
cert_test_block_3 3840 1 16 32 16
cert_test_block_3 3840 2 32 48 16
cert_test_block_3 3840 3 48 64 16
theorem test3840_complete : Interval test3840 0 64 :=
  (interval_append test3840 0 32 64
  (interval_append test3840 0 16 32
  test3840_block_0
  test3840_block_1)
  (interval_append test3840 32 48 64
  test3840_block_2
  test3840_block_3))
cert_nodeInterval_3 3840 3904
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0282
