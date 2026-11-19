module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0721Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 15360
cert_test_block_3 15360 0 0 16 16
cert_test_block_3 15360 1 16 32 16
cert_test_block_3 15360 2 32 48 16
cert_test_block_3 15360 3 48 64 16
cert_test_block_3 15360 4 64 67 3
theorem test15360_complete : Interval test15360 0 67 :=
  (interval_append test15360 0 32 67
  (interval_append test15360 0 16 32
  test15360_block_0
  test15360_block_1)
  (interval_append test15360 32 48 67
  test15360_block_2
  (interval_append test15360 48 64 67
  test15360_block_3
  test15360_block_4)))
cert_nodeInterval_3 15360 15427
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
