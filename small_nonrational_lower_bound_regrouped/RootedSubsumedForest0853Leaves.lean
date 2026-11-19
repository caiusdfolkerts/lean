module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0853Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0853
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTest_block_3 0 1
cert_leafTest_block_3 1 2
cert_leafTest_block_3 2 3
cert_leafTest_block_3 3 4
theorem leafTest_complete : Interval leafTest 0 4 :=
  (interval_append leafTest 0 2 4
  (interval_append leafTest 0 1 2
  leafTest_block_0
  leafTest_block_1)
  (interval_append leafTest 2 3 4
  leafTest_block_2
  leafTest_block_3))
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0853
