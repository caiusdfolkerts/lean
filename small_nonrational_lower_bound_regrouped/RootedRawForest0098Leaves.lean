module
prelude
public import RootedRawForest0098Leaves000
public import RootedRawForest0098Leaves001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0098
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 36 := (interval_append leafTest 0 32 36 leafInterval0 leafInterval32)

end Papers.RationalityTen.RootedForests.RootedRawForest0098
