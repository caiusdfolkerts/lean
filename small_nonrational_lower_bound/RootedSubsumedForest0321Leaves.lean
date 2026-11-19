module
prelude
public import RootedSubsumedForest0321Leaves000
public import RootedSubsumedForest0321Leaves001
public import RootedSubsumedForest0321Leaves002
public import RootedSubsumedForest0321Leaves003
public import RootedSubsumedForest0321Leaves004

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 136 := (interval_append leafTest 0 64 136 (interval_append leafTest 0 32 64 leafInterval0 leafInterval32) (interval_append leafTest 64 96 136 leafInterval64 (interval_append leafTest 96 128 136 leafInterval96 leafInterval128)))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
