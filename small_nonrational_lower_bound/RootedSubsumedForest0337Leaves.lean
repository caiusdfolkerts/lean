module
prelude
public import RootedSubsumedForest0337Leaves000
public import RootedSubsumedForest0337Leaves001
public import RootedSubsumedForest0337Leaves002
public import RootedSubsumedForest0337Leaves003
public import RootedSubsumedForest0337Leaves004

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 145 := (interval_append leafTest 0 64 145 (interval_append leafTest 0 32 64 leafInterval0 leafInterval32) (interval_append leafTest 64 96 145 leafInterval64 (interval_append leafTest 96 128 145 leafInterval96 leafInterval128)))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
