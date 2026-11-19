module
prelude
public import RootedSubsumedForest0869Leaves000
public import RootedSubsumedForest0869Leaves001
public import RootedSubsumedForest0869Leaves002
public import RootedSubsumedForest0869Leaves003
public import RootedSubsumedForest0869Leaves004
public import RootedSubsumedForest0869Leaves005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 181 := (interval_append leafTest 0 96 181 (interval_append leafTest 0 32 96 leafInterval0 (interval_append leafTest 32 64 96 leafInterval32 leafInterval64)) (interval_append leafTest 96 128 181 leafInterval96 (interval_append leafTest 128 160 181 leafInterval128 leafInterval160)))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
