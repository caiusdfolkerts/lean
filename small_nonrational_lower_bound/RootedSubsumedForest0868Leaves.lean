module
prelude
public import RootedSubsumedForest0868Leaves000
public import RootedSubsumedForest0868Leaves001
public import RootedSubsumedForest0868Leaves002
public import RootedSubsumedForest0868Leaves003
public import RootedSubsumedForest0868Leaves004
public import RootedSubsumedForest0868Leaves005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 180 := (interval_append leafTest 0 96 180 (interval_append leafTest 0 32 96 leafInterval0 (interval_append leafTest 32 64 96 leafInterval32 leafInterval64)) (interval_append leafTest 96 128 180 leafInterval96 (interval_append leafTest 128 160 180 leafInterval128 leafInterval160)))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
