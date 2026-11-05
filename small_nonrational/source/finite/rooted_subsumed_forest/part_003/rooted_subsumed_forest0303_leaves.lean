module
prelude
public import RootedSubsumedForest0303Leaves000
public import RootedSubsumedForest0303Leaves001
public import RootedSubsumedForest0303Leaves002
public import RootedSubsumedForest0303Leaves003

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 105 := (interval_append leafTest 0 64 105 (interval_append leafTest 0 32 64 leafInterval0 leafInterval32) (interval_append leafTest 64 96 105 leafInterval64 leafInterval96))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
