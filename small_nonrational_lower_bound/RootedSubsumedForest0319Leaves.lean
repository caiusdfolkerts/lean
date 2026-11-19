module
prelude
public import RootedSubsumedForest0319Leaves000
public import RootedSubsumedForest0319Leaves001
public import RootedSubsumedForest0319Leaves002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 69 := (interval_append leafTest 0 32 69 leafInterval0 (interval_append leafTest 32 64 69 leafInterval32 leafInterval64))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
