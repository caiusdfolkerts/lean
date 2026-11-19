module
prelude
public import RootedSubsumedForest0354Leaves000
public import RootedSubsumedForest0354Leaves001
public import RootedSubsumedForest0354Leaves002
public import RootedSubsumedForest0354Leaves003
public import RootedSubsumedForest0354Leaves004

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 156 := (interval_append leafTest 0 64 156 (interval_append leafTest 0 32 64 leafInterval0 leafInterval32) (interval_append leafTest 64 96 156 leafInterval64 (interval_append leafTest 96 128 156 leafInterval96 leafInterval128)))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
