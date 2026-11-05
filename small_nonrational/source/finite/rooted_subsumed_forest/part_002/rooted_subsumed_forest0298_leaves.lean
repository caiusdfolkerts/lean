module
prelude
public import RootedSubsumedForest0298Leaves000
public import RootedSubsumedForest0298Leaves001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 43 := (interval_append leafTest 0 32 43 leafInterval0 leafInterval32)

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
