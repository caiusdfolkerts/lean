module
prelude
public import SmallSubsumedForest17Leaves000
public import SmallSubsumedForest17Leaves001
public import SmallSubsumedForest17Leaves002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 87 := (interval_append leafTest 0 32 87 leafInterval0 (interval_append leafTest 32 64 87 leafInterval32 leafInterval64))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
