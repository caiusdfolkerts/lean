module
prelude
public import SmallSubsumedForest20Leaves000
public import SmallSubsumedForest20Leaves001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 61 := (interval_append leafTest 0 32 61 leafInterval0 leafInterval32)

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
