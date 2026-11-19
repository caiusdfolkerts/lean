module
prelude
public import SmallSubsumedForest18Leaves000
public import SmallSubsumedForest18Leaves001
public import SmallSubsumedForest18Leaves002
public import SmallSubsumedForest18Leaves003
public import SmallSubsumedForest18Leaves004
public import SmallSubsumedForest18Leaves005
public import SmallSubsumedForest18Leaves006
public import SmallSubsumedForest18Leaves007
public import SmallSubsumedForest18Leaves008
public import SmallSubsumedForest18Leaves009
public import SmallSubsumedForest18Leaves010
public import SmallSubsumedForest18Leaves011
public import SmallSubsumedForest18Leaves012
public import SmallSubsumedForest18Leaves013

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 432 := (interval_append leafTest 0 224 432 (interval_append leafTest 0 96 224 (interval_append leafTest 0 32 96 leafInterval0 (interval_append leafTest 32 64 96 leafInterval32 leafInterval64)) (interval_append leafTest 96 160 224 (interval_append leafTest 96 128 160 leafInterval96 leafInterval128) (interval_append leafTest 160 192 224 leafInterval160 leafInterval192))) (interval_append leafTest 224 320 432 (interval_append leafTest 224 256 320 leafInterval224 (interval_append leafTest 256 288 320 leafInterval256 leafInterval288)) (interval_append leafTest 320 384 432 (interval_append leafTest 320 352 384 leafInterval320 leafInterval352) (interval_append leafTest 384 416 432 leafInterval384 leafInterval416))))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
