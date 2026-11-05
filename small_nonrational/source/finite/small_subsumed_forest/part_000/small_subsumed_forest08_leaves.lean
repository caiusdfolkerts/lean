module
prelude
public import SmallSubsumedForest08Leaves000
public import SmallSubsumedForest08Leaves001
public import SmallSubsumedForest08Leaves002
public import SmallSubsumedForest08Leaves003
public import SmallSubsumedForest08Leaves004
public import SmallSubsumedForest08Leaves005
public import SmallSubsumedForest08Leaves006
public import SmallSubsumedForest08Leaves007
public import SmallSubsumedForest08Leaves008

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 257 := (interval_append leafTest 0 128 257 (interval_append leafTest 0 64 128 (interval_append leafTest 0 32 64 leafInterval0 leafInterval32) (interval_append leafTest 64 96 128 leafInterval64 leafInterval96)) (interval_append leafTest 128 192 257 (interval_append leafTest 128 160 192 leafInterval128 leafInterval160) (interval_append leafTest 192 224 257 leafInterval192 (interval_append leafTest 224 256 257 leafInterval224 leafInterval256))))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
