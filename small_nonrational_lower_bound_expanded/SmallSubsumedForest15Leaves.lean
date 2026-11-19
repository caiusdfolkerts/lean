module
prelude
public import SmallSubsumedForest15Leaves000
public import SmallSubsumedForest15Leaves001
public import SmallSubsumedForest15Leaves002
public import SmallSubsumedForest15Leaves003
public import SmallSubsumedForest15Leaves004
public import SmallSubsumedForest15Leaves005
public import SmallSubsumedForest15Leaves006
public import SmallSubsumedForest15Leaves007
public import SmallSubsumedForest15Leaves008
public import SmallSubsumedForest15Leaves009
public import SmallSubsumedForest15Leaves010
public import SmallSubsumedForest15Leaves011
public import SmallSubsumedForest15Leaves012
public import SmallSubsumedForest15Leaves013
public import SmallSubsumedForest15Leaves014
public import SmallSubsumedForest15Leaves015
public import SmallSubsumedForest15Leaves016
public import SmallSubsumedForest15Leaves017
public import SmallSubsumedForest15Leaves018

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 578 := (interval_append leafTest 0 288 578 (interval_append leafTest 0 128 288 (interval_append leafTest 0 64 128 (interval_append leafTest 0 32 64 leafInterval0 leafInterval32) (interval_append leafTest 64 96 128 leafInterval64 leafInterval96)) (interval_append leafTest 128 192 288 (interval_append leafTest 128 160 192 leafInterval128 leafInterval160) (interval_append leafTest 192 224 288 leafInterval192 (interval_append leafTest 224 256 288 leafInterval224 leafInterval256)))) (interval_append leafTest 288 448 578 (interval_append leafTest 288 352 448 (interval_append leafTest 288 320 352 leafInterval288 leafInterval320) (interval_append leafTest 352 384 448 leafInterval352 (interval_append leafTest 384 416 448 leafInterval384 leafInterval416))) (interval_append leafTest 448 512 578 (interval_append leafTest 448 480 512 leafInterval448 leafInterval480) (interval_append leafTest 512 544 578 leafInterval512 (interval_append leafTest 544 576 578 leafInterval544 leafInterval576)))))

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
