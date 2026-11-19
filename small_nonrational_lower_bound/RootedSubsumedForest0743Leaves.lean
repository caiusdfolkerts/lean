module
prelude
public import RootedSubsumedForest0743Leaves000
public import RootedSubsumedForest0743Leaves001
public import RootedSubsumedForest0743Leaves002
public import RootedSubsumedForest0743Leaves003
public import RootedSubsumedForest0743Leaves004
public import RootedSubsumedForest0743Leaves005
public import RootedSubsumedForest0743Leaves006
public import RootedSubsumedForest0743Leaves007
public import RootedSubsumedForest0743Leaves008
public import RootedSubsumedForest0743Leaves009
public import RootedSubsumedForest0743Leaves010
public import RootedSubsumedForest0743Leaves011
public import RootedSubsumedForest0743Leaves012
public import RootedSubsumedForest0743Leaves013
public import RootedSubsumedForest0743Leaves014

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 451 := (interval_append leafTest 0 224 451 (interval_append leafTest 0 96 224 (interval_append leafTest 0 32 96 leafInterval0 (interval_append leafTest 32 64 96 leafInterval32 leafInterval64)) (interval_append leafTest 96 160 224 (interval_append leafTest 96 128 160 leafInterval96 leafInterval128) (interval_append leafTest 160 192 224 leafInterval160 leafInterval192))) (interval_append leafTest 224 352 451 (interval_append leafTest 224 288 352 (interval_append leafTest 224 256 288 leafInterval224 leafInterval256) (interval_append leafTest 288 320 352 leafInterval288 leafInterval320)) (interval_append leafTest 352 416 451 (interval_append leafTest 352 384 416 leafInterval352 leafInterval384) (interval_append leafTest 416 448 451 leafInterval416 leafInterval448))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
