module
prelude
public import RootedSubsumedForest0338LeavesGrouped000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 383 := (interval_append leafTest 0 192 383 (interval_append leafTest 0 96 192 (interval_append leafTest 0 32 96 leafInterval0 (interval_append leafTest 32 64 96 leafInterval32 leafInterval64)) (interval_append leafTest 96 128 192 leafInterval96 (interval_append leafTest 128 160 192 leafInterval128 leafInterval160))) (interval_append leafTest 192 288 383 (interval_append leafTest 192 224 288 leafInterval192 (interval_append leafTest 224 256 288 leafInterval224 leafInterval256)) (interval_append leafTest 288 320 383 leafInterval288 (interval_append leafTest 320 352 383 leafInterval320 leafInterval352))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
