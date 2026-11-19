module
prelude
public import RootedRawForest0066Leaves000
public import RootedRawForest0066Leaves001
public import RootedRawForest0066Leaves002
public import RootedRawForest0066Leaves003
public import RootedRawForest0066Leaves004
public import RootedRawForest0066Leaves005

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0066
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 162 := (interval_append leafTest 0 96 162 (interval_append leafTest 0 32 96 leafInterval0 (interval_append leafTest 32 64 96 leafInterval32 leafInterval64)) (interval_append leafTest 96 128 162 leafInterval96 (interval_append leafTest 128 160 162 leafInterval128 leafInterval160)))

end Papers.RationalityTen.RootedForests.RootedRawForest0066
