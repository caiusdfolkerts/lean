module
prelude
public import RootedSubsumedForest0870Leaves000
public import RootedSubsumedForest0870Leaves001
public import RootedSubsumedForest0870Leaves002
public import RootedSubsumedForest0870Leaves003
public import RootedSubsumedForest0870Leaves004
public import RootedSubsumedForest0870Leaves005
public import RootedSubsumedForest0870Leaves006
public import RootedSubsumedForest0870Leaves007
public import RootedSubsumedForest0870Leaves008
public import RootedSubsumedForest0870Leaves009
public import RootedSubsumedForest0870Leaves010
public import RootedSubsumedForest0870Leaves011
public import RootedSubsumedForest0870Leaves012
public import RootedSubsumedForest0870Leaves013
public import RootedSubsumedForest0870Leaves014
public import RootedSubsumedForest0870Leaves015
public import RootedSubsumedForest0870Leaves016
public import RootedSubsumedForest0870Leaves017
public import RootedSubsumedForest0870Leaves018
public import RootedSubsumedForest0870Leaves019
public import RootedSubsumedForest0870Leaves020
public import RootedSubsumedForest0870Leaves021
public import RootedSubsumedForest0870Leaves022
public import RootedSubsumedForest0870Leaves023
public import RootedSubsumedForest0870Leaves024
public import RootedSubsumedForest0870Leaves025
public import RootedSubsumedForest0870Leaves026

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 835 := (interval_append leafTest 0 416 835 (interval_append leafTest 0 192 416 (interval_append leafTest 0 96 192 (interval_append leafTest 0 32 96 leafInterval0 (interval_append leafTest 32 64 96 leafInterval32 leafInterval64)) (interval_append leafTest 96 128 192 leafInterval96 (interval_append leafTest 128 160 192 leafInterval128 leafInterval160))) (interval_append leafTest 192 288 416 (interval_append leafTest 192 224 288 leafInterval192 (interval_append leafTest 224 256 288 leafInterval224 leafInterval256)) (interval_append leafTest 288 352 416 (interval_append leafTest 288 320 352 leafInterval288 leafInterval320) (interval_append leafTest 352 384 416 leafInterval352 leafInterval384)))) (interval_append leafTest 416 640 835 (interval_append leafTest 416 512 640 (interval_append leafTest 416 448 512 leafInterval416 (interval_append leafTest 448 480 512 leafInterval448 leafInterval480)) (interval_append leafTest 512 576 640 (interval_append leafTest 512 544 576 leafInterval512 leafInterval544) (interval_append leafTest 576 608 640 leafInterval576 leafInterval608))) (interval_append leafTest 640 736 835 (interval_append leafTest 640 672 736 leafInterval640 (interval_append leafTest 672 704 736 leafInterval672 leafInterval704)) (interval_append leafTest 736 800 835 (interval_append leafTest 736 768 800 leafInterval736 leafInterval768) (interval_append leafTest 800 832 835 leafInterval800 leafInterval832)))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
