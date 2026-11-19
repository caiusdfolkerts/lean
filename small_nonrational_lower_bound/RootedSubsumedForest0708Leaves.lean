module
prelude
public import RootedSubsumedForest0708Leaves000
public import RootedSubsumedForest0708Leaves001
public import RootedSubsumedForest0708Leaves002
public import RootedSubsumedForest0708Leaves003
public import RootedSubsumedForest0708Leaves004
public import RootedSubsumedForest0708Leaves005
public import RootedSubsumedForest0708Leaves006
public import RootedSubsumedForest0708Leaves007
public import RootedSubsumedForest0708Leaves008
public import RootedSubsumedForest0708Leaves009
public import RootedSubsumedForest0708Leaves010
public import RootedSubsumedForest0708Leaves011
public import RootedSubsumedForest0708Leaves012
public import RootedSubsumedForest0708Leaves013
public import RootedSubsumedForest0708Leaves014
public import RootedSubsumedForest0708Leaves015
public import RootedSubsumedForest0708Leaves016
public import RootedSubsumedForest0708Leaves017
public import RootedSubsumedForest0708Leaves018
public import RootedSubsumedForest0708Leaves019
public import RootedSubsumedForest0708Leaves020
public import RootedSubsumedForest0708Leaves021
public import RootedSubsumedForest0708Leaves022
public import RootedSubsumedForest0708Leaves023
public import RootedSubsumedForest0708Leaves024
public import RootedSubsumedForest0708Leaves025
public import RootedSubsumedForest0708Leaves026
public import RootedSubsumedForest0708Leaves027
public import RootedSubsumedForest0708Leaves028
public import RootedSubsumedForest0708Leaves029
public import RootedSubsumedForest0708Leaves030
public import RootedSubsumedForest0708Leaves031
public import RootedSubsumedForest0708Leaves032
public import RootedSubsumedForest0708Leaves033
public import RootedSubsumedForest0708Leaves034
public import RootedSubsumedForest0708Leaves035
public import RootedSubsumedForest0708Leaves036
public import RootedSubsumedForest0708Leaves037
public import RootedSubsumedForest0708Leaves038
public import RootedSubsumedForest0708Leaves039
public import RootedSubsumedForest0708Leaves040
public import RootedSubsumedForest0708Leaves041
public import RootedSubsumedForest0708Leaves042
public import RootedSubsumedForest0708Leaves043
public import RootedSubsumedForest0708Leaves044
public import RootedSubsumedForest0708Leaves045
public import RootedSubsumedForest0708Leaves046
public import RootedSubsumedForest0708Leaves047
public import RootedSubsumedForest0708Leaves048
public import RootedSubsumedForest0708Leaves049
public import RootedSubsumedForest0708Leaves050

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_complete : Interval leafTest 0 1631 := (interval_append leafTest 0 800 1631 (interval_append leafTest 0 384 800 (interval_append leafTest 0 192 384 (interval_append leafTest 0 96 192 (interval_append leafTest 0 32 96 leafInterval0 (interval_append leafTest 32 64 96 leafInterval32 leafInterval64)) (interval_append leafTest 96 128 192 leafInterval96 (interval_append leafTest 128 160 192 leafInterval128 leafInterval160))) (interval_append leafTest 192 288 384 (interval_append leafTest 192 224 288 leafInterval192 (interval_append leafTest 224 256 288 leafInterval224 leafInterval256)) (interval_append leafTest 288 320 384 leafInterval288 (interval_append leafTest 320 352 384 leafInterval320 leafInterval352)))) (interval_append leafTest 384 576 800 (interval_append leafTest 384 480 576 (interval_append leafTest 384 416 480 leafInterval384 (interval_append leafTest 416 448 480 leafInterval416 leafInterval448)) (interval_append leafTest 480 512 576 leafInterval480 (interval_append leafTest 512 544 576 leafInterval512 leafInterval544))) (interval_append leafTest 576 672 800 (interval_append leafTest 576 608 672 leafInterval576 (interval_append leafTest 608 640 672 leafInterval608 leafInterval640)) (interval_append leafTest 672 736 800 (interval_append leafTest 672 704 736 leafInterval672 leafInterval704) (interval_append leafTest 736 768 800 leafInterval736 leafInterval768))))) (interval_append leafTest 800 1216 1631 (interval_append leafTest 800 992 1216 (interval_append leafTest 800 896 992 (interval_append leafTest 800 832 896 leafInterval800 (interval_append leafTest 832 864 896 leafInterval832 leafInterval864)) (interval_append leafTest 896 928 992 leafInterval896 (interval_append leafTest 928 960 992 leafInterval928 leafInterval960))) (interval_append leafTest 992 1088 1216 (interval_append leafTest 992 1024 1088 leafInterval992 (interval_append leafTest 1024 1056 1088 leafInterval1024 leafInterval1056)) (interval_append leafTest 1088 1152 1216 (interval_append leafTest 1088 1120 1152 leafInterval1088 leafInterval1120) (interval_append leafTest 1152 1184 1216 leafInterval1152 leafInterval1184)))) (interval_append leafTest 1216 1408 1631 (interval_append leafTest 1216 1312 1408 (interval_append leafTest 1216 1248 1312 leafInterval1216 (interval_append leafTest 1248 1280 1312 leafInterval1248 leafInterval1280)) (interval_append leafTest 1312 1344 1408 leafInterval1312 (interval_append leafTest 1344 1376 1408 leafInterval1344 leafInterval1376))) (interval_append leafTest 1408 1504 1631 (interval_append leafTest 1408 1440 1504 leafInterval1408 (interval_append leafTest 1440 1472 1504 leafInterval1440 leafInterval1472)) (interval_append leafTest 1504 1568 1631 (interval_append leafTest 1504 1536 1568 leafInterval1504 leafInterval1536) (interval_append leafTest 1568 1600 1631 leafInterval1568 leafInterval1600))))))

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
