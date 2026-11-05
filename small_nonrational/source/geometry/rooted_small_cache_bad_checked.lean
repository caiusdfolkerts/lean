module
prelude
public import RootedSmallCacheBad000
public import RootedSmallCacheBad001
public import RootedSmallCacheBad002
public import RootedSmallCacheBad003
public import RootedSmallCacheBad004
public import RootedSmallCacheBad005
public import RootedSmallCacheBad006
public import RootedSmallCacheBad007
public import RootedSmallCacheBad008
public import RootedSmallCacheBad009
public import RootedSmallCacheBad010
public import RootedSmallCacheBad011
public import RootedSmallCacheBad012
public import RootedSmallCacheBad013
public import RootedSmallCacheBad014
public import RootedSmallCacheBad015
public import RootedSmallCacheBad016
public import RootedSmallCacheBad017
public import RootedSmallCacheBad018
public import RootedSmallCacheBad019
public import RootedSmallCacheBad020
public import RootedSmallCacheBad021
public import RootedSmallCacheBad022
public import RootedSmallCacheBad023
public import RootedSmallCacheBad024
public import RootedSmallCacheBad025
public import RootedSmallCacheBad026

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallCache
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem badTest_complete : Interval badTest 0 3436 := (interval_append badTest 0 1664 3436 (interval_append badTest 0 768 1664 (interval_append badTest 0 384 768 (interval_append badTest 0 128 384 badTest_interval_0 (interval_append badTest 128 256 384 badTest_interval_128 badTest_interval_256)) (interval_append badTest 384 512 768 badTest_interval_384 (interval_append badTest 512 640 768 badTest_interval_512 badTest_interval_640))) (interval_append badTest 768 1152 1664 (interval_append badTest 768 896 1152 badTest_interval_768 (interval_append badTest 896 1024 1152 badTest_interval_896 badTest_interval_1024)) (interval_append badTest 1152 1408 1664 (interval_append badTest 1152 1280 1408 badTest_interval_1152 badTest_interval_1280) (interval_append badTest 1408 1536 1664 badTest_interval_1408 badTest_interval_1536)))) (interval_append badTest 1664 2560 3436 (interval_append badTest 1664 2048 2560 (interval_append badTest 1664 1792 2048 badTest_interval_1664 (interval_append badTest 1792 1920 2048 badTest_interval_1792 badTest_interval_1920)) (interval_append badTest 2048 2304 2560 (interval_append badTest 2048 2176 2304 badTest_interval_2048 badTest_interval_2176) (interval_append badTest 2304 2432 2560 badTest_interval_2304 badTest_interval_2432))) (interval_append badTest 2560 2944 3436 (interval_append badTest 2560 2688 2944 badTest_interval_2560 (interval_append badTest 2688 2816 2944 badTest_interval_2688 badTest_interval_2816)) (interval_append badTest 2944 3200 3436 (interval_append badTest 2944 3072 3200 badTest_interval_2944 badTest_interval_3072) (interval_append badTest 3200 3328 3436 badTest_interval_3200 badTest_interval_3328)))))

end Papers.RationalityTen.RootedSmallCache
