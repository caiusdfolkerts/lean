module
prelude
public import RootedSmallCacheRidges000
public import RootedSmallCacheRidges001
public import RootedSmallCacheRidges002
public import RootedSmallCacheRidges003
public import RootedSmallCacheRidges004
public import RootedSmallCacheRidges005
public import RootedSmallCacheRidges006
public import RootedSmallCacheRidges007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallCache
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeTest_complete : Interval ridgeTest 0 1024 := (interval_append ridgeTest 0 512 1024 (interval_append ridgeTest 0 256 512 (interval_append ridgeTest 0 128 256 ridgeTest_interval_0 ridgeTest_interval_128) (interval_append ridgeTest 256 384 512 ridgeTest_interval_256 ridgeTest_interval_384)) (interval_append ridgeTest 512 768 1024 (interval_append ridgeTest 512 640 768 ridgeTest_interval_512 ridgeTest_interval_640) (interval_append ridgeTest 768 896 1024 ridgeTest_interval_768 ridgeTest_interval_896)))

end Papers.RationalityTen.RootedSmallCache
