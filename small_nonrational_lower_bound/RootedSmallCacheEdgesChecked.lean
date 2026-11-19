module
prelude
public import RootedSmallCacheEdges000
public import RootedSmallCacheEdges001
public import RootedSmallCacheEdges002
public import RootedSmallCacheEdges003
public import RootedSmallCacheEdges004
public import RootedSmallCacheEdges005
public import RootedSmallCacheEdges006
public import RootedSmallCacheEdges007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallCache
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem edgeTest_complete : Interval edgeTest 0 1024 := (interval_append edgeTest 0 512 1024 (interval_append edgeTest 0 256 512 (interval_append edgeTest 0 128 256 edgeTest_interval_0 edgeTest_interval_128) (interval_append edgeTest 256 384 512 edgeTest_interval_256 edgeTest_interval_384)) (interval_append edgeTest 512 768 1024 (interval_append edgeTest 512 640 768 edgeTest_interval_512 edgeTest_interval_640) (interval_append edgeTest 768 896 1024 edgeTest_interval_768 edgeTest_interval_896)))

end Papers.RationalityTen.RootedSmallCache
