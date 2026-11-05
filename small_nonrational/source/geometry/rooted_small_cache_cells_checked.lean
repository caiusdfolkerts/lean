module
prelude
public import RootedSmallCacheCells000
public import RootedSmallCacheCells001
public import RootedSmallCacheCells002
public import RootedSmallCacheCells003
public import RootedSmallCacheCells004
public import RootedSmallCacheCells005
public import RootedSmallCacheCells006
public import RootedSmallCacheCells007
public import RootedSmallCacheCells008
public import RootedSmallCacheCells009
public import RootedSmallCacheCells010
public import RootedSmallCacheCells011
public import RootedSmallCacheCells012
public import RootedSmallCacheCells013

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallCache
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem cellTest_complete : Interval cellTest 0 3436 := (interval_append cellTest 0 1792 3436 (interval_append cellTest 0 768 1792 (interval_append cellTest 0 256 768 cellTest_interval_0 (interval_append cellTest 256 512 768 cellTest_interval_256 cellTest_interval_512)) (interval_append cellTest 768 1280 1792 (interval_append cellTest 768 1024 1280 cellTest_interval_768 cellTest_interval_1024) (interval_append cellTest 1280 1536 1792 cellTest_interval_1280 cellTest_interval_1536))) (interval_append cellTest 1792 2560 3436 (interval_append cellTest 1792 2048 2560 cellTest_interval_1792 (interval_append cellTest 2048 2304 2560 cellTest_interval_2048 cellTest_interval_2304)) (interval_append cellTest 2560 3072 3436 (interval_append cellTest 2560 2816 3072 cellTest_interval_2560 cellTest_interval_2816) (interval_append cellTest 3072 3328 3436 cellTest_interval_3072 cellTest_interval_3328))))

end Papers.RationalityTen.RootedSmallCache
