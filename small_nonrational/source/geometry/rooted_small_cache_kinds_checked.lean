module
prelude
public import RootedSmallCacheKinds000

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallCache
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindTest_complete : Interval kindTest 0 5 := kindTest_interval_0

end Papers.RationalityTen.RootedSmallCache
