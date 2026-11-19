module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed022GrowthCacheData
public import RootedSevenMixed022GrowthCacheKindSupport3

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed022
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_kindTest_3
cert_kindTest_block_3 0 1
cert_kindTest_block_3 1 2
cert_kindTest_block_3 2 3
theorem kindTest_0_block_3 : Interval kindTest_0 3 4 := by
  intro i hlo hhi
  have h : i = 3 := by omega
  subst i
  exact kindTest_large_3

cert_kindTest_block_3 4 5
cert_kindTest_complete_3
cert_kindTestInterval_2
end Papers.RationalityTen.RootedCaches.RootedSevenMixed022
