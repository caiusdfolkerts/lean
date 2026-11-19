module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed033GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed033
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_3 512
cert_wellFormedTest_block_2 512 0 0 16 16
cert_wellFormedTest_block_2 512 1 16 17 1
theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 17 :=
  (interval_append wellFormedTest_512 0 16 17
  wellFormedTest_512_block_0
  wellFormedTest_512_block_1)
cert_wellFormedTestInterval_2 512 529
end Papers.RationalityTen.RootedCaches.RootedSevenMixed033
