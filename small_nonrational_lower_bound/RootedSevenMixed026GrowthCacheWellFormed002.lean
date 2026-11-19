module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed026GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed026
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_3 512
cert_wellFormedTest_block_2 512 0 0 16 16
cert_wellFormedTest_block_2 512 1 16 32 16
cert_wellFormedTest_block_2 512 2 32 44 12
theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 44 :=
  (interval_append wellFormedTest_512 0 16 44
  wellFormedTest_512_block_0
  (interval_append wellFormedTest_512 16 32 44
  wellFormedTest_512_block_1
  wellFormedTest_512_block_2))
cert_wellFormedTestInterval_2 512 556
end Papers.RationalityTen.RootedCaches.RootedSevenMixed026
