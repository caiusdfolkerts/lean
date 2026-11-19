module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public import RootedSevenPure027GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure027
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_5 512
cert_wellFormedTest_block_3 512 0 0 16 16
cert_wellFormedTest_block_3 512 1 16 32 16
cert_wellFormedTest_block_3 512 2 32 48 16
theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 48 :=
  (interval_append wellFormedTest_512 0 16 48
  wellFormedTest_512_block_0
  (interval_append wellFormedTest_512 16 32 48
  wellFormedTest_512_block_1
  wellFormedTest_512_block_2))
cert_wellFormedTestInterval_3 512 560
end Papers.RationalityTen.RootedCaches.RootedSevenPure027
