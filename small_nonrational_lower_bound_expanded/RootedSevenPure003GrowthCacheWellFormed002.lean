module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public import RootedSevenPure003GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure003
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_5 512
cert_wellFormedTest_block_3 512 0 0 16 16
cert_wellFormedTest_block_3 512 1 16 32 16
cert_wellFormedTest_block_3 512 2 32 48 16
cert_wellFormedTest_block_3 512 3 48 64 16
cert_wellFormedTest_block_3 512 4 64 74 10
cert_wellFormedTest_complete_4
cert_wellFormedTestInterval_3 512 586
end Papers.RationalityTen.RootedCaches.RootedSevenPure003
