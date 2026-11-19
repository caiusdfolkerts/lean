module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed031GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed031
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_3 512
cert_wellFormedTest_block_2 512 0 0 16 16
cert_wellFormedTest_block_2 512 1 16 32 16
cert_wellFormedTest_block_2 512 2 32 48 16
cert_wellFormedTest_block_2 512 3 48 64 16
cert_wellFormedTest_block_2 512 4 64 80 16
cert_wellFormedTest_block_2 512 5 80 96 16
cert_wellFormedTest_block_2 512 6 96 112 16
cert_wellFormedTest_block_2 512 7 112 128 16
cert_wellFormedTest_block_2 512 8 128 143 15
theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 143 :=
  (interval_append wellFormedTest_512 0 64 143
  (interval_append wellFormedTest_512 0 32 64
  (interval_append wellFormedTest_512 0 16 32
  wellFormedTest_512_block_0
  wellFormedTest_512_block_1)
  (interval_append wellFormedTest_512 32 48 64
  wellFormedTest_512_block_2
  wellFormedTest_512_block_3))
  (interval_append wellFormedTest_512 64 96 143
  (interval_append wellFormedTest_512 64 80 96
  wellFormedTest_512_block_4
  wellFormedTest_512_block_5)
  (interval_append wellFormedTest_512 96 112 143
  wellFormedTest_512_block_6
  (interval_append wellFormedTest_512 112 128 143
  wellFormedTest_512_block_7
  wellFormedTest_512_block_8))))
cert_wellFormedTestInterval_2 512 655
end Papers.RationalityTen.RootedCaches.RootedSevenMixed031
