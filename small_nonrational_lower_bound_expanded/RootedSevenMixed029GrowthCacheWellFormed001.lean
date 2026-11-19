module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed029GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed029
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_3 256
cert_wellFormedTest_block_2 256 0 0 16 16
cert_wellFormedTest_block_2 256 1 16 32 16
cert_wellFormedTest_block_2 256 2 32 48 16
cert_wellFormedTest_block_2 256 3 48 64 16
cert_wellFormedTest_block_2 256 4 64 80 16
cert_wellFormedTest_block_2 256 5 80 96 16
cert_wellFormedTest_block_2 256 6 96 112 16
cert_wellFormedTest_block_2 256 7 112 120 8
theorem wellFormedTest_256_complete : Interval wellFormedTest_256 0 120 :=
  (interval_append wellFormedTest_256 0 64 120
  (interval_append wellFormedTest_256 0 32 64
  (interval_append wellFormedTest_256 0 16 32
  wellFormedTest_256_block_0
  wellFormedTest_256_block_1)
  (interval_append wellFormedTest_256 32 48 64
  wellFormedTest_256_block_2
  wellFormedTest_256_block_3))
  (interval_append wellFormedTest_256 64 96 120
  (interval_append wellFormedTest_256 64 80 96
  wellFormedTest_256_block_4
  wellFormedTest_256_block_5)
  (interval_append wellFormedTest_256 96 112 120
  wellFormedTest_256_block_6
  wellFormedTest_256_block_7)))
cert_wellFormedTestInterval_2 256 376
end Papers.RationalityTen.RootedCaches.RootedSevenMixed029
