module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_6 5120
cert_wellFormedTest_block_4 5120 0 0 16 16
cert_wellFormedTest_block_4 5120 1 16 32 16
cert_wellFormedTest_block_4 5120 2 32 48 16
cert_wellFormedTest_block_4 5120 3 48 64 16
cert_wellFormedTest_block_4 5120 4 64 80 16
cert_wellFormedTest_block_4 5120 5 80 96 16
cert_wellFormedTest_block_4 5120 6 96 112 16
cert_wellFormedTest_block_4 5120 7 112 118 6
theorem wellFormedTest_5120_complete : Interval wellFormedTest_5120 0 118 :=
  (interval_append wellFormedTest_5120 0 64 118
  (interval_append wellFormedTest_5120 0 32 64
  (interval_append wellFormedTest_5120 0 16 32
  wellFormedTest_5120_block_0
  wellFormedTest_5120_block_1)
  (interval_append wellFormedTest_5120 32 48 64
  wellFormedTest_5120_block_2
  wellFormedTest_5120_block_3))
  (interval_append wellFormedTest_5120 64 96 118
  (interval_append wellFormedTest_5120 64 80 96
  wellFormedTest_5120_block_4
  wellFormedTest_5120_block_5)
  (interval_append wellFormedTest_5120 96 112 118
  wellFormedTest_5120_block_6
  wellFormedTest_5120_block_7)))
cert_wellFormedTestInterval_4 5120 5238
end Papers.RationalityTen.RootedCaches.RootedSixBase03
