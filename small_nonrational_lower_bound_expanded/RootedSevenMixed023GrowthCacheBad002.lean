module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed023GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed023
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest_2 512
cert_badTest_block_2 512 0 0 8 8
cert_badTest_block_2 512 1 8 16 8
cert_badTest_block_2 512 2 16 24 8
cert_badTest_block_2 512 3 24 32 8
cert_badTest_block_2 512 4 32 40 8
cert_badTest_block_2 512 5 40 44 4
theorem badTest_512_complete : Interval badTest_512 0 44 :=
  (interval_append badTest_512 0 24 44
  (interval_append badTest_512 0 8 24
  badTest_512_block_0
  (interval_append badTest_512 8 16 24
  badTest_512_block_1
  badTest_512_block_2))
  (interval_append badTest_512 24 32 44
  badTest_512_block_3
  (interval_append badTest_512 32 40 44
  badTest_512_block_4
  badTest_512_block_5)))
cert_badTestInterval_2 512 556
end Papers.RationalityTen.RootedCaches.RootedSevenMixed023
