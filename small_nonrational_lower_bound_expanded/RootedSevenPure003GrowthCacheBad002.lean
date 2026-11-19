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
cert_badTest_4 512
cert_badTest_block_3 512 0 0 8 8
cert_badTest_block_3 512 1 8 16 8
cert_badTest_block_3 512 2 16 24 8
cert_badTest_block_3 512 3 24 32 8
cert_badTest_block_3 512 4 32 40 8
cert_badTest_block_3 512 5 40 48 8
cert_badTest_block_3 512 6 48 56 8
cert_badTest_block_3 512 7 56 64 8
cert_badTest_block_3 512 8 64 72 8
cert_badTest_block_3 512 9 72 74 2
theorem badTest_512_complete : Interval badTest_512 0 74 :=
  (interval_append badTest_512 0 40 74
  (interval_append badTest_512 0 16 40
  (interval_append badTest_512 0 8 16
  badTest_512_block_0
  badTest_512_block_1)
  (interval_append badTest_512 16 24 40
  badTest_512_block_2
  (interval_append badTest_512 24 32 40
  badTest_512_block_3
  badTest_512_block_4)))
  (interval_append badTest_512 40 56 74
  (interval_append badTest_512 40 48 56
  badTest_512_block_5
  badTest_512_block_6)
  (interval_append badTest_512 56 64 74
  badTest_512_block_7
  (interval_append badTest_512 64 72 74
  badTest_512_block_8
  badTest_512_block_9))))
cert_badTestInterval_3 512 586
end Papers.RationalityTen.RootedCaches.RootedSevenPure003
