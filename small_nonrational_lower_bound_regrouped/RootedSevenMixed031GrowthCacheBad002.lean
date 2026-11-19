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
cert_badTest_2 512
cert_badTest_block_2 512 0 0 8 8
cert_badTest_block_2 512 1 8 16 8
cert_badTest_block_2 512 2 16 24 8
cert_badTest_block_2 512 3 24 32 8
cert_badTest_block_2 512 4 32 40 8
cert_badTest_block_2 512 5 40 48 8
cert_badTest_block_2 512 6 48 56 8
cert_badTest_block_2 512 7 56 64 8
cert_badTest_block_2 512 8 64 72 8
cert_badTest_block_2 512 9 72 80 8
cert_badTest_block_2 512 10 80 88 8
cert_badTest_block_2 512 11 88 96 8
cert_badTest_block_2 512 12 96 104 8
cert_badTest_block_2 512 13 104 112 8
cert_badTest_block_2 512 14 112 120 8
cert_badTest_block_2 512 15 120 128 8
cert_badTest_block_2 512 16 128 136 8
cert_badTest_block_2 512 17 136 143 7
theorem badTest_512_complete : Interval badTest_512 0 143 :=
  (interval_append badTest_512 0 72 143
  (interval_append badTest_512 0 32 72
  (interval_append badTest_512 0 16 32
  (interval_append badTest_512 0 8 16
  badTest_512_block_0
  badTest_512_block_1)
  (interval_append badTest_512 16 24 32
  badTest_512_block_2
  badTest_512_block_3))
  (interval_append badTest_512 32 48 72
  (interval_append badTest_512 32 40 48
  badTest_512_block_4
  badTest_512_block_5)
  (interval_append badTest_512 48 56 72
  badTest_512_block_6
  (interval_append badTest_512 56 64 72
  badTest_512_block_7
  badTest_512_block_8))))
  (interval_append badTest_512 72 104 143
  (interval_append badTest_512 72 88 104
  (interval_append badTest_512 72 80 88
  badTest_512_block_9
  badTest_512_block_10)
  (interval_append badTest_512 88 96 104
  badTest_512_block_11
  badTest_512_block_12))
  (interval_append badTest_512 104 120 143
  (interval_append badTest_512 104 112 120
  badTest_512_block_13
  badTest_512_block_14)
  (interval_append badTest_512 120 128 143
  badTest_512_block_15
  (interval_append badTest_512 128 136 143
  badTest_512_block_16
  badTest_512_block_17)))))
cert_badTestInterval_2 512 655
end Papers.RationalityTen.RootedCaches.RootedSevenMixed031
