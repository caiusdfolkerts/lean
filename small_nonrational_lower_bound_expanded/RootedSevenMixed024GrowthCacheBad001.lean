module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed024GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed024
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest_2 256
cert_badTest_block_2 256 0 0 8 8
cert_badTest_block_2 256 1 8 16 8
cert_badTest_block_2 256 2 16 24 8
cert_badTest_block_2 256 3 24 32 8
cert_badTest_block_2 256 4 32 40 8
cert_badTest_block_2 256 5 40 48 8
cert_badTest_block_2 256 6 48 56 8
cert_badTest_block_2 256 7 56 64 8
cert_badTest_block_2 256 8 64 72 8
cert_badTest_block_2 256 9 72 80 8
cert_badTest_block_2 256 10 80 88 8
cert_badTest_block_2 256 11 88 96 8
cert_badTest_block_2 256 12 96 104 8
cert_badTest_block_2 256 13 104 112 8
cert_badTest_block_2 256 14 112 120 8
cert_badTest_block_2 256 15 120 128 8
cert_badTest_block_2 256 16 128 136 8
cert_badTest_block_2 256 17 136 144 8
cert_badTest_block_2 256 18 144 152 8
cert_badTest_block_2 256 19 152 160 8
cert_badTest_block_2 256 20 160 168 8
cert_badTest_block_2 256 21 168 176 8
cert_badTest_block_2 256 22 176 184 8
cert_badTest_block_2 256 23 184 192 8
cert_badTest_block_2 256 24 192 200 8
cert_badTest_block_2 256 25 200 208 8
cert_badTest_block_2 256 26 208 210 2
theorem badTest_256_complete : Interval badTest_256 0 210 :=
  (interval_append badTest_256 0 104 210
  (interval_append badTest_256 0 48 104
  (interval_append badTest_256 0 24 48
  (interval_append badTest_256 0 8 24
  badTest_256_block_0
  (interval_append badTest_256 8 16 24
  badTest_256_block_1
  badTest_256_block_2))
  (interval_append badTest_256 24 32 48
  badTest_256_block_3
  (interval_append badTest_256 32 40 48
  badTest_256_block_4
  badTest_256_block_5)))
  (interval_append badTest_256 48 72 104
  (interval_append badTest_256 48 56 72
  badTest_256_block_6
  (interval_append badTest_256 56 64 72
  badTest_256_block_7
  badTest_256_block_8))
  (interval_append badTest_256 72 88 104
  (interval_append badTest_256 72 80 88
  badTest_256_block_9
  badTest_256_block_10)
  (interval_append badTest_256 88 96 104
  badTest_256_block_11
  badTest_256_block_12))))
  (interval_append badTest_256 104 160 210
  (interval_append badTest_256 104 128 160
  (interval_append badTest_256 104 112 128
  badTest_256_block_13
  (interval_append badTest_256 112 120 128
  badTest_256_block_14
  badTest_256_block_15))
  (interval_append badTest_256 128 144 160
  (interval_append badTest_256 128 136 144
  badTest_256_block_16
  badTest_256_block_17)
  (interval_append badTest_256 144 152 160
  badTest_256_block_18
  badTest_256_block_19)))
  (interval_append badTest_256 160 184 210
  (interval_append badTest_256 160 168 184
  badTest_256_block_20
  (interval_append badTest_256 168 176 184
  badTest_256_block_21
  badTest_256_block_22))
  (interval_append badTest_256 184 200 210
  (interval_append badTest_256 184 192 200
  badTest_256_block_23
  badTest_256_block_24)
  (interval_append badTest_256 200 208 210
  badTest_256_block_25
  badTest_256_block_26)))))
cert_badTestInterval_2 256 466
end Papers.RationalityTen.RootedCaches.RootedSevenMixed024
