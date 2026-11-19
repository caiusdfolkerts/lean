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
cert_badTest_2 0
cert_badTest_block_2 0 0 0 8 8
cert_badTest_block_2 0 1 8 16 8
cert_badTest_block_2 0 2 16 24 8
cert_badTest_block_2 0 3 24 32 8
cert_badTest_block_2 0 4 32 40 8
cert_badTest_block_2 0 5 40 48 8
cert_badTest_block_2 0 6 48 56 8
cert_badTest_block_2 0 7 56 64 8
cert_badTest_block_2 0 8 64 72 8
cert_badTest_block_2 0 9 72 80 8
cert_badTest_block_2 0 10 80 88 8
cert_badTest_block_2 0 11 88 96 8
cert_badTest_block_2 0 12 96 104 8
cert_badTest_block_2 0 13 104 112 8
cert_badTest_block_2 0 14 112 120 8
cert_badTest_block_2 0 15 120 128 8
cert_badTest_block_2 0 16 128 136 8
cert_badTest_block_2 0 17 136 144 8
cert_badTest_block_2 0 18 144 152 8
cert_badTest_block_2 0 19 152 160 8
cert_badTest_block_2 0 20 160 168 8
cert_badTest_block_2 0 21 168 176 8
cert_badTest_block_2 0 22 176 184 8
cert_badTest_block_2 0 23 184 192 8
cert_badTest_block_2 0 24 192 200 8
cert_badTest_block_2 0 25 200 208 8
cert_badTest_block_2 0 26 208 216 8
cert_badTest_block_2 0 27 216 224 8
cert_badTest_block_2 0 28 224 232 8
cert_badTest_block_2 0 29 232 240 8
cert_badTest_block_2 0 30 240 248 8
cert_badTest_block_2 0 31 248 256 8
theorem badTest_0_complete : Interval badTest_0 0 256 :=
  (interval_append badTest_0 0 128 256
  (interval_append badTest_0 0 64 128
  (interval_append badTest_0 0 32 64
  (interval_append badTest_0 0 16 32
  (interval_append badTest_0 0 8 16
  badTest_0_block_0
  badTest_0_block_1)
  (interval_append badTest_0 16 24 32
  badTest_0_block_2
  badTest_0_block_3))
  (interval_append badTest_0 32 48 64
  (interval_append badTest_0 32 40 48
  badTest_0_block_4
  badTest_0_block_5)
  (interval_append badTest_0 48 56 64
  badTest_0_block_6
  badTest_0_block_7)))
  (interval_append badTest_0 64 96 128
  (interval_append badTest_0 64 80 96
  (interval_append badTest_0 64 72 80
  badTest_0_block_8
  badTest_0_block_9)
  (interval_append badTest_0 80 88 96
  badTest_0_block_10
  badTest_0_block_11))
  (interval_append badTest_0 96 112 128
  (interval_append badTest_0 96 104 112
  badTest_0_block_12
  badTest_0_block_13)
  (interval_append badTest_0 112 120 128
  badTest_0_block_14
  badTest_0_block_15))))
  (interval_append badTest_0 128 192 256
  (interval_append badTest_0 128 160 192
  (interval_append badTest_0 128 144 160
  (interval_append badTest_0 128 136 144
  badTest_0_block_16
  badTest_0_block_17)
  (interval_append badTest_0 144 152 160
  badTest_0_block_18
  badTest_0_block_19))
  (interval_append badTest_0 160 176 192
  (interval_append badTest_0 160 168 176
  badTest_0_block_20
  badTest_0_block_21)
  (interval_append badTest_0 176 184 192
  badTest_0_block_22
  badTest_0_block_23)))
  (interval_append badTest_0 192 224 256
  (interval_append badTest_0 192 208 224
  (interval_append badTest_0 192 200 208
  badTest_0_block_24
  badTest_0_block_25)
  (interval_append badTest_0 208 216 224
  badTest_0_block_26
  badTest_0_block_27))
  (interval_append badTest_0 224 240 256
  (interval_append badTest_0 224 232 240
  badTest_0_block_28
  badTest_0_block_29)
  (interval_append badTest_0 240 248 256
  badTest_0_block_30
  badTest_0_block_31)))))
cert_badTestInterval_2 0 256
end Papers.RationalityTen.RootedCaches.RootedSevenMixed031
