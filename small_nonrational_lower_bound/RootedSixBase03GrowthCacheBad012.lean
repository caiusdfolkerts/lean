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
cert_badTest_6 3072
cert_badTest_block_4 3072 0 0 8 8
cert_badTest_block_4 3072 1 8 16 8
cert_badTest_block_4 3072 2 16 24 8
cert_badTest_block_4 3072 3 24 32 8
cert_badTest_block_4 3072 4 32 40 8
cert_badTest_block_4 3072 5 40 48 8
cert_badTest_block_4 3072 6 48 56 8
cert_badTest_block_4 3072 7 56 64 8
cert_badTest_block_4 3072 8 64 72 8
cert_badTest_block_4 3072 9 72 80 8
cert_badTest_block_4 3072 10 80 88 8
cert_badTest_block_4 3072 11 88 96 8
cert_badTest_block_4 3072 12 96 104 8
cert_badTest_block_4 3072 13 104 112 8
cert_badTest_block_4 3072 14 112 120 8
cert_badTest_block_4 3072 15 120 128 8
cert_badTest_block_4 3072 16 128 136 8
cert_badTest_block_4 3072 17 136 144 8
cert_badTest_block_4 3072 18 144 152 8
cert_badTest_block_4 3072 19 152 160 8
cert_badTest_block_4 3072 20 160 168 8
cert_badTest_block_4 3072 21 168 176 8
cert_badTest_block_4 3072 22 176 184 8
cert_badTest_block_4 3072 23 184 192 8
cert_badTest_block_4 3072 24 192 200 8
cert_badTest_block_4 3072 25 200 208 8
cert_badTest_block_4 3072 26 208 216 8
cert_badTest_block_4 3072 27 216 224 8
cert_badTest_block_4 3072 28 224 232 8
cert_badTest_block_4 3072 29 232 240 8
cert_badTest_block_4 3072 30 240 248 8
cert_badTest_block_4 3072 31 248 256 8
theorem badTest_3072_complete : Interval badTest_3072 0 256 :=
  (interval_append badTest_3072 0 128 256
  (interval_append badTest_3072 0 64 128
  (interval_append badTest_3072 0 32 64
  (interval_append badTest_3072 0 16 32
  (interval_append badTest_3072 0 8 16
  badTest_3072_block_0
  badTest_3072_block_1)
  (interval_append badTest_3072 16 24 32
  badTest_3072_block_2
  badTest_3072_block_3))
  (interval_append badTest_3072 32 48 64
  (interval_append badTest_3072 32 40 48
  badTest_3072_block_4
  badTest_3072_block_5)
  (interval_append badTest_3072 48 56 64
  badTest_3072_block_6
  badTest_3072_block_7)))
  (interval_append badTest_3072 64 96 128
  (interval_append badTest_3072 64 80 96
  (interval_append badTest_3072 64 72 80
  badTest_3072_block_8
  badTest_3072_block_9)
  (interval_append badTest_3072 80 88 96
  badTest_3072_block_10
  badTest_3072_block_11))
  (interval_append badTest_3072 96 112 128
  (interval_append badTest_3072 96 104 112
  badTest_3072_block_12
  badTest_3072_block_13)
  (interval_append badTest_3072 112 120 128
  badTest_3072_block_14
  badTest_3072_block_15))))
  (interval_append badTest_3072 128 192 256
  (interval_append badTest_3072 128 160 192
  (interval_append badTest_3072 128 144 160
  (interval_append badTest_3072 128 136 144
  badTest_3072_block_16
  badTest_3072_block_17)
  (interval_append badTest_3072 144 152 160
  badTest_3072_block_18
  badTest_3072_block_19))
  (interval_append badTest_3072 160 176 192
  (interval_append badTest_3072 160 168 176
  badTest_3072_block_20
  badTest_3072_block_21)
  (interval_append badTest_3072 176 184 192
  badTest_3072_block_22
  badTest_3072_block_23)))
  (interval_append badTest_3072 192 224 256
  (interval_append badTest_3072 192 208 224
  (interval_append badTest_3072 192 200 208
  badTest_3072_block_24
  badTest_3072_block_25)
  (interval_append badTest_3072 208 216 224
  badTest_3072_block_26
  badTest_3072_block_27))
  (interval_append badTest_3072 224 240 256
  (interval_append badTest_3072 224 232 240
  badTest_3072_block_28
  badTest_3072_block_29)
  (interval_append badTest_3072 240 248 256
  badTest_3072_block_30
  badTest_3072_block_31)))))
cert_badTestInterval_4 3072 3328
end Papers.RationalityTen.RootedCaches.RootedSixBase03
