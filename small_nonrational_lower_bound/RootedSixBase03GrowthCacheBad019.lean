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
cert_badTest_6 4864
cert_badTest_block_4 4864 0 0 8 8
cert_badTest_block_4 4864 1 8 16 8
cert_badTest_block_4 4864 2 16 24 8
cert_badTest_block_4 4864 3 24 32 8
cert_badTest_block_4 4864 4 32 40 8
cert_badTest_block_4 4864 5 40 48 8
cert_badTest_block_4 4864 6 48 56 8
cert_badTest_block_4 4864 7 56 64 8
cert_badTest_block_4 4864 8 64 72 8
cert_badTest_block_4 4864 9 72 80 8
cert_badTest_block_4 4864 10 80 88 8
cert_badTest_block_4 4864 11 88 96 8
cert_badTest_block_4 4864 12 96 104 8
cert_badTest_block_4 4864 13 104 112 8
cert_badTest_block_4 4864 14 112 120 8
cert_badTest_block_4 4864 15 120 128 8
cert_badTest_block_4 4864 16 128 136 8
cert_badTest_block_4 4864 17 136 144 8
cert_badTest_block_4 4864 18 144 152 8
cert_badTest_block_4 4864 19 152 160 8
cert_badTest_block_4 4864 20 160 168 8
cert_badTest_block_4 4864 21 168 176 8
cert_badTest_block_4 4864 22 176 184 8
cert_badTest_block_4 4864 23 184 192 8
cert_badTest_block_4 4864 24 192 200 8
cert_badTest_block_4 4864 25 200 208 8
cert_badTest_block_4 4864 26 208 216 8
cert_badTest_block_4 4864 27 216 224 8
cert_badTest_block_4 4864 28 224 232 8
cert_badTest_block_4 4864 29 232 240 8
cert_badTest_block_4 4864 30 240 248 8
cert_badTest_block_4 4864 31 248 256 8
theorem badTest_4864_complete : Interval badTest_4864 0 256 :=
  (interval_append badTest_4864 0 128 256
  (interval_append badTest_4864 0 64 128
  (interval_append badTest_4864 0 32 64
  (interval_append badTest_4864 0 16 32
  (interval_append badTest_4864 0 8 16
  badTest_4864_block_0
  badTest_4864_block_1)
  (interval_append badTest_4864 16 24 32
  badTest_4864_block_2
  badTest_4864_block_3))
  (interval_append badTest_4864 32 48 64
  (interval_append badTest_4864 32 40 48
  badTest_4864_block_4
  badTest_4864_block_5)
  (interval_append badTest_4864 48 56 64
  badTest_4864_block_6
  badTest_4864_block_7)))
  (interval_append badTest_4864 64 96 128
  (interval_append badTest_4864 64 80 96
  (interval_append badTest_4864 64 72 80
  badTest_4864_block_8
  badTest_4864_block_9)
  (interval_append badTest_4864 80 88 96
  badTest_4864_block_10
  badTest_4864_block_11))
  (interval_append badTest_4864 96 112 128
  (interval_append badTest_4864 96 104 112
  badTest_4864_block_12
  badTest_4864_block_13)
  (interval_append badTest_4864 112 120 128
  badTest_4864_block_14
  badTest_4864_block_15))))
  (interval_append badTest_4864 128 192 256
  (interval_append badTest_4864 128 160 192
  (interval_append badTest_4864 128 144 160
  (interval_append badTest_4864 128 136 144
  badTest_4864_block_16
  badTest_4864_block_17)
  (interval_append badTest_4864 144 152 160
  badTest_4864_block_18
  badTest_4864_block_19))
  (interval_append badTest_4864 160 176 192
  (interval_append badTest_4864 160 168 176
  badTest_4864_block_20
  badTest_4864_block_21)
  (interval_append badTest_4864 176 184 192
  badTest_4864_block_22
  badTest_4864_block_23)))
  (interval_append badTest_4864 192 224 256
  (interval_append badTest_4864 192 208 224
  (interval_append badTest_4864 192 200 208
  badTest_4864_block_24
  badTest_4864_block_25)
  (interval_append badTest_4864 208 216 224
  badTest_4864_block_26
  badTest_4864_block_27))
  (interval_append badTest_4864 224 240 256
  (interval_append badTest_4864 224 232 240
  badTest_4864_block_28
  badTest_4864_block_29)
  (interval_append badTest_4864 240 248 256
  badTest_4864_block_30
  badTest_4864_block_31)))))
cert_badTestInterval_4 4864 5120
end Papers.RationalityTen.RootedCaches.RootedSixBase03
