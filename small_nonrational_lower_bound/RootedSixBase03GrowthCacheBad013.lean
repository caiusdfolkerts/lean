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
cert_badTest_6 3328
cert_badTest_block_4 3328 0 0 8 8
cert_badTest_block_4 3328 1 8 16 8
cert_badTest_block_4 3328 2 16 24 8
cert_badTest_block_4 3328 3 24 32 8
cert_badTest_block_4 3328 4 32 40 8
cert_badTest_block_4 3328 5 40 48 8
cert_badTest_block_4 3328 6 48 56 8
cert_badTest_block_4 3328 7 56 64 8
cert_badTest_block_4 3328 8 64 72 8
cert_badTest_block_4 3328 9 72 80 8
cert_badTest_block_4 3328 10 80 88 8
cert_badTest_block_4 3328 11 88 96 8
cert_badTest_block_4 3328 12 96 104 8
cert_badTest_block_4 3328 13 104 112 8
cert_badTest_block_4 3328 14 112 120 8
cert_badTest_block_4 3328 15 120 128 8
cert_badTest_block_4 3328 16 128 136 8
cert_badTest_block_4 3328 17 136 144 8
cert_badTest_block_4 3328 18 144 152 8
cert_badTest_block_4 3328 19 152 160 8
cert_badTest_block_4 3328 20 160 168 8
cert_badTest_block_4 3328 21 168 176 8
cert_badTest_block_4 3328 22 176 184 8
cert_badTest_block_4 3328 23 184 192 8
cert_badTest_block_4 3328 24 192 200 8
cert_badTest_block_4 3328 25 200 208 8
cert_badTest_block_4 3328 26 208 216 8
cert_badTest_block_4 3328 27 216 224 8
cert_badTest_block_4 3328 28 224 232 8
cert_badTest_block_4 3328 29 232 240 8
cert_badTest_block_4 3328 30 240 248 8
cert_badTest_block_4 3328 31 248 256 8
theorem badTest_3328_complete : Interval badTest_3328 0 256 :=
  (interval_append badTest_3328 0 128 256
  (interval_append badTest_3328 0 64 128
  (interval_append badTest_3328 0 32 64
  (interval_append badTest_3328 0 16 32
  (interval_append badTest_3328 0 8 16
  badTest_3328_block_0
  badTest_3328_block_1)
  (interval_append badTest_3328 16 24 32
  badTest_3328_block_2
  badTest_3328_block_3))
  (interval_append badTest_3328 32 48 64
  (interval_append badTest_3328 32 40 48
  badTest_3328_block_4
  badTest_3328_block_5)
  (interval_append badTest_3328 48 56 64
  badTest_3328_block_6
  badTest_3328_block_7)))
  (interval_append badTest_3328 64 96 128
  (interval_append badTest_3328 64 80 96
  (interval_append badTest_3328 64 72 80
  badTest_3328_block_8
  badTest_3328_block_9)
  (interval_append badTest_3328 80 88 96
  badTest_3328_block_10
  badTest_3328_block_11))
  (interval_append badTest_3328 96 112 128
  (interval_append badTest_3328 96 104 112
  badTest_3328_block_12
  badTest_3328_block_13)
  (interval_append badTest_3328 112 120 128
  badTest_3328_block_14
  badTest_3328_block_15))))
  (interval_append badTest_3328 128 192 256
  (interval_append badTest_3328 128 160 192
  (interval_append badTest_3328 128 144 160
  (interval_append badTest_3328 128 136 144
  badTest_3328_block_16
  badTest_3328_block_17)
  (interval_append badTest_3328 144 152 160
  badTest_3328_block_18
  badTest_3328_block_19))
  (interval_append badTest_3328 160 176 192
  (interval_append badTest_3328 160 168 176
  badTest_3328_block_20
  badTest_3328_block_21)
  (interval_append badTest_3328 176 184 192
  badTest_3328_block_22
  badTest_3328_block_23)))
  (interval_append badTest_3328 192 224 256
  (interval_append badTest_3328 192 208 224
  (interval_append badTest_3328 192 200 208
  badTest_3328_block_24
  badTest_3328_block_25)
  (interval_append badTest_3328 208 216 224
  badTest_3328_block_26
  badTest_3328_block_27))
  (interval_append badTest_3328 224 240 256
  (interval_append badTest_3328 224 232 240
  badTest_3328_block_28
  badTest_3328_block_29)
  (interval_append badTest_3328 240 248 256
  badTest_3328_block_30
  badTest_3328_block_31)))))
cert_badTestInterval_4 3328 3584
end Papers.RationalityTen.RootedCaches.RootedSixBase03
