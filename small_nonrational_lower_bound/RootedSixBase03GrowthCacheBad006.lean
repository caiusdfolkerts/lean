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
cert_badTest_6 1536
cert_badTest_block_4 1536 0 0 8 8
cert_badTest_block_4 1536 1 8 16 8
cert_badTest_block_4 1536 2 16 24 8
cert_badTest_block_4 1536 3 24 32 8
cert_badTest_block_4 1536 4 32 40 8
cert_badTest_block_4 1536 5 40 48 8
cert_badTest_block_4 1536 6 48 56 8
cert_badTest_block_4 1536 7 56 64 8
cert_badTest_block_4 1536 8 64 72 8
cert_badTest_block_4 1536 9 72 80 8
cert_badTest_block_4 1536 10 80 88 8
cert_badTest_block_4 1536 11 88 96 8
cert_badTest_block_4 1536 12 96 104 8
cert_badTest_block_4 1536 13 104 112 8
cert_badTest_block_4 1536 14 112 120 8
cert_badTest_block_4 1536 15 120 128 8
cert_badTest_block_4 1536 16 128 136 8
cert_badTest_block_4 1536 17 136 144 8
cert_badTest_block_4 1536 18 144 152 8
cert_badTest_block_4 1536 19 152 160 8
cert_badTest_block_4 1536 20 160 168 8
cert_badTest_block_4 1536 21 168 176 8
cert_badTest_block_4 1536 22 176 184 8
cert_badTest_block_4 1536 23 184 192 8
cert_badTest_block_4 1536 24 192 200 8
cert_badTest_block_4 1536 25 200 208 8
cert_badTest_block_4 1536 26 208 216 8
cert_badTest_block_4 1536 27 216 224 8
cert_badTest_block_4 1536 28 224 232 8
cert_badTest_block_4 1536 29 232 240 8
cert_badTest_block_4 1536 30 240 248 8
cert_badTest_block_4 1536 31 248 256 8
theorem badTest_1536_complete : Interval badTest_1536 0 256 :=
  (interval_append badTest_1536 0 128 256
  (interval_append badTest_1536 0 64 128
  (interval_append badTest_1536 0 32 64
  (interval_append badTest_1536 0 16 32
  (interval_append badTest_1536 0 8 16
  badTest_1536_block_0
  badTest_1536_block_1)
  (interval_append badTest_1536 16 24 32
  badTest_1536_block_2
  badTest_1536_block_3))
  (interval_append badTest_1536 32 48 64
  (interval_append badTest_1536 32 40 48
  badTest_1536_block_4
  badTest_1536_block_5)
  (interval_append badTest_1536 48 56 64
  badTest_1536_block_6
  badTest_1536_block_7)))
  (interval_append badTest_1536 64 96 128
  (interval_append badTest_1536 64 80 96
  (interval_append badTest_1536 64 72 80
  badTest_1536_block_8
  badTest_1536_block_9)
  (interval_append badTest_1536 80 88 96
  badTest_1536_block_10
  badTest_1536_block_11))
  (interval_append badTest_1536 96 112 128
  (interval_append badTest_1536 96 104 112
  badTest_1536_block_12
  badTest_1536_block_13)
  (interval_append badTest_1536 112 120 128
  badTest_1536_block_14
  badTest_1536_block_15))))
  (interval_append badTest_1536 128 192 256
  (interval_append badTest_1536 128 160 192
  (interval_append badTest_1536 128 144 160
  (interval_append badTest_1536 128 136 144
  badTest_1536_block_16
  badTest_1536_block_17)
  (interval_append badTest_1536 144 152 160
  badTest_1536_block_18
  badTest_1536_block_19))
  (interval_append badTest_1536 160 176 192
  (interval_append badTest_1536 160 168 176
  badTest_1536_block_20
  badTest_1536_block_21)
  (interval_append badTest_1536 176 184 192
  badTest_1536_block_22
  badTest_1536_block_23)))
  (interval_append badTest_1536 192 224 256
  (interval_append badTest_1536 192 208 224
  (interval_append badTest_1536 192 200 208
  badTest_1536_block_24
  badTest_1536_block_25)
  (interval_append badTest_1536 208 216 224
  badTest_1536_block_26
  badTest_1536_block_27))
  (interval_append badTest_1536 224 240 256
  (interval_append badTest_1536 224 232 240
  badTest_1536_block_28
  badTest_1536_block_29)
  (interval_append badTest_1536 240 248 256
  badTest_1536_block_30
  badTest_1536_block_31)))))
cert_badTestInterval_4 1536 1792
end Papers.RationalityTen.RootedCaches.RootedSixBase03
