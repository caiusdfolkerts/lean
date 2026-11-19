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
cert_badTest_6 768
cert_badTest_block_4 768 0 0 8 8
cert_badTest_block_4 768 1 8 16 8
cert_badTest_block_4 768 2 16 24 8
cert_badTest_block_4 768 3 24 32 8
cert_badTest_block_4 768 4 32 40 8
cert_badTest_block_4 768 5 40 48 8
cert_badTest_block_4 768 6 48 56 8
cert_badTest_block_4 768 7 56 64 8
cert_badTest_block_4 768 8 64 72 8
cert_badTest_block_4 768 9 72 80 8
cert_badTest_block_4 768 10 80 88 8
cert_badTest_block_4 768 11 88 96 8
cert_badTest_block_4 768 12 96 104 8
cert_badTest_block_4 768 13 104 112 8
cert_badTest_block_4 768 14 112 120 8
cert_badTest_block_4 768 15 120 128 8
cert_badTest_block_4 768 16 128 136 8
cert_badTest_block_4 768 17 136 144 8
cert_badTest_block_4 768 18 144 152 8
cert_badTest_block_4 768 19 152 160 8
cert_badTest_block_4 768 20 160 168 8
cert_badTest_block_4 768 21 168 176 8
cert_badTest_block_4 768 22 176 184 8
cert_badTest_block_4 768 23 184 192 8
cert_badTest_block_4 768 24 192 200 8
cert_badTest_block_4 768 25 200 208 8
cert_badTest_block_4 768 26 208 216 8
cert_badTest_block_4 768 27 216 224 8
cert_badTest_block_4 768 28 224 232 8
cert_badTest_block_4 768 29 232 240 8
cert_badTest_block_4 768 30 240 248 8
cert_badTest_block_4 768 31 248 256 8
theorem badTest_768_complete : Interval badTest_768 0 256 :=
  (interval_append badTest_768 0 128 256
  (interval_append badTest_768 0 64 128
  (interval_append badTest_768 0 32 64
  (interval_append badTest_768 0 16 32
  (interval_append badTest_768 0 8 16
  badTest_768_block_0
  badTest_768_block_1)
  (interval_append badTest_768 16 24 32
  badTest_768_block_2
  badTest_768_block_3))
  (interval_append badTest_768 32 48 64
  (interval_append badTest_768 32 40 48
  badTest_768_block_4
  badTest_768_block_5)
  (interval_append badTest_768 48 56 64
  badTest_768_block_6
  badTest_768_block_7)))
  (interval_append badTest_768 64 96 128
  (interval_append badTest_768 64 80 96
  (interval_append badTest_768 64 72 80
  badTest_768_block_8
  badTest_768_block_9)
  (interval_append badTest_768 80 88 96
  badTest_768_block_10
  badTest_768_block_11))
  (interval_append badTest_768 96 112 128
  (interval_append badTest_768 96 104 112
  badTest_768_block_12
  badTest_768_block_13)
  (interval_append badTest_768 112 120 128
  badTest_768_block_14
  badTest_768_block_15))))
  (interval_append badTest_768 128 192 256
  (interval_append badTest_768 128 160 192
  (interval_append badTest_768 128 144 160
  (interval_append badTest_768 128 136 144
  badTest_768_block_16
  badTest_768_block_17)
  (interval_append badTest_768 144 152 160
  badTest_768_block_18
  badTest_768_block_19))
  (interval_append badTest_768 160 176 192
  (interval_append badTest_768 160 168 176
  badTest_768_block_20
  badTest_768_block_21)
  (interval_append badTest_768 176 184 192
  badTest_768_block_22
  badTest_768_block_23)))
  (interval_append badTest_768 192 224 256
  (interval_append badTest_768 192 208 224
  (interval_append badTest_768 192 200 208
  badTest_768_block_24
  badTest_768_block_25)
  (interval_append badTest_768 208 216 224
  badTest_768_block_26
  badTest_768_block_27))
  (interval_append badTest_768 224 240 256
  (interval_append badTest_768 224 232 240
  badTest_768_block_28
  badTest_768_block_29)
  (interval_append badTest_768 240 248 256
  badTest_768_block_30
  badTest_768_block_31)))))
cert_badTestInterval_4 768 1024
end Papers.RationalityTen.RootedCaches.RootedSixBase03
