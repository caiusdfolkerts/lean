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
cert_badTest_6 2816
cert_badTest_block_4 2816 0 0 8 8
cert_badTest_block_4 2816 1 8 16 8
cert_badTest_block_4 2816 2 16 24 8
cert_badTest_block_4 2816 3 24 32 8
cert_badTest_block_4 2816 4 32 40 8
cert_badTest_block_4 2816 5 40 48 8
cert_badTest_block_4 2816 6 48 56 8
cert_badTest_block_4 2816 7 56 64 8
cert_badTest_block_4 2816 8 64 72 8
cert_badTest_block_4 2816 9 72 80 8
cert_badTest_block_4 2816 10 80 88 8
cert_badTest_block_4 2816 11 88 96 8
cert_badTest_block_4 2816 12 96 104 8
cert_badTest_block_4 2816 13 104 112 8
cert_badTest_block_4 2816 14 112 120 8
cert_badTest_block_4 2816 15 120 128 8
cert_badTest_block_4 2816 16 128 136 8
cert_badTest_block_4 2816 17 136 144 8
cert_badTest_block_4 2816 18 144 152 8
cert_badTest_block_4 2816 19 152 160 8
cert_badTest_block_4 2816 20 160 168 8
cert_badTest_block_4 2816 21 168 176 8
cert_badTest_block_4 2816 22 176 184 8
cert_badTest_block_4 2816 23 184 192 8
cert_badTest_block_4 2816 24 192 200 8
cert_badTest_block_4 2816 25 200 208 8
cert_badTest_block_4 2816 26 208 216 8
cert_badTest_block_4 2816 27 216 224 8
cert_badTest_block_4 2816 28 224 232 8
cert_badTest_block_4 2816 29 232 240 8
cert_badTest_block_4 2816 30 240 248 8
cert_badTest_block_4 2816 31 248 256 8
theorem badTest_2816_complete : Interval badTest_2816 0 256 :=
  (interval_append badTest_2816 0 128 256
  (interval_append badTest_2816 0 64 128
  (interval_append badTest_2816 0 32 64
  (interval_append badTest_2816 0 16 32
  (interval_append badTest_2816 0 8 16
  badTest_2816_block_0
  badTest_2816_block_1)
  (interval_append badTest_2816 16 24 32
  badTest_2816_block_2
  badTest_2816_block_3))
  (interval_append badTest_2816 32 48 64
  (interval_append badTest_2816 32 40 48
  badTest_2816_block_4
  badTest_2816_block_5)
  (interval_append badTest_2816 48 56 64
  badTest_2816_block_6
  badTest_2816_block_7)))
  (interval_append badTest_2816 64 96 128
  (interval_append badTest_2816 64 80 96
  (interval_append badTest_2816 64 72 80
  badTest_2816_block_8
  badTest_2816_block_9)
  (interval_append badTest_2816 80 88 96
  badTest_2816_block_10
  badTest_2816_block_11))
  (interval_append badTest_2816 96 112 128
  (interval_append badTest_2816 96 104 112
  badTest_2816_block_12
  badTest_2816_block_13)
  (interval_append badTest_2816 112 120 128
  badTest_2816_block_14
  badTest_2816_block_15))))
  (interval_append badTest_2816 128 192 256
  (interval_append badTest_2816 128 160 192
  (interval_append badTest_2816 128 144 160
  (interval_append badTest_2816 128 136 144
  badTest_2816_block_16
  badTest_2816_block_17)
  (interval_append badTest_2816 144 152 160
  badTest_2816_block_18
  badTest_2816_block_19))
  (interval_append badTest_2816 160 176 192
  (interval_append badTest_2816 160 168 176
  badTest_2816_block_20
  badTest_2816_block_21)
  (interval_append badTest_2816 176 184 192
  badTest_2816_block_22
  badTest_2816_block_23)))
  (interval_append badTest_2816 192 224 256
  (interval_append badTest_2816 192 208 224
  (interval_append badTest_2816 192 200 208
  badTest_2816_block_24
  badTest_2816_block_25)
  (interval_append badTest_2816 208 216 224
  badTest_2816_block_26
  badTest_2816_block_27))
  (interval_append badTest_2816 224 240 256
  (interval_append badTest_2816 224 232 240
  badTest_2816_block_28
  badTest_2816_block_29)
  (interval_append badTest_2816 240 248 256
  badTest_2816_block_30
  badTest_2816_block_31)))))
cert_badTestInterval_4 2816 3072
end Papers.RationalityTen.RootedCaches.RootedSixBase03
