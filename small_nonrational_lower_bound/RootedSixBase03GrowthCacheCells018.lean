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
cert_cellTest_9 4608
cert_cellTest_block_5 4608 0 0 8 8
cert_cellTest_block_5 4608 1 8 16 8
cert_cellTest_block_5 4608 2 16 24 8
cert_cellTest_block_5 4608 3 24 32 8
cert_cellTest_block_5 4608 4 32 40 8
cert_cellTest_block_5 4608 5 40 48 8
cert_cellTest_block_5 4608 6 48 56 8
cert_cellTest_block_5 4608 7 56 64 8
cert_cellTest_block_5 4608 8 64 72 8
cert_cellTest_block_5 4608 9 72 80 8
cert_cellTest_block_5 4608 10 80 88 8
cert_cellTest_block_5 4608 11 88 96 8
cert_cellTest_block_5 4608 12 96 104 8
cert_cellTest_block_5 4608 13 104 112 8
cert_cellTest_block_5 4608 14 112 120 8
cert_cellTest_block_5 4608 15 120 128 8
cert_cellTest_block_5 4608 16 128 136 8
cert_cellTest_block_5 4608 17 136 144 8
cert_cellTest_block_5 4608 18 144 152 8
cert_cellTest_block_5 4608 19 152 160 8
cert_cellTest_block_5 4608 20 160 168 8
cert_cellTest_block_5 4608 21 168 176 8
cert_cellTest_block_5 4608 22 176 184 8
cert_cellTest_block_5 4608 23 184 192 8
cert_cellTest_block_5 4608 24 192 200 8
cert_cellTest_block_5 4608 25 200 208 8
cert_cellTest_block_5 4608 26 208 216 8
cert_cellTest_block_5 4608 27 216 224 8
cert_cellTest_block_5 4608 28 224 232 8
cert_cellTest_block_5 4608 29 232 240 8
cert_cellTest_block_5 4608 30 240 248 8
cert_cellTest_block_5 4608 31 248 256 8
theorem cellTest_4608_complete : Interval cellTest_4608 0 256 :=
  (interval_append cellTest_4608 0 128 256
  (interval_append cellTest_4608 0 64 128
  (interval_append cellTest_4608 0 32 64
  (interval_append cellTest_4608 0 16 32
  (interval_append cellTest_4608 0 8 16
  cellTest_4608_block_0
  cellTest_4608_block_1)
  (interval_append cellTest_4608 16 24 32
  cellTest_4608_block_2
  cellTest_4608_block_3))
  (interval_append cellTest_4608 32 48 64
  (interval_append cellTest_4608 32 40 48
  cellTest_4608_block_4
  cellTest_4608_block_5)
  (interval_append cellTest_4608 48 56 64
  cellTest_4608_block_6
  cellTest_4608_block_7)))
  (interval_append cellTest_4608 64 96 128
  (interval_append cellTest_4608 64 80 96
  (interval_append cellTest_4608 64 72 80
  cellTest_4608_block_8
  cellTest_4608_block_9)
  (interval_append cellTest_4608 80 88 96
  cellTest_4608_block_10
  cellTest_4608_block_11))
  (interval_append cellTest_4608 96 112 128
  (interval_append cellTest_4608 96 104 112
  cellTest_4608_block_12
  cellTest_4608_block_13)
  (interval_append cellTest_4608 112 120 128
  cellTest_4608_block_14
  cellTest_4608_block_15))))
  (interval_append cellTest_4608 128 192 256
  (interval_append cellTest_4608 128 160 192
  (interval_append cellTest_4608 128 144 160
  (interval_append cellTest_4608 128 136 144
  cellTest_4608_block_16
  cellTest_4608_block_17)
  (interval_append cellTest_4608 144 152 160
  cellTest_4608_block_18
  cellTest_4608_block_19))
  (interval_append cellTest_4608 160 176 192
  (interval_append cellTest_4608 160 168 176
  cellTest_4608_block_20
  cellTest_4608_block_21)
  (interval_append cellTest_4608 176 184 192
  cellTest_4608_block_22
  cellTest_4608_block_23)))
  (interval_append cellTest_4608 192 224 256
  (interval_append cellTest_4608 192 208 224
  (interval_append cellTest_4608 192 200 208
  cellTest_4608_block_24
  cellTest_4608_block_25)
  (interval_append cellTest_4608 208 216 224
  cellTest_4608_block_26
  cellTest_4608_block_27))
  (interval_append cellTest_4608 224 240 256
  (interval_append cellTest_4608 224 232 240
  cellTest_4608_block_28
  cellTest_4608_block_29)
  (interval_append cellTest_4608 240 248 256
  cellTest_4608_block_30
  cellTest_4608_block_31)))))
cert_cellTestInterval_4 4608 4864
end Papers.RationalityTen.RootedCaches.RootedSixBase03
