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
cert_cellTest_9 1792
cert_cellTest_block_5 1792 0 0 8 8
cert_cellTest_block_5 1792 1 8 16 8
cert_cellTest_block_5 1792 2 16 24 8
cert_cellTest_block_5 1792 3 24 32 8
cert_cellTest_block_5 1792 4 32 40 8
cert_cellTest_block_5 1792 5 40 48 8
cert_cellTest_block_5 1792 6 48 56 8
cert_cellTest_block_5 1792 7 56 64 8
cert_cellTest_block_5 1792 8 64 72 8
cert_cellTest_block_5 1792 9 72 80 8
cert_cellTest_block_5 1792 10 80 88 8
cert_cellTest_block_5 1792 11 88 96 8
cert_cellTest_block_5 1792 12 96 104 8
cert_cellTest_block_5 1792 13 104 112 8
cert_cellTest_block_5 1792 14 112 120 8
cert_cellTest_block_5 1792 15 120 128 8
cert_cellTest_block_5 1792 16 128 136 8
cert_cellTest_block_5 1792 17 136 144 8
cert_cellTest_block_5 1792 18 144 152 8
cert_cellTest_block_5 1792 19 152 160 8
cert_cellTest_block_5 1792 20 160 168 8
cert_cellTest_block_5 1792 21 168 176 8
cert_cellTest_block_5 1792 22 176 184 8
cert_cellTest_block_5 1792 23 184 192 8
cert_cellTest_block_5 1792 24 192 200 8
cert_cellTest_block_5 1792 25 200 208 8
cert_cellTest_block_5 1792 26 208 216 8
cert_cellTest_block_5 1792 27 216 224 8
cert_cellTest_block_5 1792 28 224 232 8
cert_cellTest_block_5 1792 29 232 240 8
cert_cellTest_block_5 1792 30 240 248 8
cert_cellTest_block_5 1792 31 248 256 8
theorem cellTest_1792_complete : Interval cellTest_1792 0 256 :=
  (interval_append cellTest_1792 0 128 256
  (interval_append cellTest_1792 0 64 128
  (interval_append cellTest_1792 0 32 64
  (interval_append cellTest_1792 0 16 32
  (interval_append cellTest_1792 0 8 16
  cellTest_1792_block_0
  cellTest_1792_block_1)
  (interval_append cellTest_1792 16 24 32
  cellTest_1792_block_2
  cellTest_1792_block_3))
  (interval_append cellTest_1792 32 48 64
  (interval_append cellTest_1792 32 40 48
  cellTest_1792_block_4
  cellTest_1792_block_5)
  (interval_append cellTest_1792 48 56 64
  cellTest_1792_block_6
  cellTest_1792_block_7)))
  (interval_append cellTest_1792 64 96 128
  (interval_append cellTest_1792 64 80 96
  (interval_append cellTest_1792 64 72 80
  cellTest_1792_block_8
  cellTest_1792_block_9)
  (interval_append cellTest_1792 80 88 96
  cellTest_1792_block_10
  cellTest_1792_block_11))
  (interval_append cellTest_1792 96 112 128
  (interval_append cellTest_1792 96 104 112
  cellTest_1792_block_12
  cellTest_1792_block_13)
  (interval_append cellTest_1792 112 120 128
  cellTest_1792_block_14
  cellTest_1792_block_15))))
  (interval_append cellTest_1792 128 192 256
  (interval_append cellTest_1792 128 160 192
  (interval_append cellTest_1792 128 144 160
  (interval_append cellTest_1792 128 136 144
  cellTest_1792_block_16
  cellTest_1792_block_17)
  (interval_append cellTest_1792 144 152 160
  cellTest_1792_block_18
  cellTest_1792_block_19))
  (interval_append cellTest_1792 160 176 192
  (interval_append cellTest_1792 160 168 176
  cellTest_1792_block_20
  cellTest_1792_block_21)
  (interval_append cellTest_1792 176 184 192
  cellTest_1792_block_22
  cellTest_1792_block_23)))
  (interval_append cellTest_1792 192 224 256
  (interval_append cellTest_1792 192 208 224
  (interval_append cellTest_1792 192 200 208
  cellTest_1792_block_24
  cellTest_1792_block_25)
  (interval_append cellTest_1792 208 216 224
  cellTest_1792_block_26
  cellTest_1792_block_27))
  (interval_append cellTest_1792 224 240 256
  (interval_append cellTest_1792 224 232 240
  cellTest_1792_block_28
  cellTest_1792_block_29)
  (interval_append cellTest_1792 240 248 256
  cellTest_1792_block_30
  cellTest_1792_block_31)))))
cert_cellTestInterval_4 1792 2048
end Papers.RationalityTen.RootedCaches.RootedSixBase03
