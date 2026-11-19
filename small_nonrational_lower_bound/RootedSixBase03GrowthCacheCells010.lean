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
cert_cellTest_9 2560
cert_cellTest_block_5 2560 0 0 8 8
cert_cellTest_block_5 2560 1 8 16 8
cert_cellTest_block_5 2560 2 16 24 8
cert_cellTest_block_5 2560 3 24 32 8
cert_cellTest_block_5 2560 4 32 40 8
cert_cellTest_block_5 2560 5 40 48 8
cert_cellTest_block_5 2560 6 48 56 8
cert_cellTest_block_5 2560 7 56 64 8
cert_cellTest_block_5 2560 8 64 72 8
cert_cellTest_block_5 2560 9 72 80 8
cert_cellTest_block_5 2560 10 80 88 8
cert_cellTest_block_5 2560 11 88 96 8
cert_cellTest_block_5 2560 12 96 104 8
cert_cellTest_block_5 2560 13 104 112 8
cert_cellTest_block_5 2560 14 112 120 8
cert_cellTest_block_5 2560 15 120 128 8
cert_cellTest_block_5 2560 16 128 136 8
cert_cellTest_block_5 2560 17 136 144 8
cert_cellTest_block_5 2560 18 144 152 8
cert_cellTest_block_5 2560 19 152 160 8
cert_cellTest_block_5 2560 20 160 168 8
cert_cellTest_block_5 2560 21 168 176 8
cert_cellTest_block_5 2560 22 176 184 8
cert_cellTest_block_5 2560 23 184 192 8
cert_cellTest_block_5 2560 24 192 200 8
cert_cellTest_block_5 2560 25 200 208 8
cert_cellTest_block_5 2560 26 208 216 8
cert_cellTest_block_5 2560 27 216 224 8
cert_cellTest_block_5 2560 28 224 232 8
cert_cellTest_block_5 2560 29 232 240 8
cert_cellTest_block_5 2560 30 240 248 8
cert_cellTest_block_5 2560 31 248 256 8
theorem cellTest_2560_complete : Interval cellTest_2560 0 256 :=
  (interval_append cellTest_2560 0 128 256
  (interval_append cellTest_2560 0 64 128
  (interval_append cellTest_2560 0 32 64
  (interval_append cellTest_2560 0 16 32
  (interval_append cellTest_2560 0 8 16
  cellTest_2560_block_0
  cellTest_2560_block_1)
  (interval_append cellTest_2560 16 24 32
  cellTest_2560_block_2
  cellTest_2560_block_3))
  (interval_append cellTest_2560 32 48 64
  (interval_append cellTest_2560 32 40 48
  cellTest_2560_block_4
  cellTest_2560_block_5)
  (interval_append cellTest_2560 48 56 64
  cellTest_2560_block_6
  cellTest_2560_block_7)))
  (interval_append cellTest_2560 64 96 128
  (interval_append cellTest_2560 64 80 96
  (interval_append cellTest_2560 64 72 80
  cellTest_2560_block_8
  cellTest_2560_block_9)
  (interval_append cellTest_2560 80 88 96
  cellTest_2560_block_10
  cellTest_2560_block_11))
  (interval_append cellTest_2560 96 112 128
  (interval_append cellTest_2560 96 104 112
  cellTest_2560_block_12
  cellTest_2560_block_13)
  (interval_append cellTest_2560 112 120 128
  cellTest_2560_block_14
  cellTest_2560_block_15))))
  (interval_append cellTest_2560 128 192 256
  (interval_append cellTest_2560 128 160 192
  (interval_append cellTest_2560 128 144 160
  (interval_append cellTest_2560 128 136 144
  cellTest_2560_block_16
  cellTest_2560_block_17)
  (interval_append cellTest_2560 144 152 160
  cellTest_2560_block_18
  cellTest_2560_block_19))
  (interval_append cellTest_2560 160 176 192
  (interval_append cellTest_2560 160 168 176
  cellTest_2560_block_20
  cellTest_2560_block_21)
  (interval_append cellTest_2560 176 184 192
  cellTest_2560_block_22
  cellTest_2560_block_23)))
  (interval_append cellTest_2560 192 224 256
  (interval_append cellTest_2560 192 208 224
  (interval_append cellTest_2560 192 200 208
  cellTest_2560_block_24
  cellTest_2560_block_25)
  (interval_append cellTest_2560 208 216 224
  cellTest_2560_block_26
  cellTest_2560_block_27))
  (interval_append cellTest_2560 224 240 256
  (interval_append cellTest_2560 224 232 240
  cellTest_2560_block_28
  cellTest_2560_block_29)
  (interval_append cellTest_2560 240 248 256
  cellTest_2560_block_30
  cellTest_2560_block_31)))))
cert_cellTestInterval_4 2560 2816
end Papers.RationalityTen.RootedCaches.RootedSixBase03
