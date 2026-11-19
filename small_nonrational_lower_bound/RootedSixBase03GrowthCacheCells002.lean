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
cert_cellTest_9 512
cert_cellTest_block_5 512 0 0 8 8
cert_cellTest_block_5 512 1 8 16 8
cert_cellTest_block_5 512 2 16 24 8
cert_cellTest_block_5 512 3 24 32 8
cert_cellTest_block_5 512 4 32 40 8
cert_cellTest_block_5 512 5 40 48 8
cert_cellTest_block_5 512 6 48 56 8
cert_cellTest_block_5 512 7 56 64 8
cert_cellTest_block_5 512 8 64 72 8
cert_cellTest_block_5 512 9 72 80 8
cert_cellTest_block_5 512 10 80 88 8
cert_cellTest_block_5 512 11 88 96 8
cert_cellTest_block_5 512 12 96 104 8
cert_cellTest_block_5 512 13 104 112 8
cert_cellTest_block_5 512 14 112 120 8
cert_cellTest_block_5 512 15 120 128 8
cert_cellTest_block_5 512 16 128 136 8
cert_cellTest_block_5 512 17 136 144 8
cert_cellTest_block_5 512 18 144 152 8
cert_cellTest_block_5 512 19 152 160 8
cert_cellTest_block_5 512 20 160 168 8
cert_cellTest_block_5 512 21 168 176 8
cert_cellTest_block_5 512 22 176 184 8
cert_cellTest_block_5 512 23 184 192 8
cert_cellTest_block_5 512 24 192 200 8
cert_cellTest_block_5 512 25 200 208 8
cert_cellTest_block_5 512 26 208 216 8
cert_cellTest_block_5 512 27 216 224 8
cert_cellTest_block_5 512 28 224 232 8
cert_cellTest_block_5 512 29 232 240 8
cert_cellTest_block_5 512 30 240 248 8
cert_cellTest_block_5 512 31 248 256 8
theorem cellTest_512_complete : Interval cellTest_512 0 256 :=
  (interval_append cellTest_512 0 128 256
  (interval_append cellTest_512 0 64 128
  (interval_append cellTest_512 0 32 64
  (interval_append cellTest_512 0 16 32
  (interval_append cellTest_512 0 8 16
  cellTest_512_block_0
  cellTest_512_block_1)
  (interval_append cellTest_512 16 24 32
  cellTest_512_block_2
  cellTest_512_block_3))
  (interval_append cellTest_512 32 48 64
  (interval_append cellTest_512 32 40 48
  cellTest_512_block_4
  cellTest_512_block_5)
  (interval_append cellTest_512 48 56 64
  cellTest_512_block_6
  cellTest_512_block_7)))
  (interval_append cellTest_512 64 96 128
  (interval_append cellTest_512 64 80 96
  (interval_append cellTest_512 64 72 80
  cellTest_512_block_8
  cellTest_512_block_9)
  (interval_append cellTest_512 80 88 96
  cellTest_512_block_10
  cellTest_512_block_11))
  (interval_append cellTest_512 96 112 128
  (interval_append cellTest_512 96 104 112
  cellTest_512_block_12
  cellTest_512_block_13)
  (interval_append cellTest_512 112 120 128
  cellTest_512_block_14
  cellTest_512_block_15))))
  (interval_append cellTest_512 128 192 256
  (interval_append cellTest_512 128 160 192
  (interval_append cellTest_512 128 144 160
  (interval_append cellTest_512 128 136 144
  cellTest_512_block_16
  cellTest_512_block_17)
  (interval_append cellTest_512 144 152 160
  cellTest_512_block_18
  cellTest_512_block_19))
  (interval_append cellTest_512 160 176 192
  (interval_append cellTest_512 160 168 176
  cellTest_512_block_20
  cellTest_512_block_21)
  (interval_append cellTest_512 176 184 192
  cellTest_512_block_22
  cellTest_512_block_23)))
  (interval_append cellTest_512 192 224 256
  (interval_append cellTest_512 192 208 224
  (interval_append cellTest_512 192 200 208
  cellTest_512_block_24
  cellTest_512_block_25)
  (interval_append cellTest_512 208 216 224
  cellTest_512_block_26
  cellTest_512_block_27))
  (interval_append cellTest_512 224 240 256
  (interval_append cellTest_512 224 232 240
  cellTest_512_block_28
  cellTest_512_block_29)
  (interval_append cellTest_512 240 248 256
  cellTest_512_block_30
  cellTest_512_block_31)))))
cert_cellTestInterval_4 512 768
end Papers.RationalityTen.RootedCaches.RootedSixBase03
