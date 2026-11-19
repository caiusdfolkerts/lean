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
cert_cellTest_9 3584
cert_cellTest_block_5 3584 0 0 8 8
cert_cellTest_block_5 3584 1 8 16 8
cert_cellTest_block_5 3584 2 16 24 8
cert_cellTest_block_5 3584 3 24 32 8
cert_cellTest_block_5 3584 4 32 40 8
cert_cellTest_block_5 3584 5 40 48 8
cert_cellTest_block_5 3584 6 48 56 8
cert_cellTest_block_5 3584 7 56 64 8
cert_cellTest_block_5 3584 8 64 72 8
cert_cellTest_block_5 3584 9 72 80 8
cert_cellTest_block_5 3584 10 80 88 8
cert_cellTest_block_5 3584 11 88 96 8
cert_cellTest_block_5 3584 12 96 104 8
cert_cellTest_block_5 3584 13 104 112 8
cert_cellTest_block_5 3584 14 112 120 8
cert_cellTest_block_5 3584 15 120 128 8
cert_cellTest_block_5 3584 16 128 136 8
cert_cellTest_block_5 3584 17 136 144 8
cert_cellTest_block_5 3584 18 144 152 8
cert_cellTest_block_5 3584 19 152 160 8
cert_cellTest_block_5 3584 20 160 168 8
cert_cellTest_block_5 3584 21 168 176 8
cert_cellTest_block_5 3584 22 176 184 8
cert_cellTest_block_5 3584 23 184 192 8
cert_cellTest_block_5 3584 24 192 200 8
cert_cellTest_block_5 3584 25 200 208 8
cert_cellTest_block_5 3584 26 208 216 8
cert_cellTest_block_5 3584 27 216 224 8
cert_cellTest_block_5 3584 28 224 232 8
cert_cellTest_block_5 3584 29 232 240 8
cert_cellTest_block_5 3584 30 240 248 8
cert_cellTest_block_5 3584 31 248 256 8
theorem cellTest_3584_complete : Interval cellTest_3584 0 256 :=
  (interval_append cellTest_3584 0 128 256
  (interval_append cellTest_3584 0 64 128
  (interval_append cellTest_3584 0 32 64
  (interval_append cellTest_3584 0 16 32
  (interval_append cellTest_3584 0 8 16
  cellTest_3584_block_0
  cellTest_3584_block_1)
  (interval_append cellTest_3584 16 24 32
  cellTest_3584_block_2
  cellTest_3584_block_3))
  (interval_append cellTest_3584 32 48 64
  (interval_append cellTest_3584 32 40 48
  cellTest_3584_block_4
  cellTest_3584_block_5)
  (interval_append cellTest_3584 48 56 64
  cellTest_3584_block_6
  cellTest_3584_block_7)))
  (interval_append cellTest_3584 64 96 128
  (interval_append cellTest_3584 64 80 96
  (interval_append cellTest_3584 64 72 80
  cellTest_3584_block_8
  cellTest_3584_block_9)
  (interval_append cellTest_3584 80 88 96
  cellTest_3584_block_10
  cellTest_3584_block_11))
  (interval_append cellTest_3584 96 112 128
  (interval_append cellTest_3584 96 104 112
  cellTest_3584_block_12
  cellTest_3584_block_13)
  (interval_append cellTest_3584 112 120 128
  cellTest_3584_block_14
  cellTest_3584_block_15))))
  (interval_append cellTest_3584 128 192 256
  (interval_append cellTest_3584 128 160 192
  (interval_append cellTest_3584 128 144 160
  (interval_append cellTest_3584 128 136 144
  cellTest_3584_block_16
  cellTest_3584_block_17)
  (interval_append cellTest_3584 144 152 160
  cellTest_3584_block_18
  cellTest_3584_block_19))
  (interval_append cellTest_3584 160 176 192
  (interval_append cellTest_3584 160 168 176
  cellTest_3584_block_20
  cellTest_3584_block_21)
  (interval_append cellTest_3584 176 184 192
  cellTest_3584_block_22
  cellTest_3584_block_23)))
  (interval_append cellTest_3584 192 224 256
  (interval_append cellTest_3584 192 208 224
  (interval_append cellTest_3584 192 200 208
  cellTest_3584_block_24
  cellTest_3584_block_25)
  (interval_append cellTest_3584 208 216 224
  cellTest_3584_block_26
  cellTest_3584_block_27))
  (interval_append cellTest_3584 224 240 256
  (interval_append cellTest_3584 224 232 240
  cellTest_3584_block_28
  cellTest_3584_block_29)
  (interval_append cellTest_3584 240 248 256
  cellTest_3584_block_30
  cellTest_3584_block_31)))))
cert_cellTestInterval_4 3584 3840
end Papers.RationalityTen.RootedCaches.RootedSixBase03
