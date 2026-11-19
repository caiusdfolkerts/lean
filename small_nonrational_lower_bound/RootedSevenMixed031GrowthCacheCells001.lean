module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed031GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed031
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest_3 256
cert_cellTest_block_3 256 0 0 8 8
cert_cellTest_block_3 256 1 8 16 8
cert_cellTest_block_3 256 2 16 24 8
cert_cellTest_block_3 256 3 24 32 8
cert_cellTest_block_3 256 4 32 40 8
cert_cellTest_block_3 256 5 40 48 8
cert_cellTest_block_3 256 6 48 56 8
cert_cellTest_block_3 256 7 56 64 8
cert_cellTest_block_3 256 8 64 72 8
cert_cellTest_block_3 256 9 72 80 8
cert_cellTest_block_3 256 10 80 88 8
cert_cellTest_block_3 256 11 88 96 8
cert_cellTest_block_3 256 12 96 104 8
cert_cellTest_block_3 256 13 104 112 8
cert_cellTest_block_3 256 14 112 120 8
cert_cellTest_block_3 256 15 120 128 8
cert_cellTest_block_3 256 16 128 136 8
cert_cellTest_block_3 256 17 136 144 8
cert_cellTest_block_3 256 18 144 152 8
cert_cellTest_block_3 256 19 152 160 8
cert_cellTest_block_3 256 20 160 168 8
cert_cellTest_block_3 256 21 168 176 8
cert_cellTest_block_3 256 22 176 184 8
cert_cellTest_block_3 256 23 184 192 8
cert_cellTest_block_3 256 24 192 200 8
cert_cellTest_block_3 256 25 200 208 8
cert_cellTest_block_3 256 26 208 216 8
cert_cellTest_block_3 256 27 216 224 8
cert_cellTest_block_3 256 28 224 232 8
cert_cellTest_block_3 256 29 232 240 8
cert_cellTest_block_3 256 30 240 248 8
cert_cellTest_block_3 256 31 248 256 8
theorem cellTest_256_complete : Interval cellTest_256 0 256 :=
  (interval_append cellTest_256 0 128 256
  (interval_append cellTest_256 0 64 128
  (interval_append cellTest_256 0 32 64
  (interval_append cellTest_256 0 16 32
  (interval_append cellTest_256 0 8 16
  cellTest_256_block_0
  cellTest_256_block_1)
  (interval_append cellTest_256 16 24 32
  cellTest_256_block_2
  cellTest_256_block_3))
  (interval_append cellTest_256 32 48 64
  (interval_append cellTest_256 32 40 48
  cellTest_256_block_4
  cellTest_256_block_5)
  (interval_append cellTest_256 48 56 64
  cellTest_256_block_6
  cellTest_256_block_7)))
  (interval_append cellTest_256 64 96 128
  (interval_append cellTest_256 64 80 96
  (interval_append cellTest_256 64 72 80
  cellTest_256_block_8
  cellTest_256_block_9)
  (interval_append cellTest_256 80 88 96
  cellTest_256_block_10
  cellTest_256_block_11))
  (interval_append cellTest_256 96 112 128
  (interval_append cellTest_256 96 104 112
  cellTest_256_block_12
  cellTest_256_block_13)
  (interval_append cellTest_256 112 120 128
  cellTest_256_block_14
  cellTest_256_block_15))))
  (interval_append cellTest_256 128 192 256
  (interval_append cellTest_256 128 160 192
  (interval_append cellTest_256 128 144 160
  (interval_append cellTest_256 128 136 144
  cellTest_256_block_16
  cellTest_256_block_17)
  (interval_append cellTest_256 144 152 160
  cellTest_256_block_18
  cellTest_256_block_19))
  (interval_append cellTest_256 160 176 192
  (interval_append cellTest_256 160 168 176
  cellTest_256_block_20
  cellTest_256_block_21)
  (interval_append cellTest_256 176 184 192
  cellTest_256_block_22
  cellTest_256_block_23)))
  (interval_append cellTest_256 192 224 256
  (interval_append cellTest_256 192 208 224
  (interval_append cellTest_256 192 200 208
  cellTest_256_block_24
  cellTest_256_block_25)
  (interval_append cellTest_256 208 216 224
  cellTest_256_block_26
  cellTest_256_block_27))
  (interval_append cellTest_256 224 240 256
  (interval_append cellTest_256 224 232 240
  cellTest_256_block_28
  cellTest_256_block_29)
  (interval_append cellTest_256 240 248 256
  cellTest_256_block_30
  cellTest_256_block_31)))))
cert_cellTestInterval_2 256 512
end Papers.RationalityTen.RootedCaches.RootedSevenMixed031
