module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public import RootedSevenPure008GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure008
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest_6 512
cert_cellTest_block_4 512 0 0 8 8
cert_cellTest_block_4 512 1 8 16 8
cert_cellTest_block_4 512 2 16 24 8
cert_cellTest_block_4 512 3 24 32 8
cert_cellTest_block_4 512 4 32 40 8
cert_cellTest_block_4 512 5 40 48 8
cert_cellTest_block_4 512 6 48 56 8
cert_cellTest_block_4 512 7 56 64 8
cert_cellTest_block_4 512 8 64 72 8
cert_cellTest_block_4 512 9 72 80 8
cert_cellTest_block_4 512 10 80 88 8
cert_cellTest_block_4 512 11 88 96 8
cert_cellTest_block_4 512 12 96 104 8
cert_cellTest_block_4 512 13 104 112 8
cert_cellTest_block_4 512 14 112 120 8
cert_cellTest_block_4 512 15 120 128 8
cert_cellTest_block_4 512 16 128 136 8
cert_cellTest_block_4 512 17 136 144 8
cert_cellTest_block_4 512 18 144 152 8
cert_cellTest_block_4 512 19 152 160 8
cert_cellTest_block_4 512 20 160 168 8
cert_cellTest_block_4 512 21 168 176 8
cert_cellTest_block_4 512 22 176 184 8
cert_cellTest_block_4 512 23 184 192 8
cert_cellTest_block_4 512 24 192 200 8
cert_cellTest_block_4 512 25 200 208 8
cert_cellTest_block_4 512 26 208 216 8
cert_cellTest_block_4 512 27 216 224 8
cert_cellTest_block_4 512 28 224 232 8
cert_cellTest_block_4 512 29 232 240 8
cert_cellTest_block_4 512 30 240 246 6
theorem cellTest_512_complete : Interval cellTest_512 0 246 :=
  (interval_append cellTest_512 0 120 246
  (interval_append cellTest_512 0 56 120
  (interval_append cellTest_512 0 24 56
  (interval_append cellTest_512 0 8 24
  cellTest_512_block_0
  (interval_append cellTest_512 8 16 24
  cellTest_512_block_1
  cellTest_512_block_2))
  (interval_append cellTest_512 24 40 56
  (interval_append cellTest_512 24 32 40
  cellTest_512_block_3
  cellTest_512_block_4)
  (interval_append cellTest_512 40 48 56
  cellTest_512_block_5
  cellTest_512_block_6)))
  (interval_append cellTest_512 56 88 120
  (interval_append cellTest_512 56 72 88
  (interval_append cellTest_512 56 64 72
  cellTest_512_block_7
  cellTest_512_block_8)
  (interval_append cellTest_512 72 80 88
  cellTest_512_block_9
  cellTest_512_block_10))
  (interval_append cellTest_512 88 104 120
  (interval_append cellTest_512 88 96 104
  cellTest_512_block_11
  cellTest_512_block_12)
  (interval_append cellTest_512 104 112 120
  cellTest_512_block_13
  cellTest_512_block_14))))
  (interval_append cellTest_512 120 184 246
  (interval_append cellTest_512 120 152 184
  (interval_append cellTest_512 120 136 152
  (interval_append cellTest_512 120 128 136
  cellTest_512_block_15
  cellTest_512_block_16)
  (interval_append cellTest_512 136 144 152
  cellTest_512_block_17
  cellTest_512_block_18))
  (interval_append cellTest_512 152 168 184
  (interval_append cellTest_512 152 160 168
  cellTest_512_block_19
  cellTest_512_block_20)
  (interval_append cellTest_512 168 176 184
  cellTest_512_block_21
  cellTest_512_block_22)))
  (interval_append cellTest_512 184 216 246
  (interval_append cellTest_512 184 200 216
  (interval_append cellTest_512 184 192 200
  cellTest_512_block_23
  cellTest_512_block_24)
  (interval_append cellTest_512 200 208 216
  cellTest_512_block_25
  cellTest_512_block_26))
  (interval_append cellTest_512 216 232 246
  (interval_append cellTest_512 216 224 232
  cellTest_512_block_27
  cellTest_512_block_28)
  (interval_append cellTest_512 232 240 246
  cellTest_512_block_29
  cellTest_512_block_30)))))
cert_cellTestInterval_3 512 758
end Papers.RationalityTen.RootedCaches.RootedSevenPure008
