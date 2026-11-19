module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra06GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_1280 (i : Nat) := cellTest (i+1280)
cert_cellTest_block_6 1280 0 0 8 8
cert_cellTest_block_6 1280 1 8 16 8
cert_cellTest_block_6 1280 2 16 24 8
cert_cellTest_block_6 1280 3 24 32 8
cert_cellTest_block_6 1280 4 32 40 8
cert_cellTest_block_6 1280 5 40 48 8
cert_cellTest_block_6 1280 6 48 56 8
cert_cellTest_block_6 1280 7 56 64 8
cert_cellTest_block_6 1280 8 64 72 8
cert_cellTest_block_6 1280 9 72 80 8
cert_cellTest_block_6 1280 10 80 88 8
cert_cellTest_block_6 1280 11 88 96 8
cert_cellTest_block_6 1280 12 96 104 8
cert_cellTest_block_6 1280 13 104 112 8
cert_cellTest_block_6 1280 14 112 120 8
cert_cellTest_block_6 1280 15 120 128 8
cert_cellTest_block_6 1280 16 128 136 8
cert_cellTest_block_6 1280 17 136 144 8
cert_cellTest_block_6 1280 18 144 152 8
cert_cellTest_block_6 1280 19 152 160 8
cert_cellTest_block_6 1280 20 160 168 8
cert_cellTest_block_6 1280 21 168 176 8
cert_cellTest_block_6 1280 22 176 184 8
cert_cellTest_block_6 1280 23 184 192 8
cert_cellTest_block_6 1280 24 192 200 8
cert_cellTest_block_6 1280 25 200 208 8
cert_cellTest_block_6 1280 26 208 216 8
cert_cellTest_block_6 1280 27 216 224 8
cert_cellTest_block_6 1280 28 224 232 8
cert_cellTest_block_6 1280 29 232 240 8
cert_cellTest_block_6 1280 30 240 248 8
cert_cellTest_block_6 1280 31 248 256 8
theorem cellTest_1280_complete : Interval cellTest_1280 0 256 :=
  (interval_append cellTest_1280 0 128 256
  (interval_append cellTest_1280 0 64 128
  (interval_append cellTest_1280 0 32 64
  (interval_append cellTest_1280 0 16 32
  (interval_append cellTest_1280 0 8 16
  cellTest_1280_block_0
  cellTest_1280_block_1)
  (interval_append cellTest_1280 16 24 32
  cellTest_1280_block_2
  cellTest_1280_block_3))
  (interval_append cellTest_1280 32 48 64
  (interval_append cellTest_1280 32 40 48
  cellTest_1280_block_4
  cellTest_1280_block_5)
  (interval_append cellTest_1280 48 56 64
  cellTest_1280_block_6
  cellTest_1280_block_7)))
  (interval_append cellTest_1280 64 96 128
  (interval_append cellTest_1280 64 80 96
  (interval_append cellTest_1280 64 72 80
  cellTest_1280_block_8
  cellTest_1280_block_9)
  (interval_append cellTest_1280 80 88 96
  cellTest_1280_block_10
  cellTest_1280_block_11))
  (interval_append cellTest_1280 96 112 128
  (interval_append cellTest_1280 96 104 112
  cellTest_1280_block_12
  cellTest_1280_block_13)
  (interval_append cellTest_1280 112 120 128
  cellTest_1280_block_14
  cellTest_1280_block_15))))
  (interval_append cellTest_1280 128 192 256
  (interval_append cellTest_1280 128 160 192
  (interval_append cellTest_1280 128 144 160
  (interval_append cellTest_1280 128 136 144
  cellTest_1280_block_16
  cellTest_1280_block_17)
  (interval_append cellTest_1280 144 152 160
  cellTest_1280_block_18
  cellTest_1280_block_19))
  (interval_append cellTest_1280 160 176 192
  (interval_append cellTest_1280 160 168 176
  cellTest_1280_block_20
  cellTest_1280_block_21)
  (interval_append cellTest_1280 176 184 192
  cellTest_1280_block_22
  cellTest_1280_block_23)))
  (interval_append cellTest_1280 192 224 256
  (interval_append cellTest_1280 192 208 224
  (interval_append cellTest_1280 192 200 208
  cellTest_1280_block_24
  cellTest_1280_block_25)
  (interval_append cellTest_1280 208 216 224
  cellTest_1280_block_26
  cellTest_1280_block_27))
  (interval_append cellTest_1280 224 240 256
  (interval_append cellTest_1280 224 232 240
  cellTest_1280_block_28
  cellTest_1280_block_29)
  (interval_append cellTest_1280 240 248 256
  cellTest_1280_block_30
  cellTest_1280_block_31)))))
theorem cellTestInterval1280 : Interval cellTest 1280 1536 := by
  intro i hlo hhi
  have h := cellTest_1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [cellTest_1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
