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
def cellTest_2048 (i : Nat) := cellTest (i+2048)
cert_cellTest_block_6 2048 0 0 8 8
cert_cellTest_block_6 2048 1 8 16 8
cert_cellTest_block_6 2048 2 16 24 8
cert_cellTest_block_6 2048 3 24 32 8
cert_cellTest_block_6 2048 4 32 40 8
cert_cellTest_block_6 2048 5 40 48 8
cert_cellTest_block_6 2048 6 48 56 8
cert_cellTest_block_6 2048 7 56 64 8
cert_cellTest_block_6 2048 8 64 72 8
cert_cellTest_block_6 2048 9 72 80 8
cert_cellTest_block_6 2048 10 80 88 8
cert_cellTest_block_6 2048 11 88 96 8
cert_cellTest_block_6 2048 12 96 104 8
cert_cellTest_block_6 2048 13 104 112 8
cert_cellTest_block_6 2048 14 112 120 8
cert_cellTest_block_6 2048 15 120 128 8
cert_cellTest_block_6 2048 16 128 136 8
cert_cellTest_block_6 2048 17 136 144 8
cert_cellTest_block_6 2048 18 144 152 8
cert_cellTest_block_6 2048 19 152 160 8
cert_cellTest_block_6 2048 20 160 168 8
cert_cellTest_block_6 2048 21 168 176 8
cert_cellTest_block_6 2048 22 176 184 8
cert_cellTest_block_6 2048 23 184 192 8
cert_cellTest_block_6 2048 24 192 200 8
cert_cellTest_block_6 2048 25 200 208 8
cert_cellTest_block_6 2048 26 208 216 8
cert_cellTest_block_6 2048 27 216 224 8
cert_cellTest_block_6 2048 28 224 232 8
cert_cellTest_block_6 2048 29 232 240 8
cert_cellTest_block_6 2048 30 240 248 8
cert_cellTest_block_6 2048 31 248 252 4
theorem cellTest_2048_complete : Interval cellTest_2048 0 252 :=
  (interval_append cellTest_2048 0 128 252
  (interval_append cellTest_2048 0 64 128
  (interval_append cellTest_2048 0 32 64
  (interval_append cellTest_2048 0 16 32
  (interval_append cellTest_2048 0 8 16
  cellTest_2048_block_0
  cellTest_2048_block_1)
  (interval_append cellTest_2048 16 24 32
  cellTest_2048_block_2
  cellTest_2048_block_3))
  (interval_append cellTest_2048 32 48 64
  (interval_append cellTest_2048 32 40 48
  cellTest_2048_block_4
  cellTest_2048_block_5)
  (interval_append cellTest_2048 48 56 64
  cellTest_2048_block_6
  cellTest_2048_block_7)))
  (interval_append cellTest_2048 64 96 128
  (interval_append cellTest_2048 64 80 96
  (interval_append cellTest_2048 64 72 80
  cellTest_2048_block_8
  cellTest_2048_block_9)
  (interval_append cellTest_2048 80 88 96
  cellTest_2048_block_10
  cellTest_2048_block_11))
  (interval_append cellTest_2048 96 112 128
  (interval_append cellTest_2048 96 104 112
  cellTest_2048_block_12
  cellTest_2048_block_13)
  (interval_append cellTest_2048 112 120 128
  cellTest_2048_block_14
  cellTest_2048_block_15))))
  (interval_append cellTest_2048 128 192 252
  (interval_append cellTest_2048 128 160 192
  (interval_append cellTest_2048 128 144 160
  (interval_append cellTest_2048 128 136 144
  cellTest_2048_block_16
  cellTest_2048_block_17)
  (interval_append cellTest_2048 144 152 160
  cellTest_2048_block_18
  cellTest_2048_block_19))
  (interval_append cellTest_2048 160 176 192
  (interval_append cellTest_2048 160 168 176
  cellTest_2048_block_20
  cellTest_2048_block_21)
  (interval_append cellTest_2048 176 184 192
  cellTest_2048_block_22
  cellTest_2048_block_23)))
  (interval_append cellTest_2048 192 224 252
  (interval_append cellTest_2048 192 208 224
  (interval_append cellTest_2048 192 200 208
  cellTest_2048_block_24
  cellTest_2048_block_25)
  (interval_append cellTest_2048 208 216 224
  cellTest_2048_block_26
  cellTest_2048_block_27))
  (interval_append cellTest_2048 224 240 252
  (interval_append cellTest_2048 224 232 240
  cellTest_2048_block_28
  cellTest_2048_block_29)
  (interval_append cellTest_2048 240 248 252
  cellTest_2048_block_30
  cellTest_2048_block_31)))))
theorem cellTestInterval2048 : Interval cellTest 2048 2300 := by
  intro i hlo hhi
  have h := cellTest_2048_complete (i-2048) (Nat.zero_le _) (by omega)
  simpa only [cellTest_2048, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
