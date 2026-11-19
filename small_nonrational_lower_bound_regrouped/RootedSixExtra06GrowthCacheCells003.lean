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
def cellTest_768 (i : Nat) := cellTest (i+768)
cert_cellTest_block_6 768 0 0 8 8
cert_cellTest_block_6 768 1 8 16 8
cert_cellTest_block_6 768 2 16 24 8
cert_cellTest_block_6 768 3 24 32 8
cert_cellTest_block_6 768 4 32 40 8
cert_cellTest_block_6 768 5 40 48 8
cert_cellTest_block_6 768 6 48 56 8
cert_cellTest_block_6 768 7 56 64 8
cert_cellTest_block_6 768 8 64 72 8
cert_cellTest_block_6 768 9 72 80 8
cert_cellTest_block_6 768 10 80 88 8
cert_cellTest_block_6 768 11 88 96 8
cert_cellTest_block_6 768 12 96 104 8
cert_cellTest_block_6 768 13 104 112 8
cert_cellTest_block_6 768 14 112 120 8
cert_cellTest_block_6 768 15 120 128 8
cert_cellTest_block_6 768 16 128 136 8
cert_cellTest_block_6 768 17 136 144 8
cert_cellTest_block_6 768 18 144 152 8
cert_cellTest_block_6 768 19 152 160 8
cert_cellTest_block_6 768 20 160 168 8
cert_cellTest_block_6 768 21 168 176 8
cert_cellTest_block_6 768 22 176 184 8
cert_cellTest_block_6 768 23 184 192 8
cert_cellTest_block_6 768 24 192 200 8
cert_cellTest_block_6 768 25 200 208 8
cert_cellTest_block_6 768 26 208 216 8
cert_cellTest_block_6 768 27 216 224 8
cert_cellTest_block_6 768 28 224 232 8
cert_cellTest_block_6 768 29 232 240 8
cert_cellTest_block_6 768 30 240 248 8
cert_cellTest_block_6 768 31 248 256 8
theorem cellTest_768_complete : Interval cellTest_768 0 256 :=
  (interval_append cellTest_768 0 128 256
  (interval_append cellTest_768 0 64 128
  (interval_append cellTest_768 0 32 64
  (interval_append cellTest_768 0 16 32
  (interval_append cellTest_768 0 8 16
  cellTest_768_block_0
  cellTest_768_block_1)
  (interval_append cellTest_768 16 24 32
  cellTest_768_block_2
  cellTest_768_block_3))
  (interval_append cellTest_768 32 48 64
  (interval_append cellTest_768 32 40 48
  cellTest_768_block_4
  cellTest_768_block_5)
  (interval_append cellTest_768 48 56 64
  cellTest_768_block_6
  cellTest_768_block_7)))
  (interval_append cellTest_768 64 96 128
  (interval_append cellTest_768 64 80 96
  (interval_append cellTest_768 64 72 80
  cellTest_768_block_8
  cellTest_768_block_9)
  (interval_append cellTest_768 80 88 96
  cellTest_768_block_10
  cellTest_768_block_11))
  (interval_append cellTest_768 96 112 128
  (interval_append cellTest_768 96 104 112
  cellTest_768_block_12
  cellTest_768_block_13)
  (interval_append cellTest_768 112 120 128
  cellTest_768_block_14
  cellTest_768_block_15))))
  (interval_append cellTest_768 128 192 256
  (interval_append cellTest_768 128 160 192
  (interval_append cellTest_768 128 144 160
  (interval_append cellTest_768 128 136 144
  cellTest_768_block_16
  cellTest_768_block_17)
  (interval_append cellTest_768 144 152 160
  cellTest_768_block_18
  cellTest_768_block_19))
  (interval_append cellTest_768 160 176 192
  (interval_append cellTest_768 160 168 176
  cellTest_768_block_20
  cellTest_768_block_21)
  (interval_append cellTest_768 176 184 192
  cellTest_768_block_22
  cellTest_768_block_23)))
  (interval_append cellTest_768 192 224 256
  (interval_append cellTest_768 192 208 224
  (interval_append cellTest_768 192 200 208
  cellTest_768_block_24
  cellTest_768_block_25)
  (interval_append cellTest_768 208 216 224
  cellTest_768_block_26
  cellTest_768_block_27))
  (interval_append cellTest_768 224 240 256
  (interval_append cellTest_768 224 232 240
  cellTest_768_block_28
  cellTest_768_block_29)
  (interval_append cellTest_768 240 248 256
  cellTest_768_block_30
  cellTest_768_block_31)))))
theorem cellTestInterval768 : Interval cellTest 768 1024 := by
  intro i hlo hhi
  have h := cellTest_768_complete (i-768) (Nat.zero_le _) (by omega)
  simpa only [cellTest_768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
