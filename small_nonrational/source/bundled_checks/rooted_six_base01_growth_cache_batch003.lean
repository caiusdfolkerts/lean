module
prelude
public import RootedSixBase01GrowthCacheData

/- RootedSixBase01GrowthCacheCells048 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_12288 (i : Nat) := cellTest (i+12288)
theorem cellTest_12288_block_0 : Interval cellTest_12288 0 8 :=
  interval_of_check cellTest_12288 0 8 (by decide +kernel)

theorem cellTest_12288_block_1 : Interval cellTest_12288 8 16 :=
  interval_of_check cellTest_12288 8 8 (by decide +kernel)

theorem cellTest_12288_block_2 : Interval cellTest_12288 16 24 :=
  interval_of_check cellTest_12288 16 8 (by decide +kernel)

theorem cellTest_12288_block_3 : Interval cellTest_12288 24 32 :=
  interval_of_check cellTest_12288 24 8 (by decide +kernel)

theorem cellTest_12288_block_4 : Interval cellTest_12288 32 40 :=
  interval_of_check cellTest_12288 32 8 (by decide +kernel)

theorem cellTest_12288_block_5 : Interval cellTest_12288 40 48 :=
  interval_of_check cellTest_12288 40 8 (by decide +kernel)

theorem cellTest_12288_block_6 : Interval cellTest_12288 48 56 :=
  interval_of_check cellTest_12288 48 8 (by decide +kernel)

theorem cellTest_12288_block_7 : Interval cellTest_12288 56 64 :=
  interval_of_check cellTest_12288 56 8 (by decide +kernel)

theorem cellTest_12288_block_8 : Interval cellTest_12288 64 72 :=
  interval_of_check cellTest_12288 64 8 (by decide +kernel)

theorem cellTest_12288_block_9 : Interval cellTest_12288 72 80 :=
  interval_of_check cellTest_12288 72 8 (by decide +kernel)

theorem cellTest_12288_block_10 : Interval cellTest_12288 80 88 :=
  interval_of_check cellTest_12288 80 8 (by decide +kernel)

theorem cellTest_12288_block_11 : Interval cellTest_12288 88 96 :=
  interval_of_check cellTest_12288 88 8 (by decide +kernel)

theorem cellTest_12288_block_12 : Interval cellTest_12288 96 104 :=
  interval_of_check cellTest_12288 96 8 (by decide +kernel)

theorem cellTest_12288_block_13 : Interval cellTest_12288 104 112 :=
  interval_of_check cellTest_12288 104 8 (by decide +kernel)

theorem cellTest_12288_block_14 : Interval cellTest_12288 112 120 :=
  interval_of_check cellTest_12288 112 8 (by decide +kernel)

theorem cellTest_12288_block_15 : Interval cellTest_12288 120 128 :=
  interval_of_check cellTest_12288 120 8 (by decide +kernel)

theorem cellTest_12288_block_16 : Interval cellTest_12288 128 136 :=
  interval_of_check cellTest_12288 128 8 (by decide +kernel)

theorem cellTest_12288_block_17 : Interval cellTest_12288 136 144 :=
  interval_of_check cellTest_12288 136 8 (by decide +kernel)

theorem cellTest_12288_block_18 : Interval cellTest_12288 144 152 :=
  interval_of_check cellTest_12288 144 8 (by decide +kernel)

theorem cellTest_12288_block_19 : Interval cellTest_12288 152 160 :=
  interval_of_check cellTest_12288 152 8 (by decide +kernel)

theorem cellTest_12288_block_20 : Interval cellTest_12288 160 168 :=
  interval_of_check cellTest_12288 160 8 (by decide +kernel)

theorem cellTest_12288_block_21 : Interval cellTest_12288 168 176 :=
  interval_of_check cellTest_12288 168 8 (by decide +kernel)

theorem cellTest_12288_block_22 : Interval cellTest_12288 176 184 :=
  interval_of_check cellTest_12288 176 8 (by decide +kernel)

theorem cellTest_12288_block_23 : Interval cellTest_12288 184 192 :=
  interval_of_check cellTest_12288 184 8 (by decide +kernel)

theorem cellTest_12288_block_24 : Interval cellTest_12288 192 200 :=
  interval_of_check cellTest_12288 192 8 (by decide +kernel)

theorem cellTest_12288_block_25 : Interval cellTest_12288 200 208 :=
  interval_of_check cellTest_12288 200 8 (by decide +kernel)

theorem cellTest_12288_block_26 : Interval cellTest_12288 208 216 :=
  interval_of_check cellTest_12288 208 8 (by decide +kernel)

theorem cellTest_12288_block_27 : Interval cellTest_12288 216 224 :=
  interval_of_check cellTest_12288 216 8 (by decide +kernel)

theorem cellTest_12288_block_28 : Interval cellTest_12288 224 232 :=
  interval_of_check cellTest_12288 224 8 (by decide +kernel)

theorem cellTest_12288_block_29 : Interval cellTest_12288 232 240 :=
  interval_of_check cellTest_12288 232 8 (by decide +kernel)

theorem cellTest_12288_block_30 : Interval cellTest_12288 240 248 :=
  interval_of_check cellTest_12288 240 8 (by decide +kernel)

theorem cellTest_12288_block_31 : Interval cellTest_12288 248 256 :=
  interval_of_check cellTest_12288 248 8 (by decide +kernel)

theorem cellTest_12288_complete : Interval cellTest_12288 0 256 :=
  (interval_append cellTest_12288 0 128 256
  (interval_append cellTest_12288 0 64 128
  (interval_append cellTest_12288 0 32 64
  (interval_append cellTest_12288 0 16 32
  (interval_append cellTest_12288 0 8 16
  cellTest_12288_block_0
  cellTest_12288_block_1)
  (interval_append cellTest_12288 16 24 32
  cellTest_12288_block_2
  cellTest_12288_block_3))
  (interval_append cellTest_12288 32 48 64
  (interval_append cellTest_12288 32 40 48
  cellTest_12288_block_4
  cellTest_12288_block_5)
  (interval_append cellTest_12288 48 56 64
  cellTest_12288_block_6
  cellTest_12288_block_7)))
  (interval_append cellTest_12288 64 96 128
  (interval_append cellTest_12288 64 80 96
  (interval_append cellTest_12288 64 72 80
  cellTest_12288_block_8
  cellTest_12288_block_9)
  (interval_append cellTest_12288 80 88 96
  cellTest_12288_block_10
  cellTest_12288_block_11))
  (interval_append cellTest_12288 96 112 128
  (interval_append cellTest_12288 96 104 112
  cellTest_12288_block_12
  cellTest_12288_block_13)
  (interval_append cellTest_12288 112 120 128
  cellTest_12288_block_14
  cellTest_12288_block_15))))
  (interval_append cellTest_12288 128 192 256
  (interval_append cellTest_12288 128 160 192
  (interval_append cellTest_12288 128 144 160
  (interval_append cellTest_12288 128 136 144
  cellTest_12288_block_16
  cellTest_12288_block_17)
  (interval_append cellTest_12288 144 152 160
  cellTest_12288_block_18
  cellTest_12288_block_19))
  (interval_append cellTest_12288 160 176 192
  (interval_append cellTest_12288 160 168 176
  cellTest_12288_block_20
  cellTest_12288_block_21)
  (interval_append cellTest_12288 176 184 192
  cellTest_12288_block_22
  cellTest_12288_block_23)))
  (interval_append cellTest_12288 192 224 256
  (interval_append cellTest_12288 192 208 224
  (interval_append cellTest_12288 192 200 208
  cellTest_12288_block_24
  cellTest_12288_block_25)
  (interval_append cellTest_12288 208 216 224
  cellTest_12288_block_26
  cellTest_12288_block_27))
  (interval_append cellTest_12288 224 240 256
  (interval_append cellTest_12288 224 232 240
  cellTest_12288_block_28
  cellTest_12288_block_29)
  (interval_append cellTest_12288 240 248 256
  cellTest_12288_block_30
  cellTest_12288_block_31)))))
theorem cellTestInterval12288 : Interval cellTest 12288 12544 := by
  intro i hlo hhi
  have h := cellTest_12288_complete (i-12288) (Nat.zero_le _) (by omega)
  simpa only [cellTest_12288, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells049 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_12544 (i : Nat) := cellTest (i+12544)
theorem cellTest_12544_block_0 : Interval cellTest_12544 0 8 :=
  interval_of_check cellTest_12544 0 8 (by decide +kernel)

theorem cellTest_12544_block_1 : Interval cellTest_12544 8 16 :=
  interval_of_check cellTest_12544 8 8 (by decide +kernel)

theorem cellTest_12544_block_2 : Interval cellTest_12544 16 24 :=
  interval_of_check cellTest_12544 16 8 (by decide +kernel)

theorem cellTest_12544_block_3 : Interval cellTest_12544 24 32 :=
  interval_of_check cellTest_12544 24 8 (by decide +kernel)

theorem cellTest_12544_block_4 : Interval cellTest_12544 32 40 :=
  interval_of_check cellTest_12544 32 8 (by decide +kernel)

theorem cellTest_12544_block_5 : Interval cellTest_12544 40 48 :=
  interval_of_check cellTest_12544 40 8 (by decide +kernel)

theorem cellTest_12544_block_6 : Interval cellTest_12544 48 56 :=
  interval_of_check cellTest_12544 48 8 (by decide +kernel)

theorem cellTest_12544_block_7 : Interval cellTest_12544 56 64 :=
  interval_of_check cellTest_12544 56 8 (by decide +kernel)

theorem cellTest_12544_block_8 : Interval cellTest_12544 64 72 :=
  interval_of_check cellTest_12544 64 8 (by decide +kernel)

theorem cellTest_12544_block_9 : Interval cellTest_12544 72 80 :=
  interval_of_check cellTest_12544 72 8 (by decide +kernel)

theorem cellTest_12544_block_10 : Interval cellTest_12544 80 88 :=
  interval_of_check cellTest_12544 80 8 (by decide +kernel)

theorem cellTest_12544_block_11 : Interval cellTest_12544 88 96 :=
  interval_of_check cellTest_12544 88 8 (by decide +kernel)

theorem cellTest_12544_block_12 : Interval cellTest_12544 96 104 :=
  interval_of_check cellTest_12544 96 8 (by decide +kernel)

theorem cellTest_12544_block_13 : Interval cellTest_12544 104 112 :=
  interval_of_check cellTest_12544 104 8 (by decide +kernel)

theorem cellTest_12544_block_14 : Interval cellTest_12544 112 120 :=
  interval_of_check cellTest_12544 112 8 (by decide +kernel)

theorem cellTest_12544_block_15 : Interval cellTest_12544 120 128 :=
  interval_of_check cellTest_12544 120 8 (by decide +kernel)

theorem cellTest_12544_block_16 : Interval cellTest_12544 128 136 :=
  interval_of_check cellTest_12544 128 8 (by decide +kernel)

theorem cellTest_12544_block_17 : Interval cellTest_12544 136 144 :=
  interval_of_check cellTest_12544 136 8 (by decide +kernel)

theorem cellTest_12544_block_18 : Interval cellTest_12544 144 152 :=
  interval_of_check cellTest_12544 144 8 (by decide +kernel)

theorem cellTest_12544_block_19 : Interval cellTest_12544 152 160 :=
  interval_of_check cellTest_12544 152 8 (by decide +kernel)

theorem cellTest_12544_block_20 : Interval cellTest_12544 160 168 :=
  interval_of_check cellTest_12544 160 8 (by decide +kernel)

theorem cellTest_12544_block_21 : Interval cellTest_12544 168 176 :=
  interval_of_check cellTest_12544 168 8 (by decide +kernel)

theorem cellTest_12544_block_22 : Interval cellTest_12544 176 184 :=
  interval_of_check cellTest_12544 176 8 (by decide +kernel)

theorem cellTest_12544_block_23 : Interval cellTest_12544 184 192 :=
  interval_of_check cellTest_12544 184 8 (by decide +kernel)

theorem cellTest_12544_block_24 : Interval cellTest_12544 192 200 :=
  interval_of_check cellTest_12544 192 8 (by decide +kernel)

theorem cellTest_12544_block_25 : Interval cellTest_12544 200 208 :=
  interval_of_check cellTest_12544 200 8 (by decide +kernel)

theorem cellTest_12544_block_26 : Interval cellTest_12544 208 216 :=
  interval_of_check cellTest_12544 208 8 (by decide +kernel)

theorem cellTest_12544_block_27 : Interval cellTest_12544 216 224 :=
  interval_of_check cellTest_12544 216 8 (by decide +kernel)

theorem cellTest_12544_block_28 : Interval cellTest_12544 224 232 :=
  interval_of_check cellTest_12544 224 8 (by decide +kernel)

theorem cellTest_12544_block_29 : Interval cellTest_12544 232 240 :=
  interval_of_check cellTest_12544 232 8 (by decide +kernel)

theorem cellTest_12544_block_30 : Interval cellTest_12544 240 248 :=
  interval_of_check cellTest_12544 240 8 (by decide +kernel)

theorem cellTest_12544_block_31 : Interval cellTest_12544 248 256 :=
  interval_of_check cellTest_12544 248 8 (by decide +kernel)

theorem cellTest_12544_complete : Interval cellTest_12544 0 256 :=
  (interval_append cellTest_12544 0 128 256
  (interval_append cellTest_12544 0 64 128
  (interval_append cellTest_12544 0 32 64
  (interval_append cellTest_12544 0 16 32
  (interval_append cellTest_12544 0 8 16
  cellTest_12544_block_0
  cellTest_12544_block_1)
  (interval_append cellTest_12544 16 24 32
  cellTest_12544_block_2
  cellTest_12544_block_3))
  (interval_append cellTest_12544 32 48 64
  (interval_append cellTest_12544 32 40 48
  cellTest_12544_block_4
  cellTest_12544_block_5)
  (interval_append cellTest_12544 48 56 64
  cellTest_12544_block_6
  cellTest_12544_block_7)))
  (interval_append cellTest_12544 64 96 128
  (interval_append cellTest_12544 64 80 96
  (interval_append cellTest_12544 64 72 80
  cellTest_12544_block_8
  cellTest_12544_block_9)
  (interval_append cellTest_12544 80 88 96
  cellTest_12544_block_10
  cellTest_12544_block_11))
  (interval_append cellTest_12544 96 112 128
  (interval_append cellTest_12544 96 104 112
  cellTest_12544_block_12
  cellTest_12544_block_13)
  (interval_append cellTest_12544 112 120 128
  cellTest_12544_block_14
  cellTest_12544_block_15))))
  (interval_append cellTest_12544 128 192 256
  (interval_append cellTest_12544 128 160 192
  (interval_append cellTest_12544 128 144 160
  (interval_append cellTest_12544 128 136 144
  cellTest_12544_block_16
  cellTest_12544_block_17)
  (interval_append cellTest_12544 144 152 160
  cellTest_12544_block_18
  cellTest_12544_block_19))
  (interval_append cellTest_12544 160 176 192
  (interval_append cellTest_12544 160 168 176
  cellTest_12544_block_20
  cellTest_12544_block_21)
  (interval_append cellTest_12544 176 184 192
  cellTest_12544_block_22
  cellTest_12544_block_23)))
  (interval_append cellTest_12544 192 224 256
  (interval_append cellTest_12544 192 208 224
  (interval_append cellTest_12544 192 200 208
  cellTest_12544_block_24
  cellTest_12544_block_25)
  (interval_append cellTest_12544 208 216 224
  cellTest_12544_block_26
  cellTest_12544_block_27))
  (interval_append cellTest_12544 224 240 256
  (interval_append cellTest_12544 224 232 240
  cellTest_12544_block_28
  cellTest_12544_block_29)
  (interval_append cellTest_12544 240 248 256
  cellTest_12544_block_30
  cellTest_12544_block_31)))))
theorem cellTestInterval12544 : Interval cellTest 12544 12800 := by
  intro i hlo hhi
  have h := cellTest_12544_complete (i-12544) (Nat.zero_le _) (by omega)
  simpa only [cellTest_12544, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells050 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_12800 (i : Nat) := cellTest (i+12800)
theorem cellTest_12800_block_0 : Interval cellTest_12800 0 8 :=
  interval_of_check cellTest_12800 0 8 (by decide +kernel)

theorem cellTest_12800_block_1 : Interval cellTest_12800 8 16 :=
  interval_of_check cellTest_12800 8 8 (by decide +kernel)

theorem cellTest_12800_block_2 : Interval cellTest_12800 16 24 :=
  interval_of_check cellTest_12800 16 8 (by decide +kernel)

theorem cellTest_12800_block_3 : Interval cellTest_12800 24 32 :=
  interval_of_check cellTest_12800 24 8 (by decide +kernel)

theorem cellTest_12800_block_4 : Interval cellTest_12800 32 40 :=
  interval_of_check cellTest_12800 32 8 (by decide +kernel)

theorem cellTest_12800_block_5 : Interval cellTest_12800 40 48 :=
  interval_of_check cellTest_12800 40 8 (by decide +kernel)

theorem cellTest_12800_block_6 : Interval cellTest_12800 48 56 :=
  interval_of_check cellTest_12800 48 8 (by decide +kernel)

theorem cellTest_12800_block_7 : Interval cellTest_12800 56 64 :=
  interval_of_check cellTest_12800 56 8 (by decide +kernel)

theorem cellTest_12800_block_8 : Interval cellTest_12800 64 72 :=
  interval_of_check cellTest_12800 64 8 (by decide +kernel)

theorem cellTest_12800_block_9 : Interval cellTest_12800 72 80 :=
  interval_of_check cellTest_12800 72 8 (by decide +kernel)

theorem cellTest_12800_block_10 : Interval cellTest_12800 80 88 :=
  interval_of_check cellTest_12800 80 8 (by decide +kernel)

theorem cellTest_12800_block_11 : Interval cellTest_12800 88 96 :=
  interval_of_check cellTest_12800 88 8 (by decide +kernel)

theorem cellTest_12800_block_12 : Interval cellTest_12800 96 104 :=
  interval_of_check cellTest_12800 96 8 (by decide +kernel)

theorem cellTest_12800_block_13 : Interval cellTest_12800 104 112 :=
  interval_of_check cellTest_12800 104 8 (by decide +kernel)

theorem cellTest_12800_block_14 : Interval cellTest_12800 112 120 :=
  interval_of_check cellTest_12800 112 8 (by decide +kernel)

theorem cellTest_12800_block_15 : Interval cellTest_12800 120 128 :=
  interval_of_check cellTest_12800 120 8 (by decide +kernel)

theorem cellTest_12800_block_16 : Interval cellTest_12800 128 136 :=
  interval_of_check cellTest_12800 128 8 (by decide +kernel)

theorem cellTest_12800_block_17 : Interval cellTest_12800 136 144 :=
  interval_of_check cellTest_12800 136 8 (by decide +kernel)

theorem cellTest_12800_block_18 : Interval cellTest_12800 144 152 :=
  interval_of_check cellTest_12800 144 8 (by decide +kernel)

theorem cellTest_12800_block_19 : Interval cellTest_12800 152 160 :=
  interval_of_check cellTest_12800 152 8 (by decide +kernel)

theorem cellTest_12800_block_20 : Interval cellTest_12800 160 168 :=
  interval_of_check cellTest_12800 160 8 (by decide +kernel)

theorem cellTest_12800_block_21 : Interval cellTest_12800 168 176 :=
  interval_of_check cellTest_12800 168 8 (by decide +kernel)

theorem cellTest_12800_block_22 : Interval cellTest_12800 176 184 :=
  interval_of_check cellTest_12800 176 8 (by decide +kernel)

theorem cellTest_12800_block_23 : Interval cellTest_12800 184 192 :=
  interval_of_check cellTest_12800 184 8 (by decide +kernel)

theorem cellTest_12800_block_24 : Interval cellTest_12800 192 200 :=
  interval_of_check cellTest_12800 192 8 (by decide +kernel)

theorem cellTest_12800_block_25 : Interval cellTest_12800 200 208 :=
  interval_of_check cellTest_12800 200 8 (by decide +kernel)

theorem cellTest_12800_block_26 : Interval cellTest_12800 208 216 :=
  interval_of_check cellTest_12800 208 8 (by decide +kernel)

theorem cellTest_12800_block_27 : Interval cellTest_12800 216 224 :=
  interval_of_check cellTest_12800 216 8 (by decide +kernel)

theorem cellTest_12800_block_28 : Interval cellTest_12800 224 232 :=
  interval_of_check cellTest_12800 224 8 (by decide +kernel)

theorem cellTest_12800_block_29 : Interval cellTest_12800 232 240 :=
  interval_of_check cellTest_12800 232 8 (by decide +kernel)

theorem cellTest_12800_block_30 : Interval cellTest_12800 240 248 :=
  interval_of_check cellTest_12800 240 8 (by decide +kernel)

theorem cellTest_12800_block_31 : Interval cellTest_12800 248 256 :=
  interval_of_check cellTest_12800 248 8 (by decide +kernel)

theorem cellTest_12800_complete : Interval cellTest_12800 0 256 :=
  (interval_append cellTest_12800 0 128 256
  (interval_append cellTest_12800 0 64 128
  (interval_append cellTest_12800 0 32 64
  (interval_append cellTest_12800 0 16 32
  (interval_append cellTest_12800 0 8 16
  cellTest_12800_block_0
  cellTest_12800_block_1)
  (interval_append cellTest_12800 16 24 32
  cellTest_12800_block_2
  cellTest_12800_block_3))
  (interval_append cellTest_12800 32 48 64
  (interval_append cellTest_12800 32 40 48
  cellTest_12800_block_4
  cellTest_12800_block_5)
  (interval_append cellTest_12800 48 56 64
  cellTest_12800_block_6
  cellTest_12800_block_7)))
  (interval_append cellTest_12800 64 96 128
  (interval_append cellTest_12800 64 80 96
  (interval_append cellTest_12800 64 72 80
  cellTest_12800_block_8
  cellTest_12800_block_9)
  (interval_append cellTest_12800 80 88 96
  cellTest_12800_block_10
  cellTest_12800_block_11))
  (interval_append cellTest_12800 96 112 128
  (interval_append cellTest_12800 96 104 112
  cellTest_12800_block_12
  cellTest_12800_block_13)
  (interval_append cellTest_12800 112 120 128
  cellTest_12800_block_14
  cellTest_12800_block_15))))
  (interval_append cellTest_12800 128 192 256
  (interval_append cellTest_12800 128 160 192
  (interval_append cellTest_12800 128 144 160
  (interval_append cellTest_12800 128 136 144
  cellTest_12800_block_16
  cellTest_12800_block_17)
  (interval_append cellTest_12800 144 152 160
  cellTest_12800_block_18
  cellTest_12800_block_19))
  (interval_append cellTest_12800 160 176 192
  (interval_append cellTest_12800 160 168 176
  cellTest_12800_block_20
  cellTest_12800_block_21)
  (interval_append cellTest_12800 176 184 192
  cellTest_12800_block_22
  cellTest_12800_block_23)))
  (interval_append cellTest_12800 192 224 256
  (interval_append cellTest_12800 192 208 224
  (interval_append cellTest_12800 192 200 208
  cellTest_12800_block_24
  cellTest_12800_block_25)
  (interval_append cellTest_12800 208 216 224
  cellTest_12800_block_26
  cellTest_12800_block_27))
  (interval_append cellTest_12800 224 240 256
  (interval_append cellTest_12800 224 232 240
  cellTest_12800_block_28
  cellTest_12800_block_29)
  (interval_append cellTest_12800 240 248 256
  cellTest_12800_block_30
  cellTest_12800_block_31)))))
theorem cellTestInterval12800 : Interval cellTest 12800 13056 := by
  intro i hlo hhi
  have h := cellTest_12800_complete (i-12800) (Nat.zero_le _) (by omega)
  simpa only [cellTest_12800, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells051 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_13056 (i : Nat) := cellTest (i+13056)
theorem cellTest_13056_block_0 : Interval cellTest_13056 0 8 :=
  interval_of_check cellTest_13056 0 8 (by decide +kernel)

theorem cellTest_13056_block_1 : Interval cellTest_13056 8 16 :=
  interval_of_check cellTest_13056 8 8 (by decide +kernel)

theorem cellTest_13056_block_2 : Interval cellTest_13056 16 24 :=
  interval_of_check cellTest_13056 16 8 (by decide +kernel)

theorem cellTest_13056_block_3 : Interval cellTest_13056 24 32 :=
  interval_of_check cellTest_13056 24 8 (by decide +kernel)

theorem cellTest_13056_block_4 : Interval cellTest_13056 32 40 :=
  interval_of_check cellTest_13056 32 8 (by decide +kernel)

theorem cellTest_13056_block_5 : Interval cellTest_13056 40 48 :=
  interval_of_check cellTest_13056 40 8 (by decide +kernel)

theorem cellTest_13056_block_6 : Interval cellTest_13056 48 56 :=
  interval_of_check cellTest_13056 48 8 (by decide +kernel)

theorem cellTest_13056_block_7 : Interval cellTest_13056 56 64 :=
  interval_of_check cellTest_13056 56 8 (by decide +kernel)

theorem cellTest_13056_block_8 : Interval cellTest_13056 64 72 :=
  interval_of_check cellTest_13056 64 8 (by decide +kernel)

theorem cellTest_13056_block_9 : Interval cellTest_13056 72 80 :=
  interval_of_check cellTest_13056 72 8 (by decide +kernel)

theorem cellTest_13056_block_10 : Interval cellTest_13056 80 88 :=
  interval_of_check cellTest_13056 80 8 (by decide +kernel)

theorem cellTest_13056_block_11 : Interval cellTest_13056 88 96 :=
  interval_of_check cellTest_13056 88 8 (by decide +kernel)

theorem cellTest_13056_block_12 : Interval cellTest_13056 96 104 :=
  interval_of_check cellTest_13056 96 8 (by decide +kernel)

theorem cellTest_13056_block_13 : Interval cellTest_13056 104 112 :=
  interval_of_check cellTest_13056 104 8 (by decide +kernel)

theorem cellTest_13056_block_14 : Interval cellTest_13056 112 120 :=
  interval_of_check cellTest_13056 112 8 (by decide +kernel)

theorem cellTest_13056_block_15 : Interval cellTest_13056 120 128 :=
  interval_of_check cellTest_13056 120 8 (by decide +kernel)

theorem cellTest_13056_block_16 : Interval cellTest_13056 128 136 :=
  interval_of_check cellTest_13056 128 8 (by decide +kernel)

theorem cellTest_13056_block_17 : Interval cellTest_13056 136 144 :=
  interval_of_check cellTest_13056 136 8 (by decide +kernel)

theorem cellTest_13056_block_18 : Interval cellTest_13056 144 152 :=
  interval_of_check cellTest_13056 144 8 (by decide +kernel)

theorem cellTest_13056_block_19 : Interval cellTest_13056 152 160 :=
  interval_of_check cellTest_13056 152 8 (by decide +kernel)

theorem cellTest_13056_block_20 : Interval cellTest_13056 160 168 :=
  interval_of_check cellTest_13056 160 8 (by decide +kernel)

theorem cellTest_13056_block_21 : Interval cellTest_13056 168 176 :=
  interval_of_check cellTest_13056 168 8 (by decide +kernel)

theorem cellTest_13056_block_22 : Interval cellTest_13056 176 184 :=
  interval_of_check cellTest_13056 176 8 (by decide +kernel)

theorem cellTest_13056_block_23 : Interval cellTest_13056 184 192 :=
  interval_of_check cellTest_13056 184 8 (by decide +kernel)

theorem cellTest_13056_block_24 : Interval cellTest_13056 192 200 :=
  interval_of_check cellTest_13056 192 8 (by decide +kernel)

theorem cellTest_13056_block_25 : Interval cellTest_13056 200 208 :=
  interval_of_check cellTest_13056 200 8 (by decide +kernel)

theorem cellTest_13056_block_26 : Interval cellTest_13056 208 216 :=
  interval_of_check cellTest_13056 208 8 (by decide +kernel)

theorem cellTest_13056_block_27 : Interval cellTest_13056 216 224 :=
  interval_of_check cellTest_13056 216 8 (by decide +kernel)

theorem cellTest_13056_block_28 : Interval cellTest_13056 224 232 :=
  interval_of_check cellTest_13056 224 8 (by decide +kernel)

theorem cellTest_13056_block_29 : Interval cellTest_13056 232 240 :=
  interval_of_check cellTest_13056 232 8 (by decide +kernel)

theorem cellTest_13056_block_30 : Interval cellTest_13056 240 248 :=
  interval_of_check cellTest_13056 240 8 (by decide +kernel)

theorem cellTest_13056_block_31 : Interval cellTest_13056 248 256 :=
  interval_of_check cellTest_13056 248 8 (by decide +kernel)

theorem cellTest_13056_complete : Interval cellTest_13056 0 256 :=
  (interval_append cellTest_13056 0 128 256
  (interval_append cellTest_13056 0 64 128
  (interval_append cellTest_13056 0 32 64
  (interval_append cellTest_13056 0 16 32
  (interval_append cellTest_13056 0 8 16
  cellTest_13056_block_0
  cellTest_13056_block_1)
  (interval_append cellTest_13056 16 24 32
  cellTest_13056_block_2
  cellTest_13056_block_3))
  (interval_append cellTest_13056 32 48 64
  (interval_append cellTest_13056 32 40 48
  cellTest_13056_block_4
  cellTest_13056_block_5)
  (interval_append cellTest_13056 48 56 64
  cellTest_13056_block_6
  cellTest_13056_block_7)))
  (interval_append cellTest_13056 64 96 128
  (interval_append cellTest_13056 64 80 96
  (interval_append cellTest_13056 64 72 80
  cellTest_13056_block_8
  cellTest_13056_block_9)
  (interval_append cellTest_13056 80 88 96
  cellTest_13056_block_10
  cellTest_13056_block_11))
  (interval_append cellTest_13056 96 112 128
  (interval_append cellTest_13056 96 104 112
  cellTest_13056_block_12
  cellTest_13056_block_13)
  (interval_append cellTest_13056 112 120 128
  cellTest_13056_block_14
  cellTest_13056_block_15))))
  (interval_append cellTest_13056 128 192 256
  (interval_append cellTest_13056 128 160 192
  (interval_append cellTest_13056 128 144 160
  (interval_append cellTest_13056 128 136 144
  cellTest_13056_block_16
  cellTest_13056_block_17)
  (interval_append cellTest_13056 144 152 160
  cellTest_13056_block_18
  cellTest_13056_block_19))
  (interval_append cellTest_13056 160 176 192
  (interval_append cellTest_13056 160 168 176
  cellTest_13056_block_20
  cellTest_13056_block_21)
  (interval_append cellTest_13056 176 184 192
  cellTest_13056_block_22
  cellTest_13056_block_23)))
  (interval_append cellTest_13056 192 224 256
  (interval_append cellTest_13056 192 208 224
  (interval_append cellTest_13056 192 200 208
  cellTest_13056_block_24
  cellTest_13056_block_25)
  (interval_append cellTest_13056 208 216 224
  cellTest_13056_block_26
  cellTest_13056_block_27))
  (interval_append cellTest_13056 224 240 256
  (interval_append cellTest_13056 224 232 240
  cellTest_13056_block_28
  cellTest_13056_block_29)
  (interval_append cellTest_13056 240 248 256
  cellTest_13056_block_30
  cellTest_13056_block_31)))))
theorem cellTestInterval13056 : Interval cellTest 13056 13312 := by
  intro i hlo hhi
  have h := cellTest_13056_complete (i-13056) (Nat.zero_le _) (by omega)
  simpa only [cellTest_13056, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells052 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_13312 (i : Nat) := cellTest (i+13312)
theorem cellTest_13312_block_0 : Interval cellTest_13312 0 8 :=
  interval_of_check cellTest_13312 0 8 (by decide +kernel)

theorem cellTest_13312_block_1 : Interval cellTest_13312 8 16 :=
  interval_of_check cellTest_13312 8 8 (by decide +kernel)

theorem cellTest_13312_block_2 : Interval cellTest_13312 16 24 :=
  interval_of_check cellTest_13312 16 8 (by decide +kernel)

theorem cellTest_13312_block_3 : Interval cellTest_13312 24 32 :=
  interval_of_check cellTest_13312 24 8 (by decide +kernel)

theorem cellTest_13312_block_4 : Interval cellTest_13312 32 40 :=
  interval_of_check cellTest_13312 32 8 (by decide +kernel)

theorem cellTest_13312_block_5 : Interval cellTest_13312 40 48 :=
  interval_of_check cellTest_13312 40 8 (by decide +kernel)

theorem cellTest_13312_block_6 : Interval cellTest_13312 48 56 :=
  interval_of_check cellTest_13312 48 8 (by decide +kernel)

theorem cellTest_13312_block_7 : Interval cellTest_13312 56 64 :=
  interval_of_check cellTest_13312 56 8 (by decide +kernel)

theorem cellTest_13312_block_8 : Interval cellTest_13312 64 72 :=
  interval_of_check cellTest_13312 64 8 (by decide +kernel)

theorem cellTest_13312_block_9 : Interval cellTest_13312 72 80 :=
  interval_of_check cellTest_13312 72 8 (by decide +kernel)

theorem cellTest_13312_block_10 : Interval cellTest_13312 80 88 :=
  interval_of_check cellTest_13312 80 8 (by decide +kernel)

theorem cellTest_13312_block_11 : Interval cellTest_13312 88 96 :=
  interval_of_check cellTest_13312 88 8 (by decide +kernel)

theorem cellTest_13312_block_12 : Interval cellTest_13312 96 104 :=
  interval_of_check cellTest_13312 96 8 (by decide +kernel)

theorem cellTest_13312_block_13 : Interval cellTest_13312 104 112 :=
  interval_of_check cellTest_13312 104 8 (by decide +kernel)

theorem cellTest_13312_block_14 : Interval cellTest_13312 112 120 :=
  interval_of_check cellTest_13312 112 8 (by decide +kernel)

theorem cellTest_13312_block_15 : Interval cellTest_13312 120 128 :=
  interval_of_check cellTest_13312 120 8 (by decide +kernel)

theorem cellTest_13312_block_16 : Interval cellTest_13312 128 136 :=
  interval_of_check cellTest_13312 128 8 (by decide +kernel)

theorem cellTest_13312_block_17 : Interval cellTest_13312 136 144 :=
  interval_of_check cellTest_13312 136 8 (by decide +kernel)

theorem cellTest_13312_block_18 : Interval cellTest_13312 144 152 :=
  interval_of_check cellTest_13312 144 8 (by decide +kernel)

theorem cellTest_13312_block_19 : Interval cellTest_13312 152 160 :=
  interval_of_check cellTest_13312 152 8 (by decide +kernel)

theorem cellTest_13312_block_20 : Interval cellTest_13312 160 168 :=
  interval_of_check cellTest_13312 160 8 (by decide +kernel)

theorem cellTest_13312_block_21 : Interval cellTest_13312 168 176 :=
  interval_of_check cellTest_13312 168 8 (by decide +kernel)

theorem cellTest_13312_block_22 : Interval cellTest_13312 176 184 :=
  interval_of_check cellTest_13312 176 8 (by decide +kernel)

theorem cellTest_13312_block_23 : Interval cellTest_13312 184 192 :=
  interval_of_check cellTest_13312 184 8 (by decide +kernel)

theorem cellTest_13312_block_24 : Interval cellTest_13312 192 200 :=
  interval_of_check cellTest_13312 192 8 (by decide +kernel)

theorem cellTest_13312_block_25 : Interval cellTest_13312 200 208 :=
  interval_of_check cellTest_13312 200 8 (by decide +kernel)

theorem cellTest_13312_block_26 : Interval cellTest_13312 208 216 :=
  interval_of_check cellTest_13312 208 8 (by decide +kernel)

theorem cellTest_13312_block_27 : Interval cellTest_13312 216 224 :=
  interval_of_check cellTest_13312 216 8 (by decide +kernel)

theorem cellTest_13312_block_28 : Interval cellTest_13312 224 232 :=
  interval_of_check cellTest_13312 224 8 (by decide +kernel)

theorem cellTest_13312_block_29 : Interval cellTest_13312 232 240 :=
  interval_of_check cellTest_13312 232 8 (by decide +kernel)

theorem cellTest_13312_block_30 : Interval cellTest_13312 240 248 :=
  interval_of_check cellTest_13312 240 8 (by decide +kernel)

theorem cellTest_13312_block_31 : Interval cellTest_13312 248 256 :=
  interval_of_check cellTest_13312 248 8 (by decide +kernel)

theorem cellTest_13312_complete : Interval cellTest_13312 0 256 :=
  (interval_append cellTest_13312 0 128 256
  (interval_append cellTest_13312 0 64 128
  (interval_append cellTest_13312 0 32 64
  (interval_append cellTest_13312 0 16 32
  (interval_append cellTest_13312 0 8 16
  cellTest_13312_block_0
  cellTest_13312_block_1)
  (interval_append cellTest_13312 16 24 32
  cellTest_13312_block_2
  cellTest_13312_block_3))
  (interval_append cellTest_13312 32 48 64
  (interval_append cellTest_13312 32 40 48
  cellTest_13312_block_4
  cellTest_13312_block_5)
  (interval_append cellTest_13312 48 56 64
  cellTest_13312_block_6
  cellTest_13312_block_7)))
  (interval_append cellTest_13312 64 96 128
  (interval_append cellTest_13312 64 80 96
  (interval_append cellTest_13312 64 72 80
  cellTest_13312_block_8
  cellTest_13312_block_9)
  (interval_append cellTest_13312 80 88 96
  cellTest_13312_block_10
  cellTest_13312_block_11))
  (interval_append cellTest_13312 96 112 128
  (interval_append cellTest_13312 96 104 112
  cellTest_13312_block_12
  cellTest_13312_block_13)
  (interval_append cellTest_13312 112 120 128
  cellTest_13312_block_14
  cellTest_13312_block_15))))
  (interval_append cellTest_13312 128 192 256
  (interval_append cellTest_13312 128 160 192
  (interval_append cellTest_13312 128 144 160
  (interval_append cellTest_13312 128 136 144
  cellTest_13312_block_16
  cellTest_13312_block_17)
  (interval_append cellTest_13312 144 152 160
  cellTest_13312_block_18
  cellTest_13312_block_19))
  (interval_append cellTest_13312 160 176 192
  (interval_append cellTest_13312 160 168 176
  cellTest_13312_block_20
  cellTest_13312_block_21)
  (interval_append cellTest_13312 176 184 192
  cellTest_13312_block_22
  cellTest_13312_block_23)))
  (interval_append cellTest_13312 192 224 256
  (interval_append cellTest_13312 192 208 224
  (interval_append cellTest_13312 192 200 208
  cellTest_13312_block_24
  cellTest_13312_block_25)
  (interval_append cellTest_13312 208 216 224
  cellTest_13312_block_26
  cellTest_13312_block_27))
  (interval_append cellTest_13312 224 240 256
  (interval_append cellTest_13312 224 232 240
  cellTest_13312_block_28
  cellTest_13312_block_29)
  (interval_append cellTest_13312 240 248 256
  cellTest_13312_block_30
  cellTest_13312_block_31)))))
theorem cellTestInterval13312 : Interval cellTest 13312 13568 := by
  intro i hlo hhi
  have h := cellTest_13312_complete (i-13312) (Nat.zero_le _) (by omega)
  simpa only [cellTest_13312, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells053 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_13568 (i : Nat) := cellTest (i+13568)
theorem cellTest_13568_block_0 : Interval cellTest_13568 0 8 :=
  interval_of_check cellTest_13568 0 8 (by decide +kernel)

theorem cellTest_13568_block_1 : Interval cellTest_13568 8 16 :=
  interval_of_check cellTest_13568 8 8 (by decide +kernel)

theorem cellTest_13568_block_2 : Interval cellTest_13568 16 24 :=
  interval_of_check cellTest_13568 16 8 (by decide +kernel)

theorem cellTest_13568_block_3 : Interval cellTest_13568 24 32 :=
  interval_of_check cellTest_13568 24 8 (by decide +kernel)

theorem cellTest_13568_block_4 : Interval cellTest_13568 32 40 :=
  interval_of_check cellTest_13568 32 8 (by decide +kernel)

theorem cellTest_13568_block_5 : Interval cellTest_13568 40 48 :=
  interval_of_check cellTest_13568 40 8 (by decide +kernel)

theorem cellTest_13568_block_6 : Interval cellTest_13568 48 56 :=
  interval_of_check cellTest_13568 48 8 (by decide +kernel)

theorem cellTest_13568_block_7 : Interval cellTest_13568 56 64 :=
  interval_of_check cellTest_13568 56 8 (by decide +kernel)

theorem cellTest_13568_block_8 : Interval cellTest_13568 64 72 :=
  interval_of_check cellTest_13568 64 8 (by decide +kernel)

theorem cellTest_13568_block_9 : Interval cellTest_13568 72 80 :=
  interval_of_check cellTest_13568 72 8 (by decide +kernel)

theorem cellTest_13568_block_10 : Interval cellTest_13568 80 88 :=
  interval_of_check cellTest_13568 80 8 (by decide +kernel)

theorem cellTest_13568_block_11 : Interval cellTest_13568 88 96 :=
  interval_of_check cellTest_13568 88 8 (by decide +kernel)

theorem cellTest_13568_block_12 : Interval cellTest_13568 96 104 :=
  interval_of_check cellTest_13568 96 8 (by decide +kernel)

theorem cellTest_13568_block_13 : Interval cellTest_13568 104 112 :=
  interval_of_check cellTest_13568 104 8 (by decide +kernel)

theorem cellTest_13568_block_14 : Interval cellTest_13568 112 120 :=
  interval_of_check cellTest_13568 112 8 (by decide +kernel)

theorem cellTest_13568_block_15 : Interval cellTest_13568 120 128 :=
  interval_of_check cellTest_13568 120 8 (by decide +kernel)

theorem cellTest_13568_block_16 : Interval cellTest_13568 128 136 :=
  interval_of_check cellTest_13568 128 8 (by decide +kernel)

theorem cellTest_13568_block_17 : Interval cellTest_13568 136 144 :=
  interval_of_check cellTest_13568 136 8 (by decide +kernel)

theorem cellTest_13568_block_18 : Interval cellTest_13568 144 152 :=
  interval_of_check cellTest_13568 144 8 (by decide +kernel)

theorem cellTest_13568_block_19 : Interval cellTest_13568 152 160 :=
  interval_of_check cellTest_13568 152 8 (by decide +kernel)

theorem cellTest_13568_block_20 : Interval cellTest_13568 160 168 :=
  interval_of_check cellTest_13568 160 8 (by decide +kernel)

theorem cellTest_13568_block_21 : Interval cellTest_13568 168 176 :=
  interval_of_check cellTest_13568 168 8 (by decide +kernel)

theorem cellTest_13568_block_22 : Interval cellTest_13568 176 184 :=
  interval_of_check cellTest_13568 176 8 (by decide +kernel)

theorem cellTest_13568_block_23 : Interval cellTest_13568 184 192 :=
  interval_of_check cellTest_13568 184 8 (by decide +kernel)

theorem cellTest_13568_block_24 : Interval cellTest_13568 192 200 :=
  interval_of_check cellTest_13568 192 8 (by decide +kernel)

theorem cellTest_13568_block_25 : Interval cellTest_13568 200 208 :=
  interval_of_check cellTest_13568 200 8 (by decide +kernel)

theorem cellTest_13568_block_26 : Interval cellTest_13568 208 216 :=
  interval_of_check cellTest_13568 208 8 (by decide +kernel)

theorem cellTest_13568_block_27 : Interval cellTest_13568 216 224 :=
  interval_of_check cellTest_13568 216 8 (by decide +kernel)

theorem cellTest_13568_block_28 : Interval cellTest_13568 224 232 :=
  interval_of_check cellTest_13568 224 8 (by decide +kernel)

theorem cellTest_13568_block_29 : Interval cellTest_13568 232 240 :=
  interval_of_check cellTest_13568 232 8 (by decide +kernel)

theorem cellTest_13568_block_30 : Interval cellTest_13568 240 248 :=
  interval_of_check cellTest_13568 240 8 (by decide +kernel)

theorem cellTest_13568_block_31 : Interval cellTest_13568 248 256 :=
  interval_of_check cellTest_13568 248 8 (by decide +kernel)

theorem cellTest_13568_complete : Interval cellTest_13568 0 256 :=
  (interval_append cellTest_13568 0 128 256
  (interval_append cellTest_13568 0 64 128
  (interval_append cellTest_13568 0 32 64
  (interval_append cellTest_13568 0 16 32
  (interval_append cellTest_13568 0 8 16
  cellTest_13568_block_0
  cellTest_13568_block_1)
  (interval_append cellTest_13568 16 24 32
  cellTest_13568_block_2
  cellTest_13568_block_3))
  (interval_append cellTest_13568 32 48 64
  (interval_append cellTest_13568 32 40 48
  cellTest_13568_block_4
  cellTest_13568_block_5)
  (interval_append cellTest_13568 48 56 64
  cellTest_13568_block_6
  cellTest_13568_block_7)))
  (interval_append cellTest_13568 64 96 128
  (interval_append cellTest_13568 64 80 96
  (interval_append cellTest_13568 64 72 80
  cellTest_13568_block_8
  cellTest_13568_block_9)
  (interval_append cellTest_13568 80 88 96
  cellTest_13568_block_10
  cellTest_13568_block_11))
  (interval_append cellTest_13568 96 112 128
  (interval_append cellTest_13568 96 104 112
  cellTest_13568_block_12
  cellTest_13568_block_13)
  (interval_append cellTest_13568 112 120 128
  cellTest_13568_block_14
  cellTest_13568_block_15))))
  (interval_append cellTest_13568 128 192 256
  (interval_append cellTest_13568 128 160 192
  (interval_append cellTest_13568 128 144 160
  (interval_append cellTest_13568 128 136 144
  cellTest_13568_block_16
  cellTest_13568_block_17)
  (interval_append cellTest_13568 144 152 160
  cellTest_13568_block_18
  cellTest_13568_block_19))
  (interval_append cellTest_13568 160 176 192
  (interval_append cellTest_13568 160 168 176
  cellTest_13568_block_20
  cellTest_13568_block_21)
  (interval_append cellTest_13568 176 184 192
  cellTest_13568_block_22
  cellTest_13568_block_23)))
  (interval_append cellTest_13568 192 224 256
  (interval_append cellTest_13568 192 208 224
  (interval_append cellTest_13568 192 200 208
  cellTest_13568_block_24
  cellTest_13568_block_25)
  (interval_append cellTest_13568 208 216 224
  cellTest_13568_block_26
  cellTest_13568_block_27))
  (interval_append cellTest_13568 224 240 256
  (interval_append cellTest_13568 224 232 240
  cellTest_13568_block_28
  cellTest_13568_block_29)
  (interval_append cellTest_13568 240 248 256
  cellTest_13568_block_30
  cellTest_13568_block_31)))))
theorem cellTestInterval13568 : Interval cellTest 13568 13824 := by
  intro i hlo hhi
  have h := cellTest_13568_complete (i-13568) (Nat.zero_le _) (by omega)
  simpa only [cellTest_13568, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells054 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_13824 (i : Nat) := cellTest (i+13824)
theorem cellTest_13824_block_0 : Interval cellTest_13824 0 8 :=
  interval_of_check cellTest_13824 0 8 (by decide +kernel)

theorem cellTest_13824_block_1 : Interval cellTest_13824 8 16 :=
  interval_of_check cellTest_13824 8 8 (by decide +kernel)

theorem cellTest_13824_block_2 : Interval cellTest_13824 16 24 :=
  interval_of_check cellTest_13824 16 8 (by decide +kernel)

theorem cellTest_13824_block_3 : Interval cellTest_13824 24 32 :=
  interval_of_check cellTest_13824 24 8 (by decide +kernel)

theorem cellTest_13824_block_4 : Interval cellTest_13824 32 40 :=
  interval_of_check cellTest_13824 32 8 (by decide +kernel)

theorem cellTest_13824_block_5 : Interval cellTest_13824 40 48 :=
  interval_of_check cellTest_13824 40 8 (by decide +kernel)

theorem cellTest_13824_block_6 : Interval cellTest_13824 48 56 :=
  interval_of_check cellTest_13824 48 8 (by decide +kernel)

theorem cellTest_13824_block_7 : Interval cellTest_13824 56 64 :=
  interval_of_check cellTest_13824 56 8 (by decide +kernel)

theorem cellTest_13824_block_8 : Interval cellTest_13824 64 72 :=
  interval_of_check cellTest_13824 64 8 (by decide +kernel)

theorem cellTest_13824_block_9 : Interval cellTest_13824 72 80 :=
  interval_of_check cellTest_13824 72 8 (by decide +kernel)

theorem cellTest_13824_block_10 : Interval cellTest_13824 80 88 :=
  interval_of_check cellTest_13824 80 8 (by decide +kernel)

theorem cellTest_13824_block_11 : Interval cellTest_13824 88 96 :=
  interval_of_check cellTest_13824 88 8 (by decide +kernel)

theorem cellTest_13824_block_12 : Interval cellTest_13824 96 104 :=
  interval_of_check cellTest_13824 96 8 (by decide +kernel)

theorem cellTest_13824_block_13 : Interval cellTest_13824 104 112 :=
  interval_of_check cellTest_13824 104 8 (by decide +kernel)

theorem cellTest_13824_block_14 : Interval cellTest_13824 112 120 :=
  interval_of_check cellTest_13824 112 8 (by decide +kernel)

theorem cellTest_13824_block_15 : Interval cellTest_13824 120 128 :=
  interval_of_check cellTest_13824 120 8 (by decide +kernel)

theorem cellTest_13824_block_16 : Interval cellTest_13824 128 136 :=
  interval_of_check cellTest_13824 128 8 (by decide +kernel)

theorem cellTest_13824_block_17 : Interval cellTest_13824 136 144 :=
  interval_of_check cellTest_13824 136 8 (by decide +kernel)

theorem cellTest_13824_block_18 : Interval cellTest_13824 144 152 :=
  interval_of_check cellTest_13824 144 8 (by decide +kernel)

theorem cellTest_13824_block_19 : Interval cellTest_13824 152 160 :=
  interval_of_check cellTest_13824 152 8 (by decide +kernel)

theorem cellTest_13824_block_20 : Interval cellTest_13824 160 168 :=
  interval_of_check cellTest_13824 160 8 (by decide +kernel)

theorem cellTest_13824_block_21 : Interval cellTest_13824 168 176 :=
  interval_of_check cellTest_13824 168 8 (by decide +kernel)

theorem cellTest_13824_block_22 : Interval cellTest_13824 176 184 :=
  interval_of_check cellTest_13824 176 8 (by decide +kernel)

theorem cellTest_13824_block_23 : Interval cellTest_13824 184 192 :=
  interval_of_check cellTest_13824 184 8 (by decide +kernel)

theorem cellTest_13824_block_24 : Interval cellTest_13824 192 200 :=
  interval_of_check cellTest_13824 192 8 (by decide +kernel)

theorem cellTest_13824_block_25 : Interval cellTest_13824 200 208 :=
  interval_of_check cellTest_13824 200 8 (by decide +kernel)

theorem cellTest_13824_block_26 : Interval cellTest_13824 208 216 :=
  interval_of_check cellTest_13824 208 8 (by decide +kernel)

theorem cellTest_13824_block_27 : Interval cellTest_13824 216 224 :=
  interval_of_check cellTest_13824 216 8 (by decide +kernel)

theorem cellTest_13824_block_28 : Interval cellTest_13824 224 232 :=
  interval_of_check cellTest_13824 224 8 (by decide +kernel)

theorem cellTest_13824_block_29 : Interval cellTest_13824 232 240 :=
  interval_of_check cellTest_13824 232 8 (by decide +kernel)

theorem cellTest_13824_block_30 : Interval cellTest_13824 240 248 :=
  interval_of_check cellTest_13824 240 8 (by decide +kernel)

theorem cellTest_13824_block_31 : Interval cellTest_13824 248 256 :=
  interval_of_check cellTest_13824 248 8 (by decide +kernel)

theorem cellTest_13824_complete : Interval cellTest_13824 0 256 :=
  (interval_append cellTest_13824 0 128 256
  (interval_append cellTest_13824 0 64 128
  (interval_append cellTest_13824 0 32 64
  (interval_append cellTest_13824 0 16 32
  (interval_append cellTest_13824 0 8 16
  cellTest_13824_block_0
  cellTest_13824_block_1)
  (interval_append cellTest_13824 16 24 32
  cellTest_13824_block_2
  cellTest_13824_block_3))
  (interval_append cellTest_13824 32 48 64
  (interval_append cellTest_13824 32 40 48
  cellTest_13824_block_4
  cellTest_13824_block_5)
  (interval_append cellTest_13824 48 56 64
  cellTest_13824_block_6
  cellTest_13824_block_7)))
  (interval_append cellTest_13824 64 96 128
  (interval_append cellTest_13824 64 80 96
  (interval_append cellTest_13824 64 72 80
  cellTest_13824_block_8
  cellTest_13824_block_9)
  (interval_append cellTest_13824 80 88 96
  cellTest_13824_block_10
  cellTest_13824_block_11))
  (interval_append cellTest_13824 96 112 128
  (interval_append cellTest_13824 96 104 112
  cellTest_13824_block_12
  cellTest_13824_block_13)
  (interval_append cellTest_13824 112 120 128
  cellTest_13824_block_14
  cellTest_13824_block_15))))
  (interval_append cellTest_13824 128 192 256
  (interval_append cellTest_13824 128 160 192
  (interval_append cellTest_13824 128 144 160
  (interval_append cellTest_13824 128 136 144
  cellTest_13824_block_16
  cellTest_13824_block_17)
  (interval_append cellTest_13824 144 152 160
  cellTest_13824_block_18
  cellTest_13824_block_19))
  (interval_append cellTest_13824 160 176 192
  (interval_append cellTest_13824 160 168 176
  cellTest_13824_block_20
  cellTest_13824_block_21)
  (interval_append cellTest_13824 176 184 192
  cellTest_13824_block_22
  cellTest_13824_block_23)))
  (interval_append cellTest_13824 192 224 256
  (interval_append cellTest_13824 192 208 224
  (interval_append cellTest_13824 192 200 208
  cellTest_13824_block_24
  cellTest_13824_block_25)
  (interval_append cellTest_13824 208 216 224
  cellTest_13824_block_26
  cellTest_13824_block_27))
  (interval_append cellTest_13824 224 240 256
  (interval_append cellTest_13824 224 232 240
  cellTest_13824_block_28
  cellTest_13824_block_29)
  (interval_append cellTest_13824 240 248 256
  cellTest_13824_block_30
  cellTest_13824_block_31)))))
theorem cellTestInterval13824 : Interval cellTest 13824 14080 := by
  intro i hlo hhi
  have h := cellTest_13824_complete (i-13824) (Nat.zero_le _) (by omega)
  simpa only [cellTest_13824, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells055 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_14080 (i : Nat) := cellTest (i+14080)
theorem cellTest_14080_block_0 : Interval cellTest_14080 0 8 :=
  interval_of_check cellTest_14080 0 8 (by decide +kernel)

theorem cellTest_14080_block_1 : Interval cellTest_14080 8 16 :=
  interval_of_check cellTest_14080 8 8 (by decide +kernel)

theorem cellTest_14080_block_2 : Interval cellTest_14080 16 24 :=
  interval_of_check cellTest_14080 16 8 (by decide +kernel)

theorem cellTest_14080_block_3 : Interval cellTest_14080 24 32 :=
  interval_of_check cellTest_14080 24 8 (by decide +kernel)

theorem cellTest_14080_block_4 : Interval cellTest_14080 32 40 :=
  interval_of_check cellTest_14080 32 8 (by decide +kernel)

theorem cellTest_14080_block_5 : Interval cellTest_14080 40 48 :=
  interval_of_check cellTest_14080 40 8 (by decide +kernel)

theorem cellTest_14080_block_6 : Interval cellTest_14080 48 56 :=
  interval_of_check cellTest_14080 48 8 (by decide +kernel)

theorem cellTest_14080_block_7 : Interval cellTest_14080 56 64 :=
  interval_of_check cellTest_14080 56 8 (by decide +kernel)

theorem cellTest_14080_block_8 : Interval cellTest_14080 64 72 :=
  interval_of_check cellTest_14080 64 8 (by decide +kernel)

theorem cellTest_14080_block_9 : Interval cellTest_14080 72 80 :=
  interval_of_check cellTest_14080 72 8 (by decide +kernel)

theorem cellTest_14080_block_10 : Interval cellTest_14080 80 88 :=
  interval_of_check cellTest_14080 80 8 (by decide +kernel)

theorem cellTest_14080_block_11 : Interval cellTest_14080 88 96 :=
  interval_of_check cellTest_14080 88 8 (by decide +kernel)

theorem cellTest_14080_block_12 : Interval cellTest_14080 96 104 :=
  interval_of_check cellTest_14080 96 8 (by decide +kernel)

theorem cellTest_14080_block_13 : Interval cellTest_14080 104 112 :=
  interval_of_check cellTest_14080 104 8 (by decide +kernel)

theorem cellTest_14080_block_14 : Interval cellTest_14080 112 120 :=
  interval_of_check cellTest_14080 112 8 (by decide +kernel)

theorem cellTest_14080_block_15 : Interval cellTest_14080 120 128 :=
  interval_of_check cellTest_14080 120 8 (by decide +kernel)

theorem cellTest_14080_block_16 : Interval cellTest_14080 128 136 :=
  interval_of_check cellTest_14080 128 8 (by decide +kernel)

theorem cellTest_14080_block_17 : Interval cellTest_14080 136 144 :=
  interval_of_check cellTest_14080 136 8 (by decide +kernel)

theorem cellTest_14080_block_18 : Interval cellTest_14080 144 152 :=
  interval_of_check cellTest_14080 144 8 (by decide +kernel)

theorem cellTest_14080_block_19 : Interval cellTest_14080 152 160 :=
  interval_of_check cellTest_14080 152 8 (by decide +kernel)

theorem cellTest_14080_block_20 : Interval cellTest_14080 160 168 :=
  interval_of_check cellTest_14080 160 8 (by decide +kernel)

theorem cellTest_14080_block_21 : Interval cellTest_14080 168 176 :=
  interval_of_check cellTest_14080 168 8 (by decide +kernel)

theorem cellTest_14080_block_22 : Interval cellTest_14080 176 184 :=
  interval_of_check cellTest_14080 176 8 (by decide +kernel)

theorem cellTest_14080_block_23 : Interval cellTest_14080 184 192 :=
  interval_of_check cellTest_14080 184 8 (by decide +kernel)

theorem cellTest_14080_block_24 : Interval cellTest_14080 192 200 :=
  interval_of_check cellTest_14080 192 8 (by decide +kernel)

theorem cellTest_14080_block_25 : Interval cellTest_14080 200 208 :=
  interval_of_check cellTest_14080 200 8 (by decide +kernel)

theorem cellTest_14080_block_26 : Interval cellTest_14080 208 216 :=
  interval_of_check cellTest_14080 208 8 (by decide +kernel)

theorem cellTest_14080_block_27 : Interval cellTest_14080 216 224 :=
  interval_of_check cellTest_14080 216 8 (by decide +kernel)

theorem cellTest_14080_block_28 : Interval cellTest_14080 224 232 :=
  interval_of_check cellTest_14080 224 8 (by decide +kernel)

theorem cellTest_14080_block_29 : Interval cellTest_14080 232 240 :=
  interval_of_check cellTest_14080 232 8 (by decide +kernel)

theorem cellTest_14080_block_30 : Interval cellTest_14080 240 248 :=
  interval_of_check cellTest_14080 240 8 (by decide +kernel)

theorem cellTest_14080_block_31 : Interval cellTest_14080 248 256 :=
  interval_of_check cellTest_14080 248 8 (by decide +kernel)

theorem cellTest_14080_complete : Interval cellTest_14080 0 256 :=
  (interval_append cellTest_14080 0 128 256
  (interval_append cellTest_14080 0 64 128
  (interval_append cellTest_14080 0 32 64
  (interval_append cellTest_14080 0 16 32
  (interval_append cellTest_14080 0 8 16
  cellTest_14080_block_0
  cellTest_14080_block_1)
  (interval_append cellTest_14080 16 24 32
  cellTest_14080_block_2
  cellTest_14080_block_3))
  (interval_append cellTest_14080 32 48 64
  (interval_append cellTest_14080 32 40 48
  cellTest_14080_block_4
  cellTest_14080_block_5)
  (interval_append cellTest_14080 48 56 64
  cellTest_14080_block_6
  cellTest_14080_block_7)))
  (interval_append cellTest_14080 64 96 128
  (interval_append cellTest_14080 64 80 96
  (interval_append cellTest_14080 64 72 80
  cellTest_14080_block_8
  cellTest_14080_block_9)
  (interval_append cellTest_14080 80 88 96
  cellTest_14080_block_10
  cellTest_14080_block_11))
  (interval_append cellTest_14080 96 112 128
  (interval_append cellTest_14080 96 104 112
  cellTest_14080_block_12
  cellTest_14080_block_13)
  (interval_append cellTest_14080 112 120 128
  cellTest_14080_block_14
  cellTest_14080_block_15))))
  (interval_append cellTest_14080 128 192 256
  (interval_append cellTest_14080 128 160 192
  (interval_append cellTest_14080 128 144 160
  (interval_append cellTest_14080 128 136 144
  cellTest_14080_block_16
  cellTest_14080_block_17)
  (interval_append cellTest_14080 144 152 160
  cellTest_14080_block_18
  cellTest_14080_block_19))
  (interval_append cellTest_14080 160 176 192
  (interval_append cellTest_14080 160 168 176
  cellTest_14080_block_20
  cellTest_14080_block_21)
  (interval_append cellTest_14080 176 184 192
  cellTest_14080_block_22
  cellTest_14080_block_23)))
  (interval_append cellTest_14080 192 224 256
  (interval_append cellTest_14080 192 208 224
  (interval_append cellTest_14080 192 200 208
  cellTest_14080_block_24
  cellTest_14080_block_25)
  (interval_append cellTest_14080 208 216 224
  cellTest_14080_block_26
  cellTest_14080_block_27))
  (interval_append cellTest_14080 224 240 256
  (interval_append cellTest_14080 224 232 240
  cellTest_14080_block_28
  cellTest_14080_block_29)
  (interval_append cellTest_14080 240 248 256
  cellTest_14080_block_30
  cellTest_14080_block_31)))))
theorem cellTestInterval14080 : Interval cellTest 14080 14336 := by
  intro i hlo hhi
  have h := cellTest_14080_complete (i-14080) (Nat.zero_le _) (by omega)
  simpa only [cellTest_14080, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells056 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_14336 (i : Nat) := cellTest (i+14336)
theorem cellTest_14336_block_0 : Interval cellTest_14336 0 8 :=
  interval_of_check cellTest_14336 0 8 (by decide +kernel)

theorem cellTest_14336_block_1 : Interval cellTest_14336 8 16 :=
  interval_of_check cellTest_14336 8 8 (by decide +kernel)

theorem cellTest_14336_block_2 : Interval cellTest_14336 16 24 :=
  interval_of_check cellTest_14336 16 8 (by decide +kernel)

theorem cellTest_14336_block_3 : Interval cellTest_14336 24 32 :=
  interval_of_check cellTest_14336 24 8 (by decide +kernel)

theorem cellTest_14336_block_4 : Interval cellTest_14336 32 40 :=
  interval_of_check cellTest_14336 32 8 (by decide +kernel)

theorem cellTest_14336_block_5 : Interval cellTest_14336 40 48 :=
  interval_of_check cellTest_14336 40 8 (by decide +kernel)

theorem cellTest_14336_block_6 : Interval cellTest_14336 48 56 :=
  interval_of_check cellTest_14336 48 8 (by decide +kernel)

theorem cellTest_14336_block_7 : Interval cellTest_14336 56 64 :=
  interval_of_check cellTest_14336 56 8 (by decide +kernel)

theorem cellTest_14336_block_8 : Interval cellTest_14336 64 72 :=
  interval_of_check cellTest_14336 64 8 (by decide +kernel)

theorem cellTest_14336_block_9 : Interval cellTest_14336 72 80 :=
  interval_of_check cellTest_14336 72 8 (by decide +kernel)

theorem cellTest_14336_block_10 : Interval cellTest_14336 80 88 :=
  interval_of_check cellTest_14336 80 8 (by decide +kernel)

theorem cellTest_14336_block_11 : Interval cellTest_14336 88 96 :=
  interval_of_check cellTest_14336 88 8 (by decide +kernel)

theorem cellTest_14336_block_12 : Interval cellTest_14336 96 104 :=
  interval_of_check cellTest_14336 96 8 (by decide +kernel)

theorem cellTest_14336_block_13 : Interval cellTest_14336 104 112 :=
  interval_of_check cellTest_14336 104 8 (by decide +kernel)

theorem cellTest_14336_block_14 : Interval cellTest_14336 112 120 :=
  interval_of_check cellTest_14336 112 8 (by decide +kernel)

theorem cellTest_14336_block_15 : Interval cellTest_14336 120 128 :=
  interval_of_check cellTest_14336 120 8 (by decide +kernel)

theorem cellTest_14336_block_16 : Interval cellTest_14336 128 136 :=
  interval_of_check cellTest_14336 128 8 (by decide +kernel)

theorem cellTest_14336_block_17 : Interval cellTest_14336 136 144 :=
  interval_of_check cellTest_14336 136 8 (by decide +kernel)

theorem cellTest_14336_block_18 : Interval cellTest_14336 144 152 :=
  interval_of_check cellTest_14336 144 8 (by decide +kernel)

theorem cellTest_14336_block_19 : Interval cellTest_14336 152 160 :=
  interval_of_check cellTest_14336 152 8 (by decide +kernel)

theorem cellTest_14336_block_20 : Interval cellTest_14336 160 168 :=
  interval_of_check cellTest_14336 160 8 (by decide +kernel)

theorem cellTest_14336_block_21 : Interval cellTest_14336 168 176 :=
  interval_of_check cellTest_14336 168 8 (by decide +kernel)

theorem cellTest_14336_block_22 : Interval cellTest_14336 176 184 :=
  interval_of_check cellTest_14336 176 8 (by decide +kernel)

theorem cellTest_14336_block_23 : Interval cellTest_14336 184 192 :=
  interval_of_check cellTest_14336 184 8 (by decide +kernel)

theorem cellTest_14336_block_24 : Interval cellTest_14336 192 200 :=
  interval_of_check cellTest_14336 192 8 (by decide +kernel)

theorem cellTest_14336_block_25 : Interval cellTest_14336 200 208 :=
  interval_of_check cellTest_14336 200 8 (by decide +kernel)

theorem cellTest_14336_block_26 : Interval cellTest_14336 208 216 :=
  interval_of_check cellTest_14336 208 8 (by decide +kernel)

theorem cellTest_14336_block_27 : Interval cellTest_14336 216 224 :=
  interval_of_check cellTest_14336 216 8 (by decide +kernel)

theorem cellTest_14336_block_28 : Interval cellTest_14336 224 232 :=
  interval_of_check cellTest_14336 224 8 (by decide +kernel)

theorem cellTest_14336_block_29 : Interval cellTest_14336 232 240 :=
  interval_of_check cellTest_14336 232 8 (by decide +kernel)

theorem cellTest_14336_block_30 : Interval cellTest_14336 240 248 :=
  interval_of_check cellTest_14336 240 8 (by decide +kernel)

theorem cellTest_14336_block_31 : Interval cellTest_14336 248 256 :=
  interval_of_check cellTest_14336 248 8 (by decide +kernel)

theorem cellTest_14336_complete : Interval cellTest_14336 0 256 :=
  (interval_append cellTest_14336 0 128 256
  (interval_append cellTest_14336 0 64 128
  (interval_append cellTest_14336 0 32 64
  (interval_append cellTest_14336 0 16 32
  (interval_append cellTest_14336 0 8 16
  cellTest_14336_block_0
  cellTest_14336_block_1)
  (interval_append cellTest_14336 16 24 32
  cellTest_14336_block_2
  cellTest_14336_block_3))
  (interval_append cellTest_14336 32 48 64
  (interval_append cellTest_14336 32 40 48
  cellTest_14336_block_4
  cellTest_14336_block_5)
  (interval_append cellTest_14336 48 56 64
  cellTest_14336_block_6
  cellTest_14336_block_7)))
  (interval_append cellTest_14336 64 96 128
  (interval_append cellTest_14336 64 80 96
  (interval_append cellTest_14336 64 72 80
  cellTest_14336_block_8
  cellTest_14336_block_9)
  (interval_append cellTest_14336 80 88 96
  cellTest_14336_block_10
  cellTest_14336_block_11))
  (interval_append cellTest_14336 96 112 128
  (interval_append cellTest_14336 96 104 112
  cellTest_14336_block_12
  cellTest_14336_block_13)
  (interval_append cellTest_14336 112 120 128
  cellTest_14336_block_14
  cellTest_14336_block_15))))
  (interval_append cellTest_14336 128 192 256
  (interval_append cellTest_14336 128 160 192
  (interval_append cellTest_14336 128 144 160
  (interval_append cellTest_14336 128 136 144
  cellTest_14336_block_16
  cellTest_14336_block_17)
  (interval_append cellTest_14336 144 152 160
  cellTest_14336_block_18
  cellTest_14336_block_19))
  (interval_append cellTest_14336 160 176 192
  (interval_append cellTest_14336 160 168 176
  cellTest_14336_block_20
  cellTest_14336_block_21)
  (interval_append cellTest_14336 176 184 192
  cellTest_14336_block_22
  cellTest_14336_block_23)))
  (interval_append cellTest_14336 192 224 256
  (interval_append cellTest_14336 192 208 224
  (interval_append cellTest_14336 192 200 208
  cellTest_14336_block_24
  cellTest_14336_block_25)
  (interval_append cellTest_14336 208 216 224
  cellTest_14336_block_26
  cellTest_14336_block_27))
  (interval_append cellTest_14336 224 240 256
  (interval_append cellTest_14336 224 232 240
  cellTest_14336_block_28
  cellTest_14336_block_29)
  (interval_append cellTest_14336 240 248 256
  cellTest_14336_block_30
  cellTest_14336_block_31)))))
theorem cellTestInterval14336 : Interval cellTest 14336 14592 := by
  intro i hlo hhi
  have h := cellTest_14336_complete (i-14336) (Nat.zero_le _) (by omega)
  simpa only [cellTest_14336, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells057 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_14592 (i : Nat) := cellTest (i+14592)
theorem cellTest_14592_block_0 : Interval cellTest_14592 0 8 :=
  interval_of_check cellTest_14592 0 8 (by decide +kernel)

theorem cellTest_14592_block_1 : Interval cellTest_14592 8 16 :=
  interval_of_check cellTest_14592 8 8 (by decide +kernel)

theorem cellTest_14592_block_2 : Interval cellTest_14592 16 24 :=
  interval_of_check cellTest_14592 16 8 (by decide +kernel)

theorem cellTest_14592_block_3 : Interval cellTest_14592 24 32 :=
  interval_of_check cellTest_14592 24 8 (by decide +kernel)

theorem cellTest_14592_block_4 : Interval cellTest_14592 32 40 :=
  interval_of_check cellTest_14592 32 8 (by decide +kernel)

theorem cellTest_14592_block_5 : Interval cellTest_14592 40 48 :=
  interval_of_check cellTest_14592 40 8 (by decide +kernel)

theorem cellTest_14592_block_6 : Interval cellTest_14592 48 56 :=
  interval_of_check cellTest_14592 48 8 (by decide +kernel)

theorem cellTest_14592_block_7 : Interval cellTest_14592 56 64 :=
  interval_of_check cellTest_14592 56 8 (by decide +kernel)

theorem cellTest_14592_block_8 : Interval cellTest_14592 64 72 :=
  interval_of_check cellTest_14592 64 8 (by decide +kernel)

theorem cellTest_14592_block_9 : Interval cellTest_14592 72 80 :=
  interval_of_check cellTest_14592 72 8 (by decide +kernel)

theorem cellTest_14592_block_10 : Interval cellTest_14592 80 88 :=
  interval_of_check cellTest_14592 80 8 (by decide +kernel)

theorem cellTest_14592_block_11 : Interval cellTest_14592 88 96 :=
  interval_of_check cellTest_14592 88 8 (by decide +kernel)

theorem cellTest_14592_block_12 : Interval cellTest_14592 96 104 :=
  interval_of_check cellTest_14592 96 8 (by decide +kernel)

theorem cellTest_14592_block_13 : Interval cellTest_14592 104 112 :=
  interval_of_check cellTest_14592 104 8 (by decide +kernel)

theorem cellTest_14592_block_14 : Interval cellTest_14592 112 120 :=
  interval_of_check cellTest_14592 112 8 (by decide +kernel)

theorem cellTest_14592_block_15 : Interval cellTest_14592 120 128 :=
  interval_of_check cellTest_14592 120 8 (by decide +kernel)

theorem cellTest_14592_block_16 : Interval cellTest_14592 128 136 :=
  interval_of_check cellTest_14592 128 8 (by decide +kernel)

theorem cellTest_14592_block_17 : Interval cellTest_14592 136 144 :=
  interval_of_check cellTest_14592 136 8 (by decide +kernel)

theorem cellTest_14592_block_18 : Interval cellTest_14592 144 152 :=
  interval_of_check cellTest_14592 144 8 (by decide +kernel)

theorem cellTest_14592_block_19 : Interval cellTest_14592 152 160 :=
  interval_of_check cellTest_14592 152 8 (by decide +kernel)

theorem cellTest_14592_block_20 : Interval cellTest_14592 160 168 :=
  interval_of_check cellTest_14592 160 8 (by decide +kernel)

theorem cellTest_14592_block_21 : Interval cellTest_14592 168 176 :=
  interval_of_check cellTest_14592 168 8 (by decide +kernel)

theorem cellTest_14592_block_22 : Interval cellTest_14592 176 184 :=
  interval_of_check cellTest_14592 176 8 (by decide +kernel)

theorem cellTest_14592_block_23 : Interval cellTest_14592 184 192 :=
  interval_of_check cellTest_14592 184 8 (by decide +kernel)

theorem cellTest_14592_block_24 : Interval cellTest_14592 192 200 :=
  interval_of_check cellTest_14592 192 8 (by decide +kernel)

theorem cellTest_14592_block_25 : Interval cellTest_14592 200 208 :=
  interval_of_check cellTest_14592 200 8 (by decide +kernel)

theorem cellTest_14592_block_26 : Interval cellTest_14592 208 216 :=
  interval_of_check cellTest_14592 208 8 (by decide +kernel)

theorem cellTest_14592_block_27 : Interval cellTest_14592 216 224 :=
  interval_of_check cellTest_14592 216 8 (by decide +kernel)

theorem cellTest_14592_block_28 : Interval cellTest_14592 224 232 :=
  interval_of_check cellTest_14592 224 8 (by decide +kernel)

theorem cellTest_14592_block_29 : Interval cellTest_14592 232 240 :=
  interval_of_check cellTest_14592 232 8 (by decide +kernel)

theorem cellTest_14592_block_30 : Interval cellTest_14592 240 248 :=
  interval_of_check cellTest_14592 240 8 (by decide +kernel)

theorem cellTest_14592_block_31 : Interval cellTest_14592 248 256 :=
  interval_of_check cellTest_14592 248 8 (by decide +kernel)

theorem cellTest_14592_complete : Interval cellTest_14592 0 256 :=
  (interval_append cellTest_14592 0 128 256
  (interval_append cellTest_14592 0 64 128
  (interval_append cellTest_14592 0 32 64
  (interval_append cellTest_14592 0 16 32
  (interval_append cellTest_14592 0 8 16
  cellTest_14592_block_0
  cellTest_14592_block_1)
  (interval_append cellTest_14592 16 24 32
  cellTest_14592_block_2
  cellTest_14592_block_3))
  (interval_append cellTest_14592 32 48 64
  (interval_append cellTest_14592 32 40 48
  cellTest_14592_block_4
  cellTest_14592_block_5)
  (interval_append cellTest_14592 48 56 64
  cellTest_14592_block_6
  cellTest_14592_block_7)))
  (interval_append cellTest_14592 64 96 128
  (interval_append cellTest_14592 64 80 96
  (interval_append cellTest_14592 64 72 80
  cellTest_14592_block_8
  cellTest_14592_block_9)
  (interval_append cellTest_14592 80 88 96
  cellTest_14592_block_10
  cellTest_14592_block_11))
  (interval_append cellTest_14592 96 112 128
  (interval_append cellTest_14592 96 104 112
  cellTest_14592_block_12
  cellTest_14592_block_13)
  (interval_append cellTest_14592 112 120 128
  cellTest_14592_block_14
  cellTest_14592_block_15))))
  (interval_append cellTest_14592 128 192 256
  (interval_append cellTest_14592 128 160 192
  (interval_append cellTest_14592 128 144 160
  (interval_append cellTest_14592 128 136 144
  cellTest_14592_block_16
  cellTest_14592_block_17)
  (interval_append cellTest_14592 144 152 160
  cellTest_14592_block_18
  cellTest_14592_block_19))
  (interval_append cellTest_14592 160 176 192
  (interval_append cellTest_14592 160 168 176
  cellTest_14592_block_20
  cellTest_14592_block_21)
  (interval_append cellTest_14592 176 184 192
  cellTest_14592_block_22
  cellTest_14592_block_23)))
  (interval_append cellTest_14592 192 224 256
  (interval_append cellTest_14592 192 208 224
  (interval_append cellTest_14592 192 200 208
  cellTest_14592_block_24
  cellTest_14592_block_25)
  (interval_append cellTest_14592 208 216 224
  cellTest_14592_block_26
  cellTest_14592_block_27))
  (interval_append cellTest_14592 224 240 256
  (interval_append cellTest_14592 224 232 240
  cellTest_14592_block_28
  cellTest_14592_block_29)
  (interval_append cellTest_14592 240 248 256
  cellTest_14592_block_30
  cellTest_14592_block_31)))))
theorem cellTestInterval14592 : Interval cellTest 14592 14848 := by
  intro i hlo hhi
  have h := cellTest_14592_complete (i-14592) (Nat.zero_le _) (by omega)
  simpa only [cellTest_14592, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells058 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_14848 (i : Nat) := cellTest (i+14848)
theorem cellTest_14848_block_0 : Interval cellTest_14848 0 8 :=
  interval_of_check cellTest_14848 0 8 (by decide +kernel)

theorem cellTest_14848_block_1 : Interval cellTest_14848 8 16 :=
  interval_of_check cellTest_14848 8 8 (by decide +kernel)

theorem cellTest_14848_block_2 : Interval cellTest_14848 16 24 :=
  interval_of_check cellTest_14848 16 8 (by decide +kernel)

theorem cellTest_14848_block_3 : Interval cellTest_14848 24 32 :=
  interval_of_check cellTest_14848 24 8 (by decide +kernel)

theorem cellTest_14848_block_4 : Interval cellTest_14848 32 40 :=
  interval_of_check cellTest_14848 32 8 (by decide +kernel)

theorem cellTest_14848_block_5 : Interval cellTest_14848 40 48 :=
  interval_of_check cellTest_14848 40 8 (by decide +kernel)

theorem cellTest_14848_block_6 : Interval cellTest_14848 48 56 :=
  interval_of_check cellTest_14848 48 8 (by decide +kernel)

theorem cellTest_14848_block_7 : Interval cellTest_14848 56 64 :=
  interval_of_check cellTest_14848 56 8 (by decide +kernel)

theorem cellTest_14848_block_8 : Interval cellTest_14848 64 72 :=
  interval_of_check cellTest_14848 64 8 (by decide +kernel)

theorem cellTest_14848_block_9 : Interval cellTest_14848 72 80 :=
  interval_of_check cellTest_14848 72 8 (by decide +kernel)

theorem cellTest_14848_block_10 : Interval cellTest_14848 80 88 :=
  interval_of_check cellTest_14848 80 8 (by decide +kernel)

theorem cellTest_14848_block_11 : Interval cellTest_14848 88 96 :=
  interval_of_check cellTest_14848 88 8 (by decide +kernel)

theorem cellTest_14848_block_12 : Interval cellTest_14848 96 104 :=
  interval_of_check cellTest_14848 96 8 (by decide +kernel)

theorem cellTest_14848_block_13 : Interval cellTest_14848 104 112 :=
  interval_of_check cellTest_14848 104 8 (by decide +kernel)

theorem cellTest_14848_block_14 : Interval cellTest_14848 112 120 :=
  interval_of_check cellTest_14848 112 8 (by decide +kernel)

theorem cellTest_14848_block_15 : Interval cellTest_14848 120 128 :=
  interval_of_check cellTest_14848 120 8 (by decide +kernel)

theorem cellTest_14848_block_16 : Interval cellTest_14848 128 136 :=
  interval_of_check cellTest_14848 128 8 (by decide +kernel)

theorem cellTest_14848_block_17 : Interval cellTest_14848 136 144 :=
  interval_of_check cellTest_14848 136 8 (by decide +kernel)

theorem cellTest_14848_block_18 : Interval cellTest_14848 144 152 :=
  interval_of_check cellTest_14848 144 8 (by decide +kernel)

theorem cellTest_14848_block_19 : Interval cellTest_14848 152 160 :=
  interval_of_check cellTest_14848 152 8 (by decide +kernel)

theorem cellTest_14848_block_20 : Interval cellTest_14848 160 168 :=
  interval_of_check cellTest_14848 160 8 (by decide +kernel)

theorem cellTest_14848_block_21 : Interval cellTest_14848 168 176 :=
  interval_of_check cellTest_14848 168 8 (by decide +kernel)

theorem cellTest_14848_block_22 : Interval cellTest_14848 176 184 :=
  interval_of_check cellTest_14848 176 8 (by decide +kernel)

theorem cellTest_14848_block_23 : Interval cellTest_14848 184 192 :=
  interval_of_check cellTest_14848 184 8 (by decide +kernel)

theorem cellTest_14848_block_24 : Interval cellTest_14848 192 200 :=
  interval_of_check cellTest_14848 192 8 (by decide +kernel)

theorem cellTest_14848_block_25 : Interval cellTest_14848 200 208 :=
  interval_of_check cellTest_14848 200 8 (by decide +kernel)

theorem cellTest_14848_block_26 : Interval cellTest_14848 208 216 :=
  interval_of_check cellTest_14848 208 8 (by decide +kernel)

theorem cellTest_14848_block_27 : Interval cellTest_14848 216 224 :=
  interval_of_check cellTest_14848 216 8 (by decide +kernel)

theorem cellTest_14848_block_28 : Interval cellTest_14848 224 232 :=
  interval_of_check cellTest_14848 224 8 (by decide +kernel)

theorem cellTest_14848_block_29 : Interval cellTest_14848 232 240 :=
  interval_of_check cellTest_14848 232 8 (by decide +kernel)

theorem cellTest_14848_block_30 : Interval cellTest_14848 240 248 :=
  interval_of_check cellTest_14848 240 8 (by decide +kernel)

theorem cellTest_14848_block_31 : Interval cellTest_14848 248 256 :=
  interval_of_check cellTest_14848 248 8 (by decide +kernel)

theorem cellTest_14848_complete : Interval cellTest_14848 0 256 :=
  (interval_append cellTest_14848 0 128 256
  (interval_append cellTest_14848 0 64 128
  (interval_append cellTest_14848 0 32 64
  (interval_append cellTest_14848 0 16 32
  (interval_append cellTest_14848 0 8 16
  cellTest_14848_block_0
  cellTest_14848_block_1)
  (interval_append cellTest_14848 16 24 32
  cellTest_14848_block_2
  cellTest_14848_block_3))
  (interval_append cellTest_14848 32 48 64
  (interval_append cellTest_14848 32 40 48
  cellTest_14848_block_4
  cellTest_14848_block_5)
  (interval_append cellTest_14848 48 56 64
  cellTest_14848_block_6
  cellTest_14848_block_7)))
  (interval_append cellTest_14848 64 96 128
  (interval_append cellTest_14848 64 80 96
  (interval_append cellTest_14848 64 72 80
  cellTest_14848_block_8
  cellTest_14848_block_9)
  (interval_append cellTest_14848 80 88 96
  cellTest_14848_block_10
  cellTest_14848_block_11))
  (interval_append cellTest_14848 96 112 128
  (interval_append cellTest_14848 96 104 112
  cellTest_14848_block_12
  cellTest_14848_block_13)
  (interval_append cellTest_14848 112 120 128
  cellTest_14848_block_14
  cellTest_14848_block_15))))
  (interval_append cellTest_14848 128 192 256
  (interval_append cellTest_14848 128 160 192
  (interval_append cellTest_14848 128 144 160
  (interval_append cellTest_14848 128 136 144
  cellTest_14848_block_16
  cellTest_14848_block_17)
  (interval_append cellTest_14848 144 152 160
  cellTest_14848_block_18
  cellTest_14848_block_19))
  (interval_append cellTest_14848 160 176 192
  (interval_append cellTest_14848 160 168 176
  cellTest_14848_block_20
  cellTest_14848_block_21)
  (interval_append cellTest_14848 176 184 192
  cellTest_14848_block_22
  cellTest_14848_block_23)))
  (interval_append cellTest_14848 192 224 256
  (interval_append cellTest_14848 192 208 224
  (interval_append cellTest_14848 192 200 208
  cellTest_14848_block_24
  cellTest_14848_block_25)
  (interval_append cellTest_14848 208 216 224
  cellTest_14848_block_26
  cellTest_14848_block_27))
  (interval_append cellTest_14848 224 240 256
  (interval_append cellTest_14848 224 232 240
  cellTest_14848_block_28
  cellTest_14848_block_29)
  (interval_append cellTest_14848 240 248 256
  cellTest_14848_block_30
  cellTest_14848_block_31)))))
theorem cellTestInterval14848 : Interval cellTest 14848 15104 := by
  intro i hlo hhi
  have h := cellTest_14848_complete (i-14848) (Nat.zero_le _) (by omega)
  simpa only [cellTest_14848, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheCells059 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_15104 (i : Nat) := cellTest (i+15104)
theorem cellTest_15104_block_0 : Interval cellTest_15104 0 8 :=
  interval_of_check cellTest_15104 0 8 (by decide +kernel)

theorem cellTest_15104_block_1 : Interval cellTest_15104 8 16 :=
  interval_of_check cellTest_15104 8 8 (by decide +kernel)

theorem cellTest_15104_block_2 : Interval cellTest_15104 16 24 :=
  interval_of_check cellTest_15104 16 8 (by decide +kernel)

theorem cellTest_15104_block_3 : Interval cellTest_15104 24 32 :=
  interval_of_check cellTest_15104 24 8 (by decide +kernel)

theorem cellTest_15104_block_4 : Interval cellTest_15104 32 40 :=
  interval_of_check cellTest_15104 32 8 (by decide +kernel)

theorem cellTest_15104_block_5 : Interval cellTest_15104 40 48 :=
  interval_of_check cellTest_15104 40 8 (by decide +kernel)

theorem cellTest_15104_block_6 : Interval cellTest_15104 48 56 :=
  interval_of_check cellTest_15104 48 8 (by decide +kernel)

theorem cellTest_15104_block_7 : Interval cellTest_15104 56 64 :=
  interval_of_check cellTest_15104 56 8 (by decide +kernel)

theorem cellTest_15104_block_8 : Interval cellTest_15104 64 72 :=
  interval_of_check cellTest_15104 64 8 (by decide +kernel)

theorem cellTest_15104_block_9 : Interval cellTest_15104 72 80 :=
  interval_of_check cellTest_15104 72 8 (by decide +kernel)

theorem cellTest_15104_block_10 : Interval cellTest_15104 80 88 :=
  interval_of_check cellTest_15104 80 8 (by decide +kernel)

theorem cellTest_15104_block_11 : Interval cellTest_15104 88 96 :=
  interval_of_check cellTest_15104 88 8 (by decide +kernel)

theorem cellTest_15104_block_12 : Interval cellTest_15104 96 104 :=
  interval_of_check cellTest_15104 96 8 (by decide +kernel)

theorem cellTest_15104_block_13 : Interval cellTest_15104 104 112 :=
  interval_of_check cellTest_15104 104 8 (by decide +kernel)

theorem cellTest_15104_block_14 : Interval cellTest_15104 112 120 :=
  interval_of_check cellTest_15104 112 8 (by decide +kernel)

theorem cellTest_15104_block_15 : Interval cellTest_15104 120 128 :=
  interval_of_check cellTest_15104 120 8 (by decide +kernel)

theorem cellTest_15104_block_16 : Interval cellTest_15104 128 136 :=
  interval_of_check cellTest_15104 128 8 (by decide +kernel)

theorem cellTest_15104_block_17 : Interval cellTest_15104 136 142 :=
  interval_of_check cellTest_15104 136 6 (by decide +kernel)

theorem cellTest_15104_complete : Interval cellTest_15104 0 142 :=
  (interval_append cellTest_15104 0 72 142
  (interval_append cellTest_15104 0 32 72
  (interval_append cellTest_15104 0 16 32
  (interval_append cellTest_15104 0 8 16
  cellTest_15104_block_0
  cellTest_15104_block_1)
  (interval_append cellTest_15104 16 24 32
  cellTest_15104_block_2
  cellTest_15104_block_3))
  (interval_append cellTest_15104 32 48 72
  (interval_append cellTest_15104 32 40 48
  cellTest_15104_block_4
  cellTest_15104_block_5)
  (interval_append cellTest_15104 48 56 72
  cellTest_15104_block_6
  (interval_append cellTest_15104 56 64 72
  cellTest_15104_block_7
  cellTest_15104_block_8))))
  (interval_append cellTest_15104 72 104 142
  (interval_append cellTest_15104 72 88 104
  (interval_append cellTest_15104 72 80 88
  cellTest_15104_block_9
  cellTest_15104_block_10)
  (interval_append cellTest_15104 88 96 104
  cellTest_15104_block_11
  cellTest_15104_block_12))
  (interval_append cellTest_15104 104 120 142
  (interval_append cellTest_15104 104 112 120
  cellTest_15104_block_13
  cellTest_15104_block_14)
  (interval_append cellTest_15104 120 128 142
  cellTest_15104_block_15
  (interval_append cellTest_15104 128 136 142
  cellTest_15104_block_16
  cellTest_15104_block_17)))))
theorem cellTestInterval15104 : Interval cellTest 15104 15246 := by
  intro i hlo hhi
  have h := cellTest_15104_complete (i-15104) (Nat.zero_le _) (by omega)
  simpa only [cellTest_15104, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_0 (i : Nat) := badTest (i+0)
theorem badTest_0_block_0 : Interval badTest_0 0 8 :=
  interval_of_check badTest_0 0 8 (by decide +kernel)

theorem badTest_0_block_1 : Interval badTest_0 8 16 :=
  interval_of_check badTest_0 8 8 (by decide +kernel)

theorem badTest_0_block_2 : Interval badTest_0 16 24 :=
  interval_of_check badTest_0 16 8 (by decide +kernel)

theorem badTest_0_block_3 : Interval badTest_0 24 32 :=
  interval_of_check badTest_0 24 8 (by decide +kernel)

theorem badTest_0_block_4 : Interval badTest_0 32 40 :=
  interval_of_check badTest_0 32 8 (by decide +kernel)

theorem badTest_0_block_5 : Interval badTest_0 40 48 :=
  interval_of_check badTest_0 40 8 (by decide +kernel)

theorem badTest_0_block_6 : Interval badTest_0 48 56 :=
  interval_of_check badTest_0 48 8 (by decide +kernel)

theorem badTest_0_block_7 : Interval badTest_0 56 64 :=
  interval_of_check badTest_0 56 8 (by decide +kernel)

theorem badTest_0_block_8 : Interval badTest_0 64 72 :=
  interval_of_check badTest_0 64 8 (by decide +kernel)

theorem badTest_0_block_9 : Interval badTest_0 72 80 :=
  interval_of_check badTest_0 72 8 (by decide +kernel)

theorem badTest_0_block_10 : Interval badTest_0 80 88 :=
  interval_of_check badTest_0 80 8 (by decide +kernel)

theorem badTest_0_block_11 : Interval badTest_0 88 96 :=
  interval_of_check badTest_0 88 8 (by decide +kernel)

theorem badTest_0_block_12 : Interval badTest_0 96 104 :=
  interval_of_check badTest_0 96 8 (by decide +kernel)

theorem badTest_0_block_13 : Interval badTest_0 104 112 :=
  interval_of_check badTest_0 104 8 (by decide +kernel)

theorem badTest_0_block_14 : Interval badTest_0 112 120 :=
  interval_of_check badTest_0 112 8 (by decide +kernel)

theorem badTest_0_block_15 : Interval badTest_0 120 128 :=
  interval_of_check badTest_0 120 8 (by decide +kernel)

theorem badTest_0_block_16 : Interval badTest_0 128 136 :=
  interval_of_check badTest_0 128 8 (by decide +kernel)

theorem badTest_0_block_17 : Interval badTest_0 136 144 :=
  interval_of_check badTest_0 136 8 (by decide +kernel)

theorem badTest_0_block_18 : Interval badTest_0 144 152 :=
  interval_of_check badTest_0 144 8 (by decide +kernel)

theorem badTest_0_block_19 : Interval badTest_0 152 160 :=
  interval_of_check badTest_0 152 8 (by decide +kernel)

theorem badTest_0_block_20 : Interval badTest_0 160 168 :=
  interval_of_check badTest_0 160 8 (by decide +kernel)

theorem badTest_0_block_21 : Interval badTest_0 168 176 :=
  interval_of_check badTest_0 168 8 (by decide +kernel)

theorem badTest_0_block_22 : Interval badTest_0 176 184 :=
  interval_of_check badTest_0 176 8 (by decide +kernel)

theorem badTest_0_block_23 : Interval badTest_0 184 192 :=
  interval_of_check badTest_0 184 8 (by decide +kernel)

theorem badTest_0_block_24 : Interval badTest_0 192 200 :=
  interval_of_check badTest_0 192 8 (by decide +kernel)

theorem badTest_0_block_25 : Interval badTest_0 200 208 :=
  interval_of_check badTest_0 200 8 (by decide +kernel)

theorem badTest_0_block_26 : Interval badTest_0 208 216 :=
  interval_of_check badTest_0 208 8 (by decide +kernel)

theorem badTest_0_block_27 : Interval badTest_0 216 224 :=
  interval_of_check badTest_0 216 8 (by decide +kernel)

theorem badTest_0_block_28 : Interval badTest_0 224 232 :=
  interval_of_check badTest_0 224 8 (by decide +kernel)

theorem badTest_0_block_29 : Interval badTest_0 232 240 :=
  interval_of_check badTest_0 232 8 (by decide +kernel)

theorem badTest_0_block_30 : Interval badTest_0 240 248 :=
  interval_of_check badTest_0 240 8 (by decide +kernel)

theorem badTest_0_block_31 : Interval badTest_0 248 256 :=
  interval_of_check badTest_0 248 8 (by decide +kernel)

theorem badTest_0_complete : Interval badTest_0 0 256 :=
  (interval_append badTest_0 0 128 256
  (interval_append badTest_0 0 64 128
  (interval_append badTest_0 0 32 64
  (interval_append badTest_0 0 16 32
  (interval_append badTest_0 0 8 16
  badTest_0_block_0
  badTest_0_block_1)
  (interval_append badTest_0 16 24 32
  badTest_0_block_2
  badTest_0_block_3))
  (interval_append badTest_0 32 48 64
  (interval_append badTest_0 32 40 48
  badTest_0_block_4
  badTest_0_block_5)
  (interval_append badTest_0 48 56 64
  badTest_0_block_6
  badTest_0_block_7)))
  (interval_append badTest_0 64 96 128
  (interval_append badTest_0 64 80 96
  (interval_append badTest_0 64 72 80
  badTest_0_block_8
  badTest_0_block_9)
  (interval_append badTest_0 80 88 96
  badTest_0_block_10
  badTest_0_block_11))
  (interval_append badTest_0 96 112 128
  (interval_append badTest_0 96 104 112
  badTest_0_block_12
  badTest_0_block_13)
  (interval_append badTest_0 112 120 128
  badTest_0_block_14
  badTest_0_block_15))))
  (interval_append badTest_0 128 192 256
  (interval_append badTest_0 128 160 192
  (interval_append badTest_0 128 144 160
  (interval_append badTest_0 128 136 144
  badTest_0_block_16
  badTest_0_block_17)
  (interval_append badTest_0 144 152 160
  badTest_0_block_18
  badTest_0_block_19))
  (interval_append badTest_0 160 176 192
  (interval_append badTest_0 160 168 176
  badTest_0_block_20
  badTest_0_block_21)
  (interval_append badTest_0 176 184 192
  badTest_0_block_22
  badTest_0_block_23)))
  (interval_append badTest_0 192 224 256
  (interval_append badTest_0 192 208 224
  (interval_append badTest_0 192 200 208
  badTest_0_block_24
  badTest_0_block_25)
  (interval_append badTest_0 208 216 224
  badTest_0_block_26
  badTest_0_block_27))
  (interval_append badTest_0 224 240 256
  (interval_append badTest_0 224 232 240
  badTest_0_block_28
  badTest_0_block_29)
  (interval_append badTest_0 240 248 256
  badTest_0_block_30
  badTest_0_block_31)))))
theorem badTestInterval0 : Interval badTest 0 256 := by
  intro i hlo hhi
  have h := badTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [badTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_256 (i : Nat) := badTest (i+256)
theorem badTest_256_block_0 : Interval badTest_256 0 8 :=
  interval_of_check badTest_256 0 8 (by decide +kernel)

theorem badTest_256_block_1 : Interval badTest_256 8 16 :=
  interval_of_check badTest_256 8 8 (by decide +kernel)

theorem badTest_256_block_2 : Interval badTest_256 16 24 :=
  interval_of_check badTest_256 16 8 (by decide +kernel)

theorem badTest_256_block_3 : Interval badTest_256 24 32 :=
  interval_of_check badTest_256 24 8 (by decide +kernel)

theorem badTest_256_block_4 : Interval badTest_256 32 40 :=
  interval_of_check badTest_256 32 8 (by decide +kernel)

theorem badTest_256_block_5 : Interval badTest_256 40 48 :=
  interval_of_check badTest_256 40 8 (by decide +kernel)

theorem badTest_256_block_6 : Interval badTest_256 48 56 :=
  interval_of_check badTest_256 48 8 (by decide +kernel)

theorem badTest_256_block_7 : Interval badTest_256 56 64 :=
  interval_of_check badTest_256 56 8 (by decide +kernel)

theorem badTest_256_block_8 : Interval badTest_256 64 72 :=
  interval_of_check badTest_256 64 8 (by decide +kernel)

theorem badTest_256_block_9 : Interval badTest_256 72 80 :=
  interval_of_check badTest_256 72 8 (by decide +kernel)

theorem badTest_256_block_10 : Interval badTest_256 80 88 :=
  interval_of_check badTest_256 80 8 (by decide +kernel)

theorem badTest_256_block_11 : Interval badTest_256 88 96 :=
  interval_of_check badTest_256 88 8 (by decide +kernel)

theorem badTest_256_block_12 : Interval badTest_256 96 104 :=
  interval_of_check badTest_256 96 8 (by decide +kernel)

theorem badTest_256_block_13 : Interval badTest_256 104 112 :=
  interval_of_check badTest_256 104 8 (by decide +kernel)

theorem badTest_256_block_14 : Interval badTest_256 112 120 :=
  interval_of_check badTest_256 112 8 (by decide +kernel)

theorem badTest_256_block_15 : Interval badTest_256 120 128 :=
  interval_of_check badTest_256 120 8 (by decide +kernel)

theorem badTest_256_block_16 : Interval badTest_256 128 136 :=
  interval_of_check badTest_256 128 8 (by decide +kernel)

theorem badTest_256_block_17 : Interval badTest_256 136 144 :=
  interval_of_check badTest_256 136 8 (by decide +kernel)

theorem badTest_256_block_18 : Interval badTest_256 144 152 :=
  interval_of_check badTest_256 144 8 (by decide +kernel)

theorem badTest_256_block_19 : Interval badTest_256 152 160 :=
  interval_of_check badTest_256 152 8 (by decide +kernel)

theorem badTest_256_block_20 : Interval badTest_256 160 168 :=
  interval_of_check badTest_256 160 8 (by decide +kernel)

theorem badTest_256_block_21 : Interval badTest_256 168 176 :=
  interval_of_check badTest_256 168 8 (by decide +kernel)

theorem badTest_256_block_22 : Interval badTest_256 176 184 :=
  interval_of_check badTest_256 176 8 (by decide +kernel)

theorem badTest_256_block_23 : Interval badTest_256 184 192 :=
  interval_of_check badTest_256 184 8 (by decide +kernel)

theorem badTest_256_block_24 : Interval badTest_256 192 200 :=
  interval_of_check badTest_256 192 8 (by decide +kernel)

theorem badTest_256_block_25 : Interval badTest_256 200 208 :=
  interval_of_check badTest_256 200 8 (by decide +kernel)

theorem badTest_256_block_26 : Interval badTest_256 208 216 :=
  interval_of_check badTest_256 208 8 (by decide +kernel)

theorem badTest_256_block_27 : Interval badTest_256 216 224 :=
  interval_of_check badTest_256 216 8 (by decide +kernel)

theorem badTest_256_block_28 : Interval badTest_256 224 232 :=
  interval_of_check badTest_256 224 8 (by decide +kernel)

theorem badTest_256_block_29 : Interval badTest_256 232 240 :=
  interval_of_check badTest_256 232 8 (by decide +kernel)

theorem badTest_256_block_30 : Interval badTest_256 240 248 :=
  interval_of_check badTest_256 240 8 (by decide +kernel)

theorem badTest_256_block_31 : Interval badTest_256 248 256 :=
  interval_of_check badTest_256 248 8 (by decide +kernel)

theorem badTest_256_complete : Interval badTest_256 0 256 :=
  (interval_append badTest_256 0 128 256
  (interval_append badTest_256 0 64 128
  (interval_append badTest_256 0 32 64
  (interval_append badTest_256 0 16 32
  (interval_append badTest_256 0 8 16
  badTest_256_block_0
  badTest_256_block_1)
  (interval_append badTest_256 16 24 32
  badTest_256_block_2
  badTest_256_block_3))
  (interval_append badTest_256 32 48 64
  (interval_append badTest_256 32 40 48
  badTest_256_block_4
  badTest_256_block_5)
  (interval_append badTest_256 48 56 64
  badTest_256_block_6
  badTest_256_block_7)))
  (interval_append badTest_256 64 96 128
  (interval_append badTest_256 64 80 96
  (interval_append badTest_256 64 72 80
  badTest_256_block_8
  badTest_256_block_9)
  (interval_append badTest_256 80 88 96
  badTest_256_block_10
  badTest_256_block_11))
  (interval_append badTest_256 96 112 128
  (interval_append badTest_256 96 104 112
  badTest_256_block_12
  badTest_256_block_13)
  (interval_append badTest_256 112 120 128
  badTest_256_block_14
  badTest_256_block_15))))
  (interval_append badTest_256 128 192 256
  (interval_append badTest_256 128 160 192
  (interval_append badTest_256 128 144 160
  (interval_append badTest_256 128 136 144
  badTest_256_block_16
  badTest_256_block_17)
  (interval_append badTest_256 144 152 160
  badTest_256_block_18
  badTest_256_block_19))
  (interval_append badTest_256 160 176 192
  (interval_append badTest_256 160 168 176
  badTest_256_block_20
  badTest_256_block_21)
  (interval_append badTest_256 176 184 192
  badTest_256_block_22
  badTest_256_block_23)))
  (interval_append badTest_256 192 224 256
  (interval_append badTest_256 192 208 224
  (interval_append badTest_256 192 200 208
  badTest_256_block_24
  badTest_256_block_25)
  (interval_append badTest_256 208 216 224
  badTest_256_block_26
  badTest_256_block_27))
  (interval_append badTest_256 224 240 256
  (interval_append badTest_256 224 232 240
  badTest_256_block_28
  badTest_256_block_29)
  (interval_append badTest_256 240 248 256
  badTest_256_block_30
  badTest_256_block_31)))))
theorem badTestInterval256 : Interval badTest 256 512 := by
  intro i hlo hhi
  have h := badTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [badTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_512 (i : Nat) := badTest (i+512)
theorem badTest_512_block_0 : Interval badTest_512 0 8 :=
  interval_of_check badTest_512 0 8 (by decide +kernel)

theorem badTest_512_block_1 : Interval badTest_512 8 16 :=
  interval_of_check badTest_512 8 8 (by decide +kernel)

theorem badTest_512_block_2 : Interval badTest_512 16 24 :=
  interval_of_check badTest_512 16 8 (by decide +kernel)

theorem badTest_512_block_3 : Interval badTest_512 24 32 :=
  interval_of_check badTest_512 24 8 (by decide +kernel)

theorem badTest_512_block_4 : Interval badTest_512 32 40 :=
  interval_of_check badTest_512 32 8 (by decide +kernel)

theorem badTest_512_block_5 : Interval badTest_512 40 48 :=
  interval_of_check badTest_512 40 8 (by decide +kernel)

theorem badTest_512_block_6 : Interval badTest_512 48 56 :=
  interval_of_check badTest_512 48 8 (by decide +kernel)

theorem badTest_512_block_7 : Interval badTest_512 56 64 :=
  interval_of_check badTest_512 56 8 (by decide +kernel)

theorem badTest_512_block_8 : Interval badTest_512 64 72 :=
  interval_of_check badTest_512 64 8 (by decide +kernel)

theorem badTest_512_block_9 : Interval badTest_512 72 80 :=
  interval_of_check badTest_512 72 8 (by decide +kernel)

theorem badTest_512_block_10 : Interval badTest_512 80 88 :=
  interval_of_check badTest_512 80 8 (by decide +kernel)

theorem badTest_512_block_11 : Interval badTest_512 88 96 :=
  interval_of_check badTest_512 88 8 (by decide +kernel)

theorem badTest_512_block_12 : Interval badTest_512 96 104 :=
  interval_of_check badTest_512 96 8 (by decide +kernel)

theorem badTest_512_block_13 : Interval badTest_512 104 112 :=
  interval_of_check badTest_512 104 8 (by decide +kernel)

theorem badTest_512_block_14 : Interval badTest_512 112 120 :=
  interval_of_check badTest_512 112 8 (by decide +kernel)

theorem badTest_512_block_15 : Interval badTest_512 120 128 :=
  interval_of_check badTest_512 120 8 (by decide +kernel)

theorem badTest_512_block_16 : Interval badTest_512 128 136 :=
  interval_of_check badTest_512 128 8 (by decide +kernel)

theorem badTest_512_block_17 : Interval badTest_512 136 144 :=
  interval_of_check badTest_512 136 8 (by decide +kernel)

theorem badTest_512_block_18 : Interval badTest_512 144 152 :=
  interval_of_check badTest_512 144 8 (by decide +kernel)

theorem badTest_512_block_19 : Interval badTest_512 152 160 :=
  interval_of_check badTest_512 152 8 (by decide +kernel)

theorem badTest_512_block_20 : Interval badTest_512 160 168 :=
  interval_of_check badTest_512 160 8 (by decide +kernel)

theorem badTest_512_block_21 : Interval badTest_512 168 176 :=
  interval_of_check badTest_512 168 8 (by decide +kernel)

theorem badTest_512_block_22 : Interval badTest_512 176 184 :=
  interval_of_check badTest_512 176 8 (by decide +kernel)

theorem badTest_512_block_23 : Interval badTest_512 184 192 :=
  interval_of_check badTest_512 184 8 (by decide +kernel)

theorem badTest_512_block_24 : Interval badTest_512 192 200 :=
  interval_of_check badTest_512 192 8 (by decide +kernel)

theorem badTest_512_block_25 : Interval badTest_512 200 208 :=
  interval_of_check badTest_512 200 8 (by decide +kernel)

theorem badTest_512_block_26 : Interval badTest_512 208 216 :=
  interval_of_check badTest_512 208 8 (by decide +kernel)

theorem badTest_512_block_27 : Interval badTest_512 216 224 :=
  interval_of_check badTest_512 216 8 (by decide +kernel)

theorem badTest_512_block_28 : Interval badTest_512 224 232 :=
  interval_of_check badTest_512 224 8 (by decide +kernel)

theorem badTest_512_block_29 : Interval badTest_512 232 240 :=
  interval_of_check badTest_512 232 8 (by decide +kernel)

theorem badTest_512_block_30 : Interval badTest_512 240 248 :=
  interval_of_check badTest_512 240 8 (by decide +kernel)

theorem badTest_512_block_31 : Interval badTest_512 248 256 :=
  interval_of_check badTest_512 248 8 (by decide +kernel)

theorem badTest_512_complete : Interval badTest_512 0 256 :=
  (interval_append badTest_512 0 128 256
  (interval_append badTest_512 0 64 128
  (interval_append badTest_512 0 32 64
  (interval_append badTest_512 0 16 32
  (interval_append badTest_512 0 8 16
  badTest_512_block_0
  badTest_512_block_1)
  (interval_append badTest_512 16 24 32
  badTest_512_block_2
  badTest_512_block_3))
  (interval_append badTest_512 32 48 64
  (interval_append badTest_512 32 40 48
  badTest_512_block_4
  badTest_512_block_5)
  (interval_append badTest_512 48 56 64
  badTest_512_block_6
  badTest_512_block_7)))
  (interval_append badTest_512 64 96 128
  (interval_append badTest_512 64 80 96
  (interval_append badTest_512 64 72 80
  badTest_512_block_8
  badTest_512_block_9)
  (interval_append badTest_512 80 88 96
  badTest_512_block_10
  badTest_512_block_11))
  (interval_append badTest_512 96 112 128
  (interval_append badTest_512 96 104 112
  badTest_512_block_12
  badTest_512_block_13)
  (interval_append badTest_512 112 120 128
  badTest_512_block_14
  badTest_512_block_15))))
  (interval_append badTest_512 128 192 256
  (interval_append badTest_512 128 160 192
  (interval_append badTest_512 128 144 160
  (interval_append badTest_512 128 136 144
  badTest_512_block_16
  badTest_512_block_17)
  (interval_append badTest_512 144 152 160
  badTest_512_block_18
  badTest_512_block_19))
  (interval_append badTest_512 160 176 192
  (interval_append badTest_512 160 168 176
  badTest_512_block_20
  badTest_512_block_21)
  (interval_append badTest_512 176 184 192
  badTest_512_block_22
  badTest_512_block_23)))
  (interval_append badTest_512 192 224 256
  (interval_append badTest_512 192 208 224
  (interval_append badTest_512 192 200 208
  badTest_512_block_24
  badTest_512_block_25)
  (interval_append badTest_512 208 216 224
  badTest_512_block_26
  badTest_512_block_27))
  (interval_append badTest_512 224 240 256
  (interval_append badTest_512 224 232 240
  badTest_512_block_28
  badTest_512_block_29)
  (interval_append badTest_512 240 248 256
  badTest_512_block_30
  badTest_512_block_31)))))
theorem badTestInterval512 : Interval badTest 512 768 := by
  intro i hlo hhi
  have h := badTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [badTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_768 (i : Nat) := badTest (i+768)
theorem badTest_768_block_0 : Interval badTest_768 0 8 :=
  interval_of_check badTest_768 0 8 (by decide +kernel)

theorem badTest_768_block_1 : Interval badTest_768 8 16 :=
  interval_of_check badTest_768 8 8 (by decide +kernel)

theorem badTest_768_block_2 : Interval badTest_768 16 24 :=
  interval_of_check badTest_768 16 8 (by decide +kernel)

theorem badTest_768_block_3 : Interval badTest_768 24 32 :=
  interval_of_check badTest_768 24 8 (by decide +kernel)

theorem badTest_768_block_4 : Interval badTest_768 32 40 :=
  interval_of_check badTest_768 32 8 (by decide +kernel)

theorem badTest_768_block_5 : Interval badTest_768 40 48 :=
  interval_of_check badTest_768 40 8 (by decide +kernel)

theorem badTest_768_block_6 : Interval badTest_768 48 56 :=
  interval_of_check badTest_768 48 8 (by decide +kernel)

theorem badTest_768_block_7 : Interval badTest_768 56 64 :=
  interval_of_check badTest_768 56 8 (by decide +kernel)

theorem badTest_768_block_8 : Interval badTest_768 64 72 :=
  interval_of_check badTest_768 64 8 (by decide +kernel)

theorem badTest_768_block_9 : Interval badTest_768 72 80 :=
  interval_of_check badTest_768 72 8 (by decide +kernel)

theorem badTest_768_block_10 : Interval badTest_768 80 88 :=
  interval_of_check badTest_768 80 8 (by decide +kernel)

theorem badTest_768_block_11 : Interval badTest_768 88 96 :=
  interval_of_check badTest_768 88 8 (by decide +kernel)

theorem badTest_768_block_12 : Interval badTest_768 96 104 :=
  interval_of_check badTest_768 96 8 (by decide +kernel)

theorem badTest_768_block_13 : Interval badTest_768 104 112 :=
  interval_of_check badTest_768 104 8 (by decide +kernel)

theorem badTest_768_block_14 : Interval badTest_768 112 120 :=
  interval_of_check badTest_768 112 8 (by decide +kernel)

theorem badTest_768_block_15 : Interval badTest_768 120 128 :=
  interval_of_check badTest_768 120 8 (by decide +kernel)

theorem badTest_768_block_16 : Interval badTest_768 128 136 :=
  interval_of_check badTest_768 128 8 (by decide +kernel)

theorem badTest_768_block_17 : Interval badTest_768 136 144 :=
  interval_of_check badTest_768 136 8 (by decide +kernel)

theorem badTest_768_block_18 : Interval badTest_768 144 152 :=
  interval_of_check badTest_768 144 8 (by decide +kernel)

theorem badTest_768_block_19 : Interval badTest_768 152 160 :=
  interval_of_check badTest_768 152 8 (by decide +kernel)

theorem badTest_768_block_20 : Interval badTest_768 160 168 :=
  interval_of_check badTest_768 160 8 (by decide +kernel)

theorem badTest_768_block_21 : Interval badTest_768 168 176 :=
  interval_of_check badTest_768 168 8 (by decide +kernel)

theorem badTest_768_block_22 : Interval badTest_768 176 184 :=
  interval_of_check badTest_768 176 8 (by decide +kernel)

theorem badTest_768_block_23 : Interval badTest_768 184 192 :=
  interval_of_check badTest_768 184 8 (by decide +kernel)

theorem badTest_768_block_24 : Interval badTest_768 192 200 :=
  interval_of_check badTest_768 192 8 (by decide +kernel)

theorem badTest_768_block_25 : Interval badTest_768 200 208 :=
  interval_of_check badTest_768 200 8 (by decide +kernel)

theorem badTest_768_block_26 : Interval badTest_768 208 216 :=
  interval_of_check badTest_768 208 8 (by decide +kernel)

theorem badTest_768_block_27 : Interval badTest_768 216 224 :=
  interval_of_check badTest_768 216 8 (by decide +kernel)

theorem badTest_768_block_28 : Interval badTest_768 224 232 :=
  interval_of_check badTest_768 224 8 (by decide +kernel)

theorem badTest_768_block_29 : Interval badTest_768 232 240 :=
  interval_of_check badTest_768 232 8 (by decide +kernel)

theorem badTest_768_block_30 : Interval badTest_768 240 248 :=
  interval_of_check badTest_768 240 8 (by decide +kernel)

theorem badTest_768_block_31 : Interval badTest_768 248 256 :=
  interval_of_check badTest_768 248 8 (by decide +kernel)

theorem badTest_768_complete : Interval badTest_768 0 256 :=
  (interval_append badTest_768 0 128 256
  (interval_append badTest_768 0 64 128
  (interval_append badTest_768 0 32 64
  (interval_append badTest_768 0 16 32
  (interval_append badTest_768 0 8 16
  badTest_768_block_0
  badTest_768_block_1)
  (interval_append badTest_768 16 24 32
  badTest_768_block_2
  badTest_768_block_3))
  (interval_append badTest_768 32 48 64
  (interval_append badTest_768 32 40 48
  badTest_768_block_4
  badTest_768_block_5)
  (interval_append badTest_768 48 56 64
  badTest_768_block_6
  badTest_768_block_7)))
  (interval_append badTest_768 64 96 128
  (interval_append badTest_768 64 80 96
  (interval_append badTest_768 64 72 80
  badTest_768_block_8
  badTest_768_block_9)
  (interval_append badTest_768 80 88 96
  badTest_768_block_10
  badTest_768_block_11))
  (interval_append badTest_768 96 112 128
  (interval_append badTest_768 96 104 112
  badTest_768_block_12
  badTest_768_block_13)
  (interval_append badTest_768 112 120 128
  badTest_768_block_14
  badTest_768_block_15))))
  (interval_append badTest_768 128 192 256
  (interval_append badTest_768 128 160 192
  (interval_append badTest_768 128 144 160
  (interval_append badTest_768 128 136 144
  badTest_768_block_16
  badTest_768_block_17)
  (interval_append badTest_768 144 152 160
  badTest_768_block_18
  badTest_768_block_19))
  (interval_append badTest_768 160 176 192
  (interval_append badTest_768 160 168 176
  badTest_768_block_20
  badTest_768_block_21)
  (interval_append badTest_768 176 184 192
  badTest_768_block_22
  badTest_768_block_23)))
  (interval_append badTest_768 192 224 256
  (interval_append badTest_768 192 208 224
  (interval_append badTest_768 192 200 208
  badTest_768_block_24
  badTest_768_block_25)
  (interval_append badTest_768 208 216 224
  badTest_768_block_26
  badTest_768_block_27))
  (interval_append badTest_768 224 240 256
  (interval_append badTest_768 224 232 240
  badTest_768_block_28
  badTest_768_block_29)
  (interval_append badTest_768 240 248 256
  badTest_768_block_30
  badTest_768_block_31)))))
theorem badTestInterval768 : Interval badTest 768 1024 := by
  intro i hlo hhi
  have h := badTest_768_complete (i-768) (Nat.zero_le _) (by omega)
  simpa only [badTest_768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
