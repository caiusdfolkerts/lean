module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheCells064 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_16384 (i : Nat) := cellTest (i+16384)
theorem cellTest_16384_block_0 : Interval cellTest_16384 0 8 :=
  interval_of_check cellTest_16384 0 8 (by decide +kernel)

theorem cellTest_16384_block_1 : Interval cellTest_16384 8 16 :=
  interval_of_check cellTest_16384 8 8 (by decide +kernel)

theorem cellTest_16384_block_2 : Interval cellTest_16384 16 24 :=
  interval_of_check cellTest_16384 16 8 (by decide +kernel)

theorem cellTest_16384_block_3 : Interval cellTest_16384 24 32 :=
  interval_of_check cellTest_16384 24 8 (by decide +kernel)

theorem cellTest_16384_block_4 : Interval cellTest_16384 32 40 :=
  interval_of_check cellTest_16384 32 8 (by decide +kernel)

theorem cellTest_16384_block_5 : Interval cellTest_16384 40 48 :=
  interval_of_check cellTest_16384 40 8 (by decide +kernel)

theorem cellTest_16384_block_6 : Interval cellTest_16384 48 56 :=
  interval_of_check cellTest_16384 48 8 (by decide +kernel)

theorem cellTest_16384_block_7 : Interval cellTest_16384 56 64 :=
  interval_of_check cellTest_16384 56 8 (by decide +kernel)

theorem cellTest_16384_block_8 : Interval cellTest_16384 64 72 :=
  interval_of_check cellTest_16384 64 8 (by decide +kernel)

theorem cellTest_16384_block_9 : Interval cellTest_16384 72 80 :=
  interval_of_check cellTest_16384 72 8 (by decide +kernel)

theorem cellTest_16384_block_10 : Interval cellTest_16384 80 88 :=
  interval_of_check cellTest_16384 80 8 (by decide +kernel)

theorem cellTest_16384_block_11 : Interval cellTest_16384 88 96 :=
  interval_of_check cellTest_16384 88 8 (by decide +kernel)

theorem cellTest_16384_block_12 : Interval cellTest_16384 96 104 :=
  interval_of_check cellTest_16384 96 8 (by decide +kernel)

theorem cellTest_16384_block_13 : Interval cellTest_16384 104 112 :=
  interval_of_check cellTest_16384 104 8 (by decide +kernel)

theorem cellTest_16384_block_14 : Interval cellTest_16384 112 120 :=
  interval_of_check cellTest_16384 112 8 (by decide +kernel)

theorem cellTest_16384_block_15 : Interval cellTest_16384 120 128 :=
  interval_of_check cellTest_16384 120 8 (by decide +kernel)

theorem cellTest_16384_block_16 : Interval cellTest_16384 128 136 :=
  interval_of_check cellTest_16384 128 8 (by decide +kernel)

theorem cellTest_16384_block_17 : Interval cellTest_16384 136 144 :=
  interval_of_check cellTest_16384 136 8 (by decide +kernel)

theorem cellTest_16384_block_18 : Interval cellTest_16384 144 152 :=
  interval_of_check cellTest_16384 144 8 (by decide +kernel)

theorem cellTest_16384_block_19 : Interval cellTest_16384 152 160 :=
  interval_of_check cellTest_16384 152 8 (by decide +kernel)

theorem cellTest_16384_block_20 : Interval cellTest_16384 160 168 :=
  interval_of_check cellTest_16384 160 8 (by decide +kernel)

theorem cellTest_16384_block_21 : Interval cellTest_16384 168 176 :=
  interval_of_check cellTest_16384 168 8 (by decide +kernel)

theorem cellTest_16384_block_22 : Interval cellTest_16384 176 184 :=
  interval_of_check cellTest_16384 176 8 (by decide +kernel)

theorem cellTest_16384_block_23 : Interval cellTest_16384 184 192 :=
  interval_of_check cellTest_16384 184 8 (by decide +kernel)

theorem cellTest_16384_block_24 : Interval cellTest_16384 192 200 :=
  interval_of_check cellTest_16384 192 8 (by decide +kernel)

theorem cellTest_16384_block_25 : Interval cellTest_16384 200 208 :=
  interval_of_check cellTest_16384 200 8 (by decide +kernel)

theorem cellTest_16384_block_26 : Interval cellTest_16384 208 216 :=
  interval_of_check cellTest_16384 208 8 (by decide +kernel)

theorem cellTest_16384_block_27 : Interval cellTest_16384 216 224 :=
  interval_of_check cellTest_16384 216 8 (by decide +kernel)

theorem cellTest_16384_block_28 : Interval cellTest_16384 224 232 :=
  interval_of_check cellTest_16384 224 8 (by decide +kernel)

theorem cellTest_16384_block_29 : Interval cellTest_16384 232 240 :=
  interval_of_check cellTest_16384 232 8 (by decide +kernel)

theorem cellTest_16384_block_30 : Interval cellTest_16384 240 248 :=
  interval_of_check cellTest_16384 240 8 (by decide +kernel)

theorem cellTest_16384_block_31 : Interval cellTest_16384 248 256 :=
  interval_of_check cellTest_16384 248 8 (by decide +kernel)

theorem cellTest_16384_complete : Interval cellTest_16384 0 256 :=
  (interval_append cellTest_16384 0 128 256
  (interval_append cellTest_16384 0 64 128
  (interval_append cellTest_16384 0 32 64
  (interval_append cellTest_16384 0 16 32
  (interval_append cellTest_16384 0 8 16
  cellTest_16384_block_0
  cellTest_16384_block_1)
  (interval_append cellTest_16384 16 24 32
  cellTest_16384_block_2
  cellTest_16384_block_3))
  (interval_append cellTest_16384 32 48 64
  (interval_append cellTest_16384 32 40 48
  cellTest_16384_block_4
  cellTest_16384_block_5)
  (interval_append cellTest_16384 48 56 64
  cellTest_16384_block_6
  cellTest_16384_block_7)))
  (interval_append cellTest_16384 64 96 128
  (interval_append cellTest_16384 64 80 96
  (interval_append cellTest_16384 64 72 80
  cellTest_16384_block_8
  cellTest_16384_block_9)
  (interval_append cellTest_16384 80 88 96
  cellTest_16384_block_10
  cellTest_16384_block_11))
  (interval_append cellTest_16384 96 112 128
  (interval_append cellTest_16384 96 104 112
  cellTest_16384_block_12
  cellTest_16384_block_13)
  (interval_append cellTest_16384 112 120 128
  cellTest_16384_block_14
  cellTest_16384_block_15))))
  (interval_append cellTest_16384 128 192 256
  (interval_append cellTest_16384 128 160 192
  (interval_append cellTest_16384 128 144 160
  (interval_append cellTest_16384 128 136 144
  cellTest_16384_block_16
  cellTest_16384_block_17)
  (interval_append cellTest_16384 144 152 160
  cellTest_16384_block_18
  cellTest_16384_block_19))
  (interval_append cellTest_16384 160 176 192
  (interval_append cellTest_16384 160 168 176
  cellTest_16384_block_20
  cellTest_16384_block_21)
  (interval_append cellTest_16384 176 184 192
  cellTest_16384_block_22
  cellTest_16384_block_23)))
  (interval_append cellTest_16384 192 224 256
  (interval_append cellTest_16384 192 208 224
  (interval_append cellTest_16384 192 200 208
  cellTest_16384_block_24
  cellTest_16384_block_25)
  (interval_append cellTest_16384 208 216 224
  cellTest_16384_block_26
  cellTest_16384_block_27))
  (interval_append cellTest_16384 224 240 256
  (interval_append cellTest_16384 224 232 240
  cellTest_16384_block_28
  cellTest_16384_block_29)
  (interval_append cellTest_16384 240 248 256
  cellTest_16384_block_30
  cellTest_16384_block_31)))))
theorem cellTestInterval16384 : Interval cellTest 16384 16640 := by
  intro i hlo hhi
  have h := cellTest_16384_complete (i-16384) (Nat.zero_le _) (by omega)
  simpa only [cellTest_16384, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells065 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_16640 (i : Nat) := cellTest (i+16640)
theorem cellTest_16640_block_0 : Interval cellTest_16640 0 8 :=
  interval_of_check cellTest_16640 0 8 (by decide +kernel)

theorem cellTest_16640_block_1 : Interval cellTest_16640 8 16 :=
  interval_of_check cellTest_16640 8 8 (by decide +kernel)

theorem cellTest_16640_block_2 : Interval cellTest_16640 16 24 :=
  interval_of_check cellTest_16640 16 8 (by decide +kernel)

theorem cellTest_16640_block_3 : Interval cellTest_16640 24 32 :=
  interval_of_check cellTest_16640 24 8 (by decide +kernel)

theorem cellTest_16640_block_4 : Interval cellTest_16640 32 40 :=
  interval_of_check cellTest_16640 32 8 (by decide +kernel)

theorem cellTest_16640_block_5 : Interval cellTest_16640 40 48 :=
  interval_of_check cellTest_16640 40 8 (by decide +kernel)

theorem cellTest_16640_block_6 : Interval cellTest_16640 48 56 :=
  interval_of_check cellTest_16640 48 8 (by decide +kernel)

theorem cellTest_16640_block_7 : Interval cellTest_16640 56 64 :=
  interval_of_check cellTest_16640 56 8 (by decide +kernel)

theorem cellTest_16640_block_8 : Interval cellTest_16640 64 72 :=
  interval_of_check cellTest_16640 64 8 (by decide +kernel)

theorem cellTest_16640_block_9 : Interval cellTest_16640 72 80 :=
  interval_of_check cellTest_16640 72 8 (by decide +kernel)

theorem cellTest_16640_block_10 : Interval cellTest_16640 80 88 :=
  interval_of_check cellTest_16640 80 8 (by decide +kernel)

theorem cellTest_16640_block_11 : Interval cellTest_16640 88 96 :=
  interval_of_check cellTest_16640 88 8 (by decide +kernel)

theorem cellTest_16640_block_12 : Interval cellTest_16640 96 104 :=
  interval_of_check cellTest_16640 96 8 (by decide +kernel)

theorem cellTest_16640_block_13 : Interval cellTest_16640 104 112 :=
  interval_of_check cellTest_16640 104 8 (by decide +kernel)

theorem cellTest_16640_block_14 : Interval cellTest_16640 112 120 :=
  interval_of_check cellTest_16640 112 8 (by decide +kernel)

theorem cellTest_16640_block_15 : Interval cellTest_16640 120 128 :=
  interval_of_check cellTest_16640 120 8 (by decide +kernel)

theorem cellTest_16640_block_16 : Interval cellTest_16640 128 136 :=
  interval_of_check cellTest_16640 128 8 (by decide +kernel)

theorem cellTest_16640_block_17 : Interval cellTest_16640 136 144 :=
  interval_of_check cellTest_16640 136 8 (by decide +kernel)

theorem cellTest_16640_block_18 : Interval cellTest_16640 144 152 :=
  interval_of_check cellTest_16640 144 8 (by decide +kernel)

theorem cellTest_16640_block_19 : Interval cellTest_16640 152 160 :=
  interval_of_check cellTest_16640 152 8 (by decide +kernel)

theorem cellTest_16640_block_20 : Interval cellTest_16640 160 168 :=
  interval_of_check cellTest_16640 160 8 (by decide +kernel)

theorem cellTest_16640_block_21 : Interval cellTest_16640 168 176 :=
  interval_of_check cellTest_16640 168 8 (by decide +kernel)

theorem cellTest_16640_block_22 : Interval cellTest_16640 176 184 :=
  interval_of_check cellTest_16640 176 8 (by decide +kernel)

theorem cellTest_16640_block_23 : Interval cellTest_16640 184 192 :=
  interval_of_check cellTest_16640 184 8 (by decide +kernel)

theorem cellTest_16640_block_24 : Interval cellTest_16640 192 200 :=
  interval_of_check cellTest_16640 192 8 (by decide +kernel)

theorem cellTest_16640_block_25 : Interval cellTest_16640 200 208 :=
  interval_of_check cellTest_16640 200 8 (by decide +kernel)

theorem cellTest_16640_block_26 : Interval cellTest_16640 208 216 :=
  interval_of_check cellTest_16640 208 8 (by decide +kernel)

theorem cellTest_16640_block_27 : Interval cellTest_16640 216 224 :=
  interval_of_check cellTest_16640 216 8 (by decide +kernel)

theorem cellTest_16640_block_28 : Interval cellTest_16640 224 232 :=
  interval_of_check cellTest_16640 224 8 (by decide +kernel)

theorem cellTest_16640_block_29 : Interval cellTest_16640 232 240 :=
  interval_of_check cellTest_16640 232 8 (by decide +kernel)

theorem cellTest_16640_block_30 : Interval cellTest_16640 240 248 :=
  interval_of_check cellTest_16640 240 8 (by decide +kernel)

theorem cellTest_16640_block_31 : Interval cellTest_16640 248 256 :=
  interval_of_check cellTest_16640 248 8 (by decide +kernel)

theorem cellTest_16640_complete : Interval cellTest_16640 0 256 :=
  (interval_append cellTest_16640 0 128 256
  (interval_append cellTest_16640 0 64 128
  (interval_append cellTest_16640 0 32 64
  (interval_append cellTest_16640 0 16 32
  (interval_append cellTest_16640 0 8 16
  cellTest_16640_block_0
  cellTest_16640_block_1)
  (interval_append cellTest_16640 16 24 32
  cellTest_16640_block_2
  cellTest_16640_block_3))
  (interval_append cellTest_16640 32 48 64
  (interval_append cellTest_16640 32 40 48
  cellTest_16640_block_4
  cellTest_16640_block_5)
  (interval_append cellTest_16640 48 56 64
  cellTest_16640_block_6
  cellTest_16640_block_7)))
  (interval_append cellTest_16640 64 96 128
  (interval_append cellTest_16640 64 80 96
  (interval_append cellTest_16640 64 72 80
  cellTest_16640_block_8
  cellTest_16640_block_9)
  (interval_append cellTest_16640 80 88 96
  cellTest_16640_block_10
  cellTest_16640_block_11))
  (interval_append cellTest_16640 96 112 128
  (interval_append cellTest_16640 96 104 112
  cellTest_16640_block_12
  cellTest_16640_block_13)
  (interval_append cellTest_16640 112 120 128
  cellTest_16640_block_14
  cellTest_16640_block_15))))
  (interval_append cellTest_16640 128 192 256
  (interval_append cellTest_16640 128 160 192
  (interval_append cellTest_16640 128 144 160
  (interval_append cellTest_16640 128 136 144
  cellTest_16640_block_16
  cellTest_16640_block_17)
  (interval_append cellTest_16640 144 152 160
  cellTest_16640_block_18
  cellTest_16640_block_19))
  (interval_append cellTest_16640 160 176 192
  (interval_append cellTest_16640 160 168 176
  cellTest_16640_block_20
  cellTest_16640_block_21)
  (interval_append cellTest_16640 176 184 192
  cellTest_16640_block_22
  cellTest_16640_block_23)))
  (interval_append cellTest_16640 192 224 256
  (interval_append cellTest_16640 192 208 224
  (interval_append cellTest_16640 192 200 208
  cellTest_16640_block_24
  cellTest_16640_block_25)
  (interval_append cellTest_16640 208 216 224
  cellTest_16640_block_26
  cellTest_16640_block_27))
  (interval_append cellTest_16640 224 240 256
  (interval_append cellTest_16640 224 232 240
  cellTest_16640_block_28
  cellTest_16640_block_29)
  (interval_append cellTest_16640 240 248 256
  cellTest_16640_block_30
  cellTest_16640_block_31)))))
theorem cellTestInterval16640 : Interval cellTest 16640 16896 := by
  intro i hlo hhi
  have h := cellTest_16640_complete (i-16640) (Nat.zero_le _) (by omega)
  simpa only [cellTest_16640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells066 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_16896 (i : Nat) := cellTest (i+16896)
theorem cellTest_16896_block_0 : Interval cellTest_16896 0 8 :=
  interval_of_check cellTest_16896 0 8 (by decide +kernel)

theorem cellTest_16896_block_1 : Interval cellTest_16896 8 16 :=
  interval_of_check cellTest_16896 8 8 (by decide +kernel)

theorem cellTest_16896_block_2 : Interval cellTest_16896 16 24 :=
  interval_of_check cellTest_16896 16 8 (by decide +kernel)

theorem cellTest_16896_block_3 : Interval cellTest_16896 24 32 :=
  interval_of_check cellTest_16896 24 8 (by decide +kernel)

theorem cellTest_16896_block_4 : Interval cellTest_16896 32 40 :=
  interval_of_check cellTest_16896 32 8 (by decide +kernel)

theorem cellTest_16896_block_5 : Interval cellTest_16896 40 48 :=
  interval_of_check cellTest_16896 40 8 (by decide +kernel)

theorem cellTest_16896_block_6 : Interval cellTest_16896 48 56 :=
  interval_of_check cellTest_16896 48 8 (by decide +kernel)

theorem cellTest_16896_block_7 : Interval cellTest_16896 56 64 :=
  interval_of_check cellTest_16896 56 8 (by decide +kernel)

theorem cellTest_16896_block_8 : Interval cellTest_16896 64 72 :=
  interval_of_check cellTest_16896 64 8 (by decide +kernel)

theorem cellTest_16896_block_9 : Interval cellTest_16896 72 80 :=
  interval_of_check cellTest_16896 72 8 (by decide +kernel)

theorem cellTest_16896_block_10 : Interval cellTest_16896 80 88 :=
  interval_of_check cellTest_16896 80 8 (by decide +kernel)

theorem cellTest_16896_block_11 : Interval cellTest_16896 88 96 :=
  interval_of_check cellTest_16896 88 8 (by decide +kernel)

theorem cellTest_16896_block_12 : Interval cellTest_16896 96 104 :=
  interval_of_check cellTest_16896 96 8 (by decide +kernel)

theorem cellTest_16896_block_13 : Interval cellTest_16896 104 112 :=
  interval_of_check cellTest_16896 104 8 (by decide +kernel)

theorem cellTest_16896_block_14 : Interval cellTest_16896 112 120 :=
  interval_of_check cellTest_16896 112 8 (by decide +kernel)

theorem cellTest_16896_block_15 : Interval cellTest_16896 120 128 :=
  interval_of_check cellTest_16896 120 8 (by decide +kernel)

theorem cellTest_16896_block_16 : Interval cellTest_16896 128 136 :=
  interval_of_check cellTest_16896 128 8 (by decide +kernel)

theorem cellTest_16896_block_17 : Interval cellTest_16896 136 144 :=
  interval_of_check cellTest_16896 136 8 (by decide +kernel)

theorem cellTest_16896_block_18 : Interval cellTest_16896 144 152 :=
  interval_of_check cellTest_16896 144 8 (by decide +kernel)

theorem cellTest_16896_block_19 : Interval cellTest_16896 152 160 :=
  interval_of_check cellTest_16896 152 8 (by decide +kernel)

theorem cellTest_16896_block_20 : Interval cellTest_16896 160 168 :=
  interval_of_check cellTest_16896 160 8 (by decide +kernel)

theorem cellTest_16896_block_21 : Interval cellTest_16896 168 176 :=
  interval_of_check cellTest_16896 168 8 (by decide +kernel)

theorem cellTest_16896_block_22 : Interval cellTest_16896 176 184 :=
  interval_of_check cellTest_16896 176 8 (by decide +kernel)

theorem cellTest_16896_block_23 : Interval cellTest_16896 184 192 :=
  interval_of_check cellTest_16896 184 8 (by decide +kernel)

theorem cellTest_16896_block_24 : Interval cellTest_16896 192 200 :=
  interval_of_check cellTest_16896 192 8 (by decide +kernel)

theorem cellTest_16896_block_25 : Interval cellTest_16896 200 208 :=
  interval_of_check cellTest_16896 200 8 (by decide +kernel)

theorem cellTest_16896_block_26 : Interval cellTest_16896 208 216 :=
  interval_of_check cellTest_16896 208 8 (by decide +kernel)

theorem cellTest_16896_block_27 : Interval cellTest_16896 216 224 :=
  interval_of_check cellTest_16896 216 8 (by decide +kernel)

theorem cellTest_16896_block_28 : Interval cellTest_16896 224 232 :=
  interval_of_check cellTest_16896 224 8 (by decide +kernel)

theorem cellTest_16896_block_29 : Interval cellTest_16896 232 240 :=
  interval_of_check cellTest_16896 232 8 (by decide +kernel)

theorem cellTest_16896_block_30 : Interval cellTest_16896 240 248 :=
  interval_of_check cellTest_16896 240 8 (by decide +kernel)

theorem cellTest_16896_block_31 : Interval cellTest_16896 248 256 :=
  interval_of_check cellTest_16896 248 8 (by decide +kernel)

theorem cellTest_16896_complete : Interval cellTest_16896 0 256 :=
  (interval_append cellTest_16896 0 128 256
  (interval_append cellTest_16896 0 64 128
  (interval_append cellTest_16896 0 32 64
  (interval_append cellTest_16896 0 16 32
  (interval_append cellTest_16896 0 8 16
  cellTest_16896_block_0
  cellTest_16896_block_1)
  (interval_append cellTest_16896 16 24 32
  cellTest_16896_block_2
  cellTest_16896_block_3))
  (interval_append cellTest_16896 32 48 64
  (interval_append cellTest_16896 32 40 48
  cellTest_16896_block_4
  cellTest_16896_block_5)
  (interval_append cellTest_16896 48 56 64
  cellTest_16896_block_6
  cellTest_16896_block_7)))
  (interval_append cellTest_16896 64 96 128
  (interval_append cellTest_16896 64 80 96
  (interval_append cellTest_16896 64 72 80
  cellTest_16896_block_8
  cellTest_16896_block_9)
  (interval_append cellTest_16896 80 88 96
  cellTest_16896_block_10
  cellTest_16896_block_11))
  (interval_append cellTest_16896 96 112 128
  (interval_append cellTest_16896 96 104 112
  cellTest_16896_block_12
  cellTest_16896_block_13)
  (interval_append cellTest_16896 112 120 128
  cellTest_16896_block_14
  cellTest_16896_block_15))))
  (interval_append cellTest_16896 128 192 256
  (interval_append cellTest_16896 128 160 192
  (interval_append cellTest_16896 128 144 160
  (interval_append cellTest_16896 128 136 144
  cellTest_16896_block_16
  cellTest_16896_block_17)
  (interval_append cellTest_16896 144 152 160
  cellTest_16896_block_18
  cellTest_16896_block_19))
  (interval_append cellTest_16896 160 176 192
  (interval_append cellTest_16896 160 168 176
  cellTest_16896_block_20
  cellTest_16896_block_21)
  (interval_append cellTest_16896 176 184 192
  cellTest_16896_block_22
  cellTest_16896_block_23)))
  (interval_append cellTest_16896 192 224 256
  (interval_append cellTest_16896 192 208 224
  (interval_append cellTest_16896 192 200 208
  cellTest_16896_block_24
  cellTest_16896_block_25)
  (interval_append cellTest_16896 208 216 224
  cellTest_16896_block_26
  cellTest_16896_block_27))
  (interval_append cellTest_16896 224 240 256
  (interval_append cellTest_16896 224 232 240
  cellTest_16896_block_28
  cellTest_16896_block_29)
  (interval_append cellTest_16896 240 248 256
  cellTest_16896_block_30
  cellTest_16896_block_31)))))
theorem cellTestInterval16896 : Interval cellTest 16896 17152 := by
  intro i hlo hhi
  have h := cellTest_16896_complete (i-16896) (Nat.zero_le _) (by omega)
  simpa only [cellTest_16896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells067 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_17152 (i : Nat) := cellTest (i+17152)
theorem cellTest_17152_block_0 : Interval cellTest_17152 0 8 :=
  interval_of_check cellTest_17152 0 8 (by decide +kernel)

theorem cellTest_17152_block_1 : Interval cellTest_17152 8 16 :=
  interval_of_check cellTest_17152 8 8 (by decide +kernel)

theorem cellTest_17152_block_2 : Interval cellTest_17152 16 24 :=
  interval_of_check cellTest_17152 16 8 (by decide +kernel)

theorem cellTest_17152_block_3 : Interval cellTest_17152 24 32 :=
  interval_of_check cellTest_17152 24 8 (by decide +kernel)

theorem cellTest_17152_block_4 : Interval cellTest_17152 32 40 :=
  interval_of_check cellTest_17152 32 8 (by decide +kernel)

theorem cellTest_17152_block_5 : Interval cellTest_17152 40 48 :=
  interval_of_check cellTest_17152 40 8 (by decide +kernel)

theorem cellTest_17152_block_6 : Interval cellTest_17152 48 56 :=
  interval_of_check cellTest_17152 48 8 (by decide +kernel)

theorem cellTest_17152_block_7 : Interval cellTest_17152 56 64 :=
  interval_of_check cellTest_17152 56 8 (by decide +kernel)

theorem cellTest_17152_block_8 : Interval cellTest_17152 64 72 :=
  interval_of_check cellTest_17152 64 8 (by decide +kernel)

theorem cellTest_17152_block_9 : Interval cellTest_17152 72 80 :=
  interval_of_check cellTest_17152 72 8 (by decide +kernel)

theorem cellTest_17152_block_10 : Interval cellTest_17152 80 88 :=
  interval_of_check cellTest_17152 80 8 (by decide +kernel)

theorem cellTest_17152_block_11 : Interval cellTest_17152 88 96 :=
  interval_of_check cellTest_17152 88 8 (by decide +kernel)

theorem cellTest_17152_block_12 : Interval cellTest_17152 96 104 :=
  interval_of_check cellTest_17152 96 8 (by decide +kernel)

theorem cellTest_17152_block_13 : Interval cellTest_17152 104 112 :=
  interval_of_check cellTest_17152 104 8 (by decide +kernel)

theorem cellTest_17152_block_14 : Interval cellTest_17152 112 120 :=
  interval_of_check cellTest_17152 112 8 (by decide +kernel)

theorem cellTest_17152_block_15 : Interval cellTest_17152 120 128 :=
  interval_of_check cellTest_17152 120 8 (by decide +kernel)

theorem cellTest_17152_block_16 : Interval cellTest_17152 128 136 :=
  interval_of_check cellTest_17152 128 8 (by decide +kernel)

theorem cellTest_17152_block_17 : Interval cellTest_17152 136 144 :=
  interval_of_check cellTest_17152 136 8 (by decide +kernel)

theorem cellTest_17152_block_18 : Interval cellTest_17152 144 152 :=
  interval_of_check cellTest_17152 144 8 (by decide +kernel)

theorem cellTest_17152_block_19 : Interval cellTest_17152 152 160 :=
  interval_of_check cellTest_17152 152 8 (by decide +kernel)

theorem cellTest_17152_block_20 : Interval cellTest_17152 160 168 :=
  interval_of_check cellTest_17152 160 8 (by decide +kernel)

theorem cellTest_17152_block_21 : Interval cellTest_17152 168 176 :=
  interval_of_check cellTest_17152 168 8 (by decide +kernel)

theorem cellTest_17152_block_22 : Interval cellTest_17152 176 184 :=
  interval_of_check cellTest_17152 176 8 (by decide +kernel)

theorem cellTest_17152_block_23 : Interval cellTest_17152 184 192 :=
  interval_of_check cellTest_17152 184 8 (by decide +kernel)

theorem cellTest_17152_block_24 : Interval cellTest_17152 192 200 :=
  interval_of_check cellTest_17152 192 8 (by decide +kernel)

theorem cellTest_17152_block_25 : Interval cellTest_17152 200 208 :=
  interval_of_check cellTest_17152 200 8 (by decide +kernel)

theorem cellTest_17152_block_26 : Interval cellTest_17152 208 216 :=
  interval_of_check cellTest_17152 208 8 (by decide +kernel)

theorem cellTest_17152_block_27 : Interval cellTest_17152 216 224 :=
  interval_of_check cellTest_17152 216 8 (by decide +kernel)

theorem cellTest_17152_block_28 : Interval cellTest_17152 224 232 :=
  interval_of_check cellTest_17152 224 8 (by decide +kernel)

theorem cellTest_17152_block_29 : Interval cellTest_17152 232 240 :=
  interval_of_check cellTest_17152 232 8 (by decide +kernel)

theorem cellTest_17152_block_30 : Interval cellTest_17152 240 248 :=
  interval_of_check cellTest_17152 240 8 (by decide +kernel)

theorem cellTest_17152_block_31 : Interval cellTest_17152 248 256 :=
  interval_of_check cellTest_17152 248 8 (by decide +kernel)

theorem cellTest_17152_complete : Interval cellTest_17152 0 256 :=
  (interval_append cellTest_17152 0 128 256
  (interval_append cellTest_17152 0 64 128
  (interval_append cellTest_17152 0 32 64
  (interval_append cellTest_17152 0 16 32
  (interval_append cellTest_17152 0 8 16
  cellTest_17152_block_0
  cellTest_17152_block_1)
  (interval_append cellTest_17152 16 24 32
  cellTest_17152_block_2
  cellTest_17152_block_3))
  (interval_append cellTest_17152 32 48 64
  (interval_append cellTest_17152 32 40 48
  cellTest_17152_block_4
  cellTest_17152_block_5)
  (interval_append cellTest_17152 48 56 64
  cellTest_17152_block_6
  cellTest_17152_block_7)))
  (interval_append cellTest_17152 64 96 128
  (interval_append cellTest_17152 64 80 96
  (interval_append cellTest_17152 64 72 80
  cellTest_17152_block_8
  cellTest_17152_block_9)
  (interval_append cellTest_17152 80 88 96
  cellTest_17152_block_10
  cellTest_17152_block_11))
  (interval_append cellTest_17152 96 112 128
  (interval_append cellTest_17152 96 104 112
  cellTest_17152_block_12
  cellTest_17152_block_13)
  (interval_append cellTest_17152 112 120 128
  cellTest_17152_block_14
  cellTest_17152_block_15))))
  (interval_append cellTest_17152 128 192 256
  (interval_append cellTest_17152 128 160 192
  (interval_append cellTest_17152 128 144 160
  (interval_append cellTest_17152 128 136 144
  cellTest_17152_block_16
  cellTest_17152_block_17)
  (interval_append cellTest_17152 144 152 160
  cellTest_17152_block_18
  cellTest_17152_block_19))
  (interval_append cellTest_17152 160 176 192
  (interval_append cellTest_17152 160 168 176
  cellTest_17152_block_20
  cellTest_17152_block_21)
  (interval_append cellTest_17152 176 184 192
  cellTest_17152_block_22
  cellTest_17152_block_23)))
  (interval_append cellTest_17152 192 224 256
  (interval_append cellTest_17152 192 208 224
  (interval_append cellTest_17152 192 200 208
  cellTest_17152_block_24
  cellTest_17152_block_25)
  (interval_append cellTest_17152 208 216 224
  cellTest_17152_block_26
  cellTest_17152_block_27))
  (interval_append cellTest_17152 224 240 256
  (interval_append cellTest_17152 224 232 240
  cellTest_17152_block_28
  cellTest_17152_block_29)
  (interval_append cellTest_17152 240 248 256
  cellTest_17152_block_30
  cellTest_17152_block_31)))))
theorem cellTestInterval17152 : Interval cellTest 17152 17408 := by
  intro i hlo hhi
  have h := cellTest_17152_complete (i-17152) (Nat.zero_le _) (by omega)
  simpa only [cellTest_17152, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells068 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_17408 (i : Nat) := cellTest (i+17408)
theorem cellTest_17408_block_0 : Interval cellTest_17408 0 8 :=
  interval_of_check cellTest_17408 0 8 (by decide +kernel)

theorem cellTest_17408_block_1 : Interval cellTest_17408 8 16 :=
  interval_of_check cellTest_17408 8 8 (by decide +kernel)

theorem cellTest_17408_block_2 : Interval cellTest_17408 16 24 :=
  interval_of_check cellTest_17408 16 8 (by decide +kernel)

theorem cellTest_17408_block_3 : Interval cellTest_17408 24 32 :=
  interval_of_check cellTest_17408 24 8 (by decide +kernel)

theorem cellTest_17408_block_4 : Interval cellTest_17408 32 40 :=
  interval_of_check cellTest_17408 32 8 (by decide +kernel)

theorem cellTest_17408_block_5 : Interval cellTest_17408 40 48 :=
  interval_of_check cellTest_17408 40 8 (by decide +kernel)

theorem cellTest_17408_block_6 : Interval cellTest_17408 48 56 :=
  interval_of_check cellTest_17408 48 8 (by decide +kernel)

theorem cellTest_17408_block_7 : Interval cellTest_17408 56 64 :=
  interval_of_check cellTest_17408 56 8 (by decide +kernel)

theorem cellTest_17408_block_8 : Interval cellTest_17408 64 72 :=
  interval_of_check cellTest_17408 64 8 (by decide +kernel)

theorem cellTest_17408_block_9 : Interval cellTest_17408 72 80 :=
  interval_of_check cellTest_17408 72 8 (by decide +kernel)

theorem cellTest_17408_block_10 : Interval cellTest_17408 80 88 :=
  interval_of_check cellTest_17408 80 8 (by decide +kernel)

theorem cellTest_17408_block_11 : Interval cellTest_17408 88 96 :=
  interval_of_check cellTest_17408 88 8 (by decide +kernel)

theorem cellTest_17408_block_12 : Interval cellTest_17408 96 104 :=
  interval_of_check cellTest_17408 96 8 (by decide +kernel)

theorem cellTest_17408_block_13 : Interval cellTest_17408 104 112 :=
  interval_of_check cellTest_17408 104 8 (by decide +kernel)

theorem cellTest_17408_block_14 : Interval cellTest_17408 112 120 :=
  interval_of_check cellTest_17408 112 8 (by decide +kernel)

theorem cellTest_17408_block_15 : Interval cellTest_17408 120 128 :=
  interval_of_check cellTest_17408 120 8 (by decide +kernel)

theorem cellTest_17408_block_16 : Interval cellTest_17408 128 136 :=
  interval_of_check cellTest_17408 128 8 (by decide +kernel)

theorem cellTest_17408_block_17 : Interval cellTest_17408 136 144 :=
  interval_of_check cellTest_17408 136 8 (by decide +kernel)

theorem cellTest_17408_block_18 : Interval cellTest_17408 144 152 :=
  interval_of_check cellTest_17408 144 8 (by decide +kernel)

theorem cellTest_17408_block_19 : Interval cellTest_17408 152 160 :=
  interval_of_check cellTest_17408 152 8 (by decide +kernel)

theorem cellTest_17408_block_20 : Interval cellTest_17408 160 168 :=
  interval_of_check cellTest_17408 160 8 (by decide +kernel)

theorem cellTest_17408_block_21 : Interval cellTest_17408 168 176 :=
  interval_of_check cellTest_17408 168 8 (by decide +kernel)

theorem cellTest_17408_block_22 : Interval cellTest_17408 176 184 :=
  interval_of_check cellTest_17408 176 8 (by decide +kernel)

theorem cellTest_17408_block_23 : Interval cellTest_17408 184 192 :=
  interval_of_check cellTest_17408 184 8 (by decide +kernel)

theorem cellTest_17408_block_24 : Interval cellTest_17408 192 200 :=
  interval_of_check cellTest_17408 192 8 (by decide +kernel)

theorem cellTest_17408_block_25 : Interval cellTest_17408 200 208 :=
  interval_of_check cellTest_17408 200 8 (by decide +kernel)

theorem cellTest_17408_block_26 : Interval cellTest_17408 208 216 :=
  interval_of_check cellTest_17408 208 8 (by decide +kernel)

theorem cellTest_17408_block_27 : Interval cellTest_17408 216 224 :=
  interval_of_check cellTest_17408 216 8 (by decide +kernel)

theorem cellTest_17408_block_28 : Interval cellTest_17408 224 232 :=
  interval_of_check cellTest_17408 224 8 (by decide +kernel)

theorem cellTest_17408_block_29 : Interval cellTest_17408 232 240 :=
  interval_of_check cellTest_17408 232 8 (by decide +kernel)

theorem cellTest_17408_block_30 : Interval cellTest_17408 240 248 :=
  interval_of_check cellTest_17408 240 8 (by decide +kernel)

theorem cellTest_17408_block_31 : Interval cellTest_17408 248 256 :=
  interval_of_check cellTest_17408 248 8 (by decide +kernel)

theorem cellTest_17408_complete : Interval cellTest_17408 0 256 :=
  (interval_append cellTest_17408 0 128 256
  (interval_append cellTest_17408 0 64 128
  (interval_append cellTest_17408 0 32 64
  (interval_append cellTest_17408 0 16 32
  (interval_append cellTest_17408 0 8 16
  cellTest_17408_block_0
  cellTest_17408_block_1)
  (interval_append cellTest_17408 16 24 32
  cellTest_17408_block_2
  cellTest_17408_block_3))
  (interval_append cellTest_17408 32 48 64
  (interval_append cellTest_17408 32 40 48
  cellTest_17408_block_4
  cellTest_17408_block_5)
  (interval_append cellTest_17408 48 56 64
  cellTest_17408_block_6
  cellTest_17408_block_7)))
  (interval_append cellTest_17408 64 96 128
  (interval_append cellTest_17408 64 80 96
  (interval_append cellTest_17408 64 72 80
  cellTest_17408_block_8
  cellTest_17408_block_9)
  (interval_append cellTest_17408 80 88 96
  cellTest_17408_block_10
  cellTest_17408_block_11))
  (interval_append cellTest_17408 96 112 128
  (interval_append cellTest_17408 96 104 112
  cellTest_17408_block_12
  cellTest_17408_block_13)
  (interval_append cellTest_17408 112 120 128
  cellTest_17408_block_14
  cellTest_17408_block_15))))
  (interval_append cellTest_17408 128 192 256
  (interval_append cellTest_17408 128 160 192
  (interval_append cellTest_17408 128 144 160
  (interval_append cellTest_17408 128 136 144
  cellTest_17408_block_16
  cellTest_17408_block_17)
  (interval_append cellTest_17408 144 152 160
  cellTest_17408_block_18
  cellTest_17408_block_19))
  (interval_append cellTest_17408 160 176 192
  (interval_append cellTest_17408 160 168 176
  cellTest_17408_block_20
  cellTest_17408_block_21)
  (interval_append cellTest_17408 176 184 192
  cellTest_17408_block_22
  cellTest_17408_block_23)))
  (interval_append cellTest_17408 192 224 256
  (interval_append cellTest_17408 192 208 224
  (interval_append cellTest_17408 192 200 208
  cellTest_17408_block_24
  cellTest_17408_block_25)
  (interval_append cellTest_17408 208 216 224
  cellTest_17408_block_26
  cellTest_17408_block_27))
  (interval_append cellTest_17408 224 240 256
  (interval_append cellTest_17408 224 232 240
  cellTest_17408_block_28
  cellTest_17408_block_29)
  (interval_append cellTest_17408 240 248 256
  cellTest_17408_block_30
  cellTest_17408_block_31)))))
theorem cellTestInterval17408 : Interval cellTest 17408 17664 := by
  intro i hlo hhi
  have h := cellTest_17408_complete (i-17408) (Nat.zero_le _) (by omega)
  simpa only [cellTest_17408, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells069 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_17664 (i : Nat) := cellTest (i+17664)
theorem cellTest_17664_block_0 : Interval cellTest_17664 0 8 :=
  interval_of_check cellTest_17664 0 8 (by decide +kernel)

theorem cellTest_17664_block_1 : Interval cellTest_17664 8 16 :=
  interval_of_check cellTest_17664 8 8 (by decide +kernel)

theorem cellTest_17664_block_2 : Interval cellTest_17664 16 24 :=
  interval_of_check cellTest_17664 16 8 (by decide +kernel)

theorem cellTest_17664_block_3 : Interval cellTest_17664 24 32 :=
  interval_of_check cellTest_17664 24 8 (by decide +kernel)

theorem cellTest_17664_block_4 : Interval cellTest_17664 32 40 :=
  interval_of_check cellTest_17664 32 8 (by decide +kernel)

theorem cellTest_17664_block_5 : Interval cellTest_17664 40 48 :=
  interval_of_check cellTest_17664 40 8 (by decide +kernel)

theorem cellTest_17664_block_6 : Interval cellTest_17664 48 56 :=
  interval_of_check cellTest_17664 48 8 (by decide +kernel)

theorem cellTest_17664_block_7 : Interval cellTest_17664 56 64 :=
  interval_of_check cellTest_17664 56 8 (by decide +kernel)

theorem cellTest_17664_block_8 : Interval cellTest_17664 64 72 :=
  interval_of_check cellTest_17664 64 8 (by decide +kernel)

theorem cellTest_17664_block_9 : Interval cellTest_17664 72 80 :=
  interval_of_check cellTest_17664 72 8 (by decide +kernel)

theorem cellTest_17664_block_10 : Interval cellTest_17664 80 88 :=
  interval_of_check cellTest_17664 80 8 (by decide +kernel)

theorem cellTest_17664_block_11 : Interval cellTest_17664 88 96 :=
  interval_of_check cellTest_17664 88 8 (by decide +kernel)

theorem cellTest_17664_block_12 : Interval cellTest_17664 96 104 :=
  interval_of_check cellTest_17664 96 8 (by decide +kernel)

theorem cellTest_17664_block_13 : Interval cellTest_17664 104 112 :=
  interval_of_check cellTest_17664 104 8 (by decide +kernel)

theorem cellTest_17664_block_14 : Interval cellTest_17664 112 120 :=
  interval_of_check cellTest_17664 112 8 (by decide +kernel)

theorem cellTest_17664_block_15 : Interval cellTest_17664 120 128 :=
  interval_of_check cellTest_17664 120 8 (by decide +kernel)

theorem cellTest_17664_block_16 : Interval cellTest_17664 128 136 :=
  interval_of_check cellTest_17664 128 8 (by decide +kernel)

theorem cellTest_17664_block_17 : Interval cellTest_17664 136 144 :=
  interval_of_check cellTest_17664 136 8 (by decide +kernel)

theorem cellTest_17664_block_18 : Interval cellTest_17664 144 152 :=
  interval_of_check cellTest_17664 144 8 (by decide +kernel)

theorem cellTest_17664_block_19 : Interval cellTest_17664 152 160 :=
  interval_of_check cellTest_17664 152 8 (by decide +kernel)

theorem cellTest_17664_block_20 : Interval cellTest_17664 160 168 :=
  interval_of_check cellTest_17664 160 8 (by decide +kernel)

theorem cellTest_17664_block_21 : Interval cellTest_17664 168 176 :=
  interval_of_check cellTest_17664 168 8 (by decide +kernel)

theorem cellTest_17664_block_22 : Interval cellTest_17664 176 184 :=
  interval_of_check cellTest_17664 176 8 (by decide +kernel)

theorem cellTest_17664_block_23 : Interval cellTest_17664 184 192 :=
  interval_of_check cellTest_17664 184 8 (by decide +kernel)

theorem cellTest_17664_block_24 : Interval cellTest_17664 192 200 :=
  interval_of_check cellTest_17664 192 8 (by decide +kernel)

theorem cellTest_17664_block_25 : Interval cellTest_17664 200 208 :=
  interval_of_check cellTest_17664 200 8 (by decide +kernel)

theorem cellTest_17664_block_26 : Interval cellTest_17664 208 216 :=
  interval_of_check cellTest_17664 208 8 (by decide +kernel)

theorem cellTest_17664_block_27 : Interval cellTest_17664 216 224 :=
  interval_of_check cellTest_17664 216 8 (by decide +kernel)

theorem cellTest_17664_block_28 : Interval cellTest_17664 224 232 :=
  interval_of_check cellTest_17664 224 8 (by decide +kernel)

theorem cellTest_17664_block_29 : Interval cellTest_17664 232 240 :=
  interval_of_check cellTest_17664 232 8 (by decide +kernel)

theorem cellTest_17664_block_30 : Interval cellTest_17664 240 248 :=
  interval_of_check cellTest_17664 240 8 (by decide +kernel)

theorem cellTest_17664_block_31 : Interval cellTest_17664 248 256 :=
  interval_of_check cellTest_17664 248 8 (by decide +kernel)

theorem cellTest_17664_complete : Interval cellTest_17664 0 256 :=
  (interval_append cellTest_17664 0 128 256
  (interval_append cellTest_17664 0 64 128
  (interval_append cellTest_17664 0 32 64
  (interval_append cellTest_17664 0 16 32
  (interval_append cellTest_17664 0 8 16
  cellTest_17664_block_0
  cellTest_17664_block_1)
  (interval_append cellTest_17664 16 24 32
  cellTest_17664_block_2
  cellTest_17664_block_3))
  (interval_append cellTest_17664 32 48 64
  (interval_append cellTest_17664 32 40 48
  cellTest_17664_block_4
  cellTest_17664_block_5)
  (interval_append cellTest_17664 48 56 64
  cellTest_17664_block_6
  cellTest_17664_block_7)))
  (interval_append cellTest_17664 64 96 128
  (interval_append cellTest_17664 64 80 96
  (interval_append cellTest_17664 64 72 80
  cellTest_17664_block_8
  cellTest_17664_block_9)
  (interval_append cellTest_17664 80 88 96
  cellTest_17664_block_10
  cellTest_17664_block_11))
  (interval_append cellTest_17664 96 112 128
  (interval_append cellTest_17664 96 104 112
  cellTest_17664_block_12
  cellTest_17664_block_13)
  (interval_append cellTest_17664 112 120 128
  cellTest_17664_block_14
  cellTest_17664_block_15))))
  (interval_append cellTest_17664 128 192 256
  (interval_append cellTest_17664 128 160 192
  (interval_append cellTest_17664 128 144 160
  (interval_append cellTest_17664 128 136 144
  cellTest_17664_block_16
  cellTest_17664_block_17)
  (interval_append cellTest_17664 144 152 160
  cellTest_17664_block_18
  cellTest_17664_block_19))
  (interval_append cellTest_17664 160 176 192
  (interval_append cellTest_17664 160 168 176
  cellTest_17664_block_20
  cellTest_17664_block_21)
  (interval_append cellTest_17664 176 184 192
  cellTest_17664_block_22
  cellTest_17664_block_23)))
  (interval_append cellTest_17664 192 224 256
  (interval_append cellTest_17664 192 208 224
  (interval_append cellTest_17664 192 200 208
  cellTest_17664_block_24
  cellTest_17664_block_25)
  (interval_append cellTest_17664 208 216 224
  cellTest_17664_block_26
  cellTest_17664_block_27))
  (interval_append cellTest_17664 224 240 256
  (interval_append cellTest_17664 224 232 240
  cellTest_17664_block_28
  cellTest_17664_block_29)
  (interval_append cellTest_17664 240 248 256
  cellTest_17664_block_30
  cellTest_17664_block_31)))))
theorem cellTestInterval17664 : Interval cellTest 17664 17920 := by
  intro i hlo hhi
  have h := cellTest_17664_complete (i-17664) (Nat.zero_le _) (by omega)
  simpa only [cellTest_17664, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells070 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_17920 (i : Nat) := cellTest (i+17920)
theorem cellTest_17920_block_0 : Interval cellTest_17920 0 8 :=
  interval_of_check cellTest_17920 0 8 (by decide +kernel)

theorem cellTest_17920_block_1 : Interval cellTest_17920 8 16 :=
  interval_of_check cellTest_17920 8 8 (by decide +kernel)

theorem cellTest_17920_block_2 : Interval cellTest_17920 16 24 :=
  interval_of_check cellTest_17920 16 8 (by decide +kernel)

theorem cellTest_17920_block_3 : Interval cellTest_17920 24 32 :=
  interval_of_check cellTest_17920 24 8 (by decide +kernel)

theorem cellTest_17920_block_4 : Interval cellTest_17920 32 40 :=
  interval_of_check cellTest_17920 32 8 (by decide +kernel)

theorem cellTest_17920_block_5 : Interval cellTest_17920 40 48 :=
  interval_of_check cellTest_17920 40 8 (by decide +kernel)

theorem cellTest_17920_block_6 : Interval cellTest_17920 48 56 :=
  interval_of_check cellTest_17920 48 8 (by decide +kernel)

theorem cellTest_17920_block_7 : Interval cellTest_17920 56 64 :=
  interval_of_check cellTest_17920 56 8 (by decide +kernel)

theorem cellTest_17920_block_8 : Interval cellTest_17920 64 72 :=
  interval_of_check cellTest_17920 64 8 (by decide +kernel)

theorem cellTest_17920_block_9 : Interval cellTest_17920 72 80 :=
  interval_of_check cellTest_17920 72 8 (by decide +kernel)

theorem cellTest_17920_block_10 : Interval cellTest_17920 80 88 :=
  interval_of_check cellTest_17920 80 8 (by decide +kernel)

theorem cellTest_17920_block_11 : Interval cellTest_17920 88 96 :=
  interval_of_check cellTest_17920 88 8 (by decide +kernel)

theorem cellTest_17920_block_12 : Interval cellTest_17920 96 104 :=
  interval_of_check cellTest_17920 96 8 (by decide +kernel)

theorem cellTest_17920_block_13 : Interval cellTest_17920 104 112 :=
  interval_of_check cellTest_17920 104 8 (by decide +kernel)

theorem cellTest_17920_block_14 : Interval cellTest_17920 112 120 :=
  interval_of_check cellTest_17920 112 8 (by decide +kernel)

theorem cellTest_17920_block_15 : Interval cellTest_17920 120 128 :=
  interval_of_check cellTest_17920 120 8 (by decide +kernel)

theorem cellTest_17920_block_16 : Interval cellTest_17920 128 136 :=
  interval_of_check cellTest_17920 128 8 (by decide +kernel)

theorem cellTest_17920_block_17 : Interval cellTest_17920 136 144 :=
  interval_of_check cellTest_17920 136 8 (by decide +kernel)

theorem cellTest_17920_block_18 : Interval cellTest_17920 144 152 :=
  interval_of_check cellTest_17920 144 8 (by decide +kernel)

theorem cellTest_17920_block_19 : Interval cellTest_17920 152 160 :=
  interval_of_check cellTest_17920 152 8 (by decide +kernel)

theorem cellTest_17920_block_20 : Interval cellTest_17920 160 168 :=
  interval_of_check cellTest_17920 160 8 (by decide +kernel)

theorem cellTest_17920_block_21 : Interval cellTest_17920 168 176 :=
  interval_of_check cellTest_17920 168 8 (by decide +kernel)

theorem cellTest_17920_block_22 : Interval cellTest_17920 176 184 :=
  interval_of_check cellTest_17920 176 8 (by decide +kernel)

theorem cellTest_17920_block_23 : Interval cellTest_17920 184 192 :=
  interval_of_check cellTest_17920 184 8 (by decide +kernel)

theorem cellTest_17920_block_24 : Interval cellTest_17920 192 200 :=
  interval_of_check cellTest_17920 192 8 (by decide +kernel)

theorem cellTest_17920_block_25 : Interval cellTest_17920 200 208 :=
  interval_of_check cellTest_17920 200 8 (by decide +kernel)

theorem cellTest_17920_block_26 : Interval cellTest_17920 208 216 :=
  interval_of_check cellTest_17920 208 8 (by decide +kernel)

theorem cellTest_17920_block_27 : Interval cellTest_17920 216 224 :=
  interval_of_check cellTest_17920 216 8 (by decide +kernel)

theorem cellTest_17920_block_28 : Interval cellTest_17920 224 232 :=
  interval_of_check cellTest_17920 224 8 (by decide +kernel)

theorem cellTest_17920_block_29 : Interval cellTest_17920 232 240 :=
  interval_of_check cellTest_17920 232 8 (by decide +kernel)

theorem cellTest_17920_block_30 : Interval cellTest_17920 240 248 :=
  interval_of_check cellTest_17920 240 8 (by decide +kernel)

theorem cellTest_17920_block_31 : Interval cellTest_17920 248 256 :=
  interval_of_check cellTest_17920 248 8 (by decide +kernel)

theorem cellTest_17920_complete : Interval cellTest_17920 0 256 :=
  (interval_append cellTest_17920 0 128 256
  (interval_append cellTest_17920 0 64 128
  (interval_append cellTest_17920 0 32 64
  (interval_append cellTest_17920 0 16 32
  (interval_append cellTest_17920 0 8 16
  cellTest_17920_block_0
  cellTest_17920_block_1)
  (interval_append cellTest_17920 16 24 32
  cellTest_17920_block_2
  cellTest_17920_block_3))
  (interval_append cellTest_17920 32 48 64
  (interval_append cellTest_17920 32 40 48
  cellTest_17920_block_4
  cellTest_17920_block_5)
  (interval_append cellTest_17920 48 56 64
  cellTest_17920_block_6
  cellTest_17920_block_7)))
  (interval_append cellTest_17920 64 96 128
  (interval_append cellTest_17920 64 80 96
  (interval_append cellTest_17920 64 72 80
  cellTest_17920_block_8
  cellTest_17920_block_9)
  (interval_append cellTest_17920 80 88 96
  cellTest_17920_block_10
  cellTest_17920_block_11))
  (interval_append cellTest_17920 96 112 128
  (interval_append cellTest_17920 96 104 112
  cellTest_17920_block_12
  cellTest_17920_block_13)
  (interval_append cellTest_17920 112 120 128
  cellTest_17920_block_14
  cellTest_17920_block_15))))
  (interval_append cellTest_17920 128 192 256
  (interval_append cellTest_17920 128 160 192
  (interval_append cellTest_17920 128 144 160
  (interval_append cellTest_17920 128 136 144
  cellTest_17920_block_16
  cellTest_17920_block_17)
  (interval_append cellTest_17920 144 152 160
  cellTest_17920_block_18
  cellTest_17920_block_19))
  (interval_append cellTest_17920 160 176 192
  (interval_append cellTest_17920 160 168 176
  cellTest_17920_block_20
  cellTest_17920_block_21)
  (interval_append cellTest_17920 176 184 192
  cellTest_17920_block_22
  cellTest_17920_block_23)))
  (interval_append cellTest_17920 192 224 256
  (interval_append cellTest_17920 192 208 224
  (interval_append cellTest_17920 192 200 208
  cellTest_17920_block_24
  cellTest_17920_block_25)
  (interval_append cellTest_17920 208 216 224
  cellTest_17920_block_26
  cellTest_17920_block_27))
  (interval_append cellTest_17920 224 240 256
  (interval_append cellTest_17920 224 232 240
  cellTest_17920_block_28
  cellTest_17920_block_29)
  (interval_append cellTest_17920 240 248 256
  cellTest_17920_block_30
  cellTest_17920_block_31)))))
theorem cellTestInterval17920 : Interval cellTest 17920 18176 := by
  intro i hlo hhi
  have h := cellTest_17920_complete (i-17920) (Nat.zero_le _) (by omega)
  simpa only [cellTest_17920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells071 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_18176 (i : Nat) := cellTest (i+18176)
theorem cellTest_18176_block_0 : Interval cellTest_18176 0 8 :=
  interval_of_check cellTest_18176 0 8 (by decide +kernel)

theorem cellTest_18176_block_1 : Interval cellTest_18176 8 16 :=
  interval_of_check cellTest_18176 8 8 (by decide +kernel)

theorem cellTest_18176_block_2 : Interval cellTest_18176 16 24 :=
  interval_of_check cellTest_18176 16 8 (by decide +kernel)

theorem cellTest_18176_block_3 : Interval cellTest_18176 24 32 :=
  interval_of_check cellTest_18176 24 8 (by decide +kernel)

theorem cellTest_18176_block_4 : Interval cellTest_18176 32 40 :=
  interval_of_check cellTest_18176 32 8 (by decide +kernel)

theorem cellTest_18176_block_5 : Interval cellTest_18176 40 48 :=
  interval_of_check cellTest_18176 40 8 (by decide +kernel)

theorem cellTest_18176_block_6 : Interval cellTest_18176 48 56 :=
  interval_of_check cellTest_18176 48 8 (by decide +kernel)

theorem cellTest_18176_block_7 : Interval cellTest_18176 56 64 :=
  interval_of_check cellTest_18176 56 8 (by decide +kernel)

theorem cellTest_18176_block_8 : Interval cellTest_18176 64 72 :=
  interval_of_check cellTest_18176 64 8 (by decide +kernel)

theorem cellTest_18176_block_9 : Interval cellTest_18176 72 80 :=
  interval_of_check cellTest_18176 72 8 (by decide +kernel)

theorem cellTest_18176_block_10 : Interval cellTest_18176 80 88 :=
  interval_of_check cellTest_18176 80 8 (by decide +kernel)

theorem cellTest_18176_block_11 : Interval cellTest_18176 88 96 :=
  interval_of_check cellTest_18176 88 8 (by decide +kernel)

theorem cellTest_18176_block_12 : Interval cellTest_18176 96 104 :=
  interval_of_check cellTest_18176 96 8 (by decide +kernel)

theorem cellTest_18176_block_13 : Interval cellTest_18176 104 112 :=
  interval_of_check cellTest_18176 104 8 (by decide +kernel)

theorem cellTest_18176_block_14 : Interval cellTest_18176 112 120 :=
  interval_of_check cellTest_18176 112 8 (by decide +kernel)

theorem cellTest_18176_block_15 : Interval cellTest_18176 120 128 :=
  interval_of_check cellTest_18176 120 8 (by decide +kernel)

theorem cellTest_18176_block_16 : Interval cellTest_18176 128 136 :=
  interval_of_check cellTest_18176 128 8 (by decide +kernel)

theorem cellTest_18176_block_17 : Interval cellTest_18176 136 144 :=
  interval_of_check cellTest_18176 136 8 (by decide +kernel)

theorem cellTest_18176_block_18 : Interval cellTest_18176 144 152 :=
  interval_of_check cellTest_18176 144 8 (by decide +kernel)

theorem cellTest_18176_block_19 : Interval cellTest_18176 152 160 :=
  interval_of_check cellTest_18176 152 8 (by decide +kernel)

theorem cellTest_18176_block_20 : Interval cellTest_18176 160 168 :=
  interval_of_check cellTest_18176 160 8 (by decide +kernel)

theorem cellTest_18176_block_21 : Interval cellTest_18176 168 176 :=
  interval_of_check cellTest_18176 168 8 (by decide +kernel)

theorem cellTest_18176_block_22 : Interval cellTest_18176 176 184 :=
  interval_of_check cellTest_18176 176 8 (by decide +kernel)

theorem cellTest_18176_block_23 : Interval cellTest_18176 184 192 :=
  interval_of_check cellTest_18176 184 8 (by decide +kernel)

theorem cellTest_18176_block_24 : Interval cellTest_18176 192 200 :=
  interval_of_check cellTest_18176 192 8 (by decide +kernel)

theorem cellTest_18176_block_25 : Interval cellTest_18176 200 208 :=
  interval_of_check cellTest_18176 200 8 (by decide +kernel)

theorem cellTest_18176_block_26 : Interval cellTest_18176 208 216 :=
  interval_of_check cellTest_18176 208 8 (by decide +kernel)

theorem cellTest_18176_block_27 : Interval cellTest_18176 216 224 :=
  interval_of_check cellTest_18176 216 8 (by decide +kernel)

theorem cellTest_18176_block_28 : Interval cellTest_18176 224 232 :=
  interval_of_check cellTest_18176 224 8 (by decide +kernel)

theorem cellTest_18176_block_29 : Interval cellTest_18176 232 240 :=
  interval_of_check cellTest_18176 232 8 (by decide +kernel)

theorem cellTest_18176_block_30 : Interval cellTest_18176 240 248 :=
  interval_of_check cellTest_18176 240 8 (by decide +kernel)

theorem cellTest_18176_block_31 : Interval cellTest_18176 248 256 :=
  interval_of_check cellTest_18176 248 8 (by decide +kernel)

theorem cellTest_18176_complete : Interval cellTest_18176 0 256 :=
  (interval_append cellTest_18176 0 128 256
  (interval_append cellTest_18176 0 64 128
  (interval_append cellTest_18176 0 32 64
  (interval_append cellTest_18176 0 16 32
  (interval_append cellTest_18176 0 8 16
  cellTest_18176_block_0
  cellTest_18176_block_1)
  (interval_append cellTest_18176 16 24 32
  cellTest_18176_block_2
  cellTest_18176_block_3))
  (interval_append cellTest_18176 32 48 64
  (interval_append cellTest_18176 32 40 48
  cellTest_18176_block_4
  cellTest_18176_block_5)
  (interval_append cellTest_18176 48 56 64
  cellTest_18176_block_6
  cellTest_18176_block_7)))
  (interval_append cellTest_18176 64 96 128
  (interval_append cellTest_18176 64 80 96
  (interval_append cellTest_18176 64 72 80
  cellTest_18176_block_8
  cellTest_18176_block_9)
  (interval_append cellTest_18176 80 88 96
  cellTest_18176_block_10
  cellTest_18176_block_11))
  (interval_append cellTest_18176 96 112 128
  (interval_append cellTest_18176 96 104 112
  cellTest_18176_block_12
  cellTest_18176_block_13)
  (interval_append cellTest_18176 112 120 128
  cellTest_18176_block_14
  cellTest_18176_block_15))))
  (interval_append cellTest_18176 128 192 256
  (interval_append cellTest_18176 128 160 192
  (interval_append cellTest_18176 128 144 160
  (interval_append cellTest_18176 128 136 144
  cellTest_18176_block_16
  cellTest_18176_block_17)
  (interval_append cellTest_18176 144 152 160
  cellTest_18176_block_18
  cellTest_18176_block_19))
  (interval_append cellTest_18176 160 176 192
  (interval_append cellTest_18176 160 168 176
  cellTest_18176_block_20
  cellTest_18176_block_21)
  (interval_append cellTest_18176 176 184 192
  cellTest_18176_block_22
  cellTest_18176_block_23)))
  (interval_append cellTest_18176 192 224 256
  (interval_append cellTest_18176 192 208 224
  (interval_append cellTest_18176 192 200 208
  cellTest_18176_block_24
  cellTest_18176_block_25)
  (interval_append cellTest_18176 208 216 224
  cellTest_18176_block_26
  cellTest_18176_block_27))
  (interval_append cellTest_18176 224 240 256
  (interval_append cellTest_18176 224 232 240
  cellTest_18176_block_28
  cellTest_18176_block_29)
  (interval_append cellTest_18176 240 248 256
  cellTest_18176_block_30
  cellTest_18176_block_31)))))
theorem cellTestInterval18176 : Interval cellTest 18176 18432 := by
  intro i hlo hhi
  have h := cellTest_18176_complete (i-18176) (Nat.zero_le _) (by omega)
  simpa only [cellTest_18176, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells072 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_18432 (i : Nat) := cellTest (i+18432)
theorem cellTest_18432_block_0 : Interval cellTest_18432 0 8 :=
  interval_of_check cellTest_18432 0 8 (by decide +kernel)

theorem cellTest_18432_block_1 : Interval cellTest_18432 8 16 :=
  interval_of_check cellTest_18432 8 8 (by decide +kernel)

theorem cellTest_18432_block_2 : Interval cellTest_18432 16 24 :=
  interval_of_check cellTest_18432 16 8 (by decide +kernel)

theorem cellTest_18432_block_3 : Interval cellTest_18432 24 32 :=
  interval_of_check cellTest_18432 24 8 (by decide +kernel)

theorem cellTest_18432_block_4 : Interval cellTest_18432 32 40 :=
  interval_of_check cellTest_18432 32 8 (by decide +kernel)

theorem cellTest_18432_block_5 : Interval cellTest_18432 40 48 :=
  interval_of_check cellTest_18432 40 8 (by decide +kernel)

theorem cellTest_18432_block_6 : Interval cellTest_18432 48 56 :=
  interval_of_check cellTest_18432 48 8 (by decide +kernel)

theorem cellTest_18432_block_7 : Interval cellTest_18432 56 64 :=
  interval_of_check cellTest_18432 56 8 (by decide +kernel)

theorem cellTest_18432_block_8 : Interval cellTest_18432 64 72 :=
  interval_of_check cellTest_18432 64 8 (by decide +kernel)

theorem cellTest_18432_block_9 : Interval cellTest_18432 72 80 :=
  interval_of_check cellTest_18432 72 8 (by decide +kernel)

theorem cellTest_18432_block_10 : Interval cellTest_18432 80 88 :=
  interval_of_check cellTest_18432 80 8 (by decide +kernel)

theorem cellTest_18432_block_11 : Interval cellTest_18432 88 96 :=
  interval_of_check cellTest_18432 88 8 (by decide +kernel)

theorem cellTest_18432_block_12 : Interval cellTest_18432 96 104 :=
  interval_of_check cellTest_18432 96 8 (by decide +kernel)

theorem cellTest_18432_block_13 : Interval cellTest_18432 104 112 :=
  interval_of_check cellTest_18432 104 8 (by decide +kernel)

theorem cellTest_18432_block_14 : Interval cellTest_18432 112 120 :=
  interval_of_check cellTest_18432 112 8 (by decide +kernel)

theorem cellTest_18432_block_15 : Interval cellTest_18432 120 128 :=
  interval_of_check cellTest_18432 120 8 (by decide +kernel)

theorem cellTest_18432_block_16 : Interval cellTest_18432 128 136 :=
  interval_of_check cellTest_18432 128 8 (by decide +kernel)

theorem cellTest_18432_block_17 : Interval cellTest_18432 136 144 :=
  interval_of_check cellTest_18432 136 8 (by decide +kernel)

theorem cellTest_18432_block_18 : Interval cellTest_18432 144 152 :=
  interval_of_check cellTest_18432 144 8 (by decide +kernel)

theorem cellTest_18432_block_19 : Interval cellTest_18432 152 160 :=
  interval_of_check cellTest_18432 152 8 (by decide +kernel)

theorem cellTest_18432_block_20 : Interval cellTest_18432 160 168 :=
  interval_of_check cellTest_18432 160 8 (by decide +kernel)

theorem cellTest_18432_block_21 : Interval cellTest_18432 168 176 :=
  interval_of_check cellTest_18432 168 8 (by decide +kernel)

theorem cellTest_18432_block_22 : Interval cellTest_18432 176 184 :=
  interval_of_check cellTest_18432 176 8 (by decide +kernel)

theorem cellTest_18432_block_23 : Interval cellTest_18432 184 192 :=
  interval_of_check cellTest_18432 184 8 (by decide +kernel)

theorem cellTest_18432_block_24 : Interval cellTest_18432 192 200 :=
  interval_of_check cellTest_18432 192 8 (by decide +kernel)

theorem cellTest_18432_block_25 : Interval cellTest_18432 200 208 :=
  interval_of_check cellTest_18432 200 8 (by decide +kernel)

theorem cellTest_18432_block_26 : Interval cellTest_18432 208 216 :=
  interval_of_check cellTest_18432 208 8 (by decide +kernel)

theorem cellTest_18432_block_27 : Interval cellTest_18432 216 224 :=
  interval_of_check cellTest_18432 216 8 (by decide +kernel)

theorem cellTest_18432_block_28 : Interval cellTest_18432 224 232 :=
  interval_of_check cellTest_18432 224 8 (by decide +kernel)

theorem cellTest_18432_block_29 : Interval cellTest_18432 232 240 :=
  interval_of_check cellTest_18432 232 8 (by decide +kernel)

theorem cellTest_18432_block_30 : Interval cellTest_18432 240 248 :=
  interval_of_check cellTest_18432 240 8 (by decide +kernel)

theorem cellTest_18432_block_31 : Interval cellTest_18432 248 256 :=
  interval_of_check cellTest_18432 248 8 (by decide +kernel)

theorem cellTest_18432_complete : Interval cellTest_18432 0 256 :=
  (interval_append cellTest_18432 0 128 256
  (interval_append cellTest_18432 0 64 128
  (interval_append cellTest_18432 0 32 64
  (interval_append cellTest_18432 0 16 32
  (interval_append cellTest_18432 0 8 16
  cellTest_18432_block_0
  cellTest_18432_block_1)
  (interval_append cellTest_18432 16 24 32
  cellTest_18432_block_2
  cellTest_18432_block_3))
  (interval_append cellTest_18432 32 48 64
  (interval_append cellTest_18432 32 40 48
  cellTest_18432_block_4
  cellTest_18432_block_5)
  (interval_append cellTest_18432 48 56 64
  cellTest_18432_block_6
  cellTest_18432_block_7)))
  (interval_append cellTest_18432 64 96 128
  (interval_append cellTest_18432 64 80 96
  (interval_append cellTest_18432 64 72 80
  cellTest_18432_block_8
  cellTest_18432_block_9)
  (interval_append cellTest_18432 80 88 96
  cellTest_18432_block_10
  cellTest_18432_block_11))
  (interval_append cellTest_18432 96 112 128
  (interval_append cellTest_18432 96 104 112
  cellTest_18432_block_12
  cellTest_18432_block_13)
  (interval_append cellTest_18432 112 120 128
  cellTest_18432_block_14
  cellTest_18432_block_15))))
  (interval_append cellTest_18432 128 192 256
  (interval_append cellTest_18432 128 160 192
  (interval_append cellTest_18432 128 144 160
  (interval_append cellTest_18432 128 136 144
  cellTest_18432_block_16
  cellTest_18432_block_17)
  (interval_append cellTest_18432 144 152 160
  cellTest_18432_block_18
  cellTest_18432_block_19))
  (interval_append cellTest_18432 160 176 192
  (interval_append cellTest_18432 160 168 176
  cellTest_18432_block_20
  cellTest_18432_block_21)
  (interval_append cellTest_18432 176 184 192
  cellTest_18432_block_22
  cellTest_18432_block_23)))
  (interval_append cellTest_18432 192 224 256
  (interval_append cellTest_18432 192 208 224
  (interval_append cellTest_18432 192 200 208
  cellTest_18432_block_24
  cellTest_18432_block_25)
  (interval_append cellTest_18432 208 216 224
  cellTest_18432_block_26
  cellTest_18432_block_27))
  (interval_append cellTest_18432 224 240 256
  (interval_append cellTest_18432 224 232 240
  cellTest_18432_block_28
  cellTest_18432_block_29)
  (interval_append cellTest_18432 240 248 256
  cellTest_18432_block_30
  cellTest_18432_block_31)))))
theorem cellTestInterval18432 : Interval cellTest 18432 18688 := by
  intro i hlo hhi
  have h := cellTest_18432_complete (i-18432) (Nat.zero_le _) (by omega)
  simpa only [cellTest_18432, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells073 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_18688 (i : Nat) := cellTest (i+18688)
theorem cellTest_18688_block_0 : Interval cellTest_18688 0 8 :=
  interval_of_check cellTest_18688 0 8 (by decide +kernel)

theorem cellTest_18688_block_1 : Interval cellTest_18688 8 16 :=
  interval_of_check cellTest_18688 8 8 (by decide +kernel)

theorem cellTest_18688_block_2 : Interval cellTest_18688 16 24 :=
  interval_of_check cellTest_18688 16 8 (by decide +kernel)

theorem cellTest_18688_block_3 : Interval cellTest_18688 24 32 :=
  interval_of_check cellTest_18688 24 8 (by decide +kernel)

theorem cellTest_18688_block_4 : Interval cellTest_18688 32 40 :=
  interval_of_check cellTest_18688 32 8 (by decide +kernel)

theorem cellTest_18688_block_5 : Interval cellTest_18688 40 48 :=
  interval_of_check cellTest_18688 40 8 (by decide +kernel)

theorem cellTest_18688_block_6 : Interval cellTest_18688 48 56 :=
  interval_of_check cellTest_18688 48 8 (by decide +kernel)

theorem cellTest_18688_block_7 : Interval cellTest_18688 56 64 :=
  interval_of_check cellTest_18688 56 8 (by decide +kernel)

theorem cellTest_18688_block_8 : Interval cellTest_18688 64 72 :=
  interval_of_check cellTest_18688 64 8 (by decide +kernel)

theorem cellTest_18688_block_9 : Interval cellTest_18688 72 80 :=
  interval_of_check cellTest_18688 72 8 (by decide +kernel)

theorem cellTest_18688_block_10 : Interval cellTest_18688 80 88 :=
  interval_of_check cellTest_18688 80 8 (by decide +kernel)

theorem cellTest_18688_block_11 : Interval cellTest_18688 88 96 :=
  interval_of_check cellTest_18688 88 8 (by decide +kernel)

theorem cellTest_18688_block_12 : Interval cellTest_18688 96 104 :=
  interval_of_check cellTest_18688 96 8 (by decide +kernel)

theorem cellTest_18688_block_13 : Interval cellTest_18688 104 112 :=
  interval_of_check cellTest_18688 104 8 (by decide +kernel)

theorem cellTest_18688_block_14 : Interval cellTest_18688 112 120 :=
  interval_of_check cellTest_18688 112 8 (by decide +kernel)

theorem cellTest_18688_block_15 : Interval cellTest_18688 120 128 :=
  interval_of_check cellTest_18688 120 8 (by decide +kernel)

theorem cellTest_18688_block_16 : Interval cellTest_18688 128 136 :=
  interval_of_check cellTest_18688 128 8 (by decide +kernel)

theorem cellTest_18688_block_17 : Interval cellTest_18688 136 144 :=
  interval_of_check cellTest_18688 136 8 (by decide +kernel)

theorem cellTest_18688_block_18 : Interval cellTest_18688 144 152 :=
  interval_of_check cellTest_18688 144 8 (by decide +kernel)

theorem cellTest_18688_block_19 : Interval cellTest_18688 152 160 :=
  interval_of_check cellTest_18688 152 8 (by decide +kernel)

theorem cellTest_18688_block_20 : Interval cellTest_18688 160 168 :=
  interval_of_check cellTest_18688 160 8 (by decide +kernel)

theorem cellTest_18688_block_21 : Interval cellTest_18688 168 176 :=
  interval_of_check cellTest_18688 168 8 (by decide +kernel)

theorem cellTest_18688_block_22 : Interval cellTest_18688 176 184 :=
  interval_of_check cellTest_18688 176 8 (by decide +kernel)

theorem cellTest_18688_block_23 : Interval cellTest_18688 184 192 :=
  interval_of_check cellTest_18688 184 8 (by decide +kernel)

theorem cellTest_18688_block_24 : Interval cellTest_18688 192 200 :=
  interval_of_check cellTest_18688 192 8 (by decide +kernel)

theorem cellTest_18688_block_25 : Interval cellTest_18688 200 208 :=
  interval_of_check cellTest_18688 200 8 (by decide +kernel)

theorem cellTest_18688_block_26 : Interval cellTest_18688 208 216 :=
  interval_of_check cellTest_18688 208 8 (by decide +kernel)

theorem cellTest_18688_block_27 : Interval cellTest_18688 216 224 :=
  interval_of_check cellTest_18688 216 8 (by decide +kernel)

theorem cellTest_18688_block_28 : Interval cellTest_18688 224 232 :=
  interval_of_check cellTest_18688 224 8 (by decide +kernel)

theorem cellTest_18688_block_29 : Interval cellTest_18688 232 240 :=
  interval_of_check cellTest_18688 232 8 (by decide +kernel)

theorem cellTest_18688_block_30 : Interval cellTest_18688 240 248 :=
  interval_of_check cellTest_18688 240 8 (by decide +kernel)

theorem cellTest_18688_block_31 : Interval cellTest_18688 248 256 :=
  interval_of_check cellTest_18688 248 8 (by decide +kernel)

theorem cellTest_18688_complete : Interval cellTest_18688 0 256 :=
  (interval_append cellTest_18688 0 128 256
  (interval_append cellTest_18688 0 64 128
  (interval_append cellTest_18688 0 32 64
  (interval_append cellTest_18688 0 16 32
  (interval_append cellTest_18688 0 8 16
  cellTest_18688_block_0
  cellTest_18688_block_1)
  (interval_append cellTest_18688 16 24 32
  cellTest_18688_block_2
  cellTest_18688_block_3))
  (interval_append cellTest_18688 32 48 64
  (interval_append cellTest_18688 32 40 48
  cellTest_18688_block_4
  cellTest_18688_block_5)
  (interval_append cellTest_18688 48 56 64
  cellTest_18688_block_6
  cellTest_18688_block_7)))
  (interval_append cellTest_18688 64 96 128
  (interval_append cellTest_18688 64 80 96
  (interval_append cellTest_18688 64 72 80
  cellTest_18688_block_8
  cellTest_18688_block_9)
  (interval_append cellTest_18688 80 88 96
  cellTest_18688_block_10
  cellTest_18688_block_11))
  (interval_append cellTest_18688 96 112 128
  (interval_append cellTest_18688 96 104 112
  cellTest_18688_block_12
  cellTest_18688_block_13)
  (interval_append cellTest_18688 112 120 128
  cellTest_18688_block_14
  cellTest_18688_block_15))))
  (interval_append cellTest_18688 128 192 256
  (interval_append cellTest_18688 128 160 192
  (interval_append cellTest_18688 128 144 160
  (interval_append cellTest_18688 128 136 144
  cellTest_18688_block_16
  cellTest_18688_block_17)
  (interval_append cellTest_18688 144 152 160
  cellTest_18688_block_18
  cellTest_18688_block_19))
  (interval_append cellTest_18688 160 176 192
  (interval_append cellTest_18688 160 168 176
  cellTest_18688_block_20
  cellTest_18688_block_21)
  (interval_append cellTest_18688 176 184 192
  cellTest_18688_block_22
  cellTest_18688_block_23)))
  (interval_append cellTest_18688 192 224 256
  (interval_append cellTest_18688 192 208 224
  (interval_append cellTest_18688 192 200 208
  cellTest_18688_block_24
  cellTest_18688_block_25)
  (interval_append cellTest_18688 208 216 224
  cellTest_18688_block_26
  cellTest_18688_block_27))
  (interval_append cellTest_18688 224 240 256
  (interval_append cellTest_18688 224 232 240
  cellTest_18688_block_28
  cellTest_18688_block_29)
  (interval_append cellTest_18688 240 248 256
  cellTest_18688_block_30
  cellTest_18688_block_31)))))
theorem cellTestInterval18688 : Interval cellTest 18688 18944 := by
  intro i hlo hhi
  have h := cellTest_18688_complete (i-18688) (Nat.zero_le _) (by omega)
  simpa only [cellTest_18688, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells074 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_18944 (i : Nat) := cellTest (i+18944)
theorem cellTest_18944_block_0 : Interval cellTest_18944 0 8 :=
  interval_of_check cellTest_18944 0 8 (by decide +kernel)

theorem cellTest_18944_block_1 : Interval cellTest_18944 8 16 :=
  interval_of_check cellTest_18944 8 8 (by decide +kernel)

theorem cellTest_18944_block_2 : Interval cellTest_18944 16 24 :=
  interval_of_check cellTest_18944 16 8 (by decide +kernel)

theorem cellTest_18944_block_3 : Interval cellTest_18944 24 32 :=
  interval_of_check cellTest_18944 24 8 (by decide +kernel)

theorem cellTest_18944_block_4 : Interval cellTest_18944 32 40 :=
  interval_of_check cellTest_18944 32 8 (by decide +kernel)

theorem cellTest_18944_block_5 : Interval cellTest_18944 40 48 :=
  interval_of_check cellTest_18944 40 8 (by decide +kernel)

theorem cellTest_18944_block_6 : Interval cellTest_18944 48 56 :=
  interval_of_check cellTest_18944 48 8 (by decide +kernel)

theorem cellTest_18944_block_7 : Interval cellTest_18944 56 64 :=
  interval_of_check cellTest_18944 56 8 (by decide +kernel)

theorem cellTest_18944_block_8 : Interval cellTest_18944 64 72 :=
  interval_of_check cellTest_18944 64 8 (by decide +kernel)

theorem cellTest_18944_block_9 : Interval cellTest_18944 72 80 :=
  interval_of_check cellTest_18944 72 8 (by decide +kernel)

theorem cellTest_18944_block_10 : Interval cellTest_18944 80 88 :=
  interval_of_check cellTest_18944 80 8 (by decide +kernel)

theorem cellTest_18944_block_11 : Interval cellTest_18944 88 96 :=
  interval_of_check cellTest_18944 88 8 (by decide +kernel)

theorem cellTest_18944_block_12 : Interval cellTest_18944 96 104 :=
  interval_of_check cellTest_18944 96 8 (by decide +kernel)

theorem cellTest_18944_block_13 : Interval cellTest_18944 104 112 :=
  interval_of_check cellTest_18944 104 8 (by decide +kernel)

theorem cellTest_18944_block_14 : Interval cellTest_18944 112 120 :=
  interval_of_check cellTest_18944 112 8 (by decide +kernel)

theorem cellTest_18944_block_15 : Interval cellTest_18944 120 128 :=
  interval_of_check cellTest_18944 120 8 (by decide +kernel)

theorem cellTest_18944_block_16 : Interval cellTest_18944 128 136 :=
  interval_of_check cellTest_18944 128 8 (by decide +kernel)

theorem cellTest_18944_block_17 : Interval cellTest_18944 136 144 :=
  interval_of_check cellTest_18944 136 8 (by decide +kernel)

theorem cellTest_18944_block_18 : Interval cellTest_18944 144 152 :=
  interval_of_check cellTest_18944 144 8 (by decide +kernel)

theorem cellTest_18944_block_19 : Interval cellTest_18944 152 160 :=
  interval_of_check cellTest_18944 152 8 (by decide +kernel)

theorem cellTest_18944_block_20 : Interval cellTest_18944 160 168 :=
  interval_of_check cellTest_18944 160 8 (by decide +kernel)

theorem cellTest_18944_block_21 : Interval cellTest_18944 168 176 :=
  interval_of_check cellTest_18944 168 8 (by decide +kernel)

theorem cellTest_18944_block_22 : Interval cellTest_18944 176 184 :=
  interval_of_check cellTest_18944 176 8 (by decide +kernel)

theorem cellTest_18944_block_23 : Interval cellTest_18944 184 192 :=
  interval_of_check cellTest_18944 184 8 (by decide +kernel)

theorem cellTest_18944_block_24 : Interval cellTest_18944 192 200 :=
  interval_of_check cellTest_18944 192 8 (by decide +kernel)

theorem cellTest_18944_block_25 : Interval cellTest_18944 200 208 :=
  interval_of_check cellTest_18944 200 8 (by decide +kernel)

theorem cellTest_18944_block_26 : Interval cellTest_18944 208 216 :=
  interval_of_check cellTest_18944 208 8 (by decide +kernel)

theorem cellTest_18944_block_27 : Interval cellTest_18944 216 224 :=
  interval_of_check cellTest_18944 216 8 (by decide +kernel)

theorem cellTest_18944_block_28 : Interval cellTest_18944 224 232 :=
  interval_of_check cellTest_18944 224 8 (by decide +kernel)

theorem cellTest_18944_block_29 : Interval cellTest_18944 232 240 :=
  interval_of_check cellTest_18944 232 8 (by decide +kernel)

theorem cellTest_18944_block_30 : Interval cellTest_18944 240 248 :=
  interval_of_check cellTest_18944 240 8 (by decide +kernel)

theorem cellTest_18944_block_31 : Interval cellTest_18944 248 256 :=
  interval_of_check cellTest_18944 248 8 (by decide +kernel)

theorem cellTest_18944_complete : Interval cellTest_18944 0 256 :=
  (interval_append cellTest_18944 0 128 256
  (interval_append cellTest_18944 0 64 128
  (interval_append cellTest_18944 0 32 64
  (interval_append cellTest_18944 0 16 32
  (interval_append cellTest_18944 0 8 16
  cellTest_18944_block_0
  cellTest_18944_block_1)
  (interval_append cellTest_18944 16 24 32
  cellTest_18944_block_2
  cellTest_18944_block_3))
  (interval_append cellTest_18944 32 48 64
  (interval_append cellTest_18944 32 40 48
  cellTest_18944_block_4
  cellTest_18944_block_5)
  (interval_append cellTest_18944 48 56 64
  cellTest_18944_block_6
  cellTest_18944_block_7)))
  (interval_append cellTest_18944 64 96 128
  (interval_append cellTest_18944 64 80 96
  (interval_append cellTest_18944 64 72 80
  cellTest_18944_block_8
  cellTest_18944_block_9)
  (interval_append cellTest_18944 80 88 96
  cellTest_18944_block_10
  cellTest_18944_block_11))
  (interval_append cellTest_18944 96 112 128
  (interval_append cellTest_18944 96 104 112
  cellTest_18944_block_12
  cellTest_18944_block_13)
  (interval_append cellTest_18944 112 120 128
  cellTest_18944_block_14
  cellTest_18944_block_15))))
  (interval_append cellTest_18944 128 192 256
  (interval_append cellTest_18944 128 160 192
  (interval_append cellTest_18944 128 144 160
  (interval_append cellTest_18944 128 136 144
  cellTest_18944_block_16
  cellTest_18944_block_17)
  (interval_append cellTest_18944 144 152 160
  cellTest_18944_block_18
  cellTest_18944_block_19))
  (interval_append cellTest_18944 160 176 192
  (interval_append cellTest_18944 160 168 176
  cellTest_18944_block_20
  cellTest_18944_block_21)
  (interval_append cellTest_18944 176 184 192
  cellTest_18944_block_22
  cellTest_18944_block_23)))
  (interval_append cellTest_18944 192 224 256
  (interval_append cellTest_18944 192 208 224
  (interval_append cellTest_18944 192 200 208
  cellTest_18944_block_24
  cellTest_18944_block_25)
  (interval_append cellTest_18944 208 216 224
  cellTest_18944_block_26
  cellTest_18944_block_27))
  (interval_append cellTest_18944 224 240 256
  (interval_append cellTest_18944 224 232 240
  cellTest_18944_block_28
  cellTest_18944_block_29)
  (interval_append cellTest_18944 240 248 256
  cellTest_18944_block_30
  cellTest_18944_block_31)))))
theorem cellTestInterval18944 : Interval cellTest 18944 19200 := by
  intro i hlo hhi
  have h := cellTest_18944_complete (i-18944) (Nat.zero_le _) (by omega)
  simpa only [cellTest_18944, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells075 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_19200 (i : Nat) := cellTest (i+19200)
theorem cellTest_19200_block_0 : Interval cellTest_19200 0 8 :=
  interval_of_check cellTest_19200 0 8 (by decide +kernel)

theorem cellTest_19200_block_1 : Interval cellTest_19200 8 16 :=
  interval_of_check cellTest_19200 8 8 (by decide +kernel)

theorem cellTest_19200_block_2 : Interval cellTest_19200 16 24 :=
  interval_of_check cellTest_19200 16 8 (by decide +kernel)

theorem cellTest_19200_block_3 : Interval cellTest_19200 24 32 :=
  interval_of_check cellTest_19200 24 8 (by decide +kernel)

theorem cellTest_19200_block_4 : Interval cellTest_19200 32 40 :=
  interval_of_check cellTest_19200 32 8 (by decide +kernel)

theorem cellTest_19200_block_5 : Interval cellTest_19200 40 48 :=
  interval_of_check cellTest_19200 40 8 (by decide +kernel)

theorem cellTest_19200_block_6 : Interval cellTest_19200 48 56 :=
  interval_of_check cellTest_19200 48 8 (by decide +kernel)

theorem cellTest_19200_block_7 : Interval cellTest_19200 56 64 :=
  interval_of_check cellTest_19200 56 8 (by decide +kernel)

theorem cellTest_19200_block_8 : Interval cellTest_19200 64 72 :=
  interval_of_check cellTest_19200 64 8 (by decide +kernel)

theorem cellTest_19200_block_9 : Interval cellTest_19200 72 80 :=
  interval_of_check cellTest_19200 72 8 (by decide +kernel)

theorem cellTest_19200_block_10 : Interval cellTest_19200 80 88 :=
  interval_of_check cellTest_19200 80 8 (by decide +kernel)

theorem cellTest_19200_block_11 : Interval cellTest_19200 88 96 :=
  interval_of_check cellTest_19200 88 8 (by decide +kernel)

theorem cellTest_19200_block_12 : Interval cellTest_19200 96 104 :=
  interval_of_check cellTest_19200 96 8 (by decide +kernel)

theorem cellTest_19200_block_13 : Interval cellTest_19200 104 112 :=
  interval_of_check cellTest_19200 104 8 (by decide +kernel)

theorem cellTest_19200_block_14 : Interval cellTest_19200 112 120 :=
  interval_of_check cellTest_19200 112 8 (by decide +kernel)

theorem cellTest_19200_block_15 : Interval cellTest_19200 120 128 :=
  interval_of_check cellTest_19200 120 8 (by decide +kernel)

theorem cellTest_19200_block_16 : Interval cellTest_19200 128 136 :=
  interval_of_check cellTest_19200 128 8 (by decide +kernel)

theorem cellTest_19200_block_17 : Interval cellTest_19200 136 144 :=
  interval_of_check cellTest_19200 136 8 (by decide +kernel)

theorem cellTest_19200_block_18 : Interval cellTest_19200 144 152 :=
  interval_of_check cellTest_19200 144 8 (by decide +kernel)

theorem cellTest_19200_block_19 : Interval cellTest_19200 152 160 :=
  interval_of_check cellTest_19200 152 8 (by decide +kernel)

theorem cellTest_19200_block_20 : Interval cellTest_19200 160 168 :=
  interval_of_check cellTest_19200 160 8 (by decide +kernel)

theorem cellTest_19200_block_21 : Interval cellTest_19200 168 176 :=
  interval_of_check cellTest_19200 168 8 (by decide +kernel)

theorem cellTest_19200_block_22 : Interval cellTest_19200 176 184 :=
  interval_of_check cellTest_19200 176 8 (by decide +kernel)

theorem cellTest_19200_block_23 : Interval cellTest_19200 184 192 :=
  interval_of_check cellTest_19200 184 8 (by decide +kernel)

theorem cellTest_19200_block_24 : Interval cellTest_19200 192 200 :=
  interval_of_check cellTest_19200 192 8 (by decide +kernel)

theorem cellTest_19200_block_25 : Interval cellTest_19200 200 208 :=
  interval_of_check cellTest_19200 200 8 (by decide +kernel)

theorem cellTest_19200_block_26 : Interval cellTest_19200 208 216 :=
  interval_of_check cellTest_19200 208 8 (by decide +kernel)

theorem cellTest_19200_block_27 : Interval cellTest_19200 216 224 :=
  interval_of_check cellTest_19200 216 8 (by decide +kernel)

theorem cellTest_19200_block_28 : Interval cellTest_19200 224 232 :=
  interval_of_check cellTest_19200 224 8 (by decide +kernel)

theorem cellTest_19200_block_29 : Interval cellTest_19200 232 240 :=
  interval_of_check cellTest_19200 232 8 (by decide +kernel)

theorem cellTest_19200_block_30 : Interval cellTest_19200 240 248 :=
  interval_of_check cellTest_19200 240 8 (by decide +kernel)

theorem cellTest_19200_block_31 : Interval cellTest_19200 248 256 :=
  interval_of_check cellTest_19200 248 8 (by decide +kernel)

theorem cellTest_19200_complete : Interval cellTest_19200 0 256 :=
  (interval_append cellTest_19200 0 128 256
  (interval_append cellTest_19200 0 64 128
  (interval_append cellTest_19200 0 32 64
  (interval_append cellTest_19200 0 16 32
  (interval_append cellTest_19200 0 8 16
  cellTest_19200_block_0
  cellTest_19200_block_1)
  (interval_append cellTest_19200 16 24 32
  cellTest_19200_block_2
  cellTest_19200_block_3))
  (interval_append cellTest_19200 32 48 64
  (interval_append cellTest_19200 32 40 48
  cellTest_19200_block_4
  cellTest_19200_block_5)
  (interval_append cellTest_19200 48 56 64
  cellTest_19200_block_6
  cellTest_19200_block_7)))
  (interval_append cellTest_19200 64 96 128
  (interval_append cellTest_19200 64 80 96
  (interval_append cellTest_19200 64 72 80
  cellTest_19200_block_8
  cellTest_19200_block_9)
  (interval_append cellTest_19200 80 88 96
  cellTest_19200_block_10
  cellTest_19200_block_11))
  (interval_append cellTest_19200 96 112 128
  (interval_append cellTest_19200 96 104 112
  cellTest_19200_block_12
  cellTest_19200_block_13)
  (interval_append cellTest_19200 112 120 128
  cellTest_19200_block_14
  cellTest_19200_block_15))))
  (interval_append cellTest_19200 128 192 256
  (interval_append cellTest_19200 128 160 192
  (interval_append cellTest_19200 128 144 160
  (interval_append cellTest_19200 128 136 144
  cellTest_19200_block_16
  cellTest_19200_block_17)
  (interval_append cellTest_19200 144 152 160
  cellTest_19200_block_18
  cellTest_19200_block_19))
  (interval_append cellTest_19200 160 176 192
  (interval_append cellTest_19200 160 168 176
  cellTest_19200_block_20
  cellTest_19200_block_21)
  (interval_append cellTest_19200 176 184 192
  cellTest_19200_block_22
  cellTest_19200_block_23)))
  (interval_append cellTest_19200 192 224 256
  (interval_append cellTest_19200 192 208 224
  (interval_append cellTest_19200 192 200 208
  cellTest_19200_block_24
  cellTest_19200_block_25)
  (interval_append cellTest_19200 208 216 224
  cellTest_19200_block_26
  cellTest_19200_block_27))
  (interval_append cellTest_19200 224 240 256
  (interval_append cellTest_19200 224 232 240
  cellTest_19200_block_28
  cellTest_19200_block_29)
  (interval_append cellTest_19200 240 248 256
  cellTest_19200_block_30
  cellTest_19200_block_31)))))
theorem cellTestInterval19200 : Interval cellTest 19200 19456 := by
  intro i hlo hhi
  have h := cellTest_19200_complete (i-19200) (Nat.zero_le _) (by omega)
  simpa only [cellTest_19200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells076 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_19456 (i : Nat) := cellTest (i+19456)
theorem cellTest_19456_block_0 : Interval cellTest_19456 0 8 :=
  interval_of_check cellTest_19456 0 8 (by decide +kernel)

theorem cellTest_19456_block_1 : Interval cellTest_19456 8 16 :=
  interval_of_check cellTest_19456 8 8 (by decide +kernel)

theorem cellTest_19456_block_2 : Interval cellTest_19456 16 24 :=
  interval_of_check cellTest_19456 16 8 (by decide +kernel)

theorem cellTest_19456_block_3 : Interval cellTest_19456 24 32 :=
  interval_of_check cellTest_19456 24 8 (by decide +kernel)

theorem cellTest_19456_block_4 : Interval cellTest_19456 32 40 :=
  interval_of_check cellTest_19456 32 8 (by decide +kernel)

theorem cellTest_19456_block_5 : Interval cellTest_19456 40 48 :=
  interval_of_check cellTest_19456 40 8 (by decide +kernel)

theorem cellTest_19456_block_6 : Interval cellTest_19456 48 56 :=
  interval_of_check cellTest_19456 48 8 (by decide +kernel)

theorem cellTest_19456_block_7 : Interval cellTest_19456 56 64 :=
  interval_of_check cellTest_19456 56 8 (by decide +kernel)

theorem cellTest_19456_block_8 : Interval cellTest_19456 64 72 :=
  interval_of_check cellTest_19456 64 8 (by decide +kernel)

theorem cellTest_19456_block_9 : Interval cellTest_19456 72 80 :=
  interval_of_check cellTest_19456 72 8 (by decide +kernel)

theorem cellTest_19456_block_10 : Interval cellTest_19456 80 88 :=
  interval_of_check cellTest_19456 80 8 (by decide +kernel)

theorem cellTest_19456_block_11 : Interval cellTest_19456 88 96 :=
  interval_of_check cellTest_19456 88 8 (by decide +kernel)

theorem cellTest_19456_block_12 : Interval cellTest_19456 96 104 :=
  interval_of_check cellTest_19456 96 8 (by decide +kernel)

theorem cellTest_19456_block_13 : Interval cellTest_19456 104 112 :=
  interval_of_check cellTest_19456 104 8 (by decide +kernel)

theorem cellTest_19456_block_14 : Interval cellTest_19456 112 120 :=
  interval_of_check cellTest_19456 112 8 (by decide +kernel)

theorem cellTest_19456_block_15 : Interval cellTest_19456 120 128 :=
  interval_of_check cellTest_19456 120 8 (by decide +kernel)

theorem cellTest_19456_block_16 : Interval cellTest_19456 128 136 :=
  interval_of_check cellTest_19456 128 8 (by decide +kernel)

theorem cellTest_19456_block_17 : Interval cellTest_19456 136 144 :=
  interval_of_check cellTest_19456 136 8 (by decide +kernel)

theorem cellTest_19456_block_18 : Interval cellTest_19456 144 152 :=
  interval_of_check cellTest_19456 144 8 (by decide +kernel)

theorem cellTest_19456_block_19 : Interval cellTest_19456 152 160 :=
  interval_of_check cellTest_19456 152 8 (by decide +kernel)

theorem cellTest_19456_block_20 : Interval cellTest_19456 160 168 :=
  interval_of_check cellTest_19456 160 8 (by decide +kernel)

theorem cellTest_19456_block_21 : Interval cellTest_19456 168 176 :=
  interval_of_check cellTest_19456 168 8 (by decide +kernel)

theorem cellTest_19456_block_22 : Interval cellTest_19456 176 184 :=
  interval_of_check cellTest_19456 176 8 (by decide +kernel)

theorem cellTest_19456_block_23 : Interval cellTest_19456 184 192 :=
  interval_of_check cellTest_19456 184 8 (by decide +kernel)

theorem cellTest_19456_block_24 : Interval cellTest_19456 192 200 :=
  interval_of_check cellTest_19456 192 8 (by decide +kernel)

theorem cellTest_19456_block_25 : Interval cellTest_19456 200 208 :=
  interval_of_check cellTest_19456 200 8 (by decide +kernel)

theorem cellTest_19456_block_26 : Interval cellTest_19456 208 216 :=
  interval_of_check cellTest_19456 208 8 (by decide +kernel)

theorem cellTest_19456_block_27 : Interval cellTest_19456 216 224 :=
  interval_of_check cellTest_19456 216 8 (by decide +kernel)

theorem cellTest_19456_block_28 : Interval cellTest_19456 224 232 :=
  interval_of_check cellTest_19456 224 8 (by decide +kernel)

theorem cellTest_19456_block_29 : Interval cellTest_19456 232 240 :=
  interval_of_check cellTest_19456 232 8 (by decide +kernel)

theorem cellTest_19456_block_30 : Interval cellTest_19456 240 248 :=
  interval_of_check cellTest_19456 240 8 (by decide +kernel)

theorem cellTest_19456_block_31 : Interval cellTest_19456 248 256 :=
  interval_of_check cellTest_19456 248 8 (by decide +kernel)

theorem cellTest_19456_complete : Interval cellTest_19456 0 256 :=
  (interval_append cellTest_19456 0 128 256
  (interval_append cellTest_19456 0 64 128
  (interval_append cellTest_19456 0 32 64
  (interval_append cellTest_19456 0 16 32
  (interval_append cellTest_19456 0 8 16
  cellTest_19456_block_0
  cellTest_19456_block_1)
  (interval_append cellTest_19456 16 24 32
  cellTest_19456_block_2
  cellTest_19456_block_3))
  (interval_append cellTest_19456 32 48 64
  (interval_append cellTest_19456 32 40 48
  cellTest_19456_block_4
  cellTest_19456_block_5)
  (interval_append cellTest_19456 48 56 64
  cellTest_19456_block_6
  cellTest_19456_block_7)))
  (interval_append cellTest_19456 64 96 128
  (interval_append cellTest_19456 64 80 96
  (interval_append cellTest_19456 64 72 80
  cellTest_19456_block_8
  cellTest_19456_block_9)
  (interval_append cellTest_19456 80 88 96
  cellTest_19456_block_10
  cellTest_19456_block_11))
  (interval_append cellTest_19456 96 112 128
  (interval_append cellTest_19456 96 104 112
  cellTest_19456_block_12
  cellTest_19456_block_13)
  (interval_append cellTest_19456 112 120 128
  cellTest_19456_block_14
  cellTest_19456_block_15))))
  (interval_append cellTest_19456 128 192 256
  (interval_append cellTest_19456 128 160 192
  (interval_append cellTest_19456 128 144 160
  (interval_append cellTest_19456 128 136 144
  cellTest_19456_block_16
  cellTest_19456_block_17)
  (interval_append cellTest_19456 144 152 160
  cellTest_19456_block_18
  cellTest_19456_block_19))
  (interval_append cellTest_19456 160 176 192
  (interval_append cellTest_19456 160 168 176
  cellTest_19456_block_20
  cellTest_19456_block_21)
  (interval_append cellTest_19456 176 184 192
  cellTest_19456_block_22
  cellTest_19456_block_23)))
  (interval_append cellTest_19456 192 224 256
  (interval_append cellTest_19456 192 208 224
  (interval_append cellTest_19456 192 200 208
  cellTest_19456_block_24
  cellTest_19456_block_25)
  (interval_append cellTest_19456 208 216 224
  cellTest_19456_block_26
  cellTest_19456_block_27))
  (interval_append cellTest_19456 224 240 256
  (interval_append cellTest_19456 224 232 240
  cellTest_19456_block_28
  cellTest_19456_block_29)
  (interval_append cellTest_19456 240 248 256
  cellTest_19456_block_30
  cellTest_19456_block_31)))))
theorem cellTestInterval19456 : Interval cellTest 19456 19712 := by
  intro i hlo hhi
  have h := cellTest_19456_complete (i-19456) (Nat.zero_le _) (by omega)
  simpa only [cellTest_19456, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells077 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_19712 (i : Nat) := cellTest (i+19712)
theorem cellTest_19712_block_0 : Interval cellTest_19712 0 8 :=
  interval_of_check cellTest_19712 0 8 (by decide +kernel)

theorem cellTest_19712_block_1 : Interval cellTest_19712 8 16 :=
  interval_of_check cellTest_19712 8 8 (by decide +kernel)

theorem cellTest_19712_block_2 : Interval cellTest_19712 16 24 :=
  interval_of_check cellTest_19712 16 8 (by decide +kernel)

theorem cellTest_19712_block_3 : Interval cellTest_19712 24 32 :=
  interval_of_check cellTest_19712 24 8 (by decide +kernel)

theorem cellTest_19712_block_4 : Interval cellTest_19712 32 40 :=
  interval_of_check cellTest_19712 32 8 (by decide +kernel)

theorem cellTest_19712_block_5 : Interval cellTest_19712 40 48 :=
  interval_of_check cellTest_19712 40 8 (by decide +kernel)

theorem cellTest_19712_block_6 : Interval cellTest_19712 48 56 :=
  interval_of_check cellTest_19712 48 8 (by decide +kernel)

theorem cellTest_19712_block_7 : Interval cellTest_19712 56 64 :=
  interval_of_check cellTest_19712 56 8 (by decide +kernel)

theorem cellTest_19712_block_8 : Interval cellTest_19712 64 72 :=
  interval_of_check cellTest_19712 64 8 (by decide +kernel)

theorem cellTest_19712_block_9 : Interval cellTest_19712 72 80 :=
  interval_of_check cellTest_19712 72 8 (by decide +kernel)

theorem cellTest_19712_block_10 : Interval cellTest_19712 80 88 :=
  interval_of_check cellTest_19712 80 8 (by decide +kernel)

theorem cellTest_19712_block_11 : Interval cellTest_19712 88 96 :=
  interval_of_check cellTest_19712 88 8 (by decide +kernel)

theorem cellTest_19712_block_12 : Interval cellTest_19712 96 104 :=
  interval_of_check cellTest_19712 96 8 (by decide +kernel)

theorem cellTest_19712_block_13 : Interval cellTest_19712 104 112 :=
  interval_of_check cellTest_19712 104 8 (by decide +kernel)

theorem cellTest_19712_block_14 : Interval cellTest_19712 112 120 :=
  interval_of_check cellTest_19712 112 8 (by decide +kernel)

theorem cellTest_19712_block_15 : Interval cellTest_19712 120 128 :=
  interval_of_check cellTest_19712 120 8 (by decide +kernel)

theorem cellTest_19712_block_16 : Interval cellTest_19712 128 136 :=
  interval_of_check cellTest_19712 128 8 (by decide +kernel)

theorem cellTest_19712_block_17 : Interval cellTest_19712 136 144 :=
  interval_of_check cellTest_19712 136 8 (by decide +kernel)

theorem cellTest_19712_block_18 : Interval cellTest_19712 144 152 :=
  interval_of_check cellTest_19712 144 8 (by decide +kernel)

theorem cellTest_19712_block_19 : Interval cellTest_19712 152 160 :=
  interval_of_check cellTest_19712 152 8 (by decide +kernel)

theorem cellTest_19712_block_20 : Interval cellTest_19712 160 168 :=
  interval_of_check cellTest_19712 160 8 (by decide +kernel)

theorem cellTest_19712_block_21 : Interval cellTest_19712 168 176 :=
  interval_of_check cellTest_19712 168 8 (by decide +kernel)

theorem cellTest_19712_block_22 : Interval cellTest_19712 176 184 :=
  interval_of_check cellTest_19712 176 8 (by decide +kernel)

theorem cellTest_19712_block_23 : Interval cellTest_19712 184 192 :=
  interval_of_check cellTest_19712 184 8 (by decide +kernel)

theorem cellTest_19712_block_24 : Interval cellTest_19712 192 200 :=
  interval_of_check cellTest_19712 192 8 (by decide +kernel)

theorem cellTest_19712_block_25 : Interval cellTest_19712 200 208 :=
  interval_of_check cellTest_19712 200 8 (by decide +kernel)

theorem cellTest_19712_block_26 : Interval cellTest_19712 208 216 :=
  interval_of_check cellTest_19712 208 8 (by decide +kernel)

theorem cellTest_19712_block_27 : Interval cellTest_19712 216 224 :=
  interval_of_check cellTest_19712 216 8 (by decide +kernel)

theorem cellTest_19712_block_28 : Interval cellTest_19712 224 232 :=
  interval_of_check cellTest_19712 224 8 (by decide +kernel)

theorem cellTest_19712_block_29 : Interval cellTest_19712 232 240 :=
  interval_of_check cellTest_19712 232 8 (by decide +kernel)

theorem cellTest_19712_block_30 : Interval cellTest_19712 240 248 :=
  interval_of_check cellTest_19712 240 8 (by decide +kernel)

theorem cellTest_19712_block_31 : Interval cellTest_19712 248 256 :=
  interval_of_check cellTest_19712 248 8 (by decide +kernel)

theorem cellTest_19712_complete : Interval cellTest_19712 0 256 :=
  (interval_append cellTest_19712 0 128 256
  (interval_append cellTest_19712 0 64 128
  (interval_append cellTest_19712 0 32 64
  (interval_append cellTest_19712 0 16 32
  (interval_append cellTest_19712 0 8 16
  cellTest_19712_block_0
  cellTest_19712_block_1)
  (interval_append cellTest_19712 16 24 32
  cellTest_19712_block_2
  cellTest_19712_block_3))
  (interval_append cellTest_19712 32 48 64
  (interval_append cellTest_19712 32 40 48
  cellTest_19712_block_4
  cellTest_19712_block_5)
  (interval_append cellTest_19712 48 56 64
  cellTest_19712_block_6
  cellTest_19712_block_7)))
  (interval_append cellTest_19712 64 96 128
  (interval_append cellTest_19712 64 80 96
  (interval_append cellTest_19712 64 72 80
  cellTest_19712_block_8
  cellTest_19712_block_9)
  (interval_append cellTest_19712 80 88 96
  cellTest_19712_block_10
  cellTest_19712_block_11))
  (interval_append cellTest_19712 96 112 128
  (interval_append cellTest_19712 96 104 112
  cellTest_19712_block_12
  cellTest_19712_block_13)
  (interval_append cellTest_19712 112 120 128
  cellTest_19712_block_14
  cellTest_19712_block_15))))
  (interval_append cellTest_19712 128 192 256
  (interval_append cellTest_19712 128 160 192
  (interval_append cellTest_19712 128 144 160
  (interval_append cellTest_19712 128 136 144
  cellTest_19712_block_16
  cellTest_19712_block_17)
  (interval_append cellTest_19712 144 152 160
  cellTest_19712_block_18
  cellTest_19712_block_19))
  (interval_append cellTest_19712 160 176 192
  (interval_append cellTest_19712 160 168 176
  cellTest_19712_block_20
  cellTest_19712_block_21)
  (interval_append cellTest_19712 176 184 192
  cellTest_19712_block_22
  cellTest_19712_block_23)))
  (interval_append cellTest_19712 192 224 256
  (interval_append cellTest_19712 192 208 224
  (interval_append cellTest_19712 192 200 208
  cellTest_19712_block_24
  cellTest_19712_block_25)
  (interval_append cellTest_19712 208 216 224
  cellTest_19712_block_26
  cellTest_19712_block_27))
  (interval_append cellTest_19712 224 240 256
  (interval_append cellTest_19712 224 232 240
  cellTest_19712_block_28
  cellTest_19712_block_29)
  (interval_append cellTest_19712 240 248 256
  cellTest_19712_block_30
  cellTest_19712_block_31)))))
theorem cellTestInterval19712 : Interval cellTest 19712 19968 := by
  intro i hlo hhi
  have h := cellTest_19712_complete (i-19712) (Nat.zero_le _) (by omega)
  simpa only [cellTest_19712, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells078 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_19968 (i : Nat) := cellTest (i+19968)
theorem cellTest_19968_block_0 : Interval cellTest_19968 0 8 :=
  interval_of_check cellTest_19968 0 8 (by decide +kernel)

theorem cellTest_19968_block_1 : Interval cellTest_19968 8 16 :=
  interval_of_check cellTest_19968 8 8 (by decide +kernel)

theorem cellTest_19968_block_2 : Interval cellTest_19968 16 24 :=
  interval_of_check cellTest_19968 16 8 (by decide +kernel)

theorem cellTest_19968_block_3 : Interval cellTest_19968 24 32 :=
  interval_of_check cellTest_19968 24 8 (by decide +kernel)

theorem cellTest_19968_block_4 : Interval cellTest_19968 32 40 :=
  interval_of_check cellTest_19968 32 8 (by decide +kernel)

theorem cellTest_19968_block_5 : Interval cellTest_19968 40 48 :=
  interval_of_check cellTest_19968 40 8 (by decide +kernel)

theorem cellTest_19968_block_6 : Interval cellTest_19968 48 56 :=
  interval_of_check cellTest_19968 48 8 (by decide +kernel)

theorem cellTest_19968_block_7 : Interval cellTest_19968 56 64 :=
  interval_of_check cellTest_19968 56 8 (by decide +kernel)

theorem cellTest_19968_block_8 : Interval cellTest_19968 64 72 :=
  interval_of_check cellTest_19968 64 8 (by decide +kernel)

theorem cellTest_19968_block_9 : Interval cellTest_19968 72 80 :=
  interval_of_check cellTest_19968 72 8 (by decide +kernel)

theorem cellTest_19968_block_10 : Interval cellTest_19968 80 88 :=
  interval_of_check cellTest_19968 80 8 (by decide +kernel)

theorem cellTest_19968_block_11 : Interval cellTest_19968 88 96 :=
  interval_of_check cellTest_19968 88 8 (by decide +kernel)

theorem cellTest_19968_block_12 : Interval cellTest_19968 96 104 :=
  interval_of_check cellTest_19968 96 8 (by decide +kernel)

theorem cellTest_19968_block_13 : Interval cellTest_19968 104 112 :=
  interval_of_check cellTest_19968 104 8 (by decide +kernel)

theorem cellTest_19968_block_14 : Interval cellTest_19968 112 120 :=
  interval_of_check cellTest_19968 112 8 (by decide +kernel)

theorem cellTest_19968_block_15 : Interval cellTest_19968 120 128 :=
  interval_of_check cellTest_19968 120 8 (by decide +kernel)

theorem cellTest_19968_block_16 : Interval cellTest_19968 128 136 :=
  interval_of_check cellTest_19968 128 8 (by decide +kernel)

theorem cellTest_19968_block_17 : Interval cellTest_19968 136 144 :=
  interval_of_check cellTest_19968 136 8 (by decide +kernel)

theorem cellTest_19968_block_18 : Interval cellTest_19968 144 152 :=
  interval_of_check cellTest_19968 144 8 (by decide +kernel)

theorem cellTest_19968_block_19 : Interval cellTest_19968 152 160 :=
  interval_of_check cellTest_19968 152 8 (by decide +kernel)

theorem cellTest_19968_block_20 : Interval cellTest_19968 160 168 :=
  interval_of_check cellTest_19968 160 8 (by decide +kernel)

theorem cellTest_19968_block_21 : Interval cellTest_19968 168 176 :=
  interval_of_check cellTest_19968 168 8 (by decide +kernel)

theorem cellTest_19968_block_22 : Interval cellTest_19968 176 184 :=
  interval_of_check cellTest_19968 176 8 (by decide +kernel)

theorem cellTest_19968_block_23 : Interval cellTest_19968 184 192 :=
  interval_of_check cellTest_19968 184 8 (by decide +kernel)

theorem cellTest_19968_block_24 : Interval cellTest_19968 192 200 :=
  interval_of_check cellTest_19968 192 8 (by decide +kernel)

theorem cellTest_19968_block_25 : Interval cellTest_19968 200 208 :=
  interval_of_check cellTest_19968 200 8 (by decide +kernel)

theorem cellTest_19968_block_26 : Interval cellTest_19968 208 216 :=
  interval_of_check cellTest_19968 208 8 (by decide +kernel)

theorem cellTest_19968_block_27 : Interval cellTest_19968 216 224 :=
  interval_of_check cellTest_19968 216 8 (by decide +kernel)

theorem cellTest_19968_block_28 : Interval cellTest_19968 224 232 :=
  interval_of_check cellTest_19968 224 8 (by decide +kernel)

theorem cellTest_19968_block_29 : Interval cellTest_19968 232 240 :=
  interval_of_check cellTest_19968 232 8 (by decide +kernel)

theorem cellTest_19968_block_30 : Interval cellTest_19968 240 248 :=
  interval_of_check cellTest_19968 240 8 (by decide +kernel)

theorem cellTest_19968_block_31 : Interval cellTest_19968 248 256 :=
  interval_of_check cellTest_19968 248 8 (by decide +kernel)

theorem cellTest_19968_complete : Interval cellTest_19968 0 256 :=
  (interval_append cellTest_19968 0 128 256
  (interval_append cellTest_19968 0 64 128
  (interval_append cellTest_19968 0 32 64
  (interval_append cellTest_19968 0 16 32
  (interval_append cellTest_19968 0 8 16
  cellTest_19968_block_0
  cellTest_19968_block_1)
  (interval_append cellTest_19968 16 24 32
  cellTest_19968_block_2
  cellTest_19968_block_3))
  (interval_append cellTest_19968 32 48 64
  (interval_append cellTest_19968 32 40 48
  cellTest_19968_block_4
  cellTest_19968_block_5)
  (interval_append cellTest_19968 48 56 64
  cellTest_19968_block_6
  cellTest_19968_block_7)))
  (interval_append cellTest_19968 64 96 128
  (interval_append cellTest_19968 64 80 96
  (interval_append cellTest_19968 64 72 80
  cellTest_19968_block_8
  cellTest_19968_block_9)
  (interval_append cellTest_19968 80 88 96
  cellTest_19968_block_10
  cellTest_19968_block_11))
  (interval_append cellTest_19968 96 112 128
  (interval_append cellTest_19968 96 104 112
  cellTest_19968_block_12
  cellTest_19968_block_13)
  (interval_append cellTest_19968 112 120 128
  cellTest_19968_block_14
  cellTest_19968_block_15))))
  (interval_append cellTest_19968 128 192 256
  (interval_append cellTest_19968 128 160 192
  (interval_append cellTest_19968 128 144 160
  (interval_append cellTest_19968 128 136 144
  cellTest_19968_block_16
  cellTest_19968_block_17)
  (interval_append cellTest_19968 144 152 160
  cellTest_19968_block_18
  cellTest_19968_block_19))
  (interval_append cellTest_19968 160 176 192
  (interval_append cellTest_19968 160 168 176
  cellTest_19968_block_20
  cellTest_19968_block_21)
  (interval_append cellTest_19968 176 184 192
  cellTest_19968_block_22
  cellTest_19968_block_23)))
  (interval_append cellTest_19968 192 224 256
  (interval_append cellTest_19968 192 208 224
  (interval_append cellTest_19968 192 200 208
  cellTest_19968_block_24
  cellTest_19968_block_25)
  (interval_append cellTest_19968 208 216 224
  cellTest_19968_block_26
  cellTest_19968_block_27))
  (interval_append cellTest_19968 224 240 256
  (interval_append cellTest_19968 224 232 240
  cellTest_19968_block_28
  cellTest_19968_block_29)
  (interval_append cellTest_19968 240 248 256
  cellTest_19968_block_30
  cellTest_19968_block_31)))))
theorem cellTestInterval19968 : Interval cellTest 19968 20224 := by
  intro i hlo hhi
  have h := cellTest_19968_complete (i-19968) (Nat.zero_le _) (by omega)
  simpa only [cellTest_19968, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells079 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_20224 (i : Nat) := cellTest (i+20224)
theorem cellTest_20224_block_0 : Interval cellTest_20224 0 8 :=
  interval_of_check cellTest_20224 0 8 (by decide +kernel)

theorem cellTest_20224_block_1 : Interval cellTest_20224 8 16 :=
  interval_of_check cellTest_20224 8 8 (by decide +kernel)

theorem cellTest_20224_block_2 : Interval cellTest_20224 16 24 :=
  interval_of_check cellTest_20224 16 8 (by decide +kernel)

theorem cellTest_20224_block_3 : Interval cellTest_20224 24 32 :=
  interval_of_check cellTest_20224 24 8 (by decide +kernel)

theorem cellTest_20224_block_4 : Interval cellTest_20224 32 40 :=
  interval_of_check cellTest_20224 32 8 (by decide +kernel)

theorem cellTest_20224_block_5 : Interval cellTest_20224 40 48 :=
  interval_of_check cellTest_20224 40 8 (by decide +kernel)

theorem cellTest_20224_block_6 : Interval cellTest_20224 48 56 :=
  interval_of_check cellTest_20224 48 8 (by decide +kernel)

theorem cellTest_20224_block_7 : Interval cellTest_20224 56 64 :=
  interval_of_check cellTest_20224 56 8 (by decide +kernel)

theorem cellTest_20224_block_8 : Interval cellTest_20224 64 72 :=
  interval_of_check cellTest_20224 64 8 (by decide +kernel)

theorem cellTest_20224_block_9 : Interval cellTest_20224 72 80 :=
  interval_of_check cellTest_20224 72 8 (by decide +kernel)

theorem cellTest_20224_block_10 : Interval cellTest_20224 80 88 :=
  interval_of_check cellTest_20224 80 8 (by decide +kernel)

theorem cellTest_20224_block_11 : Interval cellTest_20224 88 96 :=
  interval_of_check cellTest_20224 88 8 (by decide +kernel)

theorem cellTest_20224_block_12 : Interval cellTest_20224 96 104 :=
  interval_of_check cellTest_20224 96 8 (by decide +kernel)

theorem cellTest_20224_block_13 : Interval cellTest_20224 104 112 :=
  interval_of_check cellTest_20224 104 8 (by decide +kernel)

theorem cellTest_20224_block_14 : Interval cellTest_20224 112 120 :=
  interval_of_check cellTest_20224 112 8 (by decide +kernel)

theorem cellTest_20224_block_15 : Interval cellTest_20224 120 128 :=
  interval_of_check cellTest_20224 120 8 (by decide +kernel)

theorem cellTest_20224_block_16 : Interval cellTest_20224 128 136 :=
  interval_of_check cellTest_20224 128 8 (by decide +kernel)

theorem cellTest_20224_block_17 : Interval cellTest_20224 136 144 :=
  interval_of_check cellTest_20224 136 8 (by decide +kernel)

theorem cellTest_20224_block_18 : Interval cellTest_20224 144 152 :=
  interval_of_check cellTest_20224 144 8 (by decide +kernel)

theorem cellTest_20224_block_19 : Interval cellTest_20224 152 160 :=
  interval_of_check cellTest_20224 152 8 (by decide +kernel)

theorem cellTest_20224_block_20 : Interval cellTest_20224 160 168 :=
  interval_of_check cellTest_20224 160 8 (by decide +kernel)

theorem cellTest_20224_block_21 : Interval cellTest_20224 168 176 :=
  interval_of_check cellTest_20224 168 8 (by decide +kernel)

theorem cellTest_20224_block_22 : Interval cellTest_20224 176 184 :=
  interval_of_check cellTest_20224 176 8 (by decide +kernel)

theorem cellTest_20224_block_23 : Interval cellTest_20224 184 192 :=
  interval_of_check cellTest_20224 184 8 (by decide +kernel)

theorem cellTest_20224_block_24 : Interval cellTest_20224 192 200 :=
  interval_of_check cellTest_20224 192 8 (by decide +kernel)

theorem cellTest_20224_block_25 : Interval cellTest_20224 200 208 :=
  interval_of_check cellTest_20224 200 8 (by decide +kernel)

theorem cellTest_20224_block_26 : Interval cellTest_20224 208 216 :=
  interval_of_check cellTest_20224 208 8 (by decide +kernel)

theorem cellTest_20224_block_27 : Interval cellTest_20224 216 224 :=
  interval_of_check cellTest_20224 216 8 (by decide +kernel)

theorem cellTest_20224_block_28 : Interval cellTest_20224 224 232 :=
  interval_of_check cellTest_20224 224 8 (by decide +kernel)

theorem cellTest_20224_block_29 : Interval cellTest_20224 232 240 :=
  interval_of_check cellTest_20224 232 8 (by decide +kernel)

theorem cellTest_20224_block_30 : Interval cellTest_20224 240 248 :=
  interval_of_check cellTest_20224 240 8 (by decide +kernel)

theorem cellTest_20224_block_31 : Interval cellTest_20224 248 256 :=
  interval_of_check cellTest_20224 248 8 (by decide +kernel)

theorem cellTest_20224_complete : Interval cellTest_20224 0 256 :=
  (interval_append cellTest_20224 0 128 256
  (interval_append cellTest_20224 0 64 128
  (interval_append cellTest_20224 0 32 64
  (interval_append cellTest_20224 0 16 32
  (interval_append cellTest_20224 0 8 16
  cellTest_20224_block_0
  cellTest_20224_block_1)
  (interval_append cellTest_20224 16 24 32
  cellTest_20224_block_2
  cellTest_20224_block_3))
  (interval_append cellTest_20224 32 48 64
  (interval_append cellTest_20224 32 40 48
  cellTest_20224_block_4
  cellTest_20224_block_5)
  (interval_append cellTest_20224 48 56 64
  cellTest_20224_block_6
  cellTest_20224_block_7)))
  (interval_append cellTest_20224 64 96 128
  (interval_append cellTest_20224 64 80 96
  (interval_append cellTest_20224 64 72 80
  cellTest_20224_block_8
  cellTest_20224_block_9)
  (interval_append cellTest_20224 80 88 96
  cellTest_20224_block_10
  cellTest_20224_block_11))
  (interval_append cellTest_20224 96 112 128
  (interval_append cellTest_20224 96 104 112
  cellTest_20224_block_12
  cellTest_20224_block_13)
  (interval_append cellTest_20224 112 120 128
  cellTest_20224_block_14
  cellTest_20224_block_15))))
  (interval_append cellTest_20224 128 192 256
  (interval_append cellTest_20224 128 160 192
  (interval_append cellTest_20224 128 144 160
  (interval_append cellTest_20224 128 136 144
  cellTest_20224_block_16
  cellTest_20224_block_17)
  (interval_append cellTest_20224 144 152 160
  cellTest_20224_block_18
  cellTest_20224_block_19))
  (interval_append cellTest_20224 160 176 192
  (interval_append cellTest_20224 160 168 176
  cellTest_20224_block_20
  cellTest_20224_block_21)
  (interval_append cellTest_20224 176 184 192
  cellTest_20224_block_22
  cellTest_20224_block_23)))
  (interval_append cellTest_20224 192 224 256
  (interval_append cellTest_20224 192 208 224
  (interval_append cellTest_20224 192 200 208
  cellTest_20224_block_24
  cellTest_20224_block_25)
  (interval_append cellTest_20224 208 216 224
  cellTest_20224_block_26
  cellTest_20224_block_27))
  (interval_append cellTest_20224 224 240 256
  (interval_append cellTest_20224 224 232 240
  cellTest_20224_block_28
  cellTest_20224_block_29)
  (interval_append cellTest_20224 240 248 256
  cellTest_20224_block_30
  cellTest_20224_block_31)))))
theorem cellTestInterval20224 : Interval cellTest 20224 20480 := by
  intro i hlo hhi
  have h := cellTest_20224_complete (i-20224) (Nat.zero_le _) (by omega)
  simpa only [cellTest_20224, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
