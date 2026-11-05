module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheCells032 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_8192 (i : Nat) := cellTest (i+8192)
theorem cellTest_8192_block_0 : Interval cellTest_8192 0 8 :=
  interval_of_check cellTest_8192 0 8 (by decide +kernel)

theorem cellTest_8192_block_1 : Interval cellTest_8192 8 16 :=
  interval_of_check cellTest_8192 8 8 (by decide +kernel)

theorem cellTest_8192_block_2 : Interval cellTest_8192 16 24 :=
  interval_of_check cellTest_8192 16 8 (by decide +kernel)

theorem cellTest_8192_block_3 : Interval cellTest_8192 24 32 :=
  interval_of_check cellTest_8192 24 8 (by decide +kernel)

theorem cellTest_8192_block_4 : Interval cellTest_8192 32 40 :=
  interval_of_check cellTest_8192 32 8 (by decide +kernel)

theorem cellTest_8192_block_5 : Interval cellTest_8192 40 48 :=
  interval_of_check cellTest_8192 40 8 (by decide +kernel)

theorem cellTest_8192_block_6 : Interval cellTest_8192 48 56 :=
  interval_of_check cellTest_8192 48 8 (by decide +kernel)

theorem cellTest_8192_block_7 : Interval cellTest_8192 56 64 :=
  interval_of_check cellTest_8192 56 8 (by decide +kernel)

theorem cellTest_8192_block_8 : Interval cellTest_8192 64 72 :=
  interval_of_check cellTest_8192 64 8 (by decide +kernel)

theorem cellTest_8192_block_9 : Interval cellTest_8192 72 80 :=
  interval_of_check cellTest_8192 72 8 (by decide +kernel)

theorem cellTest_8192_block_10 : Interval cellTest_8192 80 88 :=
  interval_of_check cellTest_8192 80 8 (by decide +kernel)

theorem cellTest_8192_block_11 : Interval cellTest_8192 88 96 :=
  interval_of_check cellTest_8192 88 8 (by decide +kernel)

theorem cellTest_8192_block_12 : Interval cellTest_8192 96 104 :=
  interval_of_check cellTest_8192 96 8 (by decide +kernel)

theorem cellTest_8192_block_13 : Interval cellTest_8192 104 112 :=
  interval_of_check cellTest_8192 104 8 (by decide +kernel)

theorem cellTest_8192_block_14 : Interval cellTest_8192 112 120 :=
  interval_of_check cellTest_8192 112 8 (by decide +kernel)

theorem cellTest_8192_block_15 : Interval cellTest_8192 120 128 :=
  interval_of_check cellTest_8192 120 8 (by decide +kernel)

theorem cellTest_8192_block_16 : Interval cellTest_8192 128 136 :=
  interval_of_check cellTest_8192 128 8 (by decide +kernel)

theorem cellTest_8192_block_17 : Interval cellTest_8192 136 144 :=
  interval_of_check cellTest_8192 136 8 (by decide +kernel)

theorem cellTest_8192_block_18 : Interval cellTest_8192 144 152 :=
  interval_of_check cellTest_8192 144 8 (by decide +kernel)

theorem cellTest_8192_block_19 : Interval cellTest_8192 152 160 :=
  interval_of_check cellTest_8192 152 8 (by decide +kernel)

theorem cellTest_8192_block_20 : Interval cellTest_8192 160 168 :=
  interval_of_check cellTest_8192 160 8 (by decide +kernel)

theorem cellTest_8192_block_21 : Interval cellTest_8192 168 176 :=
  interval_of_check cellTest_8192 168 8 (by decide +kernel)

theorem cellTest_8192_block_22 : Interval cellTest_8192 176 184 :=
  interval_of_check cellTest_8192 176 8 (by decide +kernel)

theorem cellTest_8192_block_23 : Interval cellTest_8192 184 192 :=
  interval_of_check cellTest_8192 184 8 (by decide +kernel)

theorem cellTest_8192_block_24 : Interval cellTest_8192 192 200 :=
  interval_of_check cellTest_8192 192 8 (by decide +kernel)

theorem cellTest_8192_block_25 : Interval cellTest_8192 200 208 :=
  interval_of_check cellTest_8192 200 8 (by decide +kernel)

theorem cellTest_8192_block_26 : Interval cellTest_8192 208 216 :=
  interval_of_check cellTest_8192 208 8 (by decide +kernel)

theorem cellTest_8192_block_27 : Interval cellTest_8192 216 224 :=
  interval_of_check cellTest_8192 216 8 (by decide +kernel)

theorem cellTest_8192_block_28 : Interval cellTest_8192 224 232 :=
  interval_of_check cellTest_8192 224 8 (by decide +kernel)

theorem cellTest_8192_block_29 : Interval cellTest_8192 232 240 :=
  interval_of_check cellTest_8192 232 8 (by decide +kernel)

theorem cellTest_8192_block_30 : Interval cellTest_8192 240 248 :=
  interval_of_check cellTest_8192 240 8 (by decide +kernel)

theorem cellTest_8192_block_31 : Interval cellTest_8192 248 256 :=
  interval_of_check cellTest_8192 248 8 (by decide +kernel)

theorem cellTest_8192_complete : Interval cellTest_8192 0 256 :=
  (interval_append cellTest_8192 0 128 256
  (interval_append cellTest_8192 0 64 128
  (interval_append cellTest_8192 0 32 64
  (interval_append cellTest_8192 0 16 32
  (interval_append cellTest_8192 0 8 16
  cellTest_8192_block_0
  cellTest_8192_block_1)
  (interval_append cellTest_8192 16 24 32
  cellTest_8192_block_2
  cellTest_8192_block_3))
  (interval_append cellTest_8192 32 48 64
  (interval_append cellTest_8192 32 40 48
  cellTest_8192_block_4
  cellTest_8192_block_5)
  (interval_append cellTest_8192 48 56 64
  cellTest_8192_block_6
  cellTest_8192_block_7)))
  (interval_append cellTest_8192 64 96 128
  (interval_append cellTest_8192 64 80 96
  (interval_append cellTest_8192 64 72 80
  cellTest_8192_block_8
  cellTest_8192_block_9)
  (interval_append cellTest_8192 80 88 96
  cellTest_8192_block_10
  cellTest_8192_block_11))
  (interval_append cellTest_8192 96 112 128
  (interval_append cellTest_8192 96 104 112
  cellTest_8192_block_12
  cellTest_8192_block_13)
  (interval_append cellTest_8192 112 120 128
  cellTest_8192_block_14
  cellTest_8192_block_15))))
  (interval_append cellTest_8192 128 192 256
  (interval_append cellTest_8192 128 160 192
  (interval_append cellTest_8192 128 144 160
  (interval_append cellTest_8192 128 136 144
  cellTest_8192_block_16
  cellTest_8192_block_17)
  (interval_append cellTest_8192 144 152 160
  cellTest_8192_block_18
  cellTest_8192_block_19))
  (interval_append cellTest_8192 160 176 192
  (interval_append cellTest_8192 160 168 176
  cellTest_8192_block_20
  cellTest_8192_block_21)
  (interval_append cellTest_8192 176 184 192
  cellTest_8192_block_22
  cellTest_8192_block_23)))
  (interval_append cellTest_8192 192 224 256
  (interval_append cellTest_8192 192 208 224
  (interval_append cellTest_8192 192 200 208
  cellTest_8192_block_24
  cellTest_8192_block_25)
  (interval_append cellTest_8192 208 216 224
  cellTest_8192_block_26
  cellTest_8192_block_27))
  (interval_append cellTest_8192 224 240 256
  (interval_append cellTest_8192 224 232 240
  cellTest_8192_block_28
  cellTest_8192_block_29)
  (interval_append cellTest_8192 240 248 256
  cellTest_8192_block_30
  cellTest_8192_block_31)))))
theorem cellTestInterval8192 : Interval cellTest 8192 8448 := by
  intro i hlo hhi
  have h := cellTest_8192_complete (i-8192) (Nat.zero_le _) (by omega)
  simpa only [cellTest_8192, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells033 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_8448 (i : Nat) := cellTest (i+8448)
theorem cellTest_8448_block_0 : Interval cellTest_8448 0 8 :=
  interval_of_check cellTest_8448 0 8 (by decide +kernel)

theorem cellTest_8448_block_1 : Interval cellTest_8448 8 16 :=
  interval_of_check cellTest_8448 8 8 (by decide +kernel)

theorem cellTest_8448_block_2 : Interval cellTest_8448 16 24 :=
  interval_of_check cellTest_8448 16 8 (by decide +kernel)

theorem cellTest_8448_block_3 : Interval cellTest_8448 24 32 :=
  interval_of_check cellTest_8448 24 8 (by decide +kernel)

theorem cellTest_8448_block_4 : Interval cellTest_8448 32 40 :=
  interval_of_check cellTest_8448 32 8 (by decide +kernel)

theorem cellTest_8448_block_5 : Interval cellTest_8448 40 48 :=
  interval_of_check cellTest_8448 40 8 (by decide +kernel)

theorem cellTest_8448_block_6 : Interval cellTest_8448 48 56 :=
  interval_of_check cellTest_8448 48 8 (by decide +kernel)

theorem cellTest_8448_block_7 : Interval cellTest_8448 56 64 :=
  interval_of_check cellTest_8448 56 8 (by decide +kernel)

theorem cellTest_8448_block_8 : Interval cellTest_8448 64 72 :=
  interval_of_check cellTest_8448 64 8 (by decide +kernel)

theorem cellTest_8448_block_9 : Interval cellTest_8448 72 80 :=
  interval_of_check cellTest_8448 72 8 (by decide +kernel)

theorem cellTest_8448_block_10 : Interval cellTest_8448 80 88 :=
  interval_of_check cellTest_8448 80 8 (by decide +kernel)

theorem cellTest_8448_block_11 : Interval cellTest_8448 88 96 :=
  interval_of_check cellTest_8448 88 8 (by decide +kernel)

theorem cellTest_8448_block_12 : Interval cellTest_8448 96 104 :=
  interval_of_check cellTest_8448 96 8 (by decide +kernel)

theorem cellTest_8448_block_13 : Interval cellTest_8448 104 112 :=
  interval_of_check cellTest_8448 104 8 (by decide +kernel)

theorem cellTest_8448_block_14 : Interval cellTest_8448 112 120 :=
  interval_of_check cellTest_8448 112 8 (by decide +kernel)

theorem cellTest_8448_block_15 : Interval cellTest_8448 120 128 :=
  interval_of_check cellTest_8448 120 8 (by decide +kernel)

theorem cellTest_8448_block_16 : Interval cellTest_8448 128 136 :=
  interval_of_check cellTest_8448 128 8 (by decide +kernel)

theorem cellTest_8448_block_17 : Interval cellTest_8448 136 144 :=
  interval_of_check cellTest_8448 136 8 (by decide +kernel)

theorem cellTest_8448_block_18 : Interval cellTest_8448 144 152 :=
  interval_of_check cellTest_8448 144 8 (by decide +kernel)

theorem cellTest_8448_block_19 : Interval cellTest_8448 152 160 :=
  interval_of_check cellTest_8448 152 8 (by decide +kernel)

theorem cellTest_8448_block_20 : Interval cellTest_8448 160 168 :=
  interval_of_check cellTest_8448 160 8 (by decide +kernel)

theorem cellTest_8448_block_21 : Interval cellTest_8448 168 176 :=
  interval_of_check cellTest_8448 168 8 (by decide +kernel)

theorem cellTest_8448_block_22 : Interval cellTest_8448 176 184 :=
  interval_of_check cellTest_8448 176 8 (by decide +kernel)

theorem cellTest_8448_block_23 : Interval cellTest_8448 184 192 :=
  interval_of_check cellTest_8448 184 8 (by decide +kernel)

theorem cellTest_8448_block_24 : Interval cellTest_8448 192 200 :=
  interval_of_check cellTest_8448 192 8 (by decide +kernel)

theorem cellTest_8448_block_25 : Interval cellTest_8448 200 208 :=
  interval_of_check cellTest_8448 200 8 (by decide +kernel)

theorem cellTest_8448_block_26 : Interval cellTest_8448 208 216 :=
  interval_of_check cellTest_8448 208 8 (by decide +kernel)

theorem cellTest_8448_block_27 : Interval cellTest_8448 216 224 :=
  interval_of_check cellTest_8448 216 8 (by decide +kernel)

theorem cellTest_8448_block_28 : Interval cellTest_8448 224 232 :=
  interval_of_check cellTest_8448 224 8 (by decide +kernel)

theorem cellTest_8448_block_29 : Interval cellTest_8448 232 240 :=
  interval_of_check cellTest_8448 232 8 (by decide +kernel)

theorem cellTest_8448_block_30 : Interval cellTest_8448 240 248 :=
  interval_of_check cellTest_8448 240 8 (by decide +kernel)

theorem cellTest_8448_block_31 : Interval cellTest_8448 248 256 :=
  interval_of_check cellTest_8448 248 8 (by decide +kernel)

theorem cellTest_8448_complete : Interval cellTest_8448 0 256 :=
  (interval_append cellTest_8448 0 128 256
  (interval_append cellTest_8448 0 64 128
  (interval_append cellTest_8448 0 32 64
  (interval_append cellTest_8448 0 16 32
  (interval_append cellTest_8448 0 8 16
  cellTest_8448_block_0
  cellTest_8448_block_1)
  (interval_append cellTest_8448 16 24 32
  cellTest_8448_block_2
  cellTest_8448_block_3))
  (interval_append cellTest_8448 32 48 64
  (interval_append cellTest_8448 32 40 48
  cellTest_8448_block_4
  cellTest_8448_block_5)
  (interval_append cellTest_8448 48 56 64
  cellTest_8448_block_6
  cellTest_8448_block_7)))
  (interval_append cellTest_8448 64 96 128
  (interval_append cellTest_8448 64 80 96
  (interval_append cellTest_8448 64 72 80
  cellTest_8448_block_8
  cellTest_8448_block_9)
  (interval_append cellTest_8448 80 88 96
  cellTest_8448_block_10
  cellTest_8448_block_11))
  (interval_append cellTest_8448 96 112 128
  (interval_append cellTest_8448 96 104 112
  cellTest_8448_block_12
  cellTest_8448_block_13)
  (interval_append cellTest_8448 112 120 128
  cellTest_8448_block_14
  cellTest_8448_block_15))))
  (interval_append cellTest_8448 128 192 256
  (interval_append cellTest_8448 128 160 192
  (interval_append cellTest_8448 128 144 160
  (interval_append cellTest_8448 128 136 144
  cellTest_8448_block_16
  cellTest_8448_block_17)
  (interval_append cellTest_8448 144 152 160
  cellTest_8448_block_18
  cellTest_8448_block_19))
  (interval_append cellTest_8448 160 176 192
  (interval_append cellTest_8448 160 168 176
  cellTest_8448_block_20
  cellTest_8448_block_21)
  (interval_append cellTest_8448 176 184 192
  cellTest_8448_block_22
  cellTest_8448_block_23)))
  (interval_append cellTest_8448 192 224 256
  (interval_append cellTest_8448 192 208 224
  (interval_append cellTest_8448 192 200 208
  cellTest_8448_block_24
  cellTest_8448_block_25)
  (interval_append cellTest_8448 208 216 224
  cellTest_8448_block_26
  cellTest_8448_block_27))
  (interval_append cellTest_8448 224 240 256
  (interval_append cellTest_8448 224 232 240
  cellTest_8448_block_28
  cellTest_8448_block_29)
  (interval_append cellTest_8448 240 248 256
  cellTest_8448_block_30
  cellTest_8448_block_31)))))
theorem cellTestInterval8448 : Interval cellTest 8448 8704 := by
  intro i hlo hhi
  have h := cellTest_8448_complete (i-8448) (Nat.zero_le _) (by omega)
  simpa only [cellTest_8448, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells034 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_8704 (i : Nat) := cellTest (i+8704)
theorem cellTest_8704_block_0 : Interval cellTest_8704 0 8 :=
  interval_of_check cellTest_8704 0 8 (by decide +kernel)

theorem cellTest_8704_block_1 : Interval cellTest_8704 8 16 :=
  interval_of_check cellTest_8704 8 8 (by decide +kernel)

theorem cellTest_8704_block_2 : Interval cellTest_8704 16 24 :=
  interval_of_check cellTest_8704 16 8 (by decide +kernel)

theorem cellTest_8704_block_3 : Interval cellTest_8704 24 32 :=
  interval_of_check cellTest_8704 24 8 (by decide +kernel)

theorem cellTest_8704_block_4 : Interval cellTest_8704 32 40 :=
  interval_of_check cellTest_8704 32 8 (by decide +kernel)

theorem cellTest_8704_block_5 : Interval cellTest_8704 40 48 :=
  interval_of_check cellTest_8704 40 8 (by decide +kernel)

theorem cellTest_8704_block_6 : Interval cellTest_8704 48 56 :=
  interval_of_check cellTest_8704 48 8 (by decide +kernel)

theorem cellTest_8704_block_7 : Interval cellTest_8704 56 64 :=
  interval_of_check cellTest_8704 56 8 (by decide +kernel)

theorem cellTest_8704_block_8 : Interval cellTest_8704 64 72 :=
  interval_of_check cellTest_8704 64 8 (by decide +kernel)

theorem cellTest_8704_block_9 : Interval cellTest_8704 72 80 :=
  interval_of_check cellTest_8704 72 8 (by decide +kernel)

theorem cellTest_8704_block_10 : Interval cellTest_8704 80 88 :=
  interval_of_check cellTest_8704 80 8 (by decide +kernel)

theorem cellTest_8704_block_11 : Interval cellTest_8704 88 96 :=
  interval_of_check cellTest_8704 88 8 (by decide +kernel)

theorem cellTest_8704_block_12 : Interval cellTest_8704 96 104 :=
  interval_of_check cellTest_8704 96 8 (by decide +kernel)

theorem cellTest_8704_block_13 : Interval cellTest_8704 104 112 :=
  interval_of_check cellTest_8704 104 8 (by decide +kernel)

theorem cellTest_8704_block_14 : Interval cellTest_8704 112 120 :=
  interval_of_check cellTest_8704 112 8 (by decide +kernel)

theorem cellTest_8704_block_15 : Interval cellTest_8704 120 128 :=
  interval_of_check cellTest_8704 120 8 (by decide +kernel)

theorem cellTest_8704_block_16 : Interval cellTest_8704 128 136 :=
  interval_of_check cellTest_8704 128 8 (by decide +kernel)

theorem cellTest_8704_block_17 : Interval cellTest_8704 136 144 :=
  interval_of_check cellTest_8704 136 8 (by decide +kernel)

theorem cellTest_8704_block_18 : Interval cellTest_8704 144 152 :=
  interval_of_check cellTest_8704 144 8 (by decide +kernel)

theorem cellTest_8704_block_19 : Interval cellTest_8704 152 160 :=
  interval_of_check cellTest_8704 152 8 (by decide +kernel)

theorem cellTest_8704_block_20 : Interval cellTest_8704 160 168 :=
  interval_of_check cellTest_8704 160 8 (by decide +kernel)

theorem cellTest_8704_block_21 : Interval cellTest_8704 168 176 :=
  interval_of_check cellTest_8704 168 8 (by decide +kernel)

theorem cellTest_8704_block_22 : Interval cellTest_8704 176 184 :=
  interval_of_check cellTest_8704 176 8 (by decide +kernel)

theorem cellTest_8704_block_23 : Interval cellTest_8704 184 192 :=
  interval_of_check cellTest_8704 184 8 (by decide +kernel)

theorem cellTest_8704_block_24 : Interval cellTest_8704 192 200 :=
  interval_of_check cellTest_8704 192 8 (by decide +kernel)

theorem cellTest_8704_block_25 : Interval cellTest_8704 200 208 :=
  interval_of_check cellTest_8704 200 8 (by decide +kernel)

theorem cellTest_8704_block_26 : Interval cellTest_8704 208 216 :=
  interval_of_check cellTest_8704 208 8 (by decide +kernel)

theorem cellTest_8704_block_27 : Interval cellTest_8704 216 224 :=
  interval_of_check cellTest_8704 216 8 (by decide +kernel)

theorem cellTest_8704_block_28 : Interval cellTest_8704 224 232 :=
  interval_of_check cellTest_8704 224 8 (by decide +kernel)

theorem cellTest_8704_block_29 : Interval cellTest_8704 232 240 :=
  interval_of_check cellTest_8704 232 8 (by decide +kernel)

theorem cellTest_8704_block_30 : Interval cellTest_8704 240 248 :=
  interval_of_check cellTest_8704 240 8 (by decide +kernel)

theorem cellTest_8704_block_31 : Interval cellTest_8704 248 256 :=
  interval_of_check cellTest_8704 248 8 (by decide +kernel)

theorem cellTest_8704_complete : Interval cellTest_8704 0 256 :=
  (interval_append cellTest_8704 0 128 256
  (interval_append cellTest_8704 0 64 128
  (interval_append cellTest_8704 0 32 64
  (interval_append cellTest_8704 0 16 32
  (interval_append cellTest_8704 0 8 16
  cellTest_8704_block_0
  cellTest_8704_block_1)
  (interval_append cellTest_8704 16 24 32
  cellTest_8704_block_2
  cellTest_8704_block_3))
  (interval_append cellTest_8704 32 48 64
  (interval_append cellTest_8704 32 40 48
  cellTest_8704_block_4
  cellTest_8704_block_5)
  (interval_append cellTest_8704 48 56 64
  cellTest_8704_block_6
  cellTest_8704_block_7)))
  (interval_append cellTest_8704 64 96 128
  (interval_append cellTest_8704 64 80 96
  (interval_append cellTest_8704 64 72 80
  cellTest_8704_block_8
  cellTest_8704_block_9)
  (interval_append cellTest_8704 80 88 96
  cellTest_8704_block_10
  cellTest_8704_block_11))
  (interval_append cellTest_8704 96 112 128
  (interval_append cellTest_8704 96 104 112
  cellTest_8704_block_12
  cellTest_8704_block_13)
  (interval_append cellTest_8704 112 120 128
  cellTest_8704_block_14
  cellTest_8704_block_15))))
  (interval_append cellTest_8704 128 192 256
  (interval_append cellTest_8704 128 160 192
  (interval_append cellTest_8704 128 144 160
  (interval_append cellTest_8704 128 136 144
  cellTest_8704_block_16
  cellTest_8704_block_17)
  (interval_append cellTest_8704 144 152 160
  cellTest_8704_block_18
  cellTest_8704_block_19))
  (interval_append cellTest_8704 160 176 192
  (interval_append cellTest_8704 160 168 176
  cellTest_8704_block_20
  cellTest_8704_block_21)
  (interval_append cellTest_8704 176 184 192
  cellTest_8704_block_22
  cellTest_8704_block_23)))
  (interval_append cellTest_8704 192 224 256
  (interval_append cellTest_8704 192 208 224
  (interval_append cellTest_8704 192 200 208
  cellTest_8704_block_24
  cellTest_8704_block_25)
  (interval_append cellTest_8704 208 216 224
  cellTest_8704_block_26
  cellTest_8704_block_27))
  (interval_append cellTest_8704 224 240 256
  (interval_append cellTest_8704 224 232 240
  cellTest_8704_block_28
  cellTest_8704_block_29)
  (interval_append cellTest_8704 240 248 256
  cellTest_8704_block_30
  cellTest_8704_block_31)))))
theorem cellTestInterval8704 : Interval cellTest 8704 8960 := by
  intro i hlo hhi
  have h := cellTest_8704_complete (i-8704) (Nat.zero_le _) (by omega)
  simpa only [cellTest_8704, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells035 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_8960 (i : Nat) := cellTest (i+8960)
theorem cellTest_8960_block_0 : Interval cellTest_8960 0 8 :=
  interval_of_check cellTest_8960 0 8 (by decide +kernel)

theorem cellTest_8960_block_1 : Interval cellTest_8960 8 16 :=
  interval_of_check cellTest_8960 8 8 (by decide +kernel)

theorem cellTest_8960_block_2 : Interval cellTest_8960 16 24 :=
  interval_of_check cellTest_8960 16 8 (by decide +kernel)

theorem cellTest_8960_block_3 : Interval cellTest_8960 24 32 :=
  interval_of_check cellTest_8960 24 8 (by decide +kernel)

theorem cellTest_8960_block_4 : Interval cellTest_8960 32 40 :=
  interval_of_check cellTest_8960 32 8 (by decide +kernel)

theorem cellTest_8960_block_5 : Interval cellTest_8960 40 48 :=
  interval_of_check cellTest_8960 40 8 (by decide +kernel)

theorem cellTest_8960_block_6 : Interval cellTest_8960 48 56 :=
  interval_of_check cellTest_8960 48 8 (by decide +kernel)

theorem cellTest_8960_block_7 : Interval cellTest_8960 56 64 :=
  interval_of_check cellTest_8960 56 8 (by decide +kernel)

theorem cellTest_8960_block_8 : Interval cellTest_8960 64 72 :=
  interval_of_check cellTest_8960 64 8 (by decide +kernel)

theorem cellTest_8960_block_9 : Interval cellTest_8960 72 80 :=
  interval_of_check cellTest_8960 72 8 (by decide +kernel)

theorem cellTest_8960_block_10 : Interval cellTest_8960 80 88 :=
  interval_of_check cellTest_8960 80 8 (by decide +kernel)

theorem cellTest_8960_block_11 : Interval cellTest_8960 88 96 :=
  interval_of_check cellTest_8960 88 8 (by decide +kernel)

theorem cellTest_8960_block_12 : Interval cellTest_8960 96 104 :=
  interval_of_check cellTest_8960 96 8 (by decide +kernel)

theorem cellTest_8960_block_13 : Interval cellTest_8960 104 112 :=
  interval_of_check cellTest_8960 104 8 (by decide +kernel)

theorem cellTest_8960_block_14 : Interval cellTest_8960 112 120 :=
  interval_of_check cellTest_8960 112 8 (by decide +kernel)

theorem cellTest_8960_block_15 : Interval cellTest_8960 120 128 :=
  interval_of_check cellTest_8960 120 8 (by decide +kernel)

theorem cellTest_8960_block_16 : Interval cellTest_8960 128 136 :=
  interval_of_check cellTest_8960 128 8 (by decide +kernel)

theorem cellTest_8960_block_17 : Interval cellTest_8960 136 144 :=
  interval_of_check cellTest_8960 136 8 (by decide +kernel)

theorem cellTest_8960_block_18 : Interval cellTest_8960 144 152 :=
  interval_of_check cellTest_8960 144 8 (by decide +kernel)

theorem cellTest_8960_block_19 : Interval cellTest_8960 152 160 :=
  interval_of_check cellTest_8960 152 8 (by decide +kernel)

theorem cellTest_8960_block_20 : Interval cellTest_8960 160 168 :=
  interval_of_check cellTest_8960 160 8 (by decide +kernel)

theorem cellTest_8960_block_21 : Interval cellTest_8960 168 176 :=
  interval_of_check cellTest_8960 168 8 (by decide +kernel)

theorem cellTest_8960_block_22 : Interval cellTest_8960 176 184 :=
  interval_of_check cellTest_8960 176 8 (by decide +kernel)

theorem cellTest_8960_block_23 : Interval cellTest_8960 184 192 :=
  interval_of_check cellTest_8960 184 8 (by decide +kernel)

theorem cellTest_8960_block_24 : Interval cellTest_8960 192 200 :=
  interval_of_check cellTest_8960 192 8 (by decide +kernel)

theorem cellTest_8960_block_25 : Interval cellTest_8960 200 208 :=
  interval_of_check cellTest_8960 200 8 (by decide +kernel)

theorem cellTest_8960_block_26 : Interval cellTest_8960 208 216 :=
  interval_of_check cellTest_8960 208 8 (by decide +kernel)

theorem cellTest_8960_block_27 : Interval cellTest_8960 216 224 :=
  interval_of_check cellTest_8960 216 8 (by decide +kernel)

theorem cellTest_8960_block_28 : Interval cellTest_8960 224 232 :=
  interval_of_check cellTest_8960 224 8 (by decide +kernel)

theorem cellTest_8960_block_29 : Interval cellTest_8960 232 240 :=
  interval_of_check cellTest_8960 232 8 (by decide +kernel)

theorem cellTest_8960_block_30 : Interval cellTest_8960 240 248 :=
  interval_of_check cellTest_8960 240 8 (by decide +kernel)

theorem cellTest_8960_block_31 : Interval cellTest_8960 248 256 :=
  interval_of_check cellTest_8960 248 8 (by decide +kernel)

theorem cellTest_8960_complete : Interval cellTest_8960 0 256 :=
  (interval_append cellTest_8960 0 128 256
  (interval_append cellTest_8960 0 64 128
  (interval_append cellTest_8960 0 32 64
  (interval_append cellTest_8960 0 16 32
  (interval_append cellTest_8960 0 8 16
  cellTest_8960_block_0
  cellTest_8960_block_1)
  (interval_append cellTest_8960 16 24 32
  cellTest_8960_block_2
  cellTest_8960_block_3))
  (interval_append cellTest_8960 32 48 64
  (interval_append cellTest_8960 32 40 48
  cellTest_8960_block_4
  cellTest_8960_block_5)
  (interval_append cellTest_8960 48 56 64
  cellTest_8960_block_6
  cellTest_8960_block_7)))
  (interval_append cellTest_8960 64 96 128
  (interval_append cellTest_8960 64 80 96
  (interval_append cellTest_8960 64 72 80
  cellTest_8960_block_8
  cellTest_8960_block_9)
  (interval_append cellTest_8960 80 88 96
  cellTest_8960_block_10
  cellTest_8960_block_11))
  (interval_append cellTest_8960 96 112 128
  (interval_append cellTest_8960 96 104 112
  cellTest_8960_block_12
  cellTest_8960_block_13)
  (interval_append cellTest_8960 112 120 128
  cellTest_8960_block_14
  cellTest_8960_block_15))))
  (interval_append cellTest_8960 128 192 256
  (interval_append cellTest_8960 128 160 192
  (interval_append cellTest_8960 128 144 160
  (interval_append cellTest_8960 128 136 144
  cellTest_8960_block_16
  cellTest_8960_block_17)
  (interval_append cellTest_8960 144 152 160
  cellTest_8960_block_18
  cellTest_8960_block_19))
  (interval_append cellTest_8960 160 176 192
  (interval_append cellTest_8960 160 168 176
  cellTest_8960_block_20
  cellTest_8960_block_21)
  (interval_append cellTest_8960 176 184 192
  cellTest_8960_block_22
  cellTest_8960_block_23)))
  (interval_append cellTest_8960 192 224 256
  (interval_append cellTest_8960 192 208 224
  (interval_append cellTest_8960 192 200 208
  cellTest_8960_block_24
  cellTest_8960_block_25)
  (interval_append cellTest_8960 208 216 224
  cellTest_8960_block_26
  cellTest_8960_block_27))
  (interval_append cellTest_8960 224 240 256
  (interval_append cellTest_8960 224 232 240
  cellTest_8960_block_28
  cellTest_8960_block_29)
  (interval_append cellTest_8960 240 248 256
  cellTest_8960_block_30
  cellTest_8960_block_31)))))
theorem cellTestInterval8960 : Interval cellTest 8960 9216 := by
  intro i hlo hhi
  have h := cellTest_8960_complete (i-8960) (Nat.zero_le _) (by omega)
  simpa only [cellTest_8960, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells036 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_9216 (i : Nat) := cellTest (i+9216)
theorem cellTest_9216_block_0 : Interval cellTest_9216 0 8 :=
  interval_of_check cellTest_9216 0 8 (by decide +kernel)

theorem cellTest_9216_block_1 : Interval cellTest_9216 8 16 :=
  interval_of_check cellTest_9216 8 8 (by decide +kernel)

theorem cellTest_9216_block_2 : Interval cellTest_9216 16 24 :=
  interval_of_check cellTest_9216 16 8 (by decide +kernel)

theorem cellTest_9216_block_3 : Interval cellTest_9216 24 32 :=
  interval_of_check cellTest_9216 24 8 (by decide +kernel)

theorem cellTest_9216_block_4 : Interval cellTest_9216 32 40 :=
  interval_of_check cellTest_9216 32 8 (by decide +kernel)

theorem cellTest_9216_block_5 : Interval cellTest_9216 40 48 :=
  interval_of_check cellTest_9216 40 8 (by decide +kernel)

theorem cellTest_9216_block_6 : Interval cellTest_9216 48 56 :=
  interval_of_check cellTest_9216 48 8 (by decide +kernel)

theorem cellTest_9216_block_7 : Interval cellTest_9216 56 64 :=
  interval_of_check cellTest_9216 56 8 (by decide +kernel)

theorem cellTest_9216_block_8 : Interval cellTest_9216 64 72 :=
  interval_of_check cellTest_9216 64 8 (by decide +kernel)

theorem cellTest_9216_block_9 : Interval cellTest_9216 72 80 :=
  interval_of_check cellTest_9216 72 8 (by decide +kernel)

theorem cellTest_9216_block_10 : Interval cellTest_9216 80 88 :=
  interval_of_check cellTest_9216 80 8 (by decide +kernel)

theorem cellTest_9216_block_11 : Interval cellTest_9216 88 96 :=
  interval_of_check cellTest_9216 88 8 (by decide +kernel)

theorem cellTest_9216_block_12 : Interval cellTest_9216 96 104 :=
  interval_of_check cellTest_9216 96 8 (by decide +kernel)

theorem cellTest_9216_block_13 : Interval cellTest_9216 104 112 :=
  interval_of_check cellTest_9216 104 8 (by decide +kernel)

theorem cellTest_9216_block_14 : Interval cellTest_9216 112 120 :=
  interval_of_check cellTest_9216 112 8 (by decide +kernel)

theorem cellTest_9216_block_15 : Interval cellTest_9216 120 128 :=
  interval_of_check cellTest_9216 120 8 (by decide +kernel)

theorem cellTest_9216_block_16 : Interval cellTest_9216 128 136 :=
  interval_of_check cellTest_9216 128 8 (by decide +kernel)

theorem cellTest_9216_block_17 : Interval cellTest_9216 136 144 :=
  interval_of_check cellTest_9216 136 8 (by decide +kernel)

theorem cellTest_9216_block_18 : Interval cellTest_9216 144 152 :=
  interval_of_check cellTest_9216 144 8 (by decide +kernel)

theorem cellTest_9216_block_19 : Interval cellTest_9216 152 160 :=
  interval_of_check cellTest_9216 152 8 (by decide +kernel)

theorem cellTest_9216_block_20 : Interval cellTest_9216 160 168 :=
  interval_of_check cellTest_9216 160 8 (by decide +kernel)

theorem cellTest_9216_block_21 : Interval cellTest_9216 168 176 :=
  interval_of_check cellTest_9216 168 8 (by decide +kernel)

theorem cellTest_9216_block_22 : Interval cellTest_9216 176 184 :=
  interval_of_check cellTest_9216 176 8 (by decide +kernel)

theorem cellTest_9216_block_23 : Interval cellTest_9216 184 192 :=
  interval_of_check cellTest_9216 184 8 (by decide +kernel)

theorem cellTest_9216_block_24 : Interval cellTest_9216 192 200 :=
  interval_of_check cellTest_9216 192 8 (by decide +kernel)

theorem cellTest_9216_block_25 : Interval cellTest_9216 200 208 :=
  interval_of_check cellTest_9216 200 8 (by decide +kernel)

theorem cellTest_9216_block_26 : Interval cellTest_9216 208 216 :=
  interval_of_check cellTest_9216 208 8 (by decide +kernel)

theorem cellTest_9216_block_27 : Interval cellTest_9216 216 224 :=
  interval_of_check cellTest_9216 216 8 (by decide +kernel)

theorem cellTest_9216_block_28 : Interval cellTest_9216 224 232 :=
  interval_of_check cellTest_9216 224 8 (by decide +kernel)

theorem cellTest_9216_block_29 : Interval cellTest_9216 232 240 :=
  interval_of_check cellTest_9216 232 8 (by decide +kernel)

theorem cellTest_9216_block_30 : Interval cellTest_9216 240 248 :=
  interval_of_check cellTest_9216 240 8 (by decide +kernel)

theorem cellTest_9216_block_31 : Interval cellTest_9216 248 256 :=
  interval_of_check cellTest_9216 248 8 (by decide +kernel)

theorem cellTest_9216_complete : Interval cellTest_9216 0 256 :=
  (interval_append cellTest_9216 0 128 256
  (interval_append cellTest_9216 0 64 128
  (interval_append cellTest_9216 0 32 64
  (interval_append cellTest_9216 0 16 32
  (interval_append cellTest_9216 0 8 16
  cellTest_9216_block_0
  cellTest_9216_block_1)
  (interval_append cellTest_9216 16 24 32
  cellTest_9216_block_2
  cellTest_9216_block_3))
  (interval_append cellTest_9216 32 48 64
  (interval_append cellTest_9216 32 40 48
  cellTest_9216_block_4
  cellTest_9216_block_5)
  (interval_append cellTest_9216 48 56 64
  cellTest_9216_block_6
  cellTest_9216_block_7)))
  (interval_append cellTest_9216 64 96 128
  (interval_append cellTest_9216 64 80 96
  (interval_append cellTest_9216 64 72 80
  cellTest_9216_block_8
  cellTest_9216_block_9)
  (interval_append cellTest_9216 80 88 96
  cellTest_9216_block_10
  cellTest_9216_block_11))
  (interval_append cellTest_9216 96 112 128
  (interval_append cellTest_9216 96 104 112
  cellTest_9216_block_12
  cellTest_9216_block_13)
  (interval_append cellTest_9216 112 120 128
  cellTest_9216_block_14
  cellTest_9216_block_15))))
  (interval_append cellTest_9216 128 192 256
  (interval_append cellTest_9216 128 160 192
  (interval_append cellTest_9216 128 144 160
  (interval_append cellTest_9216 128 136 144
  cellTest_9216_block_16
  cellTest_9216_block_17)
  (interval_append cellTest_9216 144 152 160
  cellTest_9216_block_18
  cellTest_9216_block_19))
  (interval_append cellTest_9216 160 176 192
  (interval_append cellTest_9216 160 168 176
  cellTest_9216_block_20
  cellTest_9216_block_21)
  (interval_append cellTest_9216 176 184 192
  cellTest_9216_block_22
  cellTest_9216_block_23)))
  (interval_append cellTest_9216 192 224 256
  (interval_append cellTest_9216 192 208 224
  (interval_append cellTest_9216 192 200 208
  cellTest_9216_block_24
  cellTest_9216_block_25)
  (interval_append cellTest_9216 208 216 224
  cellTest_9216_block_26
  cellTest_9216_block_27))
  (interval_append cellTest_9216 224 240 256
  (interval_append cellTest_9216 224 232 240
  cellTest_9216_block_28
  cellTest_9216_block_29)
  (interval_append cellTest_9216 240 248 256
  cellTest_9216_block_30
  cellTest_9216_block_31)))))
theorem cellTestInterval9216 : Interval cellTest 9216 9472 := by
  intro i hlo hhi
  have h := cellTest_9216_complete (i-9216) (Nat.zero_le _) (by omega)
  simpa only [cellTest_9216, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells037 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_9472 (i : Nat) := cellTest (i+9472)
theorem cellTest_9472_block_0 : Interval cellTest_9472 0 8 :=
  interval_of_check cellTest_9472 0 8 (by decide +kernel)

theorem cellTest_9472_block_1 : Interval cellTest_9472 8 16 :=
  interval_of_check cellTest_9472 8 8 (by decide +kernel)

theorem cellTest_9472_block_2 : Interval cellTest_9472 16 24 :=
  interval_of_check cellTest_9472 16 8 (by decide +kernel)

theorem cellTest_9472_block_3 : Interval cellTest_9472 24 32 :=
  interval_of_check cellTest_9472 24 8 (by decide +kernel)

theorem cellTest_9472_block_4 : Interval cellTest_9472 32 40 :=
  interval_of_check cellTest_9472 32 8 (by decide +kernel)

theorem cellTest_9472_block_5 : Interval cellTest_9472 40 48 :=
  interval_of_check cellTest_9472 40 8 (by decide +kernel)

theorem cellTest_9472_block_6 : Interval cellTest_9472 48 56 :=
  interval_of_check cellTest_9472 48 8 (by decide +kernel)

theorem cellTest_9472_block_7 : Interval cellTest_9472 56 64 :=
  interval_of_check cellTest_9472 56 8 (by decide +kernel)

theorem cellTest_9472_block_8 : Interval cellTest_9472 64 72 :=
  interval_of_check cellTest_9472 64 8 (by decide +kernel)

theorem cellTest_9472_block_9 : Interval cellTest_9472 72 80 :=
  interval_of_check cellTest_9472 72 8 (by decide +kernel)

theorem cellTest_9472_block_10 : Interval cellTest_9472 80 88 :=
  interval_of_check cellTest_9472 80 8 (by decide +kernel)

theorem cellTest_9472_block_11 : Interval cellTest_9472 88 96 :=
  interval_of_check cellTest_9472 88 8 (by decide +kernel)

theorem cellTest_9472_block_12 : Interval cellTest_9472 96 104 :=
  interval_of_check cellTest_9472 96 8 (by decide +kernel)

theorem cellTest_9472_block_13 : Interval cellTest_9472 104 112 :=
  interval_of_check cellTest_9472 104 8 (by decide +kernel)

theorem cellTest_9472_block_14 : Interval cellTest_9472 112 120 :=
  interval_of_check cellTest_9472 112 8 (by decide +kernel)

theorem cellTest_9472_block_15 : Interval cellTest_9472 120 128 :=
  interval_of_check cellTest_9472 120 8 (by decide +kernel)

theorem cellTest_9472_block_16 : Interval cellTest_9472 128 136 :=
  interval_of_check cellTest_9472 128 8 (by decide +kernel)

theorem cellTest_9472_block_17 : Interval cellTest_9472 136 144 :=
  interval_of_check cellTest_9472 136 8 (by decide +kernel)

theorem cellTest_9472_block_18 : Interval cellTest_9472 144 152 :=
  interval_of_check cellTest_9472 144 8 (by decide +kernel)

theorem cellTest_9472_block_19 : Interval cellTest_9472 152 160 :=
  interval_of_check cellTest_9472 152 8 (by decide +kernel)

theorem cellTest_9472_block_20 : Interval cellTest_9472 160 168 :=
  interval_of_check cellTest_9472 160 8 (by decide +kernel)

theorem cellTest_9472_block_21 : Interval cellTest_9472 168 176 :=
  interval_of_check cellTest_9472 168 8 (by decide +kernel)

theorem cellTest_9472_block_22 : Interval cellTest_9472 176 184 :=
  interval_of_check cellTest_9472 176 8 (by decide +kernel)

theorem cellTest_9472_block_23 : Interval cellTest_9472 184 192 :=
  interval_of_check cellTest_9472 184 8 (by decide +kernel)

theorem cellTest_9472_block_24 : Interval cellTest_9472 192 200 :=
  interval_of_check cellTest_9472 192 8 (by decide +kernel)

theorem cellTest_9472_block_25 : Interval cellTest_9472 200 208 :=
  interval_of_check cellTest_9472 200 8 (by decide +kernel)

theorem cellTest_9472_block_26 : Interval cellTest_9472 208 216 :=
  interval_of_check cellTest_9472 208 8 (by decide +kernel)

theorem cellTest_9472_block_27 : Interval cellTest_9472 216 224 :=
  interval_of_check cellTest_9472 216 8 (by decide +kernel)

theorem cellTest_9472_block_28 : Interval cellTest_9472 224 232 :=
  interval_of_check cellTest_9472 224 8 (by decide +kernel)

theorem cellTest_9472_block_29 : Interval cellTest_9472 232 240 :=
  interval_of_check cellTest_9472 232 8 (by decide +kernel)

theorem cellTest_9472_block_30 : Interval cellTest_9472 240 248 :=
  interval_of_check cellTest_9472 240 8 (by decide +kernel)

theorem cellTest_9472_block_31 : Interval cellTest_9472 248 256 :=
  interval_of_check cellTest_9472 248 8 (by decide +kernel)

theorem cellTest_9472_complete : Interval cellTest_9472 0 256 :=
  (interval_append cellTest_9472 0 128 256
  (interval_append cellTest_9472 0 64 128
  (interval_append cellTest_9472 0 32 64
  (interval_append cellTest_9472 0 16 32
  (interval_append cellTest_9472 0 8 16
  cellTest_9472_block_0
  cellTest_9472_block_1)
  (interval_append cellTest_9472 16 24 32
  cellTest_9472_block_2
  cellTest_9472_block_3))
  (interval_append cellTest_9472 32 48 64
  (interval_append cellTest_9472 32 40 48
  cellTest_9472_block_4
  cellTest_9472_block_5)
  (interval_append cellTest_9472 48 56 64
  cellTest_9472_block_6
  cellTest_9472_block_7)))
  (interval_append cellTest_9472 64 96 128
  (interval_append cellTest_9472 64 80 96
  (interval_append cellTest_9472 64 72 80
  cellTest_9472_block_8
  cellTest_9472_block_9)
  (interval_append cellTest_9472 80 88 96
  cellTest_9472_block_10
  cellTest_9472_block_11))
  (interval_append cellTest_9472 96 112 128
  (interval_append cellTest_9472 96 104 112
  cellTest_9472_block_12
  cellTest_9472_block_13)
  (interval_append cellTest_9472 112 120 128
  cellTest_9472_block_14
  cellTest_9472_block_15))))
  (interval_append cellTest_9472 128 192 256
  (interval_append cellTest_9472 128 160 192
  (interval_append cellTest_9472 128 144 160
  (interval_append cellTest_9472 128 136 144
  cellTest_9472_block_16
  cellTest_9472_block_17)
  (interval_append cellTest_9472 144 152 160
  cellTest_9472_block_18
  cellTest_9472_block_19))
  (interval_append cellTest_9472 160 176 192
  (interval_append cellTest_9472 160 168 176
  cellTest_9472_block_20
  cellTest_9472_block_21)
  (interval_append cellTest_9472 176 184 192
  cellTest_9472_block_22
  cellTest_9472_block_23)))
  (interval_append cellTest_9472 192 224 256
  (interval_append cellTest_9472 192 208 224
  (interval_append cellTest_9472 192 200 208
  cellTest_9472_block_24
  cellTest_9472_block_25)
  (interval_append cellTest_9472 208 216 224
  cellTest_9472_block_26
  cellTest_9472_block_27))
  (interval_append cellTest_9472 224 240 256
  (interval_append cellTest_9472 224 232 240
  cellTest_9472_block_28
  cellTest_9472_block_29)
  (interval_append cellTest_9472 240 248 256
  cellTest_9472_block_30
  cellTest_9472_block_31)))))
theorem cellTestInterval9472 : Interval cellTest 9472 9728 := by
  intro i hlo hhi
  have h := cellTest_9472_complete (i-9472) (Nat.zero_le _) (by omega)
  simpa only [cellTest_9472, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells038 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_9728 (i : Nat) := cellTest (i+9728)
theorem cellTest_9728_block_0 : Interval cellTest_9728 0 8 :=
  interval_of_check cellTest_9728 0 8 (by decide +kernel)

theorem cellTest_9728_block_1 : Interval cellTest_9728 8 16 :=
  interval_of_check cellTest_9728 8 8 (by decide +kernel)

theorem cellTest_9728_block_2 : Interval cellTest_9728 16 24 :=
  interval_of_check cellTest_9728 16 8 (by decide +kernel)

theorem cellTest_9728_block_3 : Interval cellTest_9728 24 32 :=
  interval_of_check cellTest_9728 24 8 (by decide +kernel)

theorem cellTest_9728_block_4 : Interval cellTest_9728 32 40 :=
  interval_of_check cellTest_9728 32 8 (by decide +kernel)

theorem cellTest_9728_block_5 : Interval cellTest_9728 40 48 :=
  interval_of_check cellTest_9728 40 8 (by decide +kernel)

theorem cellTest_9728_block_6 : Interval cellTest_9728 48 56 :=
  interval_of_check cellTest_9728 48 8 (by decide +kernel)

theorem cellTest_9728_block_7 : Interval cellTest_9728 56 64 :=
  interval_of_check cellTest_9728 56 8 (by decide +kernel)

theorem cellTest_9728_block_8 : Interval cellTest_9728 64 72 :=
  interval_of_check cellTest_9728 64 8 (by decide +kernel)

theorem cellTest_9728_block_9 : Interval cellTest_9728 72 80 :=
  interval_of_check cellTest_9728 72 8 (by decide +kernel)

theorem cellTest_9728_block_10 : Interval cellTest_9728 80 88 :=
  interval_of_check cellTest_9728 80 8 (by decide +kernel)

theorem cellTest_9728_block_11 : Interval cellTest_9728 88 96 :=
  interval_of_check cellTest_9728 88 8 (by decide +kernel)

theorem cellTest_9728_block_12 : Interval cellTest_9728 96 104 :=
  interval_of_check cellTest_9728 96 8 (by decide +kernel)

theorem cellTest_9728_block_13 : Interval cellTest_9728 104 112 :=
  interval_of_check cellTest_9728 104 8 (by decide +kernel)

theorem cellTest_9728_block_14 : Interval cellTest_9728 112 120 :=
  interval_of_check cellTest_9728 112 8 (by decide +kernel)

theorem cellTest_9728_block_15 : Interval cellTest_9728 120 128 :=
  interval_of_check cellTest_9728 120 8 (by decide +kernel)

theorem cellTest_9728_block_16 : Interval cellTest_9728 128 136 :=
  interval_of_check cellTest_9728 128 8 (by decide +kernel)

theorem cellTest_9728_block_17 : Interval cellTest_9728 136 144 :=
  interval_of_check cellTest_9728 136 8 (by decide +kernel)

theorem cellTest_9728_block_18 : Interval cellTest_9728 144 152 :=
  interval_of_check cellTest_9728 144 8 (by decide +kernel)

theorem cellTest_9728_block_19 : Interval cellTest_9728 152 160 :=
  interval_of_check cellTest_9728 152 8 (by decide +kernel)

theorem cellTest_9728_block_20 : Interval cellTest_9728 160 168 :=
  interval_of_check cellTest_9728 160 8 (by decide +kernel)

theorem cellTest_9728_block_21 : Interval cellTest_9728 168 176 :=
  interval_of_check cellTest_9728 168 8 (by decide +kernel)

theorem cellTest_9728_block_22 : Interval cellTest_9728 176 184 :=
  interval_of_check cellTest_9728 176 8 (by decide +kernel)

theorem cellTest_9728_block_23 : Interval cellTest_9728 184 192 :=
  interval_of_check cellTest_9728 184 8 (by decide +kernel)

theorem cellTest_9728_block_24 : Interval cellTest_9728 192 200 :=
  interval_of_check cellTest_9728 192 8 (by decide +kernel)

theorem cellTest_9728_block_25 : Interval cellTest_9728 200 208 :=
  interval_of_check cellTest_9728 200 8 (by decide +kernel)

theorem cellTest_9728_block_26 : Interval cellTest_9728 208 216 :=
  interval_of_check cellTest_9728 208 8 (by decide +kernel)

theorem cellTest_9728_block_27 : Interval cellTest_9728 216 224 :=
  interval_of_check cellTest_9728 216 8 (by decide +kernel)

theorem cellTest_9728_block_28 : Interval cellTest_9728 224 232 :=
  interval_of_check cellTest_9728 224 8 (by decide +kernel)

theorem cellTest_9728_block_29 : Interval cellTest_9728 232 240 :=
  interval_of_check cellTest_9728 232 8 (by decide +kernel)

theorem cellTest_9728_block_30 : Interval cellTest_9728 240 248 :=
  interval_of_check cellTest_9728 240 8 (by decide +kernel)

theorem cellTest_9728_block_31 : Interval cellTest_9728 248 256 :=
  interval_of_check cellTest_9728 248 8 (by decide +kernel)

theorem cellTest_9728_complete : Interval cellTest_9728 0 256 :=
  (interval_append cellTest_9728 0 128 256
  (interval_append cellTest_9728 0 64 128
  (interval_append cellTest_9728 0 32 64
  (interval_append cellTest_9728 0 16 32
  (interval_append cellTest_9728 0 8 16
  cellTest_9728_block_0
  cellTest_9728_block_1)
  (interval_append cellTest_9728 16 24 32
  cellTest_9728_block_2
  cellTest_9728_block_3))
  (interval_append cellTest_9728 32 48 64
  (interval_append cellTest_9728 32 40 48
  cellTest_9728_block_4
  cellTest_9728_block_5)
  (interval_append cellTest_9728 48 56 64
  cellTest_9728_block_6
  cellTest_9728_block_7)))
  (interval_append cellTest_9728 64 96 128
  (interval_append cellTest_9728 64 80 96
  (interval_append cellTest_9728 64 72 80
  cellTest_9728_block_8
  cellTest_9728_block_9)
  (interval_append cellTest_9728 80 88 96
  cellTest_9728_block_10
  cellTest_9728_block_11))
  (interval_append cellTest_9728 96 112 128
  (interval_append cellTest_9728 96 104 112
  cellTest_9728_block_12
  cellTest_9728_block_13)
  (interval_append cellTest_9728 112 120 128
  cellTest_9728_block_14
  cellTest_9728_block_15))))
  (interval_append cellTest_9728 128 192 256
  (interval_append cellTest_9728 128 160 192
  (interval_append cellTest_9728 128 144 160
  (interval_append cellTest_9728 128 136 144
  cellTest_9728_block_16
  cellTest_9728_block_17)
  (interval_append cellTest_9728 144 152 160
  cellTest_9728_block_18
  cellTest_9728_block_19))
  (interval_append cellTest_9728 160 176 192
  (interval_append cellTest_9728 160 168 176
  cellTest_9728_block_20
  cellTest_9728_block_21)
  (interval_append cellTest_9728 176 184 192
  cellTest_9728_block_22
  cellTest_9728_block_23)))
  (interval_append cellTest_9728 192 224 256
  (interval_append cellTest_9728 192 208 224
  (interval_append cellTest_9728 192 200 208
  cellTest_9728_block_24
  cellTest_9728_block_25)
  (interval_append cellTest_9728 208 216 224
  cellTest_9728_block_26
  cellTest_9728_block_27))
  (interval_append cellTest_9728 224 240 256
  (interval_append cellTest_9728 224 232 240
  cellTest_9728_block_28
  cellTest_9728_block_29)
  (interval_append cellTest_9728 240 248 256
  cellTest_9728_block_30
  cellTest_9728_block_31)))))
theorem cellTestInterval9728 : Interval cellTest 9728 9984 := by
  intro i hlo hhi
  have h := cellTest_9728_complete (i-9728) (Nat.zero_le _) (by omega)
  simpa only [cellTest_9728, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells039 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_9984 (i : Nat) := cellTest (i+9984)
theorem cellTest_9984_block_0 : Interval cellTest_9984 0 8 :=
  interval_of_check cellTest_9984 0 8 (by decide +kernel)

theorem cellTest_9984_block_1 : Interval cellTest_9984 8 16 :=
  interval_of_check cellTest_9984 8 8 (by decide +kernel)

theorem cellTest_9984_block_2 : Interval cellTest_9984 16 24 :=
  interval_of_check cellTest_9984 16 8 (by decide +kernel)

theorem cellTest_9984_block_3 : Interval cellTest_9984 24 32 :=
  interval_of_check cellTest_9984 24 8 (by decide +kernel)

theorem cellTest_9984_block_4 : Interval cellTest_9984 32 40 :=
  interval_of_check cellTest_9984 32 8 (by decide +kernel)

theorem cellTest_9984_block_5 : Interval cellTest_9984 40 48 :=
  interval_of_check cellTest_9984 40 8 (by decide +kernel)

theorem cellTest_9984_block_6 : Interval cellTest_9984 48 56 :=
  interval_of_check cellTest_9984 48 8 (by decide +kernel)

theorem cellTest_9984_block_7 : Interval cellTest_9984 56 64 :=
  interval_of_check cellTest_9984 56 8 (by decide +kernel)

theorem cellTest_9984_block_8 : Interval cellTest_9984 64 72 :=
  interval_of_check cellTest_9984 64 8 (by decide +kernel)

theorem cellTest_9984_block_9 : Interval cellTest_9984 72 80 :=
  interval_of_check cellTest_9984 72 8 (by decide +kernel)

theorem cellTest_9984_block_10 : Interval cellTest_9984 80 88 :=
  interval_of_check cellTest_9984 80 8 (by decide +kernel)

theorem cellTest_9984_block_11 : Interval cellTest_9984 88 96 :=
  interval_of_check cellTest_9984 88 8 (by decide +kernel)

theorem cellTest_9984_block_12 : Interval cellTest_9984 96 104 :=
  interval_of_check cellTest_9984 96 8 (by decide +kernel)

theorem cellTest_9984_block_13 : Interval cellTest_9984 104 112 :=
  interval_of_check cellTest_9984 104 8 (by decide +kernel)

theorem cellTest_9984_block_14 : Interval cellTest_9984 112 120 :=
  interval_of_check cellTest_9984 112 8 (by decide +kernel)

theorem cellTest_9984_block_15 : Interval cellTest_9984 120 128 :=
  interval_of_check cellTest_9984 120 8 (by decide +kernel)

theorem cellTest_9984_block_16 : Interval cellTest_9984 128 136 :=
  interval_of_check cellTest_9984 128 8 (by decide +kernel)

theorem cellTest_9984_block_17 : Interval cellTest_9984 136 144 :=
  interval_of_check cellTest_9984 136 8 (by decide +kernel)

theorem cellTest_9984_block_18 : Interval cellTest_9984 144 152 :=
  interval_of_check cellTest_9984 144 8 (by decide +kernel)

theorem cellTest_9984_block_19 : Interval cellTest_9984 152 160 :=
  interval_of_check cellTest_9984 152 8 (by decide +kernel)

theorem cellTest_9984_block_20 : Interval cellTest_9984 160 168 :=
  interval_of_check cellTest_9984 160 8 (by decide +kernel)

theorem cellTest_9984_block_21 : Interval cellTest_9984 168 176 :=
  interval_of_check cellTest_9984 168 8 (by decide +kernel)

theorem cellTest_9984_block_22 : Interval cellTest_9984 176 184 :=
  interval_of_check cellTest_9984 176 8 (by decide +kernel)

theorem cellTest_9984_block_23 : Interval cellTest_9984 184 192 :=
  interval_of_check cellTest_9984 184 8 (by decide +kernel)

theorem cellTest_9984_block_24 : Interval cellTest_9984 192 200 :=
  interval_of_check cellTest_9984 192 8 (by decide +kernel)

theorem cellTest_9984_block_25 : Interval cellTest_9984 200 208 :=
  interval_of_check cellTest_9984 200 8 (by decide +kernel)

theorem cellTest_9984_block_26 : Interval cellTest_9984 208 216 :=
  interval_of_check cellTest_9984 208 8 (by decide +kernel)

theorem cellTest_9984_block_27 : Interval cellTest_9984 216 224 :=
  interval_of_check cellTest_9984 216 8 (by decide +kernel)

theorem cellTest_9984_block_28 : Interval cellTest_9984 224 232 :=
  interval_of_check cellTest_9984 224 8 (by decide +kernel)

theorem cellTest_9984_block_29 : Interval cellTest_9984 232 240 :=
  interval_of_check cellTest_9984 232 8 (by decide +kernel)

theorem cellTest_9984_block_30 : Interval cellTest_9984 240 248 :=
  interval_of_check cellTest_9984 240 8 (by decide +kernel)

theorem cellTest_9984_block_31 : Interval cellTest_9984 248 256 :=
  interval_of_check cellTest_9984 248 8 (by decide +kernel)

theorem cellTest_9984_complete : Interval cellTest_9984 0 256 :=
  (interval_append cellTest_9984 0 128 256
  (interval_append cellTest_9984 0 64 128
  (interval_append cellTest_9984 0 32 64
  (interval_append cellTest_9984 0 16 32
  (interval_append cellTest_9984 0 8 16
  cellTest_9984_block_0
  cellTest_9984_block_1)
  (interval_append cellTest_9984 16 24 32
  cellTest_9984_block_2
  cellTest_9984_block_3))
  (interval_append cellTest_9984 32 48 64
  (interval_append cellTest_9984 32 40 48
  cellTest_9984_block_4
  cellTest_9984_block_5)
  (interval_append cellTest_9984 48 56 64
  cellTest_9984_block_6
  cellTest_9984_block_7)))
  (interval_append cellTest_9984 64 96 128
  (interval_append cellTest_9984 64 80 96
  (interval_append cellTest_9984 64 72 80
  cellTest_9984_block_8
  cellTest_9984_block_9)
  (interval_append cellTest_9984 80 88 96
  cellTest_9984_block_10
  cellTest_9984_block_11))
  (interval_append cellTest_9984 96 112 128
  (interval_append cellTest_9984 96 104 112
  cellTest_9984_block_12
  cellTest_9984_block_13)
  (interval_append cellTest_9984 112 120 128
  cellTest_9984_block_14
  cellTest_9984_block_15))))
  (interval_append cellTest_9984 128 192 256
  (interval_append cellTest_9984 128 160 192
  (interval_append cellTest_9984 128 144 160
  (interval_append cellTest_9984 128 136 144
  cellTest_9984_block_16
  cellTest_9984_block_17)
  (interval_append cellTest_9984 144 152 160
  cellTest_9984_block_18
  cellTest_9984_block_19))
  (interval_append cellTest_9984 160 176 192
  (interval_append cellTest_9984 160 168 176
  cellTest_9984_block_20
  cellTest_9984_block_21)
  (interval_append cellTest_9984 176 184 192
  cellTest_9984_block_22
  cellTest_9984_block_23)))
  (interval_append cellTest_9984 192 224 256
  (interval_append cellTest_9984 192 208 224
  (interval_append cellTest_9984 192 200 208
  cellTest_9984_block_24
  cellTest_9984_block_25)
  (interval_append cellTest_9984 208 216 224
  cellTest_9984_block_26
  cellTest_9984_block_27))
  (interval_append cellTest_9984 224 240 256
  (interval_append cellTest_9984 224 232 240
  cellTest_9984_block_28
  cellTest_9984_block_29)
  (interval_append cellTest_9984 240 248 256
  cellTest_9984_block_30
  cellTest_9984_block_31)))))
theorem cellTestInterval9984 : Interval cellTest 9984 10240 := by
  intro i hlo hhi
  have h := cellTest_9984_complete (i-9984) (Nat.zero_le _) (by omega)
  simpa only [cellTest_9984, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells040 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_10240 (i : Nat) := cellTest (i+10240)
theorem cellTest_10240_block_0 : Interval cellTest_10240 0 8 :=
  interval_of_check cellTest_10240 0 8 (by decide +kernel)

theorem cellTest_10240_block_1 : Interval cellTest_10240 8 16 :=
  interval_of_check cellTest_10240 8 8 (by decide +kernel)

theorem cellTest_10240_block_2 : Interval cellTest_10240 16 24 :=
  interval_of_check cellTest_10240 16 8 (by decide +kernel)

theorem cellTest_10240_block_3 : Interval cellTest_10240 24 32 :=
  interval_of_check cellTest_10240 24 8 (by decide +kernel)

theorem cellTest_10240_block_4 : Interval cellTest_10240 32 40 :=
  interval_of_check cellTest_10240 32 8 (by decide +kernel)

theorem cellTest_10240_block_5 : Interval cellTest_10240 40 48 :=
  interval_of_check cellTest_10240 40 8 (by decide +kernel)

theorem cellTest_10240_block_6 : Interval cellTest_10240 48 56 :=
  interval_of_check cellTest_10240 48 8 (by decide +kernel)

theorem cellTest_10240_block_7 : Interval cellTest_10240 56 64 :=
  interval_of_check cellTest_10240 56 8 (by decide +kernel)

theorem cellTest_10240_block_8 : Interval cellTest_10240 64 72 :=
  interval_of_check cellTest_10240 64 8 (by decide +kernel)

theorem cellTest_10240_block_9 : Interval cellTest_10240 72 80 :=
  interval_of_check cellTest_10240 72 8 (by decide +kernel)

theorem cellTest_10240_block_10 : Interval cellTest_10240 80 88 :=
  interval_of_check cellTest_10240 80 8 (by decide +kernel)

theorem cellTest_10240_block_11 : Interval cellTest_10240 88 96 :=
  interval_of_check cellTest_10240 88 8 (by decide +kernel)

theorem cellTest_10240_block_12 : Interval cellTest_10240 96 104 :=
  interval_of_check cellTest_10240 96 8 (by decide +kernel)

theorem cellTest_10240_block_13 : Interval cellTest_10240 104 112 :=
  interval_of_check cellTest_10240 104 8 (by decide +kernel)

theorem cellTest_10240_block_14 : Interval cellTest_10240 112 120 :=
  interval_of_check cellTest_10240 112 8 (by decide +kernel)

theorem cellTest_10240_block_15 : Interval cellTest_10240 120 128 :=
  interval_of_check cellTest_10240 120 8 (by decide +kernel)

theorem cellTest_10240_block_16 : Interval cellTest_10240 128 136 :=
  interval_of_check cellTest_10240 128 8 (by decide +kernel)

theorem cellTest_10240_block_17 : Interval cellTest_10240 136 144 :=
  interval_of_check cellTest_10240 136 8 (by decide +kernel)

theorem cellTest_10240_block_18 : Interval cellTest_10240 144 152 :=
  interval_of_check cellTest_10240 144 8 (by decide +kernel)

theorem cellTest_10240_block_19 : Interval cellTest_10240 152 160 :=
  interval_of_check cellTest_10240 152 8 (by decide +kernel)

theorem cellTest_10240_block_20 : Interval cellTest_10240 160 168 :=
  interval_of_check cellTest_10240 160 8 (by decide +kernel)

theorem cellTest_10240_block_21 : Interval cellTest_10240 168 176 :=
  interval_of_check cellTest_10240 168 8 (by decide +kernel)

theorem cellTest_10240_block_22 : Interval cellTest_10240 176 184 :=
  interval_of_check cellTest_10240 176 8 (by decide +kernel)

theorem cellTest_10240_block_23 : Interval cellTest_10240 184 192 :=
  interval_of_check cellTest_10240 184 8 (by decide +kernel)

theorem cellTest_10240_block_24 : Interval cellTest_10240 192 200 :=
  interval_of_check cellTest_10240 192 8 (by decide +kernel)

theorem cellTest_10240_block_25 : Interval cellTest_10240 200 208 :=
  interval_of_check cellTest_10240 200 8 (by decide +kernel)

theorem cellTest_10240_block_26 : Interval cellTest_10240 208 216 :=
  interval_of_check cellTest_10240 208 8 (by decide +kernel)

theorem cellTest_10240_block_27 : Interval cellTest_10240 216 224 :=
  interval_of_check cellTest_10240 216 8 (by decide +kernel)

theorem cellTest_10240_block_28 : Interval cellTest_10240 224 232 :=
  interval_of_check cellTest_10240 224 8 (by decide +kernel)

theorem cellTest_10240_block_29 : Interval cellTest_10240 232 240 :=
  interval_of_check cellTest_10240 232 8 (by decide +kernel)

theorem cellTest_10240_block_30 : Interval cellTest_10240 240 248 :=
  interval_of_check cellTest_10240 240 8 (by decide +kernel)

theorem cellTest_10240_block_31 : Interval cellTest_10240 248 256 :=
  interval_of_check cellTest_10240 248 8 (by decide +kernel)

theorem cellTest_10240_complete : Interval cellTest_10240 0 256 :=
  (interval_append cellTest_10240 0 128 256
  (interval_append cellTest_10240 0 64 128
  (interval_append cellTest_10240 0 32 64
  (interval_append cellTest_10240 0 16 32
  (interval_append cellTest_10240 0 8 16
  cellTest_10240_block_0
  cellTest_10240_block_1)
  (interval_append cellTest_10240 16 24 32
  cellTest_10240_block_2
  cellTest_10240_block_3))
  (interval_append cellTest_10240 32 48 64
  (interval_append cellTest_10240 32 40 48
  cellTest_10240_block_4
  cellTest_10240_block_5)
  (interval_append cellTest_10240 48 56 64
  cellTest_10240_block_6
  cellTest_10240_block_7)))
  (interval_append cellTest_10240 64 96 128
  (interval_append cellTest_10240 64 80 96
  (interval_append cellTest_10240 64 72 80
  cellTest_10240_block_8
  cellTest_10240_block_9)
  (interval_append cellTest_10240 80 88 96
  cellTest_10240_block_10
  cellTest_10240_block_11))
  (interval_append cellTest_10240 96 112 128
  (interval_append cellTest_10240 96 104 112
  cellTest_10240_block_12
  cellTest_10240_block_13)
  (interval_append cellTest_10240 112 120 128
  cellTest_10240_block_14
  cellTest_10240_block_15))))
  (interval_append cellTest_10240 128 192 256
  (interval_append cellTest_10240 128 160 192
  (interval_append cellTest_10240 128 144 160
  (interval_append cellTest_10240 128 136 144
  cellTest_10240_block_16
  cellTest_10240_block_17)
  (interval_append cellTest_10240 144 152 160
  cellTest_10240_block_18
  cellTest_10240_block_19))
  (interval_append cellTest_10240 160 176 192
  (interval_append cellTest_10240 160 168 176
  cellTest_10240_block_20
  cellTest_10240_block_21)
  (interval_append cellTest_10240 176 184 192
  cellTest_10240_block_22
  cellTest_10240_block_23)))
  (interval_append cellTest_10240 192 224 256
  (interval_append cellTest_10240 192 208 224
  (interval_append cellTest_10240 192 200 208
  cellTest_10240_block_24
  cellTest_10240_block_25)
  (interval_append cellTest_10240 208 216 224
  cellTest_10240_block_26
  cellTest_10240_block_27))
  (interval_append cellTest_10240 224 240 256
  (interval_append cellTest_10240 224 232 240
  cellTest_10240_block_28
  cellTest_10240_block_29)
  (interval_append cellTest_10240 240 248 256
  cellTest_10240_block_30
  cellTest_10240_block_31)))))
theorem cellTestInterval10240 : Interval cellTest 10240 10496 := by
  intro i hlo hhi
  have h := cellTest_10240_complete (i-10240) (Nat.zero_le _) (by omega)
  simpa only [cellTest_10240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells041 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_10496 (i : Nat) := cellTest (i+10496)
theorem cellTest_10496_block_0 : Interval cellTest_10496 0 8 :=
  interval_of_check cellTest_10496 0 8 (by decide +kernel)

theorem cellTest_10496_block_1 : Interval cellTest_10496 8 16 :=
  interval_of_check cellTest_10496 8 8 (by decide +kernel)

theorem cellTest_10496_block_2 : Interval cellTest_10496 16 24 :=
  interval_of_check cellTest_10496 16 8 (by decide +kernel)

theorem cellTest_10496_block_3 : Interval cellTest_10496 24 32 :=
  interval_of_check cellTest_10496 24 8 (by decide +kernel)

theorem cellTest_10496_block_4 : Interval cellTest_10496 32 40 :=
  interval_of_check cellTest_10496 32 8 (by decide +kernel)

theorem cellTest_10496_block_5 : Interval cellTest_10496 40 48 :=
  interval_of_check cellTest_10496 40 8 (by decide +kernel)

theorem cellTest_10496_block_6 : Interval cellTest_10496 48 56 :=
  interval_of_check cellTest_10496 48 8 (by decide +kernel)

theorem cellTest_10496_block_7 : Interval cellTest_10496 56 64 :=
  interval_of_check cellTest_10496 56 8 (by decide +kernel)

theorem cellTest_10496_block_8 : Interval cellTest_10496 64 72 :=
  interval_of_check cellTest_10496 64 8 (by decide +kernel)

theorem cellTest_10496_block_9 : Interval cellTest_10496 72 80 :=
  interval_of_check cellTest_10496 72 8 (by decide +kernel)

theorem cellTest_10496_block_10 : Interval cellTest_10496 80 88 :=
  interval_of_check cellTest_10496 80 8 (by decide +kernel)

theorem cellTest_10496_block_11 : Interval cellTest_10496 88 96 :=
  interval_of_check cellTest_10496 88 8 (by decide +kernel)

theorem cellTest_10496_block_12 : Interval cellTest_10496 96 104 :=
  interval_of_check cellTest_10496 96 8 (by decide +kernel)

theorem cellTest_10496_block_13 : Interval cellTest_10496 104 112 :=
  interval_of_check cellTest_10496 104 8 (by decide +kernel)

theorem cellTest_10496_block_14 : Interval cellTest_10496 112 120 :=
  interval_of_check cellTest_10496 112 8 (by decide +kernel)

theorem cellTest_10496_block_15 : Interval cellTest_10496 120 128 :=
  interval_of_check cellTest_10496 120 8 (by decide +kernel)

theorem cellTest_10496_block_16 : Interval cellTest_10496 128 136 :=
  interval_of_check cellTest_10496 128 8 (by decide +kernel)

theorem cellTest_10496_block_17 : Interval cellTest_10496 136 144 :=
  interval_of_check cellTest_10496 136 8 (by decide +kernel)

theorem cellTest_10496_block_18 : Interval cellTest_10496 144 152 :=
  interval_of_check cellTest_10496 144 8 (by decide +kernel)

theorem cellTest_10496_block_19 : Interval cellTest_10496 152 160 :=
  interval_of_check cellTest_10496 152 8 (by decide +kernel)

theorem cellTest_10496_block_20 : Interval cellTest_10496 160 168 :=
  interval_of_check cellTest_10496 160 8 (by decide +kernel)

theorem cellTest_10496_block_21 : Interval cellTest_10496 168 176 :=
  interval_of_check cellTest_10496 168 8 (by decide +kernel)

theorem cellTest_10496_block_22 : Interval cellTest_10496 176 184 :=
  interval_of_check cellTest_10496 176 8 (by decide +kernel)

theorem cellTest_10496_block_23 : Interval cellTest_10496 184 192 :=
  interval_of_check cellTest_10496 184 8 (by decide +kernel)

theorem cellTest_10496_block_24 : Interval cellTest_10496 192 200 :=
  interval_of_check cellTest_10496 192 8 (by decide +kernel)

theorem cellTest_10496_block_25 : Interval cellTest_10496 200 208 :=
  interval_of_check cellTest_10496 200 8 (by decide +kernel)

theorem cellTest_10496_block_26 : Interval cellTest_10496 208 216 :=
  interval_of_check cellTest_10496 208 8 (by decide +kernel)

theorem cellTest_10496_block_27 : Interval cellTest_10496 216 224 :=
  interval_of_check cellTest_10496 216 8 (by decide +kernel)

theorem cellTest_10496_block_28 : Interval cellTest_10496 224 232 :=
  interval_of_check cellTest_10496 224 8 (by decide +kernel)

theorem cellTest_10496_block_29 : Interval cellTest_10496 232 240 :=
  interval_of_check cellTest_10496 232 8 (by decide +kernel)

theorem cellTest_10496_block_30 : Interval cellTest_10496 240 248 :=
  interval_of_check cellTest_10496 240 8 (by decide +kernel)

theorem cellTest_10496_block_31 : Interval cellTest_10496 248 256 :=
  interval_of_check cellTest_10496 248 8 (by decide +kernel)

theorem cellTest_10496_complete : Interval cellTest_10496 0 256 :=
  (interval_append cellTest_10496 0 128 256
  (interval_append cellTest_10496 0 64 128
  (interval_append cellTest_10496 0 32 64
  (interval_append cellTest_10496 0 16 32
  (interval_append cellTest_10496 0 8 16
  cellTest_10496_block_0
  cellTest_10496_block_1)
  (interval_append cellTest_10496 16 24 32
  cellTest_10496_block_2
  cellTest_10496_block_3))
  (interval_append cellTest_10496 32 48 64
  (interval_append cellTest_10496 32 40 48
  cellTest_10496_block_4
  cellTest_10496_block_5)
  (interval_append cellTest_10496 48 56 64
  cellTest_10496_block_6
  cellTest_10496_block_7)))
  (interval_append cellTest_10496 64 96 128
  (interval_append cellTest_10496 64 80 96
  (interval_append cellTest_10496 64 72 80
  cellTest_10496_block_8
  cellTest_10496_block_9)
  (interval_append cellTest_10496 80 88 96
  cellTest_10496_block_10
  cellTest_10496_block_11))
  (interval_append cellTest_10496 96 112 128
  (interval_append cellTest_10496 96 104 112
  cellTest_10496_block_12
  cellTest_10496_block_13)
  (interval_append cellTest_10496 112 120 128
  cellTest_10496_block_14
  cellTest_10496_block_15))))
  (interval_append cellTest_10496 128 192 256
  (interval_append cellTest_10496 128 160 192
  (interval_append cellTest_10496 128 144 160
  (interval_append cellTest_10496 128 136 144
  cellTest_10496_block_16
  cellTest_10496_block_17)
  (interval_append cellTest_10496 144 152 160
  cellTest_10496_block_18
  cellTest_10496_block_19))
  (interval_append cellTest_10496 160 176 192
  (interval_append cellTest_10496 160 168 176
  cellTest_10496_block_20
  cellTest_10496_block_21)
  (interval_append cellTest_10496 176 184 192
  cellTest_10496_block_22
  cellTest_10496_block_23)))
  (interval_append cellTest_10496 192 224 256
  (interval_append cellTest_10496 192 208 224
  (interval_append cellTest_10496 192 200 208
  cellTest_10496_block_24
  cellTest_10496_block_25)
  (interval_append cellTest_10496 208 216 224
  cellTest_10496_block_26
  cellTest_10496_block_27))
  (interval_append cellTest_10496 224 240 256
  (interval_append cellTest_10496 224 232 240
  cellTest_10496_block_28
  cellTest_10496_block_29)
  (interval_append cellTest_10496 240 248 256
  cellTest_10496_block_30
  cellTest_10496_block_31)))))
theorem cellTestInterval10496 : Interval cellTest 10496 10752 := by
  intro i hlo hhi
  have h := cellTest_10496_complete (i-10496) (Nat.zero_le _) (by omega)
  simpa only [cellTest_10496, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells042 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_10752 (i : Nat) := cellTest (i+10752)
theorem cellTest_10752_block_0 : Interval cellTest_10752 0 8 :=
  interval_of_check cellTest_10752 0 8 (by decide +kernel)

theorem cellTest_10752_block_1 : Interval cellTest_10752 8 16 :=
  interval_of_check cellTest_10752 8 8 (by decide +kernel)

theorem cellTest_10752_block_2 : Interval cellTest_10752 16 24 :=
  interval_of_check cellTest_10752 16 8 (by decide +kernel)

theorem cellTest_10752_block_3 : Interval cellTest_10752 24 32 :=
  interval_of_check cellTest_10752 24 8 (by decide +kernel)

theorem cellTest_10752_block_4 : Interval cellTest_10752 32 40 :=
  interval_of_check cellTest_10752 32 8 (by decide +kernel)

theorem cellTest_10752_block_5 : Interval cellTest_10752 40 48 :=
  interval_of_check cellTest_10752 40 8 (by decide +kernel)

theorem cellTest_10752_block_6 : Interval cellTest_10752 48 56 :=
  interval_of_check cellTest_10752 48 8 (by decide +kernel)

theorem cellTest_10752_block_7 : Interval cellTest_10752 56 64 :=
  interval_of_check cellTest_10752 56 8 (by decide +kernel)

theorem cellTest_10752_block_8 : Interval cellTest_10752 64 72 :=
  interval_of_check cellTest_10752 64 8 (by decide +kernel)

theorem cellTest_10752_block_9 : Interval cellTest_10752 72 80 :=
  interval_of_check cellTest_10752 72 8 (by decide +kernel)

theorem cellTest_10752_block_10 : Interval cellTest_10752 80 88 :=
  interval_of_check cellTest_10752 80 8 (by decide +kernel)

theorem cellTest_10752_block_11 : Interval cellTest_10752 88 96 :=
  interval_of_check cellTest_10752 88 8 (by decide +kernel)

theorem cellTest_10752_block_12 : Interval cellTest_10752 96 104 :=
  interval_of_check cellTest_10752 96 8 (by decide +kernel)

theorem cellTest_10752_block_13 : Interval cellTest_10752 104 112 :=
  interval_of_check cellTest_10752 104 8 (by decide +kernel)

theorem cellTest_10752_block_14 : Interval cellTest_10752 112 120 :=
  interval_of_check cellTest_10752 112 8 (by decide +kernel)

theorem cellTest_10752_block_15 : Interval cellTest_10752 120 128 :=
  interval_of_check cellTest_10752 120 8 (by decide +kernel)

theorem cellTest_10752_block_16 : Interval cellTest_10752 128 136 :=
  interval_of_check cellTest_10752 128 8 (by decide +kernel)

theorem cellTest_10752_block_17 : Interval cellTest_10752 136 144 :=
  interval_of_check cellTest_10752 136 8 (by decide +kernel)

theorem cellTest_10752_block_18 : Interval cellTest_10752 144 152 :=
  interval_of_check cellTest_10752 144 8 (by decide +kernel)

theorem cellTest_10752_block_19 : Interval cellTest_10752 152 160 :=
  interval_of_check cellTest_10752 152 8 (by decide +kernel)

theorem cellTest_10752_block_20 : Interval cellTest_10752 160 168 :=
  interval_of_check cellTest_10752 160 8 (by decide +kernel)

theorem cellTest_10752_block_21 : Interval cellTest_10752 168 176 :=
  interval_of_check cellTest_10752 168 8 (by decide +kernel)

theorem cellTest_10752_block_22 : Interval cellTest_10752 176 184 :=
  interval_of_check cellTest_10752 176 8 (by decide +kernel)

theorem cellTest_10752_block_23 : Interval cellTest_10752 184 192 :=
  interval_of_check cellTest_10752 184 8 (by decide +kernel)

theorem cellTest_10752_block_24 : Interval cellTest_10752 192 200 :=
  interval_of_check cellTest_10752 192 8 (by decide +kernel)

theorem cellTest_10752_block_25 : Interval cellTest_10752 200 208 :=
  interval_of_check cellTest_10752 200 8 (by decide +kernel)

theorem cellTest_10752_block_26 : Interval cellTest_10752 208 216 :=
  interval_of_check cellTest_10752 208 8 (by decide +kernel)

theorem cellTest_10752_block_27 : Interval cellTest_10752 216 224 :=
  interval_of_check cellTest_10752 216 8 (by decide +kernel)

theorem cellTest_10752_block_28 : Interval cellTest_10752 224 232 :=
  interval_of_check cellTest_10752 224 8 (by decide +kernel)

theorem cellTest_10752_block_29 : Interval cellTest_10752 232 240 :=
  interval_of_check cellTest_10752 232 8 (by decide +kernel)

theorem cellTest_10752_block_30 : Interval cellTest_10752 240 248 :=
  interval_of_check cellTest_10752 240 8 (by decide +kernel)

theorem cellTest_10752_block_31 : Interval cellTest_10752 248 256 :=
  interval_of_check cellTest_10752 248 8 (by decide +kernel)

theorem cellTest_10752_complete : Interval cellTest_10752 0 256 :=
  (interval_append cellTest_10752 0 128 256
  (interval_append cellTest_10752 0 64 128
  (interval_append cellTest_10752 0 32 64
  (interval_append cellTest_10752 0 16 32
  (interval_append cellTest_10752 0 8 16
  cellTest_10752_block_0
  cellTest_10752_block_1)
  (interval_append cellTest_10752 16 24 32
  cellTest_10752_block_2
  cellTest_10752_block_3))
  (interval_append cellTest_10752 32 48 64
  (interval_append cellTest_10752 32 40 48
  cellTest_10752_block_4
  cellTest_10752_block_5)
  (interval_append cellTest_10752 48 56 64
  cellTest_10752_block_6
  cellTest_10752_block_7)))
  (interval_append cellTest_10752 64 96 128
  (interval_append cellTest_10752 64 80 96
  (interval_append cellTest_10752 64 72 80
  cellTest_10752_block_8
  cellTest_10752_block_9)
  (interval_append cellTest_10752 80 88 96
  cellTest_10752_block_10
  cellTest_10752_block_11))
  (interval_append cellTest_10752 96 112 128
  (interval_append cellTest_10752 96 104 112
  cellTest_10752_block_12
  cellTest_10752_block_13)
  (interval_append cellTest_10752 112 120 128
  cellTest_10752_block_14
  cellTest_10752_block_15))))
  (interval_append cellTest_10752 128 192 256
  (interval_append cellTest_10752 128 160 192
  (interval_append cellTest_10752 128 144 160
  (interval_append cellTest_10752 128 136 144
  cellTest_10752_block_16
  cellTest_10752_block_17)
  (interval_append cellTest_10752 144 152 160
  cellTest_10752_block_18
  cellTest_10752_block_19))
  (interval_append cellTest_10752 160 176 192
  (interval_append cellTest_10752 160 168 176
  cellTest_10752_block_20
  cellTest_10752_block_21)
  (interval_append cellTest_10752 176 184 192
  cellTest_10752_block_22
  cellTest_10752_block_23)))
  (interval_append cellTest_10752 192 224 256
  (interval_append cellTest_10752 192 208 224
  (interval_append cellTest_10752 192 200 208
  cellTest_10752_block_24
  cellTest_10752_block_25)
  (interval_append cellTest_10752 208 216 224
  cellTest_10752_block_26
  cellTest_10752_block_27))
  (interval_append cellTest_10752 224 240 256
  (interval_append cellTest_10752 224 232 240
  cellTest_10752_block_28
  cellTest_10752_block_29)
  (interval_append cellTest_10752 240 248 256
  cellTest_10752_block_30
  cellTest_10752_block_31)))))
theorem cellTestInterval10752 : Interval cellTest 10752 11008 := by
  intro i hlo hhi
  have h := cellTest_10752_complete (i-10752) (Nat.zero_le _) (by omega)
  simpa only [cellTest_10752, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells043 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_11008 (i : Nat) := cellTest (i+11008)
theorem cellTest_11008_block_0 : Interval cellTest_11008 0 8 :=
  interval_of_check cellTest_11008 0 8 (by decide +kernel)

theorem cellTest_11008_block_1 : Interval cellTest_11008 8 16 :=
  interval_of_check cellTest_11008 8 8 (by decide +kernel)

theorem cellTest_11008_block_2 : Interval cellTest_11008 16 24 :=
  interval_of_check cellTest_11008 16 8 (by decide +kernel)

theorem cellTest_11008_block_3 : Interval cellTest_11008 24 32 :=
  interval_of_check cellTest_11008 24 8 (by decide +kernel)

theorem cellTest_11008_block_4 : Interval cellTest_11008 32 40 :=
  interval_of_check cellTest_11008 32 8 (by decide +kernel)

theorem cellTest_11008_block_5 : Interval cellTest_11008 40 48 :=
  interval_of_check cellTest_11008 40 8 (by decide +kernel)

theorem cellTest_11008_block_6 : Interval cellTest_11008 48 56 :=
  interval_of_check cellTest_11008 48 8 (by decide +kernel)

theorem cellTest_11008_block_7 : Interval cellTest_11008 56 64 :=
  interval_of_check cellTest_11008 56 8 (by decide +kernel)

theorem cellTest_11008_block_8 : Interval cellTest_11008 64 72 :=
  interval_of_check cellTest_11008 64 8 (by decide +kernel)

theorem cellTest_11008_block_9 : Interval cellTest_11008 72 80 :=
  interval_of_check cellTest_11008 72 8 (by decide +kernel)

theorem cellTest_11008_block_10 : Interval cellTest_11008 80 88 :=
  interval_of_check cellTest_11008 80 8 (by decide +kernel)

theorem cellTest_11008_block_11 : Interval cellTest_11008 88 96 :=
  interval_of_check cellTest_11008 88 8 (by decide +kernel)

theorem cellTest_11008_block_12 : Interval cellTest_11008 96 104 :=
  interval_of_check cellTest_11008 96 8 (by decide +kernel)

theorem cellTest_11008_block_13 : Interval cellTest_11008 104 112 :=
  interval_of_check cellTest_11008 104 8 (by decide +kernel)

theorem cellTest_11008_block_14 : Interval cellTest_11008 112 120 :=
  interval_of_check cellTest_11008 112 8 (by decide +kernel)

theorem cellTest_11008_block_15 : Interval cellTest_11008 120 128 :=
  interval_of_check cellTest_11008 120 8 (by decide +kernel)

theorem cellTest_11008_block_16 : Interval cellTest_11008 128 136 :=
  interval_of_check cellTest_11008 128 8 (by decide +kernel)

theorem cellTest_11008_block_17 : Interval cellTest_11008 136 144 :=
  interval_of_check cellTest_11008 136 8 (by decide +kernel)

theorem cellTest_11008_block_18 : Interval cellTest_11008 144 152 :=
  interval_of_check cellTest_11008 144 8 (by decide +kernel)

theorem cellTest_11008_block_19 : Interval cellTest_11008 152 160 :=
  interval_of_check cellTest_11008 152 8 (by decide +kernel)

theorem cellTest_11008_block_20 : Interval cellTest_11008 160 168 :=
  interval_of_check cellTest_11008 160 8 (by decide +kernel)

theorem cellTest_11008_block_21 : Interval cellTest_11008 168 176 :=
  interval_of_check cellTest_11008 168 8 (by decide +kernel)

theorem cellTest_11008_block_22 : Interval cellTest_11008 176 184 :=
  interval_of_check cellTest_11008 176 8 (by decide +kernel)

theorem cellTest_11008_block_23 : Interval cellTest_11008 184 192 :=
  interval_of_check cellTest_11008 184 8 (by decide +kernel)

theorem cellTest_11008_block_24 : Interval cellTest_11008 192 200 :=
  interval_of_check cellTest_11008 192 8 (by decide +kernel)

theorem cellTest_11008_block_25 : Interval cellTest_11008 200 208 :=
  interval_of_check cellTest_11008 200 8 (by decide +kernel)

theorem cellTest_11008_block_26 : Interval cellTest_11008 208 216 :=
  interval_of_check cellTest_11008 208 8 (by decide +kernel)

theorem cellTest_11008_block_27 : Interval cellTest_11008 216 224 :=
  interval_of_check cellTest_11008 216 8 (by decide +kernel)

theorem cellTest_11008_block_28 : Interval cellTest_11008 224 232 :=
  interval_of_check cellTest_11008 224 8 (by decide +kernel)

theorem cellTest_11008_block_29 : Interval cellTest_11008 232 240 :=
  interval_of_check cellTest_11008 232 8 (by decide +kernel)

theorem cellTest_11008_block_30 : Interval cellTest_11008 240 248 :=
  interval_of_check cellTest_11008 240 8 (by decide +kernel)

theorem cellTest_11008_block_31 : Interval cellTest_11008 248 256 :=
  interval_of_check cellTest_11008 248 8 (by decide +kernel)

theorem cellTest_11008_complete : Interval cellTest_11008 0 256 :=
  (interval_append cellTest_11008 0 128 256
  (interval_append cellTest_11008 0 64 128
  (interval_append cellTest_11008 0 32 64
  (interval_append cellTest_11008 0 16 32
  (interval_append cellTest_11008 0 8 16
  cellTest_11008_block_0
  cellTest_11008_block_1)
  (interval_append cellTest_11008 16 24 32
  cellTest_11008_block_2
  cellTest_11008_block_3))
  (interval_append cellTest_11008 32 48 64
  (interval_append cellTest_11008 32 40 48
  cellTest_11008_block_4
  cellTest_11008_block_5)
  (interval_append cellTest_11008 48 56 64
  cellTest_11008_block_6
  cellTest_11008_block_7)))
  (interval_append cellTest_11008 64 96 128
  (interval_append cellTest_11008 64 80 96
  (interval_append cellTest_11008 64 72 80
  cellTest_11008_block_8
  cellTest_11008_block_9)
  (interval_append cellTest_11008 80 88 96
  cellTest_11008_block_10
  cellTest_11008_block_11))
  (interval_append cellTest_11008 96 112 128
  (interval_append cellTest_11008 96 104 112
  cellTest_11008_block_12
  cellTest_11008_block_13)
  (interval_append cellTest_11008 112 120 128
  cellTest_11008_block_14
  cellTest_11008_block_15))))
  (interval_append cellTest_11008 128 192 256
  (interval_append cellTest_11008 128 160 192
  (interval_append cellTest_11008 128 144 160
  (interval_append cellTest_11008 128 136 144
  cellTest_11008_block_16
  cellTest_11008_block_17)
  (interval_append cellTest_11008 144 152 160
  cellTest_11008_block_18
  cellTest_11008_block_19))
  (interval_append cellTest_11008 160 176 192
  (interval_append cellTest_11008 160 168 176
  cellTest_11008_block_20
  cellTest_11008_block_21)
  (interval_append cellTest_11008 176 184 192
  cellTest_11008_block_22
  cellTest_11008_block_23)))
  (interval_append cellTest_11008 192 224 256
  (interval_append cellTest_11008 192 208 224
  (interval_append cellTest_11008 192 200 208
  cellTest_11008_block_24
  cellTest_11008_block_25)
  (interval_append cellTest_11008 208 216 224
  cellTest_11008_block_26
  cellTest_11008_block_27))
  (interval_append cellTest_11008 224 240 256
  (interval_append cellTest_11008 224 232 240
  cellTest_11008_block_28
  cellTest_11008_block_29)
  (interval_append cellTest_11008 240 248 256
  cellTest_11008_block_30
  cellTest_11008_block_31)))))
theorem cellTestInterval11008 : Interval cellTest 11008 11264 := by
  intro i hlo hhi
  have h := cellTest_11008_complete (i-11008) (Nat.zero_le _) (by omega)
  simpa only [cellTest_11008, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells044 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_11264 (i : Nat) := cellTest (i+11264)
theorem cellTest_11264_block_0 : Interval cellTest_11264 0 8 :=
  interval_of_check cellTest_11264 0 8 (by decide +kernel)

theorem cellTest_11264_block_1 : Interval cellTest_11264 8 16 :=
  interval_of_check cellTest_11264 8 8 (by decide +kernel)

theorem cellTest_11264_block_2 : Interval cellTest_11264 16 24 :=
  interval_of_check cellTest_11264 16 8 (by decide +kernel)

theorem cellTest_11264_block_3 : Interval cellTest_11264 24 32 :=
  interval_of_check cellTest_11264 24 8 (by decide +kernel)

theorem cellTest_11264_block_4 : Interval cellTest_11264 32 40 :=
  interval_of_check cellTest_11264 32 8 (by decide +kernel)

theorem cellTest_11264_block_5 : Interval cellTest_11264 40 48 :=
  interval_of_check cellTest_11264 40 8 (by decide +kernel)

theorem cellTest_11264_block_6 : Interval cellTest_11264 48 56 :=
  interval_of_check cellTest_11264 48 8 (by decide +kernel)

theorem cellTest_11264_block_7 : Interval cellTest_11264 56 64 :=
  interval_of_check cellTest_11264 56 8 (by decide +kernel)

theorem cellTest_11264_block_8 : Interval cellTest_11264 64 72 :=
  interval_of_check cellTest_11264 64 8 (by decide +kernel)

theorem cellTest_11264_block_9 : Interval cellTest_11264 72 80 :=
  interval_of_check cellTest_11264 72 8 (by decide +kernel)

theorem cellTest_11264_block_10 : Interval cellTest_11264 80 88 :=
  interval_of_check cellTest_11264 80 8 (by decide +kernel)

theorem cellTest_11264_block_11 : Interval cellTest_11264 88 96 :=
  interval_of_check cellTest_11264 88 8 (by decide +kernel)

theorem cellTest_11264_block_12 : Interval cellTest_11264 96 104 :=
  interval_of_check cellTest_11264 96 8 (by decide +kernel)

theorem cellTest_11264_block_13 : Interval cellTest_11264 104 112 :=
  interval_of_check cellTest_11264 104 8 (by decide +kernel)

theorem cellTest_11264_block_14 : Interval cellTest_11264 112 120 :=
  interval_of_check cellTest_11264 112 8 (by decide +kernel)

theorem cellTest_11264_block_15 : Interval cellTest_11264 120 128 :=
  interval_of_check cellTest_11264 120 8 (by decide +kernel)

theorem cellTest_11264_block_16 : Interval cellTest_11264 128 136 :=
  interval_of_check cellTest_11264 128 8 (by decide +kernel)

theorem cellTest_11264_block_17 : Interval cellTest_11264 136 144 :=
  interval_of_check cellTest_11264 136 8 (by decide +kernel)

theorem cellTest_11264_block_18 : Interval cellTest_11264 144 152 :=
  interval_of_check cellTest_11264 144 8 (by decide +kernel)

theorem cellTest_11264_block_19 : Interval cellTest_11264 152 160 :=
  interval_of_check cellTest_11264 152 8 (by decide +kernel)

theorem cellTest_11264_block_20 : Interval cellTest_11264 160 168 :=
  interval_of_check cellTest_11264 160 8 (by decide +kernel)

theorem cellTest_11264_block_21 : Interval cellTest_11264 168 176 :=
  interval_of_check cellTest_11264 168 8 (by decide +kernel)

theorem cellTest_11264_block_22 : Interval cellTest_11264 176 184 :=
  interval_of_check cellTest_11264 176 8 (by decide +kernel)

theorem cellTest_11264_block_23 : Interval cellTest_11264 184 192 :=
  interval_of_check cellTest_11264 184 8 (by decide +kernel)

theorem cellTest_11264_block_24 : Interval cellTest_11264 192 200 :=
  interval_of_check cellTest_11264 192 8 (by decide +kernel)

theorem cellTest_11264_block_25 : Interval cellTest_11264 200 208 :=
  interval_of_check cellTest_11264 200 8 (by decide +kernel)

theorem cellTest_11264_block_26 : Interval cellTest_11264 208 216 :=
  interval_of_check cellTest_11264 208 8 (by decide +kernel)

theorem cellTest_11264_block_27 : Interval cellTest_11264 216 224 :=
  interval_of_check cellTest_11264 216 8 (by decide +kernel)

theorem cellTest_11264_block_28 : Interval cellTest_11264 224 232 :=
  interval_of_check cellTest_11264 224 8 (by decide +kernel)

theorem cellTest_11264_block_29 : Interval cellTest_11264 232 240 :=
  interval_of_check cellTest_11264 232 8 (by decide +kernel)

theorem cellTest_11264_block_30 : Interval cellTest_11264 240 248 :=
  interval_of_check cellTest_11264 240 8 (by decide +kernel)

theorem cellTest_11264_block_31 : Interval cellTest_11264 248 256 :=
  interval_of_check cellTest_11264 248 8 (by decide +kernel)

theorem cellTest_11264_complete : Interval cellTest_11264 0 256 :=
  (interval_append cellTest_11264 0 128 256
  (interval_append cellTest_11264 0 64 128
  (interval_append cellTest_11264 0 32 64
  (interval_append cellTest_11264 0 16 32
  (interval_append cellTest_11264 0 8 16
  cellTest_11264_block_0
  cellTest_11264_block_1)
  (interval_append cellTest_11264 16 24 32
  cellTest_11264_block_2
  cellTest_11264_block_3))
  (interval_append cellTest_11264 32 48 64
  (interval_append cellTest_11264 32 40 48
  cellTest_11264_block_4
  cellTest_11264_block_5)
  (interval_append cellTest_11264 48 56 64
  cellTest_11264_block_6
  cellTest_11264_block_7)))
  (interval_append cellTest_11264 64 96 128
  (interval_append cellTest_11264 64 80 96
  (interval_append cellTest_11264 64 72 80
  cellTest_11264_block_8
  cellTest_11264_block_9)
  (interval_append cellTest_11264 80 88 96
  cellTest_11264_block_10
  cellTest_11264_block_11))
  (interval_append cellTest_11264 96 112 128
  (interval_append cellTest_11264 96 104 112
  cellTest_11264_block_12
  cellTest_11264_block_13)
  (interval_append cellTest_11264 112 120 128
  cellTest_11264_block_14
  cellTest_11264_block_15))))
  (interval_append cellTest_11264 128 192 256
  (interval_append cellTest_11264 128 160 192
  (interval_append cellTest_11264 128 144 160
  (interval_append cellTest_11264 128 136 144
  cellTest_11264_block_16
  cellTest_11264_block_17)
  (interval_append cellTest_11264 144 152 160
  cellTest_11264_block_18
  cellTest_11264_block_19))
  (interval_append cellTest_11264 160 176 192
  (interval_append cellTest_11264 160 168 176
  cellTest_11264_block_20
  cellTest_11264_block_21)
  (interval_append cellTest_11264 176 184 192
  cellTest_11264_block_22
  cellTest_11264_block_23)))
  (interval_append cellTest_11264 192 224 256
  (interval_append cellTest_11264 192 208 224
  (interval_append cellTest_11264 192 200 208
  cellTest_11264_block_24
  cellTest_11264_block_25)
  (interval_append cellTest_11264 208 216 224
  cellTest_11264_block_26
  cellTest_11264_block_27))
  (interval_append cellTest_11264 224 240 256
  (interval_append cellTest_11264 224 232 240
  cellTest_11264_block_28
  cellTest_11264_block_29)
  (interval_append cellTest_11264 240 248 256
  cellTest_11264_block_30
  cellTest_11264_block_31)))))
theorem cellTestInterval11264 : Interval cellTest 11264 11520 := by
  intro i hlo hhi
  have h := cellTest_11264_complete (i-11264) (Nat.zero_le _) (by omega)
  simpa only [cellTest_11264, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells045 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_11520 (i : Nat) := cellTest (i+11520)
theorem cellTest_11520_block_0 : Interval cellTest_11520 0 8 :=
  interval_of_check cellTest_11520 0 8 (by decide +kernel)

theorem cellTest_11520_block_1 : Interval cellTest_11520 8 16 :=
  interval_of_check cellTest_11520 8 8 (by decide +kernel)

theorem cellTest_11520_block_2 : Interval cellTest_11520 16 24 :=
  interval_of_check cellTest_11520 16 8 (by decide +kernel)

theorem cellTest_11520_block_3 : Interval cellTest_11520 24 32 :=
  interval_of_check cellTest_11520 24 8 (by decide +kernel)

theorem cellTest_11520_block_4 : Interval cellTest_11520 32 40 :=
  interval_of_check cellTest_11520 32 8 (by decide +kernel)

theorem cellTest_11520_block_5 : Interval cellTest_11520 40 48 :=
  interval_of_check cellTest_11520 40 8 (by decide +kernel)

theorem cellTest_11520_block_6 : Interval cellTest_11520 48 56 :=
  interval_of_check cellTest_11520 48 8 (by decide +kernel)

theorem cellTest_11520_block_7 : Interval cellTest_11520 56 64 :=
  interval_of_check cellTest_11520 56 8 (by decide +kernel)

theorem cellTest_11520_block_8 : Interval cellTest_11520 64 72 :=
  interval_of_check cellTest_11520 64 8 (by decide +kernel)

theorem cellTest_11520_block_9 : Interval cellTest_11520 72 80 :=
  interval_of_check cellTest_11520 72 8 (by decide +kernel)

theorem cellTest_11520_block_10 : Interval cellTest_11520 80 88 :=
  interval_of_check cellTest_11520 80 8 (by decide +kernel)

theorem cellTest_11520_block_11 : Interval cellTest_11520 88 96 :=
  interval_of_check cellTest_11520 88 8 (by decide +kernel)

theorem cellTest_11520_block_12 : Interval cellTest_11520 96 104 :=
  interval_of_check cellTest_11520 96 8 (by decide +kernel)

theorem cellTest_11520_block_13 : Interval cellTest_11520 104 112 :=
  interval_of_check cellTest_11520 104 8 (by decide +kernel)

theorem cellTest_11520_block_14 : Interval cellTest_11520 112 120 :=
  interval_of_check cellTest_11520 112 8 (by decide +kernel)

theorem cellTest_11520_block_15 : Interval cellTest_11520 120 128 :=
  interval_of_check cellTest_11520 120 8 (by decide +kernel)

theorem cellTest_11520_block_16 : Interval cellTest_11520 128 136 :=
  interval_of_check cellTest_11520 128 8 (by decide +kernel)

theorem cellTest_11520_block_17 : Interval cellTest_11520 136 144 :=
  interval_of_check cellTest_11520 136 8 (by decide +kernel)

theorem cellTest_11520_block_18 : Interval cellTest_11520 144 152 :=
  interval_of_check cellTest_11520 144 8 (by decide +kernel)

theorem cellTest_11520_block_19 : Interval cellTest_11520 152 160 :=
  interval_of_check cellTest_11520 152 8 (by decide +kernel)

theorem cellTest_11520_block_20 : Interval cellTest_11520 160 168 :=
  interval_of_check cellTest_11520 160 8 (by decide +kernel)

theorem cellTest_11520_block_21 : Interval cellTest_11520 168 176 :=
  interval_of_check cellTest_11520 168 8 (by decide +kernel)

theorem cellTest_11520_block_22 : Interval cellTest_11520 176 184 :=
  interval_of_check cellTest_11520 176 8 (by decide +kernel)

theorem cellTest_11520_block_23 : Interval cellTest_11520 184 192 :=
  interval_of_check cellTest_11520 184 8 (by decide +kernel)

theorem cellTest_11520_block_24 : Interval cellTest_11520 192 200 :=
  interval_of_check cellTest_11520 192 8 (by decide +kernel)

theorem cellTest_11520_block_25 : Interval cellTest_11520 200 208 :=
  interval_of_check cellTest_11520 200 8 (by decide +kernel)

theorem cellTest_11520_block_26 : Interval cellTest_11520 208 216 :=
  interval_of_check cellTest_11520 208 8 (by decide +kernel)

theorem cellTest_11520_block_27 : Interval cellTest_11520 216 224 :=
  interval_of_check cellTest_11520 216 8 (by decide +kernel)

theorem cellTest_11520_block_28 : Interval cellTest_11520 224 232 :=
  interval_of_check cellTest_11520 224 8 (by decide +kernel)

theorem cellTest_11520_block_29 : Interval cellTest_11520 232 240 :=
  interval_of_check cellTest_11520 232 8 (by decide +kernel)

theorem cellTest_11520_block_30 : Interval cellTest_11520 240 248 :=
  interval_of_check cellTest_11520 240 8 (by decide +kernel)

theorem cellTest_11520_block_31 : Interval cellTest_11520 248 256 :=
  interval_of_check cellTest_11520 248 8 (by decide +kernel)

theorem cellTest_11520_complete : Interval cellTest_11520 0 256 :=
  (interval_append cellTest_11520 0 128 256
  (interval_append cellTest_11520 0 64 128
  (interval_append cellTest_11520 0 32 64
  (interval_append cellTest_11520 0 16 32
  (interval_append cellTest_11520 0 8 16
  cellTest_11520_block_0
  cellTest_11520_block_1)
  (interval_append cellTest_11520 16 24 32
  cellTest_11520_block_2
  cellTest_11520_block_3))
  (interval_append cellTest_11520 32 48 64
  (interval_append cellTest_11520 32 40 48
  cellTest_11520_block_4
  cellTest_11520_block_5)
  (interval_append cellTest_11520 48 56 64
  cellTest_11520_block_6
  cellTest_11520_block_7)))
  (interval_append cellTest_11520 64 96 128
  (interval_append cellTest_11520 64 80 96
  (interval_append cellTest_11520 64 72 80
  cellTest_11520_block_8
  cellTest_11520_block_9)
  (interval_append cellTest_11520 80 88 96
  cellTest_11520_block_10
  cellTest_11520_block_11))
  (interval_append cellTest_11520 96 112 128
  (interval_append cellTest_11520 96 104 112
  cellTest_11520_block_12
  cellTest_11520_block_13)
  (interval_append cellTest_11520 112 120 128
  cellTest_11520_block_14
  cellTest_11520_block_15))))
  (interval_append cellTest_11520 128 192 256
  (interval_append cellTest_11520 128 160 192
  (interval_append cellTest_11520 128 144 160
  (interval_append cellTest_11520 128 136 144
  cellTest_11520_block_16
  cellTest_11520_block_17)
  (interval_append cellTest_11520 144 152 160
  cellTest_11520_block_18
  cellTest_11520_block_19))
  (interval_append cellTest_11520 160 176 192
  (interval_append cellTest_11520 160 168 176
  cellTest_11520_block_20
  cellTest_11520_block_21)
  (interval_append cellTest_11520 176 184 192
  cellTest_11520_block_22
  cellTest_11520_block_23)))
  (interval_append cellTest_11520 192 224 256
  (interval_append cellTest_11520 192 208 224
  (interval_append cellTest_11520 192 200 208
  cellTest_11520_block_24
  cellTest_11520_block_25)
  (interval_append cellTest_11520 208 216 224
  cellTest_11520_block_26
  cellTest_11520_block_27))
  (interval_append cellTest_11520 224 240 256
  (interval_append cellTest_11520 224 232 240
  cellTest_11520_block_28
  cellTest_11520_block_29)
  (interval_append cellTest_11520 240 248 256
  cellTest_11520_block_30
  cellTest_11520_block_31)))))
theorem cellTestInterval11520 : Interval cellTest 11520 11776 := by
  intro i hlo hhi
  have h := cellTest_11520_complete (i-11520) (Nat.zero_le _) (by omega)
  simpa only [cellTest_11520, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells046 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_11776 (i : Nat) := cellTest (i+11776)
theorem cellTest_11776_block_0 : Interval cellTest_11776 0 8 :=
  interval_of_check cellTest_11776 0 8 (by decide +kernel)

theorem cellTest_11776_block_1 : Interval cellTest_11776 8 16 :=
  interval_of_check cellTest_11776 8 8 (by decide +kernel)

theorem cellTest_11776_block_2 : Interval cellTest_11776 16 24 :=
  interval_of_check cellTest_11776 16 8 (by decide +kernel)

theorem cellTest_11776_block_3 : Interval cellTest_11776 24 32 :=
  interval_of_check cellTest_11776 24 8 (by decide +kernel)

theorem cellTest_11776_block_4 : Interval cellTest_11776 32 40 :=
  interval_of_check cellTest_11776 32 8 (by decide +kernel)

theorem cellTest_11776_block_5 : Interval cellTest_11776 40 48 :=
  interval_of_check cellTest_11776 40 8 (by decide +kernel)

theorem cellTest_11776_block_6 : Interval cellTest_11776 48 56 :=
  interval_of_check cellTest_11776 48 8 (by decide +kernel)

theorem cellTest_11776_block_7 : Interval cellTest_11776 56 64 :=
  interval_of_check cellTest_11776 56 8 (by decide +kernel)

theorem cellTest_11776_block_8 : Interval cellTest_11776 64 72 :=
  interval_of_check cellTest_11776 64 8 (by decide +kernel)

theorem cellTest_11776_block_9 : Interval cellTest_11776 72 80 :=
  interval_of_check cellTest_11776 72 8 (by decide +kernel)

theorem cellTest_11776_block_10 : Interval cellTest_11776 80 88 :=
  interval_of_check cellTest_11776 80 8 (by decide +kernel)

theorem cellTest_11776_block_11 : Interval cellTest_11776 88 96 :=
  interval_of_check cellTest_11776 88 8 (by decide +kernel)

theorem cellTest_11776_block_12 : Interval cellTest_11776 96 104 :=
  interval_of_check cellTest_11776 96 8 (by decide +kernel)

theorem cellTest_11776_block_13 : Interval cellTest_11776 104 112 :=
  interval_of_check cellTest_11776 104 8 (by decide +kernel)

theorem cellTest_11776_block_14 : Interval cellTest_11776 112 120 :=
  interval_of_check cellTest_11776 112 8 (by decide +kernel)

theorem cellTest_11776_block_15 : Interval cellTest_11776 120 128 :=
  interval_of_check cellTest_11776 120 8 (by decide +kernel)

theorem cellTest_11776_block_16 : Interval cellTest_11776 128 136 :=
  interval_of_check cellTest_11776 128 8 (by decide +kernel)

theorem cellTest_11776_block_17 : Interval cellTest_11776 136 144 :=
  interval_of_check cellTest_11776 136 8 (by decide +kernel)

theorem cellTest_11776_block_18 : Interval cellTest_11776 144 152 :=
  interval_of_check cellTest_11776 144 8 (by decide +kernel)

theorem cellTest_11776_block_19 : Interval cellTest_11776 152 160 :=
  interval_of_check cellTest_11776 152 8 (by decide +kernel)

theorem cellTest_11776_block_20 : Interval cellTest_11776 160 168 :=
  interval_of_check cellTest_11776 160 8 (by decide +kernel)

theorem cellTest_11776_block_21 : Interval cellTest_11776 168 176 :=
  interval_of_check cellTest_11776 168 8 (by decide +kernel)

theorem cellTest_11776_block_22 : Interval cellTest_11776 176 184 :=
  interval_of_check cellTest_11776 176 8 (by decide +kernel)

theorem cellTest_11776_block_23 : Interval cellTest_11776 184 192 :=
  interval_of_check cellTest_11776 184 8 (by decide +kernel)

theorem cellTest_11776_block_24 : Interval cellTest_11776 192 200 :=
  interval_of_check cellTest_11776 192 8 (by decide +kernel)

theorem cellTest_11776_block_25 : Interval cellTest_11776 200 208 :=
  interval_of_check cellTest_11776 200 8 (by decide +kernel)

theorem cellTest_11776_block_26 : Interval cellTest_11776 208 216 :=
  interval_of_check cellTest_11776 208 8 (by decide +kernel)

theorem cellTest_11776_block_27 : Interval cellTest_11776 216 224 :=
  interval_of_check cellTest_11776 216 8 (by decide +kernel)

theorem cellTest_11776_block_28 : Interval cellTest_11776 224 232 :=
  interval_of_check cellTest_11776 224 8 (by decide +kernel)

theorem cellTest_11776_block_29 : Interval cellTest_11776 232 240 :=
  interval_of_check cellTest_11776 232 8 (by decide +kernel)

theorem cellTest_11776_block_30 : Interval cellTest_11776 240 248 :=
  interval_of_check cellTest_11776 240 8 (by decide +kernel)

theorem cellTest_11776_block_31 : Interval cellTest_11776 248 256 :=
  interval_of_check cellTest_11776 248 8 (by decide +kernel)

theorem cellTest_11776_complete : Interval cellTest_11776 0 256 :=
  (interval_append cellTest_11776 0 128 256
  (interval_append cellTest_11776 0 64 128
  (interval_append cellTest_11776 0 32 64
  (interval_append cellTest_11776 0 16 32
  (interval_append cellTest_11776 0 8 16
  cellTest_11776_block_0
  cellTest_11776_block_1)
  (interval_append cellTest_11776 16 24 32
  cellTest_11776_block_2
  cellTest_11776_block_3))
  (interval_append cellTest_11776 32 48 64
  (interval_append cellTest_11776 32 40 48
  cellTest_11776_block_4
  cellTest_11776_block_5)
  (interval_append cellTest_11776 48 56 64
  cellTest_11776_block_6
  cellTest_11776_block_7)))
  (interval_append cellTest_11776 64 96 128
  (interval_append cellTest_11776 64 80 96
  (interval_append cellTest_11776 64 72 80
  cellTest_11776_block_8
  cellTest_11776_block_9)
  (interval_append cellTest_11776 80 88 96
  cellTest_11776_block_10
  cellTest_11776_block_11))
  (interval_append cellTest_11776 96 112 128
  (interval_append cellTest_11776 96 104 112
  cellTest_11776_block_12
  cellTest_11776_block_13)
  (interval_append cellTest_11776 112 120 128
  cellTest_11776_block_14
  cellTest_11776_block_15))))
  (interval_append cellTest_11776 128 192 256
  (interval_append cellTest_11776 128 160 192
  (interval_append cellTest_11776 128 144 160
  (interval_append cellTest_11776 128 136 144
  cellTest_11776_block_16
  cellTest_11776_block_17)
  (interval_append cellTest_11776 144 152 160
  cellTest_11776_block_18
  cellTest_11776_block_19))
  (interval_append cellTest_11776 160 176 192
  (interval_append cellTest_11776 160 168 176
  cellTest_11776_block_20
  cellTest_11776_block_21)
  (interval_append cellTest_11776 176 184 192
  cellTest_11776_block_22
  cellTest_11776_block_23)))
  (interval_append cellTest_11776 192 224 256
  (interval_append cellTest_11776 192 208 224
  (interval_append cellTest_11776 192 200 208
  cellTest_11776_block_24
  cellTest_11776_block_25)
  (interval_append cellTest_11776 208 216 224
  cellTest_11776_block_26
  cellTest_11776_block_27))
  (interval_append cellTest_11776 224 240 256
  (interval_append cellTest_11776 224 232 240
  cellTest_11776_block_28
  cellTest_11776_block_29)
  (interval_append cellTest_11776 240 248 256
  cellTest_11776_block_30
  cellTest_11776_block_31)))))
theorem cellTestInterval11776 : Interval cellTest 11776 12032 := by
  intro i hlo hhi
  have h := cellTest_11776_complete (i-11776) (Nat.zero_le _) (by omega)
  simpa only [cellTest_11776, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells047 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_12032 (i : Nat) := cellTest (i+12032)
theorem cellTest_12032_block_0 : Interval cellTest_12032 0 8 :=
  interval_of_check cellTest_12032 0 8 (by decide +kernel)

theorem cellTest_12032_block_1 : Interval cellTest_12032 8 16 :=
  interval_of_check cellTest_12032 8 8 (by decide +kernel)

theorem cellTest_12032_block_2 : Interval cellTest_12032 16 24 :=
  interval_of_check cellTest_12032 16 8 (by decide +kernel)

theorem cellTest_12032_block_3 : Interval cellTest_12032 24 32 :=
  interval_of_check cellTest_12032 24 8 (by decide +kernel)

theorem cellTest_12032_block_4 : Interval cellTest_12032 32 40 :=
  interval_of_check cellTest_12032 32 8 (by decide +kernel)

theorem cellTest_12032_block_5 : Interval cellTest_12032 40 48 :=
  interval_of_check cellTest_12032 40 8 (by decide +kernel)

theorem cellTest_12032_block_6 : Interval cellTest_12032 48 56 :=
  interval_of_check cellTest_12032 48 8 (by decide +kernel)

theorem cellTest_12032_block_7 : Interval cellTest_12032 56 64 :=
  interval_of_check cellTest_12032 56 8 (by decide +kernel)

theorem cellTest_12032_block_8 : Interval cellTest_12032 64 72 :=
  interval_of_check cellTest_12032 64 8 (by decide +kernel)

theorem cellTest_12032_block_9 : Interval cellTest_12032 72 80 :=
  interval_of_check cellTest_12032 72 8 (by decide +kernel)

theorem cellTest_12032_block_10 : Interval cellTest_12032 80 88 :=
  interval_of_check cellTest_12032 80 8 (by decide +kernel)

theorem cellTest_12032_block_11 : Interval cellTest_12032 88 96 :=
  interval_of_check cellTest_12032 88 8 (by decide +kernel)

theorem cellTest_12032_block_12 : Interval cellTest_12032 96 104 :=
  interval_of_check cellTest_12032 96 8 (by decide +kernel)

theorem cellTest_12032_block_13 : Interval cellTest_12032 104 112 :=
  interval_of_check cellTest_12032 104 8 (by decide +kernel)

theorem cellTest_12032_block_14 : Interval cellTest_12032 112 120 :=
  interval_of_check cellTest_12032 112 8 (by decide +kernel)

theorem cellTest_12032_block_15 : Interval cellTest_12032 120 128 :=
  interval_of_check cellTest_12032 120 8 (by decide +kernel)

theorem cellTest_12032_block_16 : Interval cellTest_12032 128 136 :=
  interval_of_check cellTest_12032 128 8 (by decide +kernel)

theorem cellTest_12032_block_17 : Interval cellTest_12032 136 144 :=
  interval_of_check cellTest_12032 136 8 (by decide +kernel)

theorem cellTest_12032_block_18 : Interval cellTest_12032 144 152 :=
  interval_of_check cellTest_12032 144 8 (by decide +kernel)

theorem cellTest_12032_block_19 : Interval cellTest_12032 152 160 :=
  interval_of_check cellTest_12032 152 8 (by decide +kernel)

theorem cellTest_12032_block_20 : Interval cellTest_12032 160 168 :=
  interval_of_check cellTest_12032 160 8 (by decide +kernel)

theorem cellTest_12032_block_21 : Interval cellTest_12032 168 176 :=
  interval_of_check cellTest_12032 168 8 (by decide +kernel)

theorem cellTest_12032_block_22 : Interval cellTest_12032 176 184 :=
  interval_of_check cellTest_12032 176 8 (by decide +kernel)

theorem cellTest_12032_block_23 : Interval cellTest_12032 184 192 :=
  interval_of_check cellTest_12032 184 8 (by decide +kernel)

theorem cellTest_12032_block_24 : Interval cellTest_12032 192 200 :=
  interval_of_check cellTest_12032 192 8 (by decide +kernel)

theorem cellTest_12032_block_25 : Interval cellTest_12032 200 208 :=
  interval_of_check cellTest_12032 200 8 (by decide +kernel)

theorem cellTest_12032_block_26 : Interval cellTest_12032 208 216 :=
  interval_of_check cellTest_12032 208 8 (by decide +kernel)

theorem cellTest_12032_block_27 : Interval cellTest_12032 216 224 :=
  interval_of_check cellTest_12032 216 8 (by decide +kernel)

theorem cellTest_12032_block_28 : Interval cellTest_12032 224 232 :=
  interval_of_check cellTest_12032 224 8 (by decide +kernel)

theorem cellTest_12032_block_29 : Interval cellTest_12032 232 240 :=
  interval_of_check cellTest_12032 232 8 (by decide +kernel)

theorem cellTest_12032_block_30 : Interval cellTest_12032 240 248 :=
  interval_of_check cellTest_12032 240 8 (by decide +kernel)

theorem cellTest_12032_block_31 : Interval cellTest_12032 248 256 :=
  interval_of_check cellTest_12032 248 8 (by decide +kernel)

theorem cellTest_12032_complete : Interval cellTest_12032 0 256 :=
  (interval_append cellTest_12032 0 128 256
  (interval_append cellTest_12032 0 64 128
  (interval_append cellTest_12032 0 32 64
  (interval_append cellTest_12032 0 16 32
  (interval_append cellTest_12032 0 8 16
  cellTest_12032_block_0
  cellTest_12032_block_1)
  (interval_append cellTest_12032 16 24 32
  cellTest_12032_block_2
  cellTest_12032_block_3))
  (interval_append cellTest_12032 32 48 64
  (interval_append cellTest_12032 32 40 48
  cellTest_12032_block_4
  cellTest_12032_block_5)
  (interval_append cellTest_12032 48 56 64
  cellTest_12032_block_6
  cellTest_12032_block_7)))
  (interval_append cellTest_12032 64 96 128
  (interval_append cellTest_12032 64 80 96
  (interval_append cellTest_12032 64 72 80
  cellTest_12032_block_8
  cellTest_12032_block_9)
  (interval_append cellTest_12032 80 88 96
  cellTest_12032_block_10
  cellTest_12032_block_11))
  (interval_append cellTest_12032 96 112 128
  (interval_append cellTest_12032 96 104 112
  cellTest_12032_block_12
  cellTest_12032_block_13)
  (interval_append cellTest_12032 112 120 128
  cellTest_12032_block_14
  cellTest_12032_block_15))))
  (interval_append cellTest_12032 128 192 256
  (interval_append cellTest_12032 128 160 192
  (interval_append cellTest_12032 128 144 160
  (interval_append cellTest_12032 128 136 144
  cellTest_12032_block_16
  cellTest_12032_block_17)
  (interval_append cellTest_12032 144 152 160
  cellTest_12032_block_18
  cellTest_12032_block_19))
  (interval_append cellTest_12032 160 176 192
  (interval_append cellTest_12032 160 168 176
  cellTest_12032_block_20
  cellTest_12032_block_21)
  (interval_append cellTest_12032 176 184 192
  cellTest_12032_block_22
  cellTest_12032_block_23)))
  (interval_append cellTest_12032 192 224 256
  (interval_append cellTest_12032 192 208 224
  (interval_append cellTest_12032 192 200 208
  cellTest_12032_block_24
  cellTest_12032_block_25)
  (interval_append cellTest_12032 208 216 224
  cellTest_12032_block_26
  cellTest_12032_block_27))
  (interval_append cellTest_12032 224 240 256
  (interval_append cellTest_12032 224 232 240
  cellTest_12032_block_28
  cellTest_12032_block_29)
  (interval_append cellTest_12032 240 248 256
  cellTest_12032_block_30
  cellTest_12032_block_31)))))
theorem cellTestInterval12032 : Interval cellTest 12032 12288 := by
  intro i hlo hhi
  have h := cellTest_12032_complete (i-12032) (Nat.zero_le _) (by omega)
  simpa only [cellTest_12032, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
