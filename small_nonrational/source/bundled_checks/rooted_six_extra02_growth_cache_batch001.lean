module
prelude
public import RootedSixExtra02GrowthCacheData

/- RootedSixExtra02GrowthCacheCells016 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_4096 (i : Nat) := cellTest (i+4096)
theorem cellTest_4096_block_0 : Interval cellTest_4096 0 8 :=
  interval_of_check cellTest_4096 0 8 (by decide +kernel)

theorem cellTest_4096_block_1 : Interval cellTest_4096 8 16 :=
  interval_of_check cellTest_4096 8 8 (by decide +kernel)

theorem cellTest_4096_block_2 : Interval cellTest_4096 16 24 :=
  interval_of_check cellTest_4096 16 8 (by decide +kernel)

theorem cellTest_4096_block_3 : Interval cellTest_4096 24 32 :=
  interval_of_check cellTest_4096 24 8 (by decide +kernel)

theorem cellTest_4096_block_4 : Interval cellTest_4096 32 40 :=
  interval_of_check cellTest_4096 32 8 (by decide +kernel)

theorem cellTest_4096_block_5 : Interval cellTest_4096 40 48 :=
  interval_of_check cellTest_4096 40 8 (by decide +kernel)

theorem cellTest_4096_block_6 : Interval cellTest_4096 48 56 :=
  interval_of_check cellTest_4096 48 8 (by decide +kernel)

theorem cellTest_4096_block_7 : Interval cellTest_4096 56 64 :=
  interval_of_check cellTest_4096 56 8 (by decide +kernel)

theorem cellTest_4096_block_8 : Interval cellTest_4096 64 72 :=
  interval_of_check cellTest_4096 64 8 (by decide +kernel)

theorem cellTest_4096_block_9 : Interval cellTest_4096 72 80 :=
  interval_of_check cellTest_4096 72 8 (by decide +kernel)

theorem cellTest_4096_block_10 : Interval cellTest_4096 80 88 :=
  interval_of_check cellTest_4096 80 8 (by decide +kernel)

theorem cellTest_4096_block_11 : Interval cellTest_4096 88 96 :=
  interval_of_check cellTest_4096 88 8 (by decide +kernel)

theorem cellTest_4096_block_12 : Interval cellTest_4096 96 104 :=
  interval_of_check cellTest_4096 96 8 (by decide +kernel)

theorem cellTest_4096_block_13 : Interval cellTest_4096 104 112 :=
  interval_of_check cellTest_4096 104 8 (by decide +kernel)

theorem cellTest_4096_block_14 : Interval cellTest_4096 112 120 :=
  interval_of_check cellTest_4096 112 8 (by decide +kernel)

theorem cellTest_4096_block_15 : Interval cellTest_4096 120 128 :=
  interval_of_check cellTest_4096 120 8 (by decide +kernel)

theorem cellTest_4096_block_16 : Interval cellTest_4096 128 136 :=
  interval_of_check cellTest_4096 128 8 (by decide +kernel)

theorem cellTest_4096_block_17 : Interval cellTest_4096 136 144 :=
  interval_of_check cellTest_4096 136 8 (by decide +kernel)

theorem cellTest_4096_block_18 : Interval cellTest_4096 144 152 :=
  interval_of_check cellTest_4096 144 8 (by decide +kernel)

theorem cellTest_4096_block_19 : Interval cellTest_4096 152 160 :=
  interval_of_check cellTest_4096 152 8 (by decide +kernel)

theorem cellTest_4096_block_20 : Interval cellTest_4096 160 168 :=
  interval_of_check cellTest_4096 160 8 (by decide +kernel)

theorem cellTest_4096_block_21 : Interval cellTest_4096 168 176 :=
  interval_of_check cellTest_4096 168 8 (by decide +kernel)

theorem cellTest_4096_block_22 : Interval cellTest_4096 176 184 :=
  interval_of_check cellTest_4096 176 8 (by decide +kernel)

theorem cellTest_4096_block_23 : Interval cellTest_4096 184 192 :=
  interval_of_check cellTest_4096 184 8 (by decide +kernel)

theorem cellTest_4096_block_24 : Interval cellTest_4096 192 200 :=
  interval_of_check cellTest_4096 192 8 (by decide +kernel)

theorem cellTest_4096_block_25 : Interval cellTest_4096 200 208 :=
  interval_of_check cellTest_4096 200 8 (by decide +kernel)

theorem cellTest_4096_block_26 : Interval cellTest_4096 208 216 :=
  interval_of_check cellTest_4096 208 8 (by decide +kernel)

theorem cellTest_4096_block_27 : Interval cellTest_4096 216 224 :=
  interval_of_check cellTest_4096 216 8 (by decide +kernel)

theorem cellTest_4096_block_28 : Interval cellTest_4096 224 232 :=
  interval_of_check cellTest_4096 224 8 (by decide +kernel)

theorem cellTest_4096_block_29 : Interval cellTest_4096 232 240 :=
  interval_of_check cellTest_4096 232 8 (by decide +kernel)

theorem cellTest_4096_block_30 : Interval cellTest_4096 240 248 :=
  interval_of_check cellTest_4096 240 8 (by decide +kernel)

theorem cellTest_4096_block_31 : Interval cellTest_4096 248 256 :=
  interval_of_check cellTest_4096 248 8 (by decide +kernel)

theorem cellTest_4096_complete : Interval cellTest_4096 0 256 :=
  (interval_append cellTest_4096 0 128 256
  (interval_append cellTest_4096 0 64 128
  (interval_append cellTest_4096 0 32 64
  (interval_append cellTest_4096 0 16 32
  (interval_append cellTest_4096 0 8 16
  cellTest_4096_block_0
  cellTest_4096_block_1)
  (interval_append cellTest_4096 16 24 32
  cellTest_4096_block_2
  cellTest_4096_block_3))
  (interval_append cellTest_4096 32 48 64
  (interval_append cellTest_4096 32 40 48
  cellTest_4096_block_4
  cellTest_4096_block_5)
  (interval_append cellTest_4096 48 56 64
  cellTest_4096_block_6
  cellTest_4096_block_7)))
  (interval_append cellTest_4096 64 96 128
  (interval_append cellTest_4096 64 80 96
  (interval_append cellTest_4096 64 72 80
  cellTest_4096_block_8
  cellTest_4096_block_9)
  (interval_append cellTest_4096 80 88 96
  cellTest_4096_block_10
  cellTest_4096_block_11))
  (interval_append cellTest_4096 96 112 128
  (interval_append cellTest_4096 96 104 112
  cellTest_4096_block_12
  cellTest_4096_block_13)
  (interval_append cellTest_4096 112 120 128
  cellTest_4096_block_14
  cellTest_4096_block_15))))
  (interval_append cellTest_4096 128 192 256
  (interval_append cellTest_4096 128 160 192
  (interval_append cellTest_4096 128 144 160
  (interval_append cellTest_4096 128 136 144
  cellTest_4096_block_16
  cellTest_4096_block_17)
  (interval_append cellTest_4096 144 152 160
  cellTest_4096_block_18
  cellTest_4096_block_19))
  (interval_append cellTest_4096 160 176 192
  (interval_append cellTest_4096 160 168 176
  cellTest_4096_block_20
  cellTest_4096_block_21)
  (interval_append cellTest_4096 176 184 192
  cellTest_4096_block_22
  cellTest_4096_block_23)))
  (interval_append cellTest_4096 192 224 256
  (interval_append cellTest_4096 192 208 224
  (interval_append cellTest_4096 192 200 208
  cellTest_4096_block_24
  cellTest_4096_block_25)
  (interval_append cellTest_4096 208 216 224
  cellTest_4096_block_26
  cellTest_4096_block_27))
  (interval_append cellTest_4096 224 240 256
  (interval_append cellTest_4096 224 232 240
  cellTest_4096_block_28
  cellTest_4096_block_29)
  (interval_append cellTest_4096 240 248 256
  cellTest_4096_block_30
  cellTest_4096_block_31)))))
theorem cellTestInterval4096 : Interval cellTest 4096 4352 := by
  intro i hlo hhi
  have h := cellTest_4096_complete (i-4096) (Nat.zero_le _) (by omega)
  simpa only [cellTest_4096, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells017 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_4352 (i : Nat) := cellTest (i+4352)
theorem cellTest_4352_block_0 : Interval cellTest_4352 0 8 :=
  interval_of_check cellTest_4352 0 8 (by decide +kernel)

theorem cellTest_4352_block_1 : Interval cellTest_4352 8 16 :=
  interval_of_check cellTest_4352 8 8 (by decide +kernel)

theorem cellTest_4352_block_2 : Interval cellTest_4352 16 24 :=
  interval_of_check cellTest_4352 16 8 (by decide +kernel)

theorem cellTest_4352_block_3 : Interval cellTest_4352 24 32 :=
  interval_of_check cellTest_4352 24 8 (by decide +kernel)

theorem cellTest_4352_block_4 : Interval cellTest_4352 32 40 :=
  interval_of_check cellTest_4352 32 8 (by decide +kernel)

theorem cellTest_4352_block_5 : Interval cellTest_4352 40 48 :=
  interval_of_check cellTest_4352 40 8 (by decide +kernel)

theorem cellTest_4352_block_6 : Interval cellTest_4352 48 56 :=
  interval_of_check cellTest_4352 48 8 (by decide +kernel)

theorem cellTest_4352_block_7 : Interval cellTest_4352 56 64 :=
  interval_of_check cellTest_4352 56 8 (by decide +kernel)

theorem cellTest_4352_block_8 : Interval cellTest_4352 64 72 :=
  interval_of_check cellTest_4352 64 8 (by decide +kernel)

theorem cellTest_4352_block_9 : Interval cellTest_4352 72 80 :=
  interval_of_check cellTest_4352 72 8 (by decide +kernel)

theorem cellTest_4352_block_10 : Interval cellTest_4352 80 88 :=
  interval_of_check cellTest_4352 80 8 (by decide +kernel)

theorem cellTest_4352_block_11 : Interval cellTest_4352 88 96 :=
  interval_of_check cellTest_4352 88 8 (by decide +kernel)

theorem cellTest_4352_block_12 : Interval cellTest_4352 96 104 :=
  interval_of_check cellTest_4352 96 8 (by decide +kernel)

theorem cellTest_4352_block_13 : Interval cellTest_4352 104 112 :=
  interval_of_check cellTest_4352 104 8 (by decide +kernel)

theorem cellTest_4352_block_14 : Interval cellTest_4352 112 120 :=
  interval_of_check cellTest_4352 112 8 (by decide +kernel)

theorem cellTest_4352_block_15 : Interval cellTest_4352 120 128 :=
  interval_of_check cellTest_4352 120 8 (by decide +kernel)

theorem cellTest_4352_block_16 : Interval cellTest_4352 128 136 :=
  interval_of_check cellTest_4352 128 8 (by decide +kernel)

theorem cellTest_4352_block_17 : Interval cellTest_4352 136 144 :=
  interval_of_check cellTest_4352 136 8 (by decide +kernel)

theorem cellTest_4352_block_18 : Interval cellTest_4352 144 152 :=
  interval_of_check cellTest_4352 144 8 (by decide +kernel)

theorem cellTest_4352_block_19 : Interval cellTest_4352 152 160 :=
  interval_of_check cellTest_4352 152 8 (by decide +kernel)

theorem cellTest_4352_block_20 : Interval cellTest_4352 160 168 :=
  interval_of_check cellTest_4352 160 8 (by decide +kernel)

theorem cellTest_4352_block_21 : Interval cellTest_4352 168 176 :=
  interval_of_check cellTest_4352 168 8 (by decide +kernel)

theorem cellTest_4352_block_22 : Interval cellTest_4352 176 184 :=
  interval_of_check cellTest_4352 176 8 (by decide +kernel)

theorem cellTest_4352_block_23 : Interval cellTest_4352 184 192 :=
  interval_of_check cellTest_4352 184 8 (by decide +kernel)

theorem cellTest_4352_block_24 : Interval cellTest_4352 192 200 :=
  interval_of_check cellTest_4352 192 8 (by decide +kernel)

theorem cellTest_4352_block_25 : Interval cellTest_4352 200 208 :=
  interval_of_check cellTest_4352 200 8 (by decide +kernel)

theorem cellTest_4352_block_26 : Interval cellTest_4352 208 216 :=
  interval_of_check cellTest_4352 208 8 (by decide +kernel)

theorem cellTest_4352_block_27 : Interval cellTest_4352 216 224 :=
  interval_of_check cellTest_4352 216 8 (by decide +kernel)

theorem cellTest_4352_block_28 : Interval cellTest_4352 224 232 :=
  interval_of_check cellTest_4352 224 8 (by decide +kernel)

theorem cellTest_4352_block_29 : Interval cellTest_4352 232 240 :=
  interval_of_check cellTest_4352 232 8 (by decide +kernel)

theorem cellTest_4352_block_30 : Interval cellTest_4352 240 248 :=
  interval_of_check cellTest_4352 240 8 (by decide +kernel)

theorem cellTest_4352_block_31 : Interval cellTest_4352 248 256 :=
  interval_of_check cellTest_4352 248 8 (by decide +kernel)

theorem cellTest_4352_complete : Interval cellTest_4352 0 256 :=
  (interval_append cellTest_4352 0 128 256
  (interval_append cellTest_4352 0 64 128
  (interval_append cellTest_4352 0 32 64
  (interval_append cellTest_4352 0 16 32
  (interval_append cellTest_4352 0 8 16
  cellTest_4352_block_0
  cellTest_4352_block_1)
  (interval_append cellTest_4352 16 24 32
  cellTest_4352_block_2
  cellTest_4352_block_3))
  (interval_append cellTest_4352 32 48 64
  (interval_append cellTest_4352 32 40 48
  cellTest_4352_block_4
  cellTest_4352_block_5)
  (interval_append cellTest_4352 48 56 64
  cellTest_4352_block_6
  cellTest_4352_block_7)))
  (interval_append cellTest_4352 64 96 128
  (interval_append cellTest_4352 64 80 96
  (interval_append cellTest_4352 64 72 80
  cellTest_4352_block_8
  cellTest_4352_block_9)
  (interval_append cellTest_4352 80 88 96
  cellTest_4352_block_10
  cellTest_4352_block_11))
  (interval_append cellTest_4352 96 112 128
  (interval_append cellTest_4352 96 104 112
  cellTest_4352_block_12
  cellTest_4352_block_13)
  (interval_append cellTest_4352 112 120 128
  cellTest_4352_block_14
  cellTest_4352_block_15))))
  (interval_append cellTest_4352 128 192 256
  (interval_append cellTest_4352 128 160 192
  (interval_append cellTest_4352 128 144 160
  (interval_append cellTest_4352 128 136 144
  cellTest_4352_block_16
  cellTest_4352_block_17)
  (interval_append cellTest_4352 144 152 160
  cellTest_4352_block_18
  cellTest_4352_block_19))
  (interval_append cellTest_4352 160 176 192
  (interval_append cellTest_4352 160 168 176
  cellTest_4352_block_20
  cellTest_4352_block_21)
  (interval_append cellTest_4352 176 184 192
  cellTest_4352_block_22
  cellTest_4352_block_23)))
  (interval_append cellTest_4352 192 224 256
  (interval_append cellTest_4352 192 208 224
  (interval_append cellTest_4352 192 200 208
  cellTest_4352_block_24
  cellTest_4352_block_25)
  (interval_append cellTest_4352 208 216 224
  cellTest_4352_block_26
  cellTest_4352_block_27))
  (interval_append cellTest_4352 224 240 256
  (interval_append cellTest_4352 224 232 240
  cellTest_4352_block_28
  cellTest_4352_block_29)
  (interval_append cellTest_4352 240 248 256
  cellTest_4352_block_30
  cellTest_4352_block_31)))))
theorem cellTestInterval4352 : Interval cellTest 4352 4608 := by
  intro i hlo hhi
  have h := cellTest_4352_complete (i-4352) (Nat.zero_le _) (by omega)
  simpa only [cellTest_4352, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells018 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_4608 (i : Nat) := cellTest (i+4608)
theorem cellTest_4608_block_0 : Interval cellTest_4608 0 8 :=
  interval_of_check cellTest_4608 0 8 (by decide +kernel)

theorem cellTest_4608_block_1 : Interval cellTest_4608 8 16 :=
  interval_of_check cellTest_4608 8 8 (by decide +kernel)

theorem cellTest_4608_block_2 : Interval cellTest_4608 16 24 :=
  interval_of_check cellTest_4608 16 8 (by decide +kernel)

theorem cellTest_4608_block_3 : Interval cellTest_4608 24 32 :=
  interval_of_check cellTest_4608 24 8 (by decide +kernel)

theorem cellTest_4608_block_4 : Interval cellTest_4608 32 40 :=
  interval_of_check cellTest_4608 32 8 (by decide +kernel)

theorem cellTest_4608_block_5 : Interval cellTest_4608 40 48 :=
  interval_of_check cellTest_4608 40 8 (by decide +kernel)

theorem cellTest_4608_block_6 : Interval cellTest_4608 48 56 :=
  interval_of_check cellTest_4608 48 8 (by decide +kernel)

theorem cellTest_4608_block_7 : Interval cellTest_4608 56 64 :=
  interval_of_check cellTest_4608 56 8 (by decide +kernel)

theorem cellTest_4608_block_8 : Interval cellTest_4608 64 72 :=
  interval_of_check cellTest_4608 64 8 (by decide +kernel)

theorem cellTest_4608_block_9 : Interval cellTest_4608 72 80 :=
  interval_of_check cellTest_4608 72 8 (by decide +kernel)

theorem cellTest_4608_block_10 : Interval cellTest_4608 80 88 :=
  interval_of_check cellTest_4608 80 8 (by decide +kernel)

theorem cellTest_4608_block_11 : Interval cellTest_4608 88 96 :=
  interval_of_check cellTest_4608 88 8 (by decide +kernel)

theorem cellTest_4608_block_12 : Interval cellTest_4608 96 104 :=
  interval_of_check cellTest_4608 96 8 (by decide +kernel)

theorem cellTest_4608_block_13 : Interval cellTest_4608 104 112 :=
  interval_of_check cellTest_4608 104 8 (by decide +kernel)

theorem cellTest_4608_block_14 : Interval cellTest_4608 112 120 :=
  interval_of_check cellTest_4608 112 8 (by decide +kernel)

theorem cellTest_4608_block_15 : Interval cellTest_4608 120 128 :=
  interval_of_check cellTest_4608 120 8 (by decide +kernel)

theorem cellTest_4608_block_16 : Interval cellTest_4608 128 136 :=
  interval_of_check cellTest_4608 128 8 (by decide +kernel)

theorem cellTest_4608_block_17 : Interval cellTest_4608 136 144 :=
  interval_of_check cellTest_4608 136 8 (by decide +kernel)

theorem cellTest_4608_block_18 : Interval cellTest_4608 144 152 :=
  interval_of_check cellTest_4608 144 8 (by decide +kernel)

theorem cellTest_4608_block_19 : Interval cellTest_4608 152 160 :=
  interval_of_check cellTest_4608 152 8 (by decide +kernel)

theorem cellTest_4608_block_20 : Interval cellTest_4608 160 168 :=
  interval_of_check cellTest_4608 160 8 (by decide +kernel)

theorem cellTest_4608_block_21 : Interval cellTest_4608 168 176 :=
  interval_of_check cellTest_4608 168 8 (by decide +kernel)

theorem cellTest_4608_block_22 : Interval cellTest_4608 176 184 :=
  interval_of_check cellTest_4608 176 8 (by decide +kernel)

theorem cellTest_4608_block_23 : Interval cellTest_4608 184 192 :=
  interval_of_check cellTest_4608 184 8 (by decide +kernel)

theorem cellTest_4608_block_24 : Interval cellTest_4608 192 200 :=
  interval_of_check cellTest_4608 192 8 (by decide +kernel)

theorem cellTest_4608_block_25 : Interval cellTest_4608 200 208 :=
  interval_of_check cellTest_4608 200 8 (by decide +kernel)

theorem cellTest_4608_block_26 : Interval cellTest_4608 208 216 :=
  interval_of_check cellTest_4608 208 8 (by decide +kernel)

theorem cellTest_4608_block_27 : Interval cellTest_4608 216 224 :=
  interval_of_check cellTest_4608 216 8 (by decide +kernel)

theorem cellTest_4608_block_28 : Interval cellTest_4608 224 232 :=
  interval_of_check cellTest_4608 224 8 (by decide +kernel)

theorem cellTest_4608_block_29 : Interval cellTest_4608 232 240 :=
  interval_of_check cellTest_4608 232 8 (by decide +kernel)

theorem cellTest_4608_block_30 : Interval cellTest_4608 240 248 :=
  interval_of_check cellTest_4608 240 8 (by decide +kernel)

theorem cellTest_4608_block_31 : Interval cellTest_4608 248 256 :=
  interval_of_check cellTest_4608 248 8 (by decide +kernel)

theorem cellTest_4608_complete : Interval cellTest_4608 0 256 :=
  (interval_append cellTest_4608 0 128 256
  (interval_append cellTest_4608 0 64 128
  (interval_append cellTest_4608 0 32 64
  (interval_append cellTest_4608 0 16 32
  (interval_append cellTest_4608 0 8 16
  cellTest_4608_block_0
  cellTest_4608_block_1)
  (interval_append cellTest_4608 16 24 32
  cellTest_4608_block_2
  cellTest_4608_block_3))
  (interval_append cellTest_4608 32 48 64
  (interval_append cellTest_4608 32 40 48
  cellTest_4608_block_4
  cellTest_4608_block_5)
  (interval_append cellTest_4608 48 56 64
  cellTest_4608_block_6
  cellTest_4608_block_7)))
  (interval_append cellTest_4608 64 96 128
  (interval_append cellTest_4608 64 80 96
  (interval_append cellTest_4608 64 72 80
  cellTest_4608_block_8
  cellTest_4608_block_9)
  (interval_append cellTest_4608 80 88 96
  cellTest_4608_block_10
  cellTest_4608_block_11))
  (interval_append cellTest_4608 96 112 128
  (interval_append cellTest_4608 96 104 112
  cellTest_4608_block_12
  cellTest_4608_block_13)
  (interval_append cellTest_4608 112 120 128
  cellTest_4608_block_14
  cellTest_4608_block_15))))
  (interval_append cellTest_4608 128 192 256
  (interval_append cellTest_4608 128 160 192
  (interval_append cellTest_4608 128 144 160
  (interval_append cellTest_4608 128 136 144
  cellTest_4608_block_16
  cellTest_4608_block_17)
  (interval_append cellTest_4608 144 152 160
  cellTest_4608_block_18
  cellTest_4608_block_19))
  (interval_append cellTest_4608 160 176 192
  (interval_append cellTest_4608 160 168 176
  cellTest_4608_block_20
  cellTest_4608_block_21)
  (interval_append cellTest_4608 176 184 192
  cellTest_4608_block_22
  cellTest_4608_block_23)))
  (interval_append cellTest_4608 192 224 256
  (interval_append cellTest_4608 192 208 224
  (interval_append cellTest_4608 192 200 208
  cellTest_4608_block_24
  cellTest_4608_block_25)
  (interval_append cellTest_4608 208 216 224
  cellTest_4608_block_26
  cellTest_4608_block_27))
  (interval_append cellTest_4608 224 240 256
  (interval_append cellTest_4608 224 232 240
  cellTest_4608_block_28
  cellTest_4608_block_29)
  (interval_append cellTest_4608 240 248 256
  cellTest_4608_block_30
  cellTest_4608_block_31)))))
theorem cellTestInterval4608 : Interval cellTest 4608 4864 := by
  intro i hlo hhi
  have h := cellTest_4608_complete (i-4608) (Nat.zero_le _) (by omega)
  simpa only [cellTest_4608, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells019 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_4864 (i : Nat) := cellTest (i+4864)
theorem cellTest_4864_block_0 : Interval cellTest_4864 0 8 :=
  interval_of_check cellTest_4864 0 8 (by decide +kernel)

theorem cellTest_4864_block_1 : Interval cellTest_4864 8 16 :=
  interval_of_check cellTest_4864 8 8 (by decide +kernel)

theorem cellTest_4864_block_2 : Interval cellTest_4864 16 24 :=
  interval_of_check cellTest_4864 16 8 (by decide +kernel)

theorem cellTest_4864_block_3 : Interval cellTest_4864 24 32 :=
  interval_of_check cellTest_4864 24 8 (by decide +kernel)

theorem cellTest_4864_block_4 : Interval cellTest_4864 32 40 :=
  interval_of_check cellTest_4864 32 8 (by decide +kernel)

theorem cellTest_4864_block_5 : Interval cellTest_4864 40 48 :=
  interval_of_check cellTest_4864 40 8 (by decide +kernel)

theorem cellTest_4864_block_6 : Interval cellTest_4864 48 56 :=
  interval_of_check cellTest_4864 48 8 (by decide +kernel)

theorem cellTest_4864_block_7 : Interval cellTest_4864 56 64 :=
  interval_of_check cellTest_4864 56 8 (by decide +kernel)

theorem cellTest_4864_block_8 : Interval cellTest_4864 64 72 :=
  interval_of_check cellTest_4864 64 8 (by decide +kernel)

theorem cellTest_4864_block_9 : Interval cellTest_4864 72 80 :=
  interval_of_check cellTest_4864 72 8 (by decide +kernel)

theorem cellTest_4864_block_10 : Interval cellTest_4864 80 88 :=
  interval_of_check cellTest_4864 80 8 (by decide +kernel)

theorem cellTest_4864_block_11 : Interval cellTest_4864 88 96 :=
  interval_of_check cellTest_4864 88 8 (by decide +kernel)

theorem cellTest_4864_block_12 : Interval cellTest_4864 96 104 :=
  interval_of_check cellTest_4864 96 8 (by decide +kernel)

theorem cellTest_4864_block_13 : Interval cellTest_4864 104 112 :=
  interval_of_check cellTest_4864 104 8 (by decide +kernel)

theorem cellTest_4864_block_14 : Interval cellTest_4864 112 120 :=
  interval_of_check cellTest_4864 112 8 (by decide +kernel)

theorem cellTest_4864_block_15 : Interval cellTest_4864 120 128 :=
  interval_of_check cellTest_4864 120 8 (by decide +kernel)

theorem cellTest_4864_block_16 : Interval cellTest_4864 128 136 :=
  interval_of_check cellTest_4864 128 8 (by decide +kernel)

theorem cellTest_4864_block_17 : Interval cellTest_4864 136 144 :=
  interval_of_check cellTest_4864 136 8 (by decide +kernel)

theorem cellTest_4864_block_18 : Interval cellTest_4864 144 152 :=
  interval_of_check cellTest_4864 144 8 (by decide +kernel)

theorem cellTest_4864_block_19 : Interval cellTest_4864 152 160 :=
  interval_of_check cellTest_4864 152 8 (by decide +kernel)

theorem cellTest_4864_block_20 : Interval cellTest_4864 160 168 :=
  interval_of_check cellTest_4864 160 8 (by decide +kernel)

theorem cellTest_4864_block_21 : Interval cellTest_4864 168 176 :=
  interval_of_check cellTest_4864 168 8 (by decide +kernel)

theorem cellTest_4864_block_22 : Interval cellTest_4864 176 184 :=
  interval_of_check cellTest_4864 176 8 (by decide +kernel)

theorem cellTest_4864_block_23 : Interval cellTest_4864 184 192 :=
  interval_of_check cellTest_4864 184 8 (by decide +kernel)

theorem cellTest_4864_block_24 : Interval cellTest_4864 192 200 :=
  interval_of_check cellTest_4864 192 8 (by decide +kernel)

theorem cellTest_4864_block_25 : Interval cellTest_4864 200 208 :=
  interval_of_check cellTest_4864 200 8 (by decide +kernel)

theorem cellTest_4864_block_26 : Interval cellTest_4864 208 216 :=
  interval_of_check cellTest_4864 208 8 (by decide +kernel)

theorem cellTest_4864_block_27 : Interval cellTest_4864 216 224 :=
  interval_of_check cellTest_4864 216 8 (by decide +kernel)

theorem cellTest_4864_block_28 : Interval cellTest_4864 224 232 :=
  interval_of_check cellTest_4864 224 8 (by decide +kernel)

theorem cellTest_4864_block_29 : Interval cellTest_4864 232 240 :=
  interval_of_check cellTest_4864 232 8 (by decide +kernel)

theorem cellTest_4864_block_30 : Interval cellTest_4864 240 248 :=
  interval_of_check cellTest_4864 240 8 (by decide +kernel)

theorem cellTest_4864_block_31 : Interval cellTest_4864 248 256 :=
  interval_of_check cellTest_4864 248 8 (by decide +kernel)

theorem cellTest_4864_complete : Interval cellTest_4864 0 256 :=
  (interval_append cellTest_4864 0 128 256
  (interval_append cellTest_4864 0 64 128
  (interval_append cellTest_4864 0 32 64
  (interval_append cellTest_4864 0 16 32
  (interval_append cellTest_4864 0 8 16
  cellTest_4864_block_0
  cellTest_4864_block_1)
  (interval_append cellTest_4864 16 24 32
  cellTest_4864_block_2
  cellTest_4864_block_3))
  (interval_append cellTest_4864 32 48 64
  (interval_append cellTest_4864 32 40 48
  cellTest_4864_block_4
  cellTest_4864_block_5)
  (interval_append cellTest_4864 48 56 64
  cellTest_4864_block_6
  cellTest_4864_block_7)))
  (interval_append cellTest_4864 64 96 128
  (interval_append cellTest_4864 64 80 96
  (interval_append cellTest_4864 64 72 80
  cellTest_4864_block_8
  cellTest_4864_block_9)
  (interval_append cellTest_4864 80 88 96
  cellTest_4864_block_10
  cellTest_4864_block_11))
  (interval_append cellTest_4864 96 112 128
  (interval_append cellTest_4864 96 104 112
  cellTest_4864_block_12
  cellTest_4864_block_13)
  (interval_append cellTest_4864 112 120 128
  cellTest_4864_block_14
  cellTest_4864_block_15))))
  (interval_append cellTest_4864 128 192 256
  (interval_append cellTest_4864 128 160 192
  (interval_append cellTest_4864 128 144 160
  (interval_append cellTest_4864 128 136 144
  cellTest_4864_block_16
  cellTest_4864_block_17)
  (interval_append cellTest_4864 144 152 160
  cellTest_4864_block_18
  cellTest_4864_block_19))
  (interval_append cellTest_4864 160 176 192
  (interval_append cellTest_4864 160 168 176
  cellTest_4864_block_20
  cellTest_4864_block_21)
  (interval_append cellTest_4864 176 184 192
  cellTest_4864_block_22
  cellTest_4864_block_23)))
  (interval_append cellTest_4864 192 224 256
  (interval_append cellTest_4864 192 208 224
  (interval_append cellTest_4864 192 200 208
  cellTest_4864_block_24
  cellTest_4864_block_25)
  (interval_append cellTest_4864 208 216 224
  cellTest_4864_block_26
  cellTest_4864_block_27))
  (interval_append cellTest_4864 224 240 256
  (interval_append cellTest_4864 224 232 240
  cellTest_4864_block_28
  cellTest_4864_block_29)
  (interval_append cellTest_4864 240 248 256
  cellTest_4864_block_30
  cellTest_4864_block_31)))))
theorem cellTestInterval4864 : Interval cellTest 4864 5120 := by
  intro i hlo hhi
  have h := cellTest_4864_complete (i-4864) (Nat.zero_le _) (by omega)
  simpa only [cellTest_4864, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells020 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_5120 (i : Nat) := cellTest (i+5120)
theorem cellTest_5120_block_0 : Interval cellTest_5120 0 8 :=
  interval_of_check cellTest_5120 0 8 (by decide +kernel)

theorem cellTest_5120_block_1 : Interval cellTest_5120 8 16 :=
  interval_of_check cellTest_5120 8 8 (by decide +kernel)

theorem cellTest_5120_block_2 : Interval cellTest_5120 16 24 :=
  interval_of_check cellTest_5120 16 8 (by decide +kernel)

theorem cellTest_5120_block_3 : Interval cellTest_5120 24 32 :=
  interval_of_check cellTest_5120 24 8 (by decide +kernel)

theorem cellTest_5120_block_4 : Interval cellTest_5120 32 40 :=
  interval_of_check cellTest_5120 32 8 (by decide +kernel)

theorem cellTest_5120_block_5 : Interval cellTest_5120 40 48 :=
  interval_of_check cellTest_5120 40 8 (by decide +kernel)

theorem cellTest_5120_block_6 : Interval cellTest_5120 48 56 :=
  interval_of_check cellTest_5120 48 8 (by decide +kernel)

theorem cellTest_5120_block_7 : Interval cellTest_5120 56 64 :=
  interval_of_check cellTest_5120 56 8 (by decide +kernel)

theorem cellTest_5120_block_8 : Interval cellTest_5120 64 72 :=
  interval_of_check cellTest_5120 64 8 (by decide +kernel)

theorem cellTest_5120_block_9 : Interval cellTest_5120 72 80 :=
  interval_of_check cellTest_5120 72 8 (by decide +kernel)

theorem cellTest_5120_block_10 : Interval cellTest_5120 80 88 :=
  interval_of_check cellTest_5120 80 8 (by decide +kernel)

theorem cellTest_5120_block_11 : Interval cellTest_5120 88 96 :=
  interval_of_check cellTest_5120 88 8 (by decide +kernel)

theorem cellTest_5120_block_12 : Interval cellTest_5120 96 104 :=
  interval_of_check cellTest_5120 96 8 (by decide +kernel)

theorem cellTest_5120_block_13 : Interval cellTest_5120 104 112 :=
  interval_of_check cellTest_5120 104 8 (by decide +kernel)

theorem cellTest_5120_block_14 : Interval cellTest_5120 112 120 :=
  interval_of_check cellTest_5120 112 8 (by decide +kernel)

theorem cellTest_5120_block_15 : Interval cellTest_5120 120 128 :=
  interval_of_check cellTest_5120 120 8 (by decide +kernel)

theorem cellTest_5120_block_16 : Interval cellTest_5120 128 136 :=
  interval_of_check cellTest_5120 128 8 (by decide +kernel)

theorem cellTest_5120_block_17 : Interval cellTest_5120 136 144 :=
  interval_of_check cellTest_5120 136 8 (by decide +kernel)

theorem cellTest_5120_block_18 : Interval cellTest_5120 144 152 :=
  interval_of_check cellTest_5120 144 8 (by decide +kernel)

theorem cellTest_5120_block_19 : Interval cellTest_5120 152 160 :=
  interval_of_check cellTest_5120 152 8 (by decide +kernel)

theorem cellTest_5120_block_20 : Interval cellTest_5120 160 168 :=
  interval_of_check cellTest_5120 160 8 (by decide +kernel)

theorem cellTest_5120_block_21 : Interval cellTest_5120 168 176 :=
  interval_of_check cellTest_5120 168 8 (by decide +kernel)

theorem cellTest_5120_block_22 : Interval cellTest_5120 176 184 :=
  interval_of_check cellTest_5120 176 8 (by decide +kernel)

theorem cellTest_5120_block_23 : Interval cellTest_5120 184 192 :=
  interval_of_check cellTest_5120 184 8 (by decide +kernel)

theorem cellTest_5120_block_24 : Interval cellTest_5120 192 200 :=
  interval_of_check cellTest_5120 192 8 (by decide +kernel)

theorem cellTest_5120_block_25 : Interval cellTest_5120 200 208 :=
  interval_of_check cellTest_5120 200 8 (by decide +kernel)

theorem cellTest_5120_block_26 : Interval cellTest_5120 208 216 :=
  interval_of_check cellTest_5120 208 8 (by decide +kernel)

theorem cellTest_5120_block_27 : Interval cellTest_5120 216 224 :=
  interval_of_check cellTest_5120 216 8 (by decide +kernel)

theorem cellTest_5120_block_28 : Interval cellTest_5120 224 232 :=
  interval_of_check cellTest_5120 224 8 (by decide +kernel)

theorem cellTest_5120_block_29 : Interval cellTest_5120 232 240 :=
  interval_of_check cellTest_5120 232 8 (by decide +kernel)

theorem cellTest_5120_block_30 : Interval cellTest_5120 240 248 :=
  interval_of_check cellTest_5120 240 8 (by decide +kernel)

theorem cellTest_5120_block_31 : Interval cellTest_5120 248 256 :=
  interval_of_check cellTest_5120 248 8 (by decide +kernel)

theorem cellTest_5120_complete : Interval cellTest_5120 0 256 :=
  (interval_append cellTest_5120 0 128 256
  (interval_append cellTest_5120 0 64 128
  (interval_append cellTest_5120 0 32 64
  (interval_append cellTest_5120 0 16 32
  (interval_append cellTest_5120 0 8 16
  cellTest_5120_block_0
  cellTest_5120_block_1)
  (interval_append cellTest_5120 16 24 32
  cellTest_5120_block_2
  cellTest_5120_block_3))
  (interval_append cellTest_5120 32 48 64
  (interval_append cellTest_5120 32 40 48
  cellTest_5120_block_4
  cellTest_5120_block_5)
  (interval_append cellTest_5120 48 56 64
  cellTest_5120_block_6
  cellTest_5120_block_7)))
  (interval_append cellTest_5120 64 96 128
  (interval_append cellTest_5120 64 80 96
  (interval_append cellTest_5120 64 72 80
  cellTest_5120_block_8
  cellTest_5120_block_9)
  (interval_append cellTest_5120 80 88 96
  cellTest_5120_block_10
  cellTest_5120_block_11))
  (interval_append cellTest_5120 96 112 128
  (interval_append cellTest_5120 96 104 112
  cellTest_5120_block_12
  cellTest_5120_block_13)
  (interval_append cellTest_5120 112 120 128
  cellTest_5120_block_14
  cellTest_5120_block_15))))
  (interval_append cellTest_5120 128 192 256
  (interval_append cellTest_5120 128 160 192
  (interval_append cellTest_5120 128 144 160
  (interval_append cellTest_5120 128 136 144
  cellTest_5120_block_16
  cellTest_5120_block_17)
  (interval_append cellTest_5120 144 152 160
  cellTest_5120_block_18
  cellTest_5120_block_19))
  (interval_append cellTest_5120 160 176 192
  (interval_append cellTest_5120 160 168 176
  cellTest_5120_block_20
  cellTest_5120_block_21)
  (interval_append cellTest_5120 176 184 192
  cellTest_5120_block_22
  cellTest_5120_block_23)))
  (interval_append cellTest_5120 192 224 256
  (interval_append cellTest_5120 192 208 224
  (interval_append cellTest_5120 192 200 208
  cellTest_5120_block_24
  cellTest_5120_block_25)
  (interval_append cellTest_5120 208 216 224
  cellTest_5120_block_26
  cellTest_5120_block_27))
  (interval_append cellTest_5120 224 240 256
  (interval_append cellTest_5120 224 232 240
  cellTest_5120_block_28
  cellTest_5120_block_29)
  (interval_append cellTest_5120 240 248 256
  cellTest_5120_block_30
  cellTest_5120_block_31)))))
theorem cellTestInterval5120 : Interval cellTest 5120 5376 := by
  intro i hlo hhi
  have h := cellTest_5120_complete (i-5120) (Nat.zero_le _) (by omega)
  simpa only [cellTest_5120, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells021 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_5376 (i : Nat) := cellTest (i+5376)
theorem cellTest_5376_block_0 : Interval cellTest_5376 0 8 :=
  interval_of_check cellTest_5376 0 8 (by decide +kernel)

theorem cellTest_5376_block_1 : Interval cellTest_5376 8 16 :=
  interval_of_check cellTest_5376 8 8 (by decide +kernel)

theorem cellTest_5376_block_2 : Interval cellTest_5376 16 24 :=
  interval_of_check cellTest_5376 16 8 (by decide +kernel)

theorem cellTest_5376_block_3 : Interval cellTest_5376 24 32 :=
  interval_of_check cellTest_5376 24 8 (by decide +kernel)

theorem cellTest_5376_block_4 : Interval cellTest_5376 32 40 :=
  interval_of_check cellTest_5376 32 8 (by decide +kernel)

theorem cellTest_5376_block_5 : Interval cellTest_5376 40 48 :=
  interval_of_check cellTest_5376 40 8 (by decide +kernel)

theorem cellTest_5376_block_6 : Interval cellTest_5376 48 56 :=
  interval_of_check cellTest_5376 48 8 (by decide +kernel)

theorem cellTest_5376_block_7 : Interval cellTest_5376 56 64 :=
  interval_of_check cellTest_5376 56 8 (by decide +kernel)

theorem cellTest_5376_block_8 : Interval cellTest_5376 64 72 :=
  interval_of_check cellTest_5376 64 8 (by decide +kernel)

theorem cellTest_5376_block_9 : Interval cellTest_5376 72 80 :=
  interval_of_check cellTest_5376 72 8 (by decide +kernel)

theorem cellTest_5376_block_10 : Interval cellTest_5376 80 88 :=
  interval_of_check cellTest_5376 80 8 (by decide +kernel)

theorem cellTest_5376_block_11 : Interval cellTest_5376 88 96 :=
  interval_of_check cellTest_5376 88 8 (by decide +kernel)

theorem cellTest_5376_block_12 : Interval cellTest_5376 96 104 :=
  interval_of_check cellTest_5376 96 8 (by decide +kernel)

theorem cellTest_5376_block_13 : Interval cellTest_5376 104 112 :=
  interval_of_check cellTest_5376 104 8 (by decide +kernel)

theorem cellTest_5376_block_14 : Interval cellTest_5376 112 120 :=
  interval_of_check cellTest_5376 112 8 (by decide +kernel)

theorem cellTest_5376_block_15 : Interval cellTest_5376 120 128 :=
  interval_of_check cellTest_5376 120 8 (by decide +kernel)

theorem cellTest_5376_block_16 : Interval cellTest_5376 128 136 :=
  interval_of_check cellTest_5376 128 8 (by decide +kernel)

theorem cellTest_5376_block_17 : Interval cellTest_5376 136 144 :=
  interval_of_check cellTest_5376 136 8 (by decide +kernel)

theorem cellTest_5376_block_18 : Interval cellTest_5376 144 152 :=
  interval_of_check cellTest_5376 144 8 (by decide +kernel)

theorem cellTest_5376_block_19 : Interval cellTest_5376 152 160 :=
  interval_of_check cellTest_5376 152 8 (by decide +kernel)

theorem cellTest_5376_block_20 : Interval cellTest_5376 160 168 :=
  interval_of_check cellTest_5376 160 8 (by decide +kernel)

theorem cellTest_5376_block_21 : Interval cellTest_5376 168 176 :=
  interval_of_check cellTest_5376 168 8 (by decide +kernel)

theorem cellTest_5376_block_22 : Interval cellTest_5376 176 184 :=
  interval_of_check cellTest_5376 176 8 (by decide +kernel)

theorem cellTest_5376_block_23 : Interval cellTest_5376 184 192 :=
  interval_of_check cellTest_5376 184 8 (by decide +kernel)

theorem cellTest_5376_block_24 : Interval cellTest_5376 192 200 :=
  interval_of_check cellTest_5376 192 8 (by decide +kernel)

theorem cellTest_5376_block_25 : Interval cellTest_5376 200 208 :=
  interval_of_check cellTest_5376 200 8 (by decide +kernel)

theorem cellTest_5376_block_26 : Interval cellTest_5376 208 216 :=
  interval_of_check cellTest_5376 208 8 (by decide +kernel)

theorem cellTest_5376_block_27 : Interval cellTest_5376 216 224 :=
  interval_of_check cellTest_5376 216 8 (by decide +kernel)

theorem cellTest_5376_block_28 : Interval cellTest_5376 224 232 :=
  interval_of_check cellTest_5376 224 8 (by decide +kernel)

theorem cellTest_5376_block_29 : Interval cellTest_5376 232 240 :=
  interval_of_check cellTest_5376 232 8 (by decide +kernel)

theorem cellTest_5376_block_30 : Interval cellTest_5376 240 248 :=
  interval_of_check cellTest_5376 240 8 (by decide +kernel)

theorem cellTest_5376_block_31 : Interval cellTest_5376 248 256 :=
  interval_of_check cellTest_5376 248 8 (by decide +kernel)

theorem cellTest_5376_complete : Interval cellTest_5376 0 256 :=
  (interval_append cellTest_5376 0 128 256
  (interval_append cellTest_5376 0 64 128
  (interval_append cellTest_5376 0 32 64
  (interval_append cellTest_5376 0 16 32
  (interval_append cellTest_5376 0 8 16
  cellTest_5376_block_0
  cellTest_5376_block_1)
  (interval_append cellTest_5376 16 24 32
  cellTest_5376_block_2
  cellTest_5376_block_3))
  (interval_append cellTest_5376 32 48 64
  (interval_append cellTest_5376 32 40 48
  cellTest_5376_block_4
  cellTest_5376_block_5)
  (interval_append cellTest_5376 48 56 64
  cellTest_5376_block_6
  cellTest_5376_block_7)))
  (interval_append cellTest_5376 64 96 128
  (interval_append cellTest_5376 64 80 96
  (interval_append cellTest_5376 64 72 80
  cellTest_5376_block_8
  cellTest_5376_block_9)
  (interval_append cellTest_5376 80 88 96
  cellTest_5376_block_10
  cellTest_5376_block_11))
  (interval_append cellTest_5376 96 112 128
  (interval_append cellTest_5376 96 104 112
  cellTest_5376_block_12
  cellTest_5376_block_13)
  (interval_append cellTest_5376 112 120 128
  cellTest_5376_block_14
  cellTest_5376_block_15))))
  (interval_append cellTest_5376 128 192 256
  (interval_append cellTest_5376 128 160 192
  (interval_append cellTest_5376 128 144 160
  (interval_append cellTest_5376 128 136 144
  cellTest_5376_block_16
  cellTest_5376_block_17)
  (interval_append cellTest_5376 144 152 160
  cellTest_5376_block_18
  cellTest_5376_block_19))
  (interval_append cellTest_5376 160 176 192
  (interval_append cellTest_5376 160 168 176
  cellTest_5376_block_20
  cellTest_5376_block_21)
  (interval_append cellTest_5376 176 184 192
  cellTest_5376_block_22
  cellTest_5376_block_23)))
  (interval_append cellTest_5376 192 224 256
  (interval_append cellTest_5376 192 208 224
  (interval_append cellTest_5376 192 200 208
  cellTest_5376_block_24
  cellTest_5376_block_25)
  (interval_append cellTest_5376 208 216 224
  cellTest_5376_block_26
  cellTest_5376_block_27))
  (interval_append cellTest_5376 224 240 256
  (interval_append cellTest_5376 224 232 240
  cellTest_5376_block_28
  cellTest_5376_block_29)
  (interval_append cellTest_5376 240 248 256
  cellTest_5376_block_30
  cellTest_5376_block_31)))))
theorem cellTestInterval5376 : Interval cellTest 5376 5632 := by
  intro i hlo hhi
  have h := cellTest_5376_complete (i-5376) (Nat.zero_le _) (by omega)
  simpa only [cellTest_5376, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells022 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_5632 (i : Nat) := cellTest (i+5632)
theorem cellTest_5632_block_0 : Interval cellTest_5632 0 8 :=
  interval_of_check cellTest_5632 0 8 (by decide +kernel)

theorem cellTest_5632_block_1 : Interval cellTest_5632 8 16 :=
  interval_of_check cellTest_5632 8 8 (by decide +kernel)

theorem cellTest_5632_block_2 : Interval cellTest_5632 16 24 :=
  interval_of_check cellTest_5632 16 8 (by decide +kernel)

theorem cellTest_5632_block_3 : Interval cellTest_5632 24 32 :=
  interval_of_check cellTest_5632 24 8 (by decide +kernel)

theorem cellTest_5632_block_4 : Interval cellTest_5632 32 40 :=
  interval_of_check cellTest_5632 32 8 (by decide +kernel)

theorem cellTest_5632_block_5 : Interval cellTest_5632 40 48 :=
  interval_of_check cellTest_5632 40 8 (by decide +kernel)

theorem cellTest_5632_block_6 : Interval cellTest_5632 48 56 :=
  interval_of_check cellTest_5632 48 8 (by decide +kernel)

theorem cellTest_5632_block_7 : Interval cellTest_5632 56 64 :=
  interval_of_check cellTest_5632 56 8 (by decide +kernel)

theorem cellTest_5632_block_8 : Interval cellTest_5632 64 72 :=
  interval_of_check cellTest_5632 64 8 (by decide +kernel)

theorem cellTest_5632_block_9 : Interval cellTest_5632 72 80 :=
  interval_of_check cellTest_5632 72 8 (by decide +kernel)

theorem cellTest_5632_block_10 : Interval cellTest_5632 80 88 :=
  interval_of_check cellTest_5632 80 8 (by decide +kernel)

theorem cellTest_5632_block_11 : Interval cellTest_5632 88 96 :=
  interval_of_check cellTest_5632 88 8 (by decide +kernel)

theorem cellTest_5632_block_12 : Interval cellTest_5632 96 104 :=
  interval_of_check cellTest_5632 96 8 (by decide +kernel)

theorem cellTest_5632_block_13 : Interval cellTest_5632 104 112 :=
  interval_of_check cellTest_5632 104 8 (by decide +kernel)

theorem cellTest_5632_block_14 : Interval cellTest_5632 112 120 :=
  interval_of_check cellTest_5632 112 8 (by decide +kernel)

theorem cellTest_5632_block_15 : Interval cellTest_5632 120 128 :=
  interval_of_check cellTest_5632 120 8 (by decide +kernel)

theorem cellTest_5632_block_16 : Interval cellTest_5632 128 136 :=
  interval_of_check cellTest_5632 128 8 (by decide +kernel)

theorem cellTest_5632_block_17 : Interval cellTest_5632 136 144 :=
  interval_of_check cellTest_5632 136 8 (by decide +kernel)

theorem cellTest_5632_block_18 : Interval cellTest_5632 144 152 :=
  interval_of_check cellTest_5632 144 8 (by decide +kernel)

theorem cellTest_5632_block_19 : Interval cellTest_5632 152 160 :=
  interval_of_check cellTest_5632 152 8 (by decide +kernel)

theorem cellTest_5632_block_20 : Interval cellTest_5632 160 168 :=
  interval_of_check cellTest_5632 160 8 (by decide +kernel)

theorem cellTest_5632_block_21 : Interval cellTest_5632 168 176 :=
  interval_of_check cellTest_5632 168 8 (by decide +kernel)

theorem cellTest_5632_block_22 : Interval cellTest_5632 176 184 :=
  interval_of_check cellTest_5632 176 8 (by decide +kernel)

theorem cellTest_5632_block_23 : Interval cellTest_5632 184 192 :=
  interval_of_check cellTest_5632 184 8 (by decide +kernel)

theorem cellTest_5632_block_24 : Interval cellTest_5632 192 200 :=
  interval_of_check cellTest_5632 192 8 (by decide +kernel)

theorem cellTest_5632_block_25 : Interval cellTest_5632 200 208 :=
  interval_of_check cellTest_5632 200 8 (by decide +kernel)

theorem cellTest_5632_block_26 : Interval cellTest_5632 208 216 :=
  interval_of_check cellTest_5632 208 8 (by decide +kernel)

theorem cellTest_5632_block_27 : Interval cellTest_5632 216 224 :=
  interval_of_check cellTest_5632 216 8 (by decide +kernel)

theorem cellTest_5632_block_28 : Interval cellTest_5632 224 232 :=
  interval_of_check cellTest_5632 224 8 (by decide +kernel)

theorem cellTest_5632_block_29 : Interval cellTest_5632 232 240 :=
  interval_of_check cellTest_5632 232 8 (by decide +kernel)

theorem cellTest_5632_block_30 : Interval cellTest_5632 240 248 :=
  interval_of_check cellTest_5632 240 8 (by decide +kernel)

theorem cellTest_5632_block_31 : Interval cellTest_5632 248 256 :=
  interval_of_check cellTest_5632 248 8 (by decide +kernel)

theorem cellTest_5632_complete : Interval cellTest_5632 0 256 :=
  (interval_append cellTest_5632 0 128 256
  (interval_append cellTest_5632 0 64 128
  (interval_append cellTest_5632 0 32 64
  (interval_append cellTest_5632 0 16 32
  (interval_append cellTest_5632 0 8 16
  cellTest_5632_block_0
  cellTest_5632_block_1)
  (interval_append cellTest_5632 16 24 32
  cellTest_5632_block_2
  cellTest_5632_block_3))
  (interval_append cellTest_5632 32 48 64
  (interval_append cellTest_5632 32 40 48
  cellTest_5632_block_4
  cellTest_5632_block_5)
  (interval_append cellTest_5632 48 56 64
  cellTest_5632_block_6
  cellTest_5632_block_7)))
  (interval_append cellTest_5632 64 96 128
  (interval_append cellTest_5632 64 80 96
  (interval_append cellTest_5632 64 72 80
  cellTest_5632_block_8
  cellTest_5632_block_9)
  (interval_append cellTest_5632 80 88 96
  cellTest_5632_block_10
  cellTest_5632_block_11))
  (interval_append cellTest_5632 96 112 128
  (interval_append cellTest_5632 96 104 112
  cellTest_5632_block_12
  cellTest_5632_block_13)
  (interval_append cellTest_5632 112 120 128
  cellTest_5632_block_14
  cellTest_5632_block_15))))
  (interval_append cellTest_5632 128 192 256
  (interval_append cellTest_5632 128 160 192
  (interval_append cellTest_5632 128 144 160
  (interval_append cellTest_5632 128 136 144
  cellTest_5632_block_16
  cellTest_5632_block_17)
  (interval_append cellTest_5632 144 152 160
  cellTest_5632_block_18
  cellTest_5632_block_19))
  (interval_append cellTest_5632 160 176 192
  (interval_append cellTest_5632 160 168 176
  cellTest_5632_block_20
  cellTest_5632_block_21)
  (interval_append cellTest_5632 176 184 192
  cellTest_5632_block_22
  cellTest_5632_block_23)))
  (interval_append cellTest_5632 192 224 256
  (interval_append cellTest_5632 192 208 224
  (interval_append cellTest_5632 192 200 208
  cellTest_5632_block_24
  cellTest_5632_block_25)
  (interval_append cellTest_5632 208 216 224
  cellTest_5632_block_26
  cellTest_5632_block_27))
  (interval_append cellTest_5632 224 240 256
  (interval_append cellTest_5632 224 232 240
  cellTest_5632_block_28
  cellTest_5632_block_29)
  (interval_append cellTest_5632 240 248 256
  cellTest_5632_block_30
  cellTest_5632_block_31)))))
theorem cellTestInterval5632 : Interval cellTest 5632 5888 := by
  intro i hlo hhi
  have h := cellTest_5632_complete (i-5632) (Nat.zero_le _) (by omega)
  simpa only [cellTest_5632, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells023 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_5888 (i : Nat) := cellTest (i+5888)
theorem cellTest_5888_block_0 : Interval cellTest_5888 0 8 :=
  interval_of_check cellTest_5888 0 8 (by decide +kernel)

theorem cellTest_5888_block_1 : Interval cellTest_5888 8 16 :=
  interval_of_check cellTest_5888 8 8 (by decide +kernel)

theorem cellTest_5888_block_2 : Interval cellTest_5888 16 24 :=
  interval_of_check cellTest_5888 16 8 (by decide +kernel)

theorem cellTest_5888_block_3 : Interval cellTest_5888 24 32 :=
  interval_of_check cellTest_5888 24 8 (by decide +kernel)

theorem cellTest_5888_block_4 : Interval cellTest_5888 32 40 :=
  interval_of_check cellTest_5888 32 8 (by decide +kernel)

theorem cellTest_5888_block_5 : Interval cellTest_5888 40 48 :=
  interval_of_check cellTest_5888 40 8 (by decide +kernel)

theorem cellTest_5888_block_6 : Interval cellTest_5888 48 56 :=
  interval_of_check cellTest_5888 48 8 (by decide +kernel)

theorem cellTest_5888_block_7 : Interval cellTest_5888 56 64 :=
  interval_of_check cellTest_5888 56 8 (by decide +kernel)

theorem cellTest_5888_block_8 : Interval cellTest_5888 64 72 :=
  interval_of_check cellTest_5888 64 8 (by decide +kernel)

theorem cellTest_5888_block_9 : Interval cellTest_5888 72 80 :=
  interval_of_check cellTest_5888 72 8 (by decide +kernel)

theorem cellTest_5888_block_10 : Interval cellTest_5888 80 88 :=
  interval_of_check cellTest_5888 80 8 (by decide +kernel)

theorem cellTest_5888_block_11 : Interval cellTest_5888 88 96 :=
  interval_of_check cellTest_5888 88 8 (by decide +kernel)

theorem cellTest_5888_block_12 : Interval cellTest_5888 96 104 :=
  interval_of_check cellTest_5888 96 8 (by decide +kernel)

theorem cellTest_5888_block_13 : Interval cellTest_5888 104 112 :=
  interval_of_check cellTest_5888 104 8 (by decide +kernel)

theorem cellTest_5888_block_14 : Interval cellTest_5888 112 120 :=
  interval_of_check cellTest_5888 112 8 (by decide +kernel)

theorem cellTest_5888_block_15 : Interval cellTest_5888 120 128 :=
  interval_of_check cellTest_5888 120 8 (by decide +kernel)

theorem cellTest_5888_block_16 : Interval cellTest_5888 128 136 :=
  interval_of_check cellTest_5888 128 8 (by decide +kernel)

theorem cellTest_5888_block_17 : Interval cellTest_5888 136 144 :=
  interval_of_check cellTest_5888 136 8 (by decide +kernel)

theorem cellTest_5888_block_18 : Interval cellTest_5888 144 152 :=
  interval_of_check cellTest_5888 144 8 (by decide +kernel)

theorem cellTest_5888_block_19 : Interval cellTest_5888 152 160 :=
  interval_of_check cellTest_5888 152 8 (by decide +kernel)

theorem cellTest_5888_block_20 : Interval cellTest_5888 160 168 :=
  interval_of_check cellTest_5888 160 8 (by decide +kernel)

theorem cellTest_5888_block_21 : Interval cellTest_5888 168 176 :=
  interval_of_check cellTest_5888 168 8 (by decide +kernel)

theorem cellTest_5888_block_22 : Interval cellTest_5888 176 184 :=
  interval_of_check cellTest_5888 176 8 (by decide +kernel)

theorem cellTest_5888_block_23 : Interval cellTest_5888 184 192 :=
  interval_of_check cellTest_5888 184 8 (by decide +kernel)

theorem cellTest_5888_block_24 : Interval cellTest_5888 192 200 :=
  interval_of_check cellTest_5888 192 8 (by decide +kernel)

theorem cellTest_5888_block_25 : Interval cellTest_5888 200 208 :=
  interval_of_check cellTest_5888 200 8 (by decide +kernel)

theorem cellTest_5888_block_26 : Interval cellTest_5888 208 216 :=
  interval_of_check cellTest_5888 208 8 (by decide +kernel)

theorem cellTest_5888_block_27 : Interval cellTest_5888 216 224 :=
  interval_of_check cellTest_5888 216 8 (by decide +kernel)

theorem cellTest_5888_block_28 : Interval cellTest_5888 224 232 :=
  interval_of_check cellTest_5888 224 8 (by decide +kernel)

theorem cellTest_5888_block_29 : Interval cellTest_5888 232 240 :=
  interval_of_check cellTest_5888 232 8 (by decide +kernel)

theorem cellTest_5888_block_30 : Interval cellTest_5888 240 248 :=
  interval_of_check cellTest_5888 240 8 (by decide +kernel)

theorem cellTest_5888_block_31 : Interval cellTest_5888 248 256 :=
  interval_of_check cellTest_5888 248 8 (by decide +kernel)

theorem cellTest_5888_complete : Interval cellTest_5888 0 256 :=
  (interval_append cellTest_5888 0 128 256
  (interval_append cellTest_5888 0 64 128
  (interval_append cellTest_5888 0 32 64
  (interval_append cellTest_5888 0 16 32
  (interval_append cellTest_5888 0 8 16
  cellTest_5888_block_0
  cellTest_5888_block_1)
  (interval_append cellTest_5888 16 24 32
  cellTest_5888_block_2
  cellTest_5888_block_3))
  (interval_append cellTest_5888 32 48 64
  (interval_append cellTest_5888 32 40 48
  cellTest_5888_block_4
  cellTest_5888_block_5)
  (interval_append cellTest_5888 48 56 64
  cellTest_5888_block_6
  cellTest_5888_block_7)))
  (interval_append cellTest_5888 64 96 128
  (interval_append cellTest_5888 64 80 96
  (interval_append cellTest_5888 64 72 80
  cellTest_5888_block_8
  cellTest_5888_block_9)
  (interval_append cellTest_5888 80 88 96
  cellTest_5888_block_10
  cellTest_5888_block_11))
  (interval_append cellTest_5888 96 112 128
  (interval_append cellTest_5888 96 104 112
  cellTest_5888_block_12
  cellTest_5888_block_13)
  (interval_append cellTest_5888 112 120 128
  cellTest_5888_block_14
  cellTest_5888_block_15))))
  (interval_append cellTest_5888 128 192 256
  (interval_append cellTest_5888 128 160 192
  (interval_append cellTest_5888 128 144 160
  (interval_append cellTest_5888 128 136 144
  cellTest_5888_block_16
  cellTest_5888_block_17)
  (interval_append cellTest_5888 144 152 160
  cellTest_5888_block_18
  cellTest_5888_block_19))
  (interval_append cellTest_5888 160 176 192
  (interval_append cellTest_5888 160 168 176
  cellTest_5888_block_20
  cellTest_5888_block_21)
  (interval_append cellTest_5888 176 184 192
  cellTest_5888_block_22
  cellTest_5888_block_23)))
  (interval_append cellTest_5888 192 224 256
  (interval_append cellTest_5888 192 208 224
  (interval_append cellTest_5888 192 200 208
  cellTest_5888_block_24
  cellTest_5888_block_25)
  (interval_append cellTest_5888 208 216 224
  cellTest_5888_block_26
  cellTest_5888_block_27))
  (interval_append cellTest_5888 224 240 256
  (interval_append cellTest_5888 224 232 240
  cellTest_5888_block_28
  cellTest_5888_block_29)
  (interval_append cellTest_5888 240 248 256
  cellTest_5888_block_30
  cellTest_5888_block_31)))))
theorem cellTestInterval5888 : Interval cellTest 5888 6144 := by
  intro i hlo hhi
  have h := cellTest_5888_complete (i-5888) (Nat.zero_le _) (by omega)
  simpa only [cellTest_5888, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells024 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_6144 (i : Nat) := cellTest (i+6144)
theorem cellTest_6144_block_0 : Interval cellTest_6144 0 8 :=
  interval_of_check cellTest_6144 0 8 (by decide +kernel)

theorem cellTest_6144_block_1 : Interval cellTest_6144 8 16 :=
  interval_of_check cellTest_6144 8 8 (by decide +kernel)

theorem cellTest_6144_block_2 : Interval cellTest_6144 16 24 :=
  interval_of_check cellTest_6144 16 8 (by decide +kernel)

theorem cellTest_6144_block_3 : Interval cellTest_6144 24 32 :=
  interval_of_check cellTest_6144 24 8 (by decide +kernel)

theorem cellTest_6144_block_4 : Interval cellTest_6144 32 40 :=
  interval_of_check cellTest_6144 32 8 (by decide +kernel)

theorem cellTest_6144_block_5 : Interval cellTest_6144 40 48 :=
  interval_of_check cellTest_6144 40 8 (by decide +kernel)

theorem cellTest_6144_block_6 : Interval cellTest_6144 48 56 :=
  interval_of_check cellTest_6144 48 8 (by decide +kernel)

theorem cellTest_6144_block_7 : Interval cellTest_6144 56 64 :=
  interval_of_check cellTest_6144 56 8 (by decide +kernel)

theorem cellTest_6144_block_8 : Interval cellTest_6144 64 72 :=
  interval_of_check cellTest_6144 64 8 (by decide +kernel)

theorem cellTest_6144_block_9 : Interval cellTest_6144 72 80 :=
  interval_of_check cellTest_6144 72 8 (by decide +kernel)

theorem cellTest_6144_block_10 : Interval cellTest_6144 80 88 :=
  interval_of_check cellTest_6144 80 8 (by decide +kernel)

theorem cellTest_6144_block_11 : Interval cellTest_6144 88 96 :=
  interval_of_check cellTest_6144 88 8 (by decide +kernel)

theorem cellTest_6144_block_12 : Interval cellTest_6144 96 104 :=
  interval_of_check cellTest_6144 96 8 (by decide +kernel)

theorem cellTest_6144_block_13 : Interval cellTest_6144 104 112 :=
  interval_of_check cellTest_6144 104 8 (by decide +kernel)

theorem cellTest_6144_block_14 : Interval cellTest_6144 112 120 :=
  interval_of_check cellTest_6144 112 8 (by decide +kernel)

theorem cellTest_6144_block_15 : Interval cellTest_6144 120 128 :=
  interval_of_check cellTest_6144 120 8 (by decide +kernel)

theorem cellTest_6144_block_16 : Interval cellTest_6144 128 136 :=
  interval_of_check cellTest_6144 128 8 (by decide +kernel)

theorem cellTest_6144_block_17 : Interval cellTest_6144 136 144 :=
  interval_of_check cellTest_6144 136 8 (by decide +kernel)

theorem cellTest_6144_block_18 : Interval cellTest_6144 144 152 :=
  interval_of_check cellTest_6144 144 8 (by decide +kernel)

theorem cellTest_6144_block_19 : Interval cellTest_6144 152 160 :=
  interval_of_check cellTest_6144 152 8 (by decide +kernel)

theorem cellTest_6144_block_20 : Interval cellTest_6144 160 168 :=
  interval_of_check cellTest_6144 160 8 (by decide +kernel)

theorem cellTest_6144_block_21 : Interval cellTest_6144 168 176 :=
  interval_of_check cellTest_6144 168 8 (by decide +kernel)

theorem cellTest_6144_block_22 : Interval cellTest_6144 176 184 :=
  interval_of_check cellTest_6144 176 8 (by decide +kernel)

theorem cellTest_6144_block_23 : Interval cellTest_6144 184 192 :=
  interval_of_check cellTest_6144 184 8 (by decide +kernel)

theorem cellTest_6144_block_24 : Interval cellTest_6144 192 200 :=
  interval_of_check cellTest_6144 192 8 (by decide +kernel)

theorem cellTest_6144_block_25 : Interval cellTest_6144 200 208 :=
  interval_of_check cellTest_6144 200 8 (by decide +kernel)

theorem cellTest_6144_block_26 : Interval cellTest_6144 208 216 :=
  interval_of_check cellTest_6144 208 8 (by decide +kernel)

theorem cellTest_6144_block_27 : Interval cellTest_6144 216 224 :=
  interval_of_check cellTest_6144 216 8 (by decide +kernel)

theorem cellTest_6144_block_28 : Interval cellTest_6144 224 232 :=
  interval_of_check cellTest_6144 224 8 (by decide +kernel)

theorem cellTest_6144_block_29 : Interval cellTest_6144 232 240 :=
  interval_of_check cellTest_6144 232 8 (by decide +kernel)

theorem cellTest_6144_block_30 : Interval cellTest_6144 240 248 :=
  interval_of_check cellTest_6144 240 8 (by decide +kernel)

theorem cellTest_6144_block_31 : Interval cellTest_6144 248 256 :=
  interval_of_check cellTest_6144 248 8 (by decide +kernel)

theorem cellTest_6144_complete : Interval cellTest_6144 0 256 :=
  (interval_append cellTest_6144 0 128 256
  (interval_append cellTest_6144 0 64 128
  (interval_append cellTest_6144 0 32 64
  (interval_append cellTest_6144 0 16 32
  (interval_append cellTest_6144 0 8 16
  cellTest_6144_block_0
  cellTest_6144_block_1)
  (interval_append cellTest_6144 16 24 32
  cellTest_6144_block_2
  cellTest_6144_block_3))
  (interval_append cellTest_6144 32 48 64
  (interval_append cellTest_6144 32 40 48
  cellTest_6144_block_4
  cellTest_6144_block_5)
  (interval_append cellTest_6144 48 56 64
  cellTest_6144_block_6
  cellTest_6144_block_7)))
  (interval_append cellTest_6144 64 96 128
  (interval_append cellTest_6144 64 80 96
  (interval_append cellTest_6144 64 72 80
  cellTest_6144_block_8
  cellTest_6144_block_9)
  (interval_append cellTest_6144 80 88 96
  cellTest_6144_block_10
  cellTest_6144_block_11))
  (interval_append cellTest_6144 96 112 128
  (interval_append cellTest_6144 96 104 112
  cellTest_6144_block_12
  cellTest_6144_block_13)
  (interval_append cellTest_6144 112 120 128
  cellTest_6144_block_14
  cellTest_6144_block_15))))
  (interval_append cellTest_6144 128 192 256
  (interval_append cellTest_6144 128 160 192
  (interval_append cellTest_6144 128 144 160
  (interval_append cellTest_6144 128 136 144
  cellTest_6144_block_16
  cellTest_6144_block_17)
  (interval_append cellTest_6144 144 152 160
  cellTest_6144_block_18
  cellTest_6144_block_19))
  (interval_append cellTest_6144 160 176 192
  (interval_append cellTest_6144 160 168 176
  cellTest_6144_block_20
  cellTest_6144_block_21)
  (interval_append cellTest_6144 176 184 192
  cellTest_6144_block_22
  cellTest_6144_block_23)))
  (interval_append cellTest_6144 192 224 256
  (interval_append cellTest_6144 192 208 224
  (interval_append cellTest_6144 192 200 208
  cellTest_6144_block_24
  cellTest_6144_block_25)
  (interval_append cellTest_6144 208 216 224
  cellTest_6144_block_26
  cellTest_6144_block_27))
  (interval_append cellTest_6144 224 240 256
  (interval_append cellTest_6144 224 232 240
  cellTest_6144_block_28
  cellTest_6144_block_29)
  (interval_append cellTest_6144 240 248 256
  cellTest_6144_block_30
  cellTest_6144_block_31)))))
theorem cellTestInterval6144 : Interval cellTest 6144 6400 := by
  intro i hlo hhi
  have h := cellTest_6144_complete (i-6144) (Nat.zero_le _) (by omega)
  simpa only [cellTest_6144, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells025 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_6400 (i : Nat) := cellTest (i+6400)
theorem cellTest_6400_block_0 : Interval cellTest_6400 0 8 :=
  interval_of_check cellTest_6400 0 8 (by decide +kernel)

theorem cellTest_6400_block_1 : Interval cellTest_6400 8 16 :=
  interval_of_check cellTest_6400 8 8 (by decide +kernel)

theorem cellTest_6400_block_2 : Interval cellTest_6400 16 24 :=
  interval_of_check cellTest_6400 16 8 (by decide +kernel)

theorem cellTest_6400_block_3 : Interval cellTest_6400 24 32 :=
  interval_of_check cellTest_6400 24 8 (by decide +kernel)

theorem cellTest_6400_block_4 : Interval cellTest_6400 32 40 :=
  interval_of_check cellTest_6400 32 8 (by decide +kernel)

theorem cellTest_6400_block_5 : Interval cellTest_6400 40 48 :=
  interval_of_check cellTest_6400 40 8 (by decide +kernel)

theorem cellTest_6400_block_6 : Interval cellTest_6400 48 56 :=
  interval_of_check cellTest_6400 48 8 (by decide +kernel)

theorem cellTest_6400_block_7 : Interval cellTest_6400 56 64 :=
  interval_of_check cellTest_6400 56 8 (by decide +kernel)

theorem cellTest_6400_block_8 : Interval cellTest_6400 64 72 :=
  interval_of_check cellTest_6400 64 8 (by decide +kernel)

theorem cellTest_6400_block_9 : Interval cellTest_6400 72 80 :=
  interval_of_check cellTest_6400 72 8 (by decide +kernel)

theorem cellTest_6400_block_10 : Interval cellTest_6400 80 88 :=
  interval_of_check cellTest_6400 80 8 (by decide +kernel)

theorem cellTest_6400_block_11 : Interval cellTest_6400 88 96 :=
  interval_of_check cellTest_6400 88 8 (by decide +kernel)

theorem cellTest_6400_block_12 : Interval cellTest_6400 96 104 :=
  interval_of_check cellTest_6400 96 8 (by decide +kernel)

theorem cellTest_6400_block_13 : Interval cellTest_6400 104 112 :=
  interval_of_check cellTest_6400 104 8 (by decide +kernel)

theorem cellTest_6400_block_14 : Interval cellTest_6400 112 120 :=
  interval_of_check cellTest_6400 112 8 (by decide +kernel)

theorem cellTest_6400_block_15 : Interval cellTest_6400 120 128 :=
  interval_of_check cellTest_6400 120 8 (by decide +kernel)

theorem cellTest_6400_block_16 : Interval cellTest_6400 128 136 :=
  interval_of_check cellTest_6400 128 8 (by decide +kernel)

theorem cellTest_6400_block_17 : Interval cellTest_6400 136 144 :=
  interval_of_check cellTest_6400 136 8 (by decide +kernel)

theorem cellTest_6400_block_18 : Interval cellTest_6400 144 152 :=
  interval_of_check cellTest_6400 144 8 (by decide +kernel)

theorem cellTest_6400_block_19 : Interval cellTest_6400 152 160 :=
  interval_of_check cellTest_6400 152 8 (by decide +kernel)

theorem cellTest_6400_block_20 : Interval cellTest_6400 160 168 :=
  interval_of_check cellTest_6400 160 8 (by decide +kernel)

theorem cellTest_6400_block_21 : Interval cellTest_6400 168 176 :=
  interval_of_check cellTest_6400 168 8 (by decide +kernel)

theorem cellTest_6400_block_22 : Interval cellTest_6400 176 184 :=
  interval_of_check cellTest_6400 176 8 (by decide +kernel)

theorem cellTest_6400_block_23 : Interval cellTest_6400 184 192 :=
  interval_of_check cellTest_6400 184 8 (by decide +kernel)

theorem cellTest_6400_block_24 : Interval cellTest_6400 192 200 :=
  interval_of_check cellTest_6400 192 8 (by decide +kernel)

theorem cellTest_6400_block_25 : Interval cellTest_6400 200 208 :=
  interval_of_check cellTest_6400 200 8 (by decide +kernel)

theorem cellTest_6400_block_26 : Interval cellTest_6400 208 216 :=
  interval_of_check cellTest_6400 208 8 (by decide +kernel)

theorem cellTest_6400_block_27 : Interval cellTest_6400 216 220 :=
  interval_of_check cellTest_6400 216 4 (by decide +kernel)

theorem cellTest_6400_complete : Interval cellTest_6400 0 220 :=
  (interval_append cellTest_6400 0 112 220
  (interval_append cellTest_6400 0 56 112
  (interval_append cellTest_6400 0 24 56
  (interval_append cellTest_6400 0 8 24
  cellTest_6400_block_0
  (interval_append cellTest_6400 8 16 24
  cellTest_6400_block_1
  cellTest_6400_block_2))
  (interval_append cellTest_6400 24 40 56
  (interval_append cellTest_6400 24 32 40
  cellTest_6400_block_3
  cellTest_6400_block_4)
  (interval_append cellTest_6400 40 48 56
  cellTest_6400_block_5
  cellTest_6400_block_6)))
  (interval_append cellTest_6400 56 80 112
  (interval_append cellTest_6400 56 64 80
  cellTest_6400_block_7
  (interval_append cellTest_6400 64 72 80
  cellTest_6400_block_8
  cellTest_6400_block_9))
  (interval_append cellTest_6400 80 96 112
  (interval_append cellTest_6400 80 88 96
  cellTest_6400_block_10
  cellTest_6400_block_11)
  (interval_append cellTest_6400 96 104 112
  cellTest_6400_block_12
  cellTest_6400_block_13))))
  (interval_append cellTest_6400 112 168 220
  (interval_append cellTest_6400 112 136 168
  (interval_append cellTest_6400 112 120 136
  cellTest_6400_block_14
  (interval_append cellTest_6400 120 128 136
  cellTest_6400_block_15
  cellTest_6400_block_16))
  (interval_append cellTest_6400 136 152 168
  (interval_append cellTest_6400 136 144 152
  cellTest_6400_block_17
  cellTest_6400_block_18)
  (interval_append cellTest_6400 152 160 168
  cellTest_6400_block_19
  cellTest_6400_block_20)))
  (interval_append cellTest_6400 168 192 220
  (interval_append cellTest_6400 168 176 192
  cellTest_6400_block_21
  (interval_append cellTest_6400 176 184 192
  cellTest_6400_block_22
  cellTest_6400_block_23))
  (interval_append cellTest_6400 192 208 220
  (interval_append cellTest_6400 192 200 208
  cellTest_6400_block_24
  cellTest_6400_block_25)
  (interval_append cellTest_6400 208 216 220
  cellTest_6400_block_26
  cellTest_6400_block_27)))))
theorem cellTestInterval6400 : Interval cellTest 6400 6620 := by
  intro i hlo hhi
  have h := cellTest_6400_complete (i-6400) (Nat.zero_le _) (by omega)
  simpa only [cellTest_6400, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_1024 (i : Nat) := badTest (i+1024)
theorem badTest_1024_block_0 : Interval badTest_1024 0 8 :=
  interval_of_check badTest_1024 0 8 (by decide +kernel)

theorem badTest_1024_block_1 : Interval badTest_1024 8 16 :=
  interval_of_check badTest_1024 8 8 (by decide +kernel)

theorem badTest_1024_block_2 : Interval badTest_1024 16 24 :=
  interval_of_check badTest_1024 16 8 (by decide +kernel)

theorem badTest_1024_block_3 : Interval badTest_1024 24 32 :=
  interval_of_check badTest_1024 24 8 (by decide +kernel)

theorem badTest_1024_block_4 : Interval badTest_1024 32 40 :=
  interval_of_check badTest_1024 32 8 (by decide +kernel)

theorem badTest_1024_block_5 : Interval badTest_1024 40 48 :=
  interval_of_check badTest_1024 40 8 (by decide +kernel)

theorem badTest_1024_block_6 : Interval badTest_1024 48 56 :=
  interval_of_check badTest_1024 48 8 (by decide +kernel)

theorem badTest_1024_block_7 : Interval badTest_1024 56 64 :=
  interval_of_check badTest_1024 56 8 (by decide +kernel)

theorem badTest_1024_block_8 : Interval badTest_1024 64 72 :=
  interval_of_check badTest_1024 64 8 (by decide +kernel)

theorem badTest_1024_block_9 : Interval badTest_1024 72 80 :=
  interval_of_check badTest_1024 72 8 (by decide +kernel)

theorem badTest_1024_block_10 : Interval badTest_1024 80 88 :=
  interval_of_check badTest_1024 80 8 (by decide +kernel)

theorem badTest_1024_block_11 : Interval badTest_1024 88 96 :=
  interval_of_check badTest_1024 88 8 (by decide +kernel)

theorem badTest_1024_block_12 : Interval badTest_1024 96 104 :=
  interval_of_check badTest_1024 96 8 (by decide +kernel)

theorem badTest_1024_block_13 : Interval badTest_1024 104 112 :=
  interval_of_check badTest_1024 104 8 (by decide +kernel)

theorem badTest_1024_block_14 : Interval badTest_1024 112 120 :=
  interval_of_check badTest_1024 112 8 (by decide +kernel)

theorem badTest_1024_block_15 : Interval badTest_1024 120 128 :=
  interval_of_check badTest_1024 120 8 (by decide +kernel)

theorem badTest_1024_block_16 : Interval badTest_1024 128 136 :=
  interval_of_check badTest_1024 128 8 (by decide +kernel)

theorem badTest_1024_block_17 : Interval badTest_1024 136 144 :=
  interval_of_check badTest_1024 136 8 (by decide +kernel)

theorem badTest_1024_block_18 : Interval badTest_1024 144 152 :=
  interval_of_check badTest_1024 144 8 (by decide +kernel)

theorem badTest_1024_block_19 : Interval badTest_1024 152 160 :=
  interval_of_check badTest_1024 152 8 (by decide +kernel)

theorem badTest_1024_block_20 : Interval badTest_1024 160 168 :=
  interval_of_check badTest_1024 160 8 (by decide +kernel)

theorem badTest_1024_block_21 : Interval badTest_1024 168 176 :=
  interval_of_check badTest_1024 168 8 (by decide +kernel)

theorem badTest_1024_block_22 : Interval badTest_1024 176 184 :=
  interval_of_check badTest_1024 176 8 (by decide +kernel)

theorem badTest_1024_block_23 : Interval badTest_1024 184 192 :=
  interval_of_check badTest_1024 184 8 (by decide +kernel)

theorem badTest_1024_block_24 : Interval badTest_1024 192 200 :=
  interval_of_check badTest_1024 192 8 (by decide +kernel)

theorem badTest_1024_block_25 : Interval badTest_1024 200 208 :=
  interval_of_check badTest_1024 200 8 (by decide +kernel)

theorem badTest_1024_block_26 : Interval badTest_1024 208 216 :=
  interval_of_check badTest_1024 208 8 (by decide +kernel)

theorem badTest_1024_block_27 : Interval badTest_1024 216 224 :=
  interval_of_check badTest_1024 216 8 (by decide +kernel)

theorem badTest_1024_block_28 : Interval badTest_1024 224 232 :=
  interval_of_check badTest_1024 224 8 (by decide +kernel)

theorem badTest_1024_block_29 : Interval badTest_1024 232 240 :=
  interval_of_check badTest_1024 232 8 (by decide +kernel)

theorem badTest_1024_block_30 : Interval badTest_1024 240 248 :=
  interval_of_check badTest_1024 240 8 (by decide +kernel)

theorem badTest_1024_block_31 : Interval badTest_1024 248 256 :=
  interval_of_check badTest_1024 248 8 (by decide +kernel)

theorem badTest_1024_complete : Interval badTest_1024 0 256 :=
  (interval_append badTest_1024 0 128 256
  (interval_append badTest_1024 0 64 128
  (interval_append badTest_1024 0 32 64
  (interval_append badTest_1024 0 16 32
  (interval_append badTest_1024 0 8 16
  badTest_1024_block_0
  badTest_1024_block_1)
  (interval_append badTest_1024 16 24 32
  badTest_1024_block_2
  badTest_1024_block_3))
  (interval_append badTest_1024 32 48 64
  (interval_append badTest_1024 32 40 48
  badTest_1024_block_4
  badTest_1024_block_5)
  (interval_append badTest_1024 48 56 64
  badTest_1024_block_6
  badTest_1024_block_7)))
  (interval_append badTest_1024 64 96 128
  (interval_append badTest_1024 64 80 96
  (interval_append badTest_1024 64 72 80
  badTest_1024_block_8
  badTest_1024_block_9)
  (interval_append badTest_1024 80 88 96
  badTest_1024_block_10
  badTest_1024_block_11))
  (interval_append badTest_1024 96 112 128
  (interval_append badTest_1024 96 104 112
  badTest_1024_block_12
  badTest_1024_block_13)
  (interval_append badTest_1024 112 120 128
  badTest_1024_block_14
  badTest_1024_block_15))))
  (interval_append badTest_1024 128 192 256
  (interval_append badTest_1024 128 160 192
  (interval_append badTest_1024 128 144 160
  (interval_append badTest_1024 128 136 144
  badTest_1024_block_16
  badTest_1024_block_17)
  (interval_append badTest_1024 144 152 160
  badTest_1024_block_18
  badTest_1024_block_19))
  (interval_append badTest_1024 160 176 192
  (interval_append badTest_1024 160 168 176
  badTest_1024_block_20
  badTest_1024_block_21)
  (interval_append badTest_1024 176 184 192
  badTest_1024_block_22
  badTest_1024_block_23)))
  (interval_append badTest_1024 192 224 256
  (interval_append badTest_1024 192 208 224
  (interval_append badTest_1024 192 200 208
  badTest_1024_block_24
  badTest_1024_block_25)
  (interval_append badTest_1024 208 216 224
  badTest_1024_block_26
  badTest_1024_block_27))
  (interval_append badTest_1024 224 240 256
  (interval_append badTest_1024 224 232 240
  badTest_1024_block_28
  badTest_1024_block_29)
  (interval_append badTest_1024 240 248 256
  badTest_1024_block_30
  badTest_1024_block_31)))))
theorem badTestInterval1024 : Interval badTest 1024 1280 := by
  intro i hlo hhi
  have h := badTest_1024_complete (i-1024) (Nat.zero_le _) (by omega)
  simpa only [badTest_1024, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_1280 (i : Nat) := badTest (i+1280)
theorem badTest_1280_block_0 : Interval badTest_1280 0 8 :=
  interval_of_check badTest_1280 0 8 (by decide +kernel)

theorem badTest_1280_block_1 : Interval badTest_1280 8 16 :=
  interval_of_check badTest_1280 8 8 (by decide +kernel)

theorem badTest_1280_block_2 : Interval badTest_1280 16 24 :=
  interval_of_check badTest_1280 16 8 (by decide +kernel)

theorem badTest_1280_block_3 : Interval badTest_1280 24 32 :=
  interval_of_check badTest_1280 24 8 (by decide +kernel)

theorem badTest_1280_block_4 : Interval badTest_1280 32 40 :=
  interval_of_check badTest_1280 32 8 (by decide +kernel)

theorem badTest_1280_block_5 : Interval badTest_1280 40 48 :=
  interval_of_check badTest_1280 40 8 (by decide +kernel)

theorem badTest_1280_block_6 : Interval badTest_1280 48 56 :=
  interval_of_check badTest_1280 48 8 (by decide +kernel)

theorem badTest_1280_block_7 : Interval badTest_1280 56 64 :=
  interval_of_check badTest_1280 56 8 (by decide +kernel)

theorem badTest_1280_block_8 : Interval badTest_1280 64 72 :=
  interval_of_check badTest_1280 64 8 (by decide +kernel)

theorem badTest_1280_block_9 : Interval badTest_1280 72 80 :=
  interval_of_check badTest_1280 72 8 (by decide +kernel)

theorem badTest_1280_block_10 : Interval badTest_1280 80 88 :=
  interval_of_check badTest_1280 80 8 (by decide +kernel)

theorem badTest_1280_block_11 : Interval badTest_1280 88 96 :=
  interval_of_check badTest_1280 88 8 (by decide +kernel)

theorem badTest_1280_block_12 : Interval badTest_1280 96 104 :=
  interval_of_check badTest_1280 96 8 (by decide +kernel)

theorem badTest_1280_block_13 : Interval badTest_1280 104 112 :=
  interval_of_check badTest_1280 104 8 (by decide +kernel)

theorem badTest_1280_block_14 : Interval badTest_1280 112 120 :=
  interval_of_check badTest_1280 112 8 (by decide +kernel)

theorem badTest_1280_block_15 : Interval badTest_1280 120 128 :=
  interval_of_check badTest_1280 120 8 (by decide +kernel)

theorem badTest_1280_block_16 : Interval badTest_1280 128 136 :=
  interval_of_check badTest_1280 128 8 (by decide +kernel)

theorem badTest_1280_block_17 : Interval badTest_1280 136 144 :=
  interval_of_check badTest_1280 136 8 (by decide +kernel)

theorem badTest_1280_block_18 : Interval badTest_1280 144 152 :=
  interval_of_check badTest_1280 144 8 (by decide +kernel)

theorem badTest_1280_block_19 : Interval badTest_1280 152 160 :=
  interval_of_check badTest_1280 152 8 (by decide +kernel)

theorem badTest_1280_block_20 : Interval badTest_1280 160 168 :=
  interval_of_check badTest_1280 160 8 (by decide +kernel)

theorem badTest_1280_block_21 : Interval badTest_1280 168 176 :=
  interval_of_check badTest_1280 168 8 (by decide +kernel)

theorem badTest_1280_block_22 : Interval badTest_1280 176 184 :=
  interval_of_check badTest_1280 176 8 (by decide +kernel)

theorem badTest_1280_block_23 : Interval badTest_1280 184 192 :=
  interval_of_check badTest_1280 184 8 (by decide +kernel)

theorem badTest_1280_block_24 : Interval badTest_1280 192 200 :=
  interval_of_check badTest_1280 192 8 (by decide +kernel)

theorem badTest_1280_block_25 : Interval badTest_1280 200 208 :=
  interval_of_check badTest_1280 200 8 (by decide +kernel)

theorem badTest_1280_block_26 : Interval badTest_1280 208 216 :=
  interval_of_check badTest_1280 208 8 (by decide +kernel)

theorem badTest_1280_block_27 : Interval badTest_1280 216 224 :=
  interval_of_check badTest_1280 216 8 (by decide +kernel)

theorem badTest_1280_block_28 : Interval badTest_1280 224 232 :=
  interval_of_check badTest_1280 224 8 (by decide +kernel)

theorem badTest_1280_block_29 : Interval badTest_1280 232 240 :=
  interval_of_check badTest_1280 232 8 (by decide +kernel)

theorem badTest_1280_block_30 : Interval badTest_1280 240 248 :=
  interval_of_check badTest_1280 240 8 (by decide +kernel)

theorem badTest_1280_block_31 : Interval badTest_1280 248 256 :=
  interval_of_check badTest_1280 248 8 (by decide +kernel)

theorem badTest_1280_complete : Interval badTest_1280 0 256 :=
  (interval_append badTest_1280 0 128 256
  (interval_append badTest_1280 0 64 128
  (interval_append badTest_1280 0 32 64
  (interval_append badTest_1280 0 16 32
  (interval_append badTest_1280 0 8 16
  badTest_1280_block_0
  badTest_1280_block_1)
  (interval_append badTest_1280 16 24 32
  badTest_1280_block_2
  badTest_1280_block_3))
  (interval_append badTest_1280 32 48 64
  (interval_append badTest_1280 32 40 48
  badTest_1280_block_4
  badTest_1280_block_5)
  (interval_append badTest_1280 48 56 64
  badTest_1280_block_6
  badTest_1280_block_7)))
  (interval_append badTest_1280 64 96 128
  (interval_append badTest_1280 64 80 96
  (interval_append badTest_1280 64 72 80
  badTest_1280_block_8
  badTest_1280_block_9)
  (interval_append badTest_1280 80 88 96
  badTest_1280_block_10
  badTest_1280_block_11))
  (interval_append badTest_1280 96 112 128
  (interval_append badTest_1280 96 104 112
  badTest_1280_block_12
  badTest_1280_block_13)
  (interval_append badTest_1280 112 120 128
  badTest_1280_block_14
  badTest_1280_block_15))))
  (interval_append badTest_1280 128 192 256
  (interval_append badTest_1280 128 160 192
  (interval_append badTest_1280 128 144 160
  (interval_append badTest_1280 128 136 144
  badTest_1280_block_16
  badTest_1280_block_17)
  (interval_append badTest_1280 144 152 160
  badTest_1280_block_18
  badTest_1280_block_19))
  (interval_append badTest_1280 160 176 192
  (interval_append badTest_1280 160 168 176
  badTest_1280_block_20
  badTest_1280_block_21)
  (interval_append badTest_1280 176 184 192
  badTest_1280_block_22
  badTest_1280_block_23)))
  (interval_append badTest_1280 192 224 256
  (interval_append badTest_1280 192 208 224
  (interval_append badTest_1280 192 200 208
  badTest_1280_block_24
  badTest_1280_block_25)
  (interval_append badTest_1280 208 216 224
  badTest_1280_block_26
  badTest_1280_block_27))
  (interval_append badTest_1280 224 240 256
  (interval_append badTest_1280 224 232 240
  badTest_1280_block_28
  badTest_1280_block_29)
  (interval_append badTest_1280 240 248 256
  badTest_1280_block_30
  badTest_1280_block_31)))))
theorem badTestInterval1280 : Interval badTest 1280 1536 := by
  intro i hlo hhi
  have h := badTest_1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [badTest_1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
