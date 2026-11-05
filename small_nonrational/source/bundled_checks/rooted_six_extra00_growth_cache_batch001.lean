module
prelude
public import RootedSixExtra00GrowthCacheData

/- RootedSixExtra00GrowthCacheCells016 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells017 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells018 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells019 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells020 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells021 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells022 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells023 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells024 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells025 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

theorem cellTest_6400_block_27 : Interval cellTest_6400 216 224 :=
  interval_of_check cellTest_6400 216 8 (by decide +kernel)

theorem cellTest_6400_block_28 : Interval cellTest_6400 224 232 :=
  interval_of_check cellTest_6400 224 8 (by decide +kernel)

theorem cellTest_6400_block_29 : Interval cellTest_6400 232 240 :=
  interval_of_check cellTest_6400 232 8 (by decide +kernel)

theorem cellTest_6400_block_30 : Interval cellTest_6400 240 248 :=
  interval_of_check cellTest_6400 240 8 (by decide +kernel)

theorem cellTest_6400_block_31 : Interval cellTest_6400 248 256 :=
  interval_of_check cellTest_6400 248 8 (by decide +kernel)

theorem cellTest_6400_complete : Interval cellTest_6400 0 256 :=
  (interval_append cellTest_6400 0 128 256
  (interval_append cellTest_6400 0 64 128
  (interval_append cellTest_6400 0 32 64
  (interval_append cellTest_6400 0 16 32
  (interval_append cellTest_6400 0 8 16
  cellTest_6400_block_0
  cellTest_6400_block_1)
  (interval_append cellTest_6400 16 24 32
  cellTest_6400_block_2
  cellTest_6400_block_3))
  (interval_append cellTest_6400 32 48 64
  (interval_append cellTest_6400 32 40 48
  cellTest_6400_block_4
  cellTest_6400_block_5)
  (interval_append cellTest_6400 48 56 64
  cellTest_6400_block_6
  cellTest_6400_block_7)))
  (interval_append cellTest_6400 64 96 128
  (interval_append cellTest_6400 64 80 96
  (interval_append cellTest_6400 64 72 80
  cellTest_6400_block_8
  cellTest_6400_block_9)
  (interval_append cellTest_6400 80 88 96
  cellTest_6400_block_10
  cellTest_6400_block_11))
  (interval_append cellTest_6400 96 112 128
  (interval_append cellTest_6400 96 104 112
  cellTest_6400_block_12
  cellTest_6400_block_13)
  (interval_append cellTest_6400 112 120 128
  cellTest_6400_block_14
  cellTest_6400_block_15))))
  (interval_append cellTest_6400 128 192 256
  (interval_append cellTest_6400 128 160 192
  (interval_append cellTest_6400 128 144 160
  (interval_append cellTest_6400 128 136 144
  cellTest_6400_block_16
  cellTest_6400_block_17)
  (interval_append cellTest_6400 144 152 160
  cellTest_6400_block_18
  cellTest_6400_block_19))
  (interval_append cellTest_6400 160 176 192
  (interval_append cellTest_6400 160 168 176
  cellTest_6400_block_20
  cellTest_6400_block_21)
  (interval_append cellTest_6400 176 184 192
  cellTest_6400_block_22
  cellTest_6400_block_23)))
  (interval_append cellTest_6400 192 224 256
  (interval_append cellTest_6400 192 208 224
  (interval_append cellTest_6400 192 200 208
  cellTest_6400_block_24
  cellTest_6400_block_25)
  (interval_append cellTest_6400 208 216 224
  cellTest_6400_block_26
  cellTest_6400_block_27))
  (interval_append cellTest_6400 224 240 256
  (interval_append cellTest_6400 224 232 240
  cellTest_6400_block_28
  cellTest_6400_block_29)
  (interval_append cellTest_6400 240 248 256
  cellTest_6400_block_30
  cellTest_6400_block_31)))))
theorem cellTestInterval6400 : Interval cellTest 6400 6656 := by
  intro i hlo hhi
  have h := cellTest_6400_complete (i-6400) (Nat.zero_le _) (by omega)
  simpa only [cellTest_6400, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells026 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_6656 (i : Nat) := cellTest (i+6656)
theorem cellTest_6656_block_0 : Interval cellTest_6656 0 8 :=
  interval_of_check cellTest_6656 0 8 (by decide +kernel)

theorem cellTest_6656_block_1 : Interval cellTest_6656 8 16 :=
  interval_of_check cellTest_6656 8 8 (by decide +kernel)

theorem cellTest_6656_block_2 : Interval cellTest_6656 16 24 :=
  interval_of_check cellTest_6656 16 8 (by decide +kernel)

theorem cellTest_6656_block_3 : Interval cellTest_6656 24 32 :=
  interval_of_check cellTest_6656 24 8 (by decide +kernel)

theorem cellTest_6656_block_4 : Interval cellTest_6656 32 40 :=
  interval_of_check cellTest_6656 32 8 (by decide +kernel)

theorem cellTest_6656_block_5 : Interval cellTest_6656 40 48 :=
  interval_of_check cellTest_6656 40 8 (by decide +kernel)

theorem cellTest_6656_block_6 : Interval cellTest_6656 48 56 :=
  interval_of_check cellTest_6656 48 8 (by decide +kernel)

theorem cellTest_6656_block_7 : Interval cellTest_6656 56 64 :=
  interval_of_check cellTest_6656 56 8 (by decide +kernel)

theorem cellTest_6656_block_8 : Interval cellTest_6656 64 72 :=
  interval_of_check cellTest_6656 64 8 (by decide +kernel)

theorem cellTest_6656_block_9 : Interval cellTest_6656 72 80 :=
  interval_of_check cellTest_6656 72 8 (by decide +kernel)

theorem cellTest_6656_block_10 : Interval cellTest_6656 80 88 :=
  interval_of_check cellTest_6656 80 8 (by decide +kernel)

theorem cellTest_6656_block_11 : Interval cellTest_6656 88 96 :=
  interval_of_check cellTest_6656 88 8 (by decide +kernel)

theorem cellTest_6656_block_12 : Interval cellTest_6656 96 104 :=
  interval_of_check cellTest_6656 96 8 (by decide +kernel)

theorem cellTest_6656_block_13 : Interval cellTest_6656 104 112 :=
  interval_of_check cellTest_6656 104 8 (by decide +kernel)

theorem cellTest_6656_block_14 : Interval cellTest_6656 112 120 :=
  interval_of_check cellTest_6656 112 8 (by decide +kernel)

theorem cellTest_6656_block_15 : Interval cellTest_6656 120 128 :=
  interval_of_check cellTest_6656 120 8 (by decide +kernel)

theorem cellTest_6656_block_16 : Interval cellTest_6656 128 136 :=
  interval_of_check cellTest_6656 128 8 (by decide +kernel)

theorem cellTest_6656_block_17 : Interval cellTest_6656 136 144 :=
  interval_of_check cellTest_6656 136 8 (by decide +kernel)

theorem cellTest_6656_block_18 : Interval cellTest_6656 144 152 :=
  interval_of_check cellTest_6656 144 8 (by decide +kernel)

theorem cellTest_6656_block_19 : Interval cellTest_6656 152 160 :=
  interval_of_check cellTest_6656 152 8 (by decide +kernel)

theorem cellTest_6656_block_20 : Interval cellTest_6656 160 168 :=
  interval_of_check cellTest_6656 160 8 (by decide +kernel)

theorem cellTest_6656_block_21 : Interval cellTest_6656 168 176 :=
  interval_of_check cellTest_6656 168 8 (by decide +kernel)

theorem cellTest_6656_block_22 : Interval cellTest_6656 176 184 :=
  interval_of_check cellTest_6656 176 8 (by decide +kernel)

theorem cellTest_6656_block_23 : Interval cellTest_6656 184 192 :=
  interval_of_check cellTest_6656 184 8 (by decide +kernel)

theorem cellTest_6656_block_24 : Interval cellTest_6656 192 200 :=
  interval_of_check cellTest_6656 192 8 (by decide +kernel)

theorem cellTest_6656_block_25 : Interval cellTest_6656 200 208 :=
  interval_of_check cellTest_6656 200 8 (by decide +kernel)

theorem cellTest_6656_block_26 : Interval cellTest_6656 208 216 :=
  interval_of_check cellTest_6656 208 8 (by decide +kernel)

theorem cellTest_6656_block_27 : Interval cellTest_6656 216 224 :=
  interval_of_check cellTest_6656 216 8 (by decide +kernel)

theorem cellTest_6656_block_28 : Interval cellTest_6656 224 232 :=
  interval_of_check cellTest_6656 224 8 (by decide +kernel)

theorem cellTest_6656_block_29 : Interval cellTest_6656 232 240 :=
  interval_of_check cellTest_6656 232 8 (by decide +kernel)

theorem cellTest_6656_block_30 : Interval cellTest_6656 240 248 :=
  interval_of_check cellTest_6656 240 8 (by decide +kernel)

theorem cellTest_6656_block_31 : Interval cellTest_6656 248 256 :=
  interval_of_check cellTest_6656 248 8 (by decide +kernel)

theorem cellTest_6656_complete : Interval cellTest_6656 0 256 :=
  (interval_append cellTest_6656 0 128 256
  (interval_append cellTest_6656 0 64 128
  (interval_append cellTest_6656 0 32 64
  (interval_append cellTest_6656 0 16 32
  (interval_append cellTest_6656 0 8 16
  cellTest_6656_block_0
  cellTest_6656_block_1)
  (interval_append cellTest_6656 16 24 32
  cellTest_6656_block_2
  cellTest_6656_block_3))
  (interval_append cellTest_6656 32 48 64
  (interval_append cellTest_6656 32 40 48
  cellTest_6656_block_4
  cellTest_6656_block_5)
  (interval_append cellTest_6656 48 56 64
  cellTest_6656_block_6
  cellTest_6656_block_7)))
  (interval_append cellTest_6656 64 96 128
  (interval_append cellTest_6656 64 80 96
  (interval_append cellTest_6656 64 72 80
  cellTest_6656_block_8
  cellTest_6656_block_9)
  (interval_append cellTest_6656 80 88 96
  cellTest_6656_block_10
  cellTest_6656_block_11))
  (interval_append cellTest_6656 96 112 128
  (interval_append cellTest_6656 96 104 112
  cellTest_6656_block_12
  cellTest_6656_block_13)
  (interval_append cellTest_6656 112 120 128
  cellTest_6656_block_14
  cellTest_6656_block_15))))
  (interval_append cellTest_6656 128 192 256
  (interval_append cellTest_6656 128 160 192
  (interval_append cellTest_6656 128 144 160
  (interval_append cellTest_6656 128 136 144
  cellTest_6656_block_16
  cellTest_6656_block_17)
  (interval_append cellTest_6656 144 152 160
  cellTest_6656_block_18
  cellTest_6656_block_19))
  (interval_append cellTest_6656 160 176 192
  (interval_append cellTest_6656 160 168 176
  cellTest_6656_block_20
  cellTest_6656_block_21)
  (interval_append cellTest_6656 176 184 192
  cellTest_6656_block_22
  cellTest_6656_block_23)))
  (interval_append cellTest_6656 192 224 256
  (interval_append cellTest_6656 192 208 224
  (interval_append cellTest_6656 192 200 208
  cellTest_6656_block_24
  cellTest_6656_block_25)
  (interval_append cellTest_6656 208 216 224
  cellTest_6656_block_26
  cellTest_6656_block_27))
  (interval_append cellTest_6656 224 240 256
  (interval_append cellTest_6656 224 232 240
  cellTest_6656_block_28
  cellTest_6656_block_29)
  (interval_append cellTest_6656 240 248 256
  cellTest_6656_block_30
  cellTest_6656_block_31)))))
theorem cellTestInterval6656 : Interval cellTest 6656 6912 := by
  intro i hlo hhi
  have h := cellTest_6656_complete (i-6656) (Nat.zero_le _) (by omega)
  simpa only [cellTest_6656, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells027 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_6912 (i : Nat) := cellTest (i+6912)
theorem cellTest_6912_block_0 : Interval cellTest_6912 0 8 :=
  interval_of_check cellTest_6912 0 8 (by decide +kernel)

theorem cellTest_6912_block_1 : Interval cellTest_6912 8 16 :=
  interval_of_check cellTest_6912 8 8 (by decide +kernel)

theorem cellTest_6912_block_2 : Interval cellTest_6912 16 24 :=
  interval_of_check cellTest_6912 16 8 (by decide +kernel)

theorem cellTest_6912_block_3 : Interval cellTest_6912 24 32 :=
  interval_of_check cellTest_6912 24 8 (by decide +kernel)

theorem cellTest_6912_block_4 : Interval cellTest_6912 32 40 :=
  interval_of_check cellTest_6912 32 8 (by decide +kernel)

theorem cellTest_6912_block_5 : Interval cellTest_6912 40 48 :=
  interval_of_check cellTest_6912 40 8 (by decide +kernel)

theorem cellTest_6912_block_6 : Interval cellTest_6912 48 56 :=
  interval_of_check cellTest_6912 48 8 (by decide +kernel)

theorem cellTest_6912_block_7 : Interval cellTest_6912 56 64 :=
  interval_of_check cellTest_6912 56 8 (by decide +kernel)

theorem cellTest_6912_block_8 : Interval cellTest_6912 64 72 :=
  interval_of_check cellTest_6912 64 8 (by decide +kernel)

theorem cellTest_6912_block_9 : Interval cellTest_6912 72 80 :=
  interval_of_check cellTest_6912 72 8 (by decide +kernel)

theorem cellTest_6912_block_10 : Interval cellTest_6912 80 88 :=
  interval_of_check cellTest_6912 80 8 (by decide +kernel)

theorem cellTest_6912_block_11 : Interval cellTest_6912 88 96 :=
  interval_of_check cellTest_6912 88 8 (by decide +kernel)

theorem cellTest_6912_block_12 : Interval cellTest_6912 96 104 :=
  interval_of_check cellTest_6912 96 8 (by decide +kernel)

theorem cellTest_6912_block_13 : Interval cellTest_6912 104 112 :=
  interval_of_check cellTest_6912 104 8 (by decide +kernel)

theorem cellTest_6912_block_14 : Interval cellTest_6912 112 120 :=
  interval_of_check cellTest_6912 112 8 (by decide +kernel)

theorem cellTest_6912_block_15 : Interval cellTest_6912 120 128 :=
  interval_of_check cellTest_6912 120 8 (by decide +kernel)

theorem cellTest_6912_block_16 : Interval cellTest_6912 128 136 :=
  interval_of_check cellTest_6912 128 8 (by decide +kernel)

theorem cellTest_6912_block_17 : Interval cellTest_6912 136 144 :=
  interval_of_check cellTest_6912 136 8 (by decide +kernel)

theorem cellTest_6912_block_18 : Interval cellTest_6912 144 152 :=
  interval_of_check cellTest_6912 144 8 (by decide +kernel)

theorem cellTest_6912_block_19 : Interval cellTest_6912 152 160 :=
  interval_of_check cellTest_6912 152 8 (by decide +kernel)

theorem cellTest_6912_block_20 : Interval cellTest_6912 160 168 :=
  interval_of_check cellTest_6912 160 8 (by decide +kernel)

theorem cellTest_6912_block_21 : Interval cellTest_6912 168 176 :=
  interval_of_check cellTest_6912 168 8 (by decide +kernel)

theorem cellTest_6912_block_22 : Interval cellTest_6912 176 184 :=
  interval_of_check cellTest_6912 176 8 (by decide +kernel)

theorem cellTest_6912_block_23 : Interval cellTest_6912 184 192 :=
  interval_of_check cellTest_6912 184 8 (by decide +kernel)

theorem cellTest_6912_block_24 : Interval cellTest_6912 192 200 :=
  interval_of_check cellTest_6912 192 8 (by decide +kernel)

theorem cellTest_6912_block_25 : Interval cellTest_6912 200 208 :=
  interval_of_check cellTest_6912 200 8 (by decide +kernel)

theorem cellTest_6912_block_26 : Interval cellTest_6912 208 216 :=
  interval_of_check cellTest_6912 208 8 (by decide +kernel)

theorem cellTest_6912_block_27 : Interval cellTest_6912 216 224 :=
  interval_of_check cellTest_6912 216 8 (by decide +kernel)

theorem cellTest_6912_block_28 : Interval cellTest_6912 224 232 :=
  interval_of_check cellTest_6912 224 8 (by decide +kernel)

theorem cellTest_6912_block_29 : Interval cellTest_6912 232 240 :=
  interval_of_check cellTest_6912 232 8 (by decide +kernel)

theorem cellTest_6912_block_30 : Interval cellTest_6912 240 248 :=
  interval_of_check cellTest_6912 240 8 (by decide +kernel)

theorem cellTest_6912_block_31 : Interval cellTest_6912 248 256 :=
  interval_of_check cellTest_6912 248 8 (by decide +kernel)

theorem cellTest_6912_complete : Interval cellTest_6912 0 256 :=
  (interval_append cellTest_6912 0 128 256
  (interval_append cellTest_6912 0 64 128
  (interval_append cellTest_6912 0 32 64
  (interval_append cellTest_6912 0 16 32
  (interval_append cellTest_6912 0 8 16
  cellTest_6912_block_0
  cellTest_6912_block_1)
  (interval_append cellTest_6912 16 24 32
  cellTest_6912_block_2
  cellTest_6912_block_3))
  (interval_append cellTest_6912 32 48 64
  (interval_append cellTest_6912 32 40 48
  cellTest_6912_block_4
  cellTest_6912_block_5)
  (interval_append cellTest_6912 48 56 64
  cellTest_6912_block_6
  cellTest_6912_block_7)))
  (interval_append cellTest_6912 64 96 128
  (interval_append cellTest_6912 64 80 96
  (interval_append cellTest_6912 64 72 80
  cellTest_6912_block_8
  cellTest_6912_block_9)
  (interval_append cellTest_6912 80 88 96
  cellTest_6912_block_10
  cellTest_6912_block_11))
  (interval_append cellTest_6912 96 112 128
  (interval_append cellTest_6912 96 104 112
  cellTest_6912_block_12
  cellTest_6912_block_13)
  (interval_append cellTest_6912 112 120 128
  cellTest_6912_block_14
  cellTest_6912_block_15))))
  (interval_append cellTest_6912 128 192 256
  (interval_append cellTest_6912 128 160 192
  (interval_append cellTest_6912 128 144 160
  (interval_append cellTest_6912 128 136 144
  cellTest_6912_block_16
  cellTest_6912_block_17)
  (interval_append cellTest_6912 144 152 160
  cellTest_6912_block_18
  cellTest_6912_block_19))
  (interval_append cellTest_6912 160 176 192
  (interval_append cellTest_6912 160 168 176
  cellTest_6912_block_20
  cellTest_6912_block_21)
  (interval_append cellTest_6912 176 184 192
  cellTest_6912_block_22
  cellTest_6912_block_23)))
  (interval_append cellTest_6912 192 224 256
  (interval_append cellTest_6912 192 208 224
  (interval_append cellTest_6912 192 200 208
  cellTest_6912_block_24
  cellTest_6912_block_25)
  (interval_append cellTest_6912 208 216 224
  cellTest_6912_block_26
  cellTest_6912_block_27))
  (interval_append cellTest_6912 224 240 256
  (interval_append cellTest_6912 224 232 240
  cellTest_6912_block_28
  cellTest_6912_block_29)
  (interval_append cellTest_6912 240 248 256
  cellTest_6912_block_30
  cellTest_6912_block_31)))))
theorem cellTestInterval6912 : Interval cellTest 6912 7168 := by
  intro i hlo hhi
  have h := cellTest_6912_complete (i-6912) (Nat.zero_le _) (by omega)
  simpa only [cellTest_6912, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells028 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_7168 (i : Nat) := cellTest (i+7168)
theorem cellTest_7168_block_0 : Interval cellTest_7168 0 8 :=
  interval_of_check cellTest_7168 0 8 (by decide +kernel)

theorem cellTest_7168_block_1 : Interval cellTest_7168 8 16 :=
  interval_of_check cellTest_7168 8 8 (by decide +kernel)

theorem cellTest_7168_block_2 : Interval cellTest_7168 16 24 :=
  interval_of_check cellTest_7168 16 8 (by decide +kernel)

theorem cellTest_7168_block_3 : Interval cellTest_7168 24 32 :=
  interval_of_check cellTest_7168 24 8 (by decide +kernel)

theorem cellTest_7168_block_4 : Interval cellTest_7168 32 40 :=
  interval_of_check cellTest_7168 32 8 (by decide +kernel)

theorem cellTest_7168_block_5 : Interval cellTest_7168 40 48 :=
  interval_of_check cellTest_7168 40 8 (by decide +kernel)

theorem cellTest_7168_block_6 : Interval cellTest_7168 48 56 :=
  interval_of_check cellTest_7168 48 8 (by decide +kernel)

theorem cellTest_7168_block_7 : Interval cellTest_7168 56 64 :=
  interval_of_check cellTest_7168 56 8 (by decide +kernel)

theorem cellTest_7168_block_8 : Interval cellTest_7168 64 72 :=
  interval_of_check cellTest_7168 64 8 (by decide +kernel)

theorem cellTest_7168_block_9 : Interval cellTest_7168 72 80 :=
  interval_of_check cellTest_7168 72 8 (by decide +kernel)

theorem cellTest_7168_block_10 : Interval cellTest_7168 80 88 :=
  interval_of_check cellTest_7168 80 8 (by decide +kernel)

theorem cellTest_7168_block_11 : Interval cellTest_7168 88 96 :=
  interval_of_check cellTest_7168 88 8 (by decide +kernel)

theorem cellTest_7168_block_12 : Interval cellTest_7168 96 104 :=
  interval_of_check cellTest_7168 96 8 (by decide +kernel)

theorem cellTest_7168_block_13 : Interval cellTest_7168 104 112 :=
  interval_of_check cellTest_7168 104 8 (by decide +kernel)

theorem cellTest_7168_block_14 : Interval cellTest_7168 112 120 :=
  interval_of_check cellTest_7168 112 8 (by decide +kernel)

theorem cellTest_7168_block_15 : Interval cellTest_7168 120 128 :=
  interval_of_check cellTest_7168 120 8 (by decide +kernel)

theorem cellTest_7168_block_16 : Interval cellTest_7168 128 136 :=
  interval_of_check cellTest_7168 128 8 (by decide +kernel)

theorem cellTest_7168_block_17 : Interval cellTest_7168 136 144 :=
  interval_of_check cellTest_7168 136 8 (by decide +kernel)

theorem cellTest_7168_block_18 : Interval cellTest_7168 144 152 :=
  interval_of_check cellTest_7168 144 8 (by decide +kernel)

theorem cellTest_7168_block_19 : Interval cellTest_7168 152 160 :=
  interval_of_check cellTest_7168 152 8 (by decide +kernel)

theorem cellTest_7168_block_20 : Interval cellTest_7168 160 168 :=
  interval_of_check cellTest_7168 160 8 (by decide +kernel)

theorem cellTest_7168_block_21 : Interval cellTest_7168 168 176 :=
  interval_of_check cellTest_7168 168 8 (by decide +kernel)

theorem cellTest_7168_block_22 : Interval cellTest_7168 176 184 :=
  interval_of_check cellTest_7168 176 8 (by decide +kernel)

theorem cellTest_7168_block_23 : Interval cellTest_7168 184 192 :=
  interval_of_check cellTest_7168 184 8 (by decide +kernel)

theorem cellTest_7168_block_24 : Interval cellTest_7168 192 200 :=
  interval_of_check cellTest_7168 192 8 (by decide +kernel)

theorem cellTest_7168_block_25 : Interval cellTest_7168 200 208 :=
  interval_of_check cellTest_7168 200 8 (by decide +kernel)

theorem cellTest_7168_block_26 : Interval cellTest_7168 208 216 :=
  interval_of_check cellTest_7168 208 8 (by decide +kernel)

theorem cellTest_7168_block_27 : Interval cellTest_7168 216 224 :=
  interval_of_check cellTest_7168 216 8 (by decide +kernel)

theorem cellTest_7168_block_28 : Interval cellTest_7168 224 232 :=
  interval_of_check cellTest_7168 224 8 (by decide +kernel)

theorem cellTest_7168_block_29 : Interval cellTest_7168 232 240 :=
  interval_of_check cellTest_7168 232 8 (by decide +kernel)

theorem cellTest_7168_block_30 : Interval cellTest_7168 240 248 :=
  interval_of_check cellTest_7168 240 8 (by decide +kernel)

theorem cellTest_7168_block_31 : Interval cellTest_7168 248 256 :=
  interval_of_check cellTest_7168 248 8 (by decide +kernel)

theorem cellTest_7168_complete : Interval cellTest_7168 0 256 :=
  (interval_append cellTest_7168 0 128 256
  (interval_append cellTest_7168 0 64 128
  (interval_append cellTest_7168 0 32 64
  (interval_append cellTest_7168 0 16 32
  (interval_append cellTest_7168 0 8 16
  cellTest_7168_block_0
  cellTest_7168_block_1)
  (interval_append cellTest_7168 16 24 32
  cellTest_7168_block_2
  cellTest_7168_block_3))
  (interval_append cellTest_7168 32 48 64
  (interval_append cellTest_7168 32 40 48
  cellTest_7168_block_4
  cellTest_7168_block_5)
  (interval_append cellTest_7168 48 56 64
  cellTest_7168_block_6
  cellTest_7168_block_7)))
  (interval_append cellTest_7168 64 96 128
  (interval_append cellTest_7168 64 80 96
  (interval_append cellTest_7168 64 72 80
  cellTest_7168_block_8
  cellTest_7168_block_9)
  (interval_append cellTest_7168 80 88 96
  cellTest_7168_block_10
  cellTest_7168_block_11))
  (interval_append cellTest_7168 96 112 128
  (interval_append cellTest_7168 96 104 112
  cellTest_7168_block_12
  cellTest_7168_block_13)
  (interval_append cellTest_7168 112 120 128
  cellTest_7168_block_14
  cellTest_7168_block_15))))
  (interval_append cellTest_7168 128 192 256
  (interval_append cellTest_7168 128 160 192
  (interval_append cellTest_7168 128 144 160
  (interval_append cellTest_7168 128 136 144
  cellTest_7168_block_16
  cellTest_7168_block_17)
  (interval_append cellTest_7168 144 152 160
  cellTest_7168_block_18
  cellTest_7168_block_19))
  (interval_append cellTest_7168 160 176 192
  (interval_append cellTest_7168 160 168 176
  cellTest_7168_block_20
  cellTest_7168_block_21)
  (interval_append cellTest_7168 176 184 192
  cellTest_7168_block_22
  cellTest_7168_block_23)))
  (interval_append cellTest_7168 192 224 256
  (interval_append cellTest_7168 192 208 224
  (interval_append cellTest_7168 192 200 208
  cellTest_7168_block_24
  cellTest_7168_block_25)
  (interval_append cellTest_7168 208 216 224
  cellTest_7168_block_26
  cellTest_7168_block_27))
  (interval_append cellTest_7168 224 240 256
  (interval_append cellTest_7168 224 232 240
  cellTest_7168_block_28
  cellTest_7168_block_29)
  (interval_append cellTest_7168 240 248 256
  cellTest_7168_block_30
  cellTest_7168_block_31)))))
theorem cellTestInterval7168 : Interval cellTest 7168 7424 := by
  intro i hlo hhi
  have h := cellTest_7168_complete (i-7168) (Nat.zero_le _) (by omega)
  simpa only [cellTest_7168, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells029 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_7424 (i : Nat) := cellTest (i+7424)
theorem cellTest_7424_block_0 : Interval cellTest_7424 0 8 :=
  interval_of_check cellTest_7424 0 8 (by decide +kernel)

theorem cellTest_7424_block_1 : Interval cellTest_7424 8 16 :=
  interval_of_check cellTest_7424 8 8 (by decide +kernel)

theorem cellTest_7424_block_2 : Interval cellTest_7424 16 24 :=
  interval_of_check cellTest_7424 16 8 (by decide +kernel)

theorem cellTest_7424_block_3 : Interval cellTest_7424 24 32 :=
  interval_of_check cellTest_7424 24 8 (by decide +kernel)

theorem cellTest_7424_block_4 : Interval cellTest_7424 32 40 :=
  interval_of_check cellTest_7424 32 8 (by decide +kernel)

theorem cellTest_7424_block_5 : Interval cellTest_7424 40 48 :=
  interval_of_check cellTest_7424 40 8 (by decide +kernel)

theorem cellTest_7424_block_6 : Interval cellTest_7424 48 56 :=
  interval_of_check cellTest_7424 48 8 (by decide +kernel)

theorem cellTest_7424_block_7 : Interval cellTest_7424 56 64 :=
  interval_of_check cellTest_7424 56 8 (by decide +kernel)

theorem cellTest_7424_block_8 : Interval cellTest_7424 64 72 :=
  interval_of_check cellTest_7424 64 8 (by decide +kernel)

theorem cellTest_7424_block_9 : Interval cellTest_7424 72 80 :=
  interval_of_check cellTest_7424 72 8 (by decide +kernel)

theorem cellTest_7424_block_10 : Interval cellTest_7424 80 88 :=
  interval_of_check cellTest_7424 80 8 (by decide +kernel)

theorem cellTest_7424_block_11 : Interval cellTest_7424 88 96 :=
  interval_of_check cellTest_7424 88 8 (by decide +kernel)

theorem cellTest_7424_block_12 : Interval cellTest_7424 96 104 :=
  interval_of_check cellTest_7424 96 8 (by decide +kernel)

theorem cellTest_7424_block_13 : Interval cellTest_7424 104 112 :=
  interval_of_check cellTest_7424 104 8 (by decide +kernel)

theorem cellTest_7424_block_14 : Interval cellTest_7424 112 120 :=
  interval_of_check cellTest_7424 112 8 (by decide +kernel)

theorem cellTest_7424_block_15 : Interval cellTest_7424 120 128 :=
  interval_of_check cellTest_7424 120 8 (by decide +kernel)

theorem cellTest_7424_block_16 : Interval cellTest_7424 128 136 :=
  interval_of_check cellTest_7424 128 8 (by decide +kernel)

theorem cellTest_7424_block_17 : Interval cellTest_7424 136 144 :=
  interval_of_check cellTest_7424 136 8 (by decide +kernel)

theorem cellTest_7424_block_18 : Interval cellTest_7424 144 152 :=
  interval_of_check cellTest_7424 144 8 (by decide +kernel)

theorem cellTest_7424_block_19 : Interval cellTest_7424 152 160 :=
  interval_of_check cellTest_7424 152 8 (by decide +kernel)

theorem cellTest_7424_block_20 : Interval cellTest_7424 160 168 :=
  interval_of_check cellTest_7424 160 8 (by decide +kernel)

theorem cellTest_7424_block_21 : Interval cellTest_7424 168 176 :=
  interval_of_check cellTest_7424 168 8 (by decide +kernel)

theorem cellTest_7424_block_22 : Interval cellTest_7424 176 184 :=
  interval_of_check cellTest_7424 176 8 (by decide +kernel)

theorem cellTest_7424_block_23 : Interval cellTest_7424 184 192 :=
  interval_of_check cellTest_7424 184 8 (by decide +kernel)

theorem cellTest_7424_block_24 : Interval cellTest_7424 192 200 :=
  interval_of_check cellTest_7424 192 8 (by decide +kernel)

theorem cellTest_7424_block_25 : Interval cellTest_7424 200 208 :=
  interval_of_check cellTest_7424 200 8 (by decide +kernel)

theorem cellTest_7424_block_26 : Interval cellTest_7424 208 216 :=
  interval_of_check cellTest_7424 208 8 (by decide +kernel)

theorem cellTest_7424_block_27 : Interval cellTest_7424 216 224 :=
  interval_of_check cellTest_7424 216 8 (by decide +kernel)

theorem cellTest_7424_block_28 : Interval cellTest_7424 224 232 :=
  interval_of_check cellTest_7424 224 8 (by decide +kernel)

theorem cellTest_7424_block_29 : Interval cellTest_7424 232 240 :=
  interval_of_check cellTest_7424 232 8 (by decide +kernel)

theorem cellTest_7424_block_30 : Interval cellTest_7424 240 248 :=
  interval_of_check cellTest_7424 240 8 (by decide +kernel)

theorem cellTest_7424_block_31 : Interval cellTest_7424 248 256 :=
  interval_of_check cellTest_7424 248 8 (by decide +kernel)

theorem cellTest_7424_complete : Interval cellTest_7424 0 256 :=
  (interval_append cellTest_7424 0 128 256
  (interval_append cellTest_7424 0 64 128
  (interval_append cellTest_7424 0 32 64
  (interval_append cellTest_7424 0 16 32
  (interval_append cellTest_7424 0 8 16
  cellTest_7424_block_0
  cellTest_7424_block_1)
  (interval_append cellTest_7424 16 24 32
  cellTest_7424_block_2
  cellTest_7424_block_3))
  (interval_append cellTest_7424 32 48 64
  (interval_append cellTest_7424 32 40 48
  cellTest_7424_block_4
  cellTest_7424_block_5)
  (interval_append cellTest_7424 48 56 64
  cellTest_7424_block_6
  cellTest_7424_block_7)))
  (interval_append cellTest_7424 64 96 128
  (interval_append cellTest_7424 64 80 96
  (interval_append cellTest_7424 64 72 80
  cellTest_7424_block_8
  cellTest_7424_block_9)
  (interval_append cellTest_7424 80 88 96
  cellTest_7424_block_10
  cellTest_7424_block_11))
  (interval_append cellTest_7424 96 112 128
  (interval_append cellTest_7424 96 104 112
  cellTest_7424_block_12
  cellTest_7424_block_13)
  (interval_append cellTest_7424 112 120 128
  cellTest_7424_block_14
  cellTest_7424_block_15))))
  (interval_append cellTest_7424 128 192 256
  (interval_append cellTest_7424 128 160 192
  (interval_append cellTest_7424 128 144 160
  (interval_append cellTest_7424 128 136 144
  cellTest_7424_block_16
  cellTest_7424_block_17)
  (interval_append cellTest_7424 144 152 160
  cellTest_7424_block_18
  cellTest_7424_block_19))
  (interval_append cellTest_7424 160 176 192
  (interval_append cellTest_7424 160 168 176
  cellTest_7424_block_20
  cellTest_7424_block_21)
  (interval_append cellTest_7424 176 184 192
  cellTest_7424_block_22
  cellTest_7424_block_23)))
  (interval_append cellTest_7424 192 224 256
  (interval_append cellTest_7424 192 208 224
  (interval_append cellTest_7424 192 200 208
  cellTest_7424_block_24
  cellTest_7424_block_25)
  (interval_append cellTest_7424 208 216 224
  cellTest_7424_block_26
  cellTest_7424_block_27))
  (interval_append cellTest_7424 224 240 256
  (interval_append cellTest_7424 224 232 240
  cellTest_7424_block_28
  cellTest_7424_block_29)
  (interval_append cellTest_7424 240 248 256
  cellTest_7424_block_30
  cellTest_7424_block_31)))))
theorem cellTestInterval7424 : Interval cellTest 7424 7680 := by
  intro i hlo hhi
  have h := cellTest_7424_complete (i-7424) (Nat.zero_le _) (by omega)
  simpa only [cellTest_7424, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells030 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_7680 (i : Nat) := cellTest (i+7680)
theorem cellTest_7680_block_0 : Interval cellTest_7680 0 8 :=
  interval_of_check cellTest_7680 0 8 (by decide +kernel)

theorem cellTest_7680_block_1 : Interval cellTest_7680 8 16 :=
  interval_of_check cellTest_7680 8 8 (by decide +kernel)

theorem cellTest_7680_block_2 : Interval cellTest_7680 16 24 :=
  interval_of_check cellTest_7680 16 8 (by decide +kernel)

theorem cellTest_7680_block_3 : Interval cellTest_7680 24 32 :=
  interval_of_check cellTest_7680 24 8 (by decide +kernel)

theorem cellTest_7680_block_4 : Interval cellTest_7680 32 40 :=
  interval_of_check cellTest_7680 32 8 (by decide +kernel)

theorem cellTest_7680_block_5 : Interval cellTest_7680 40 48 :=
  interval_of_check cellTest_7680 40 8 (by decide +kernel)

theorem cellTest_7680_block_6 : Interval cellTest_7680 48 56 :=
  interval_of_check cellTest_7680 48 8 (by decide +kernel)

theorem cellTest_7680_block_7 : Interval cellTest_7680 56 64 :=
  interval_of_check cellTest_7680 56 8 (by decide +kernel)

theorem cellTest_7680_block_8 : Interval cellTest_7680 64 72 :=
  interval_of_check cellTest_7680 64 8 (by decide +kernel)

theorem cellTest_7680_block_9 : Interval cellTest_7680 72 80 :=
  interval_of_check cellTest_7680 72 8 (by decide +kernel)

theorem cellTest_7680_block_10 : Interval cellTest_7680 80 88 :=
  interval_of_check cellTest_7680 80 8 (by decide +kernel)

theorem cellTest_7680_block_11 : Interval cellTest_7680 88 96 :=
  interval_of_check cellTest_7680 88 8 (by decide +kernel)

theorem cellTest_7680_block_12 : Interval cellTest_7680 96 104 :=
  interval_of_check cellTest_7680 96 8 (by decide +kernel)

theorem cellTest_7680_block_13 : Interval cellTest_7680 104 112 :=
  interval_of_check cellTest_7680 104 8 (by decide +kernel)

theorem cellTest_7680_block_14 : Interval cellTest_7680 112 120 :=
  interval_of_check cellTest_7680 112 8 (by decide +kernel)

theorem cellTest_7680_block_15 : Interval cellTest_7680 120 128 :=
  interval_of_check cellTest_7680 120 8 (by decide +kernel)

theorem cellTest_7680_block_16 : Interval cellTest_7680 128 136 :=
  interval_of_check cellTest_7680 128 8 (by decide +kernel)

theorem cellTest_7680_block_17 : Interval cellTest_7680 136 144 :=
  interval_of_check cellTest_7680 136 8 (by decide +kernel)

theorem cellTest_7680_block_18 : Interval cellTest_7680 144 152 :=
  interval_of_check cellTest_7680 144 8 (by decide +kernel)

theorem cellTest_7680_block_19 : Interval cellTest_7680 152 160 :=
  interval_of_check cellTest_7680 152 8 (by decide +kernel)

theorem cellTest_7680_block_20 : Interval cellTest_7680 160 168 :=
  interval_of_check cellTest_7680 160 8 (by decide +kernel)

theorem cellTest_7680_block_21 : Interval cellTest_7680 168 176 :=
  interval_of_check cellTest_7680 168 8 (by decide +kernel)

theorem cellTest_7680_block_22 : Interval cellTest_7680 176 184 :=
  interval_of_check cellTest_7680 176 8 (by decide +kernel)

theorem cellTest_7680_block_23 : Interval cellTest_7680 184 192 :=
  interval_of_check cellTest_7680 184 8 (by decide +kernel)

theorem cellTest_7680_block_24 : Interval cellTest_7680 192 200 :=
  interval_of_check cellTest_7680 192 8 (by decide +kernel)

theorem cellTest_7680_block_25 : Interval cellTest_7680 200 208 :=
  interval_of_check cellTest_7680 200 8 (by decide +kernel)

theorem cellTest_7680_block_26 : Interval cellTest_7680 208 216 :=
  interval_of_check cellTest_7680 208 8 (by decide +kernel)

theorem cellTest_7680_block_27 : Interval cellTest_7680 216 224 :=
  interval_of_check cellTest_7680 216 8 (by decide +kernel)

theorem cellTest_7680_block_28 : Interval cellTest_7680 224 232 :=
  interval_of_check cellTest_7680 224 8 (by decide +kernel)

theorem cellTest_7680_block_29 : Interval cellTest_7680 232 240 :=
  interval_of_check cellTest_7680 232 8 (by decide +kernel)

theorem cellTest_7680_block_30 : Interval cellTest_7680 240 248 :=
  interval_of_check cellTest_7680 240 8 (by decide +kernel)

theorem cellTest_7680_block_31 : Interval cellTest_7680 248 256 :=
  interval_of_check cellTest_7680 248 8 (by decide +kernel)

theorem cellTest_7680_complete : Interval cellTest_7680 0 256 :=
  (interval_append cellTest_7680 0 128 256
  (interval_append cellTest_7680 0 64 128
  (interval_append cellTest_7680 0 32 64
  (interval_append cellTest_7680 0 16 32
  (interval_append cellTest_7680 0 8 16
  cellTest_7680_block_0
  cellTest_7680_block_1)
  (interval_append cellTest_7680 16 24 32
  cellTest_7680_block_2
  cellTest_7680_block_3))
  (interval_append cellTest_7680 32 48 64
  (interval_append cellTest_7680 32 40 48
  cellTest_7680_block_4
  cellTest_7680_block_5)
  (interval_append cellTest_7680 48 56 64
  cellTest_7680_block_6
  cellTest_7680_block_7)))
  (interval_append cellTest_7680 64 96 128
  (interval_append cellTest_7680 64 80 96
  (interval_append cellTest_7680 64 72 80
  cellTest_7680_block_8
  cellTest_7680_block_9)
  (interval_append cellTest_7680 80 88 96
  cellTest_7680_block_10
  cellTest_7680_block_11))
  (interval_append cellTest_7680 96 112 128
  (interval_append cellTest_7680 96 104 112
  cellTest_7680_block_12
  cellTest_7680_block_13)
  (interval_append cellTest_7680 112 120 128
  cellTest_7680_block_14
  cellTest_7680_block_15))))
  (interval_append cellTest_7680 128 192 256
  (interval_append cellTest_7680 128 160 192
  (interval_append cellTest_7680 128 144 160
  (interval_append cellTest_7680 128 136 144
  cellTest_7680_block_16
  cellTest_7680_block_17)
  (interval_append cellTest_7680 144 152 160
  cellTest_7680_block_18
  cellTest_7680_block_19))
  (interval_append cellTest_7680 160 176 192
  (interval_append cellTest_7680 160 168 176
  cellTest_7680_block_20
  cellTest_7680_block_21)
  (interval_append cellTest_7680 176 184 192
  cellTest_7680_block_22
  cellTest_7680_block_23)))
  (interval_append cellTest_7680 192 224 256
  (interval_append cellTest_7680 192 208 224
  (interval_append cellTest_7680 192 200 208
  cellTest_7680_block_24
  cellTest_7680_block_25)
  (interval_append cellTest_7680 208 216 224
  cellTest_7680_block_26
  cellTest_7680_block_27))
  (interval_append cellTest_7680 224 240 256
  (interval_append cellTest_7680 224 232 240
  cellTest_7680_block_28
  cellTest_7680_block_29)
  (interval_append cellTest_7680 240 248 256
  cellTest_7680_block_30
  cellTest_7680_block_31)))))
theorem cellTestInterval7680 : Interval cellTest 7680 7936 := by
  intro i hlo hhi
  have h := cellTest_7680_complete (i-7680) (Nat.zero_le _) (by omega)
  simpa only [cellTest_7680, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheCells031 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_7936 (i : Nat) := cellTest (i+7936)
theorem cellTest_7936_block_0 : Interval cellTest_7936 0 8 :=
  interval_of_check cellTest_7936 0 8 (by decide +kernel)

theorem cellTest_7936_block_1 : Interval cellTest_7936 8 16 :=
  interval_of_check cellTest_7936 8 8 (by decide +kernel)

theorem cellTest_7936_block_2 : Interval cellTest_7936 16 24 :=
  interval_of_check cellTest_7936 16 8 (by decide +kernel)

theorem cellTest_7936_block_3 : Interval cellTest_7936 24 32 :=
  interval_of_check cellTest_7936 24 8 (by decide +kernel)

theorem cellTest_7936_block_4 : Interval cellTest_7936 32 40 :=
  interval_of_check cellTest_7936 32 8 (by decide +kernel)

theorem cellTest_7936_block_5 : Interval cellTest_7936 40 48 :=
  interval_of_check cellTest_7936 40 8 (by decide +kernel)

theorem cellTest_7936_block_6 : Interval cellTest_7936 48 56 :=
  interval_of_check cellTest_7936 48 8 (by decide +kernel)

theorem cellTest_7936_block_7 : Interval cellTest_7936 56 64 :=
  interval_of_check cellTest_7936 56 8 (by decide +kernel)

theorem cellTest_7936_block_8 : Interval cellTest_7936 64 72 :=
  interval_of_check cellTest_7936 64 8 (by decide +kernel)

theorem cellTest_7936_block_9 : Interval cellTest_7936 72 80 :=
  interval_of_check cellTest_7936 72 8 (by decide +kernel)

theorem cellTest_7936_block_10 : Interval cellTest_7936 80 88 :=
  interval_of_check cellTest_7936 80 8 (by decide +kernel)

theorem cellTest_7936_block_11 : Interval cellTest_7936 88 96 :=
  interval_of_check cellTest_7936 88 8 (by decide +kernel)

theorem cellTest_7936_block_12 : Interval cellTest_7936 96 104 :=
  interval_of_check cellTest_7936 96 8 (by decide +kernel)

theorem cellTest_7936_block_13 : Interval cellTest_7936 104 112 :=
  interval_of_check cellTest_7936 104 8 (by decide +kernel)

theorem cellTest_7936_block_14 : Interval cellTest_7936 112 120 :=
  interval_of_check cellTest_7936 112 8 (by decide +kernel)

theorem cellTest_7936_block_15 : Interval cellTest_7936 120 128 :=
  interval_of_check cellTest_7936 120 8 (by decide +kernel)

theorem cellTest_7936_block_16 : Interval cellTest_7936 128 136 :=
  interval_of_check cellTest_7936 128 8 (by decide +kernel)

theorem cellTest_7936_block_17 : Interval cellTest_7936 136 144 :=
  interval_of_check cellTest_7936 136 8 (by decide +kernel)

theorem cellTest_7936_block_18 : Interval cellTest_7936 144 152 :=
  interval_of_check cellTest_7936 144 8 (by decide +kernel)

theorem cellTest_7936_block_19 : Interval cellTest_7936 152 160 :=
  interval_of_check cellTest_7936 152 8 (by decide +kernel)

theorem cellTest_7936_block_20 : Interval cellTest_7936 160 168 :=
  interval_of_check cellTest_7936 160 8 (by decide +kernel)

theorem cellTest_7936_block_21 : Interval cellTest_7936 168 176 :=
  interval_of_check cellTest_7936 168 8 (by decide +kernel)

theorem cellTest_7936_block_22 : Interval cellTest_7936 176 184 :=
  interval_of_check cellTest_7936 176 8 (by decide +kernel)

theorem cellTest_7936_block_23 : Interval cellTest_7936 184 192 :=
  interval_of_check cellTest_7936 184 8 (by decide +kernel)

theorem cellTest_7936_block_24 : Interval cellTest_7936 192 200 :=
  interval_of_check cellTest_7936 192 8 (by decide +kernel)

theorem cellTest_7936_block_25 : Interval cellTest_7936 200 208 :=
  interval_of_check cellTest_7936 200 8 (by decide +kernel)

theorem cellTest_7936_block_26 : Interval cellTest_7936 208 216 :=
  interval_of_check cellTest_7936 208 8 (by decide +kernel)

theorem cellTest_7936_block_27 : Interval cellTest_7936 216 224 :=
  interval_of_check cellTest_7936 216 8 (by decide +kernel)

theorem cellTest_7936_block_28 : Interval cellTest_7936 224 232 :=
  interval_of_check cellTest_7936 224 8 (by decide +kernel)

theorem cellTest_7936_block_29 : Interval cellTest_7936 232 240 :=
  interval_of_check cellTest_7936 232 8 (by decide +kernel)

theorem cellTest_7936_block_30 : Interval cellTest_7936 240 248 :=
  interval_of_check cellTest_7936 240 8 (by decide +kernel)

theorem cellTest_7936_block_31 : Interval cellTest_7936 248 256 :=
  interval_of_check cellTest_7936 248 8 (by decide +kernel)

theorem cellTest_7936_complete : Interval cellTest_7936 0 256 :=
  (interval_append cellTest_7936 0 128 256
  (interval_append cellTest_7936 0 64 128
  (interval_append cellTest_7936 0 32 64
  (interval_append cellTest_7936 0 16 32
  (interval_append cellTest_7936 0 8 16
  cellTest_7936_block_0
  cellTest_7936_block_1)
  (interval_append cellTest_7936 16 24 32
  cellTest_7936_block_2
  cellTest_7936_block_3))
  (interval_append cellTest_7936 32 48 64
  (interval_append cellTest_7936 32 40 48
  cellTest_7936_block_4
  cellTest_7936_block_5)
  (interval_append cellTest_7936 48 56 64
  cellTest_7936_block_6
  cellTest_7936_block_7)))
  (interval_append cellTest_7936 64 96 128
  (interval_append cellTest_7936 64 80 96
  (interval_append cellTest_7936 64 72 80
  cellTest_7936_block_8
  cellTest_7936_block_9)
  (interval_append cellTest_7936 80 88 96
  cellTest_7936_block_10
  cellTest_7936_block_11))
  (interval_append cellTest_7936 96 112 128
  (interval_append cellTest_7936 96 104 112
  cellTest_7936_block_12
  cellTest_7936_block_13)
  (interval_append cellTest_7936 112 120 128
  cellTest_7936_block_14
  cellTest_7936_block_15))))
  (interval_append cellTest_7936 128 192 256
  (interval_append cellTest_7936 128 160 192
  (interval_append cellTest_7936 128 144 160
  (interval_append cellTest_7936 128 136 144
  cellTest_7936_block_16
  cellTest_7936_block_17)
  (interval_append cellTest_7936 144 152 160
  cellTest_7936_block_18
  cellTest_7936_block_19))
  (interval_append cellTest_7936 160 176 192
  (interval_append cellTest_7936 160 168 176
  cellTest_7936_block_20
  cellTest_7936_block_21)
  (interval_append cellTest_7936 176 184 192
  cellTest_7936_block_22
  cellTest_7936_block_23)))
  (interval_append cellTest_7936 192 224 256
  (interval_append cellTest_7936 192 208 224
  (interval_append cellTest_7936 192 200 208
  cellTest_7936_block_24
  cellTest_7936_block_25)
  (interval_append cellTest_7936 208 216 224
  cellTest_7936_block_26
  cellTest_7936_block_27))
  (interval_append cellTest_7936 224 240 256
  (interval_append cellTest_7936 224 232 240
  cellTest_7936_block_28
  cellTest_7936_block_29)
  (interval_append cellTest_7936 240 248 256
  cellTest_7936_block_30
  cellTest_7936_block_31)))))
theorem cellTestInterval7936 : Interval cellTest 7936 8192 := by
  intro i hlo hhi
  have h := cellTest_7936_complete (i-7936) (Nat.zero_le _) (by omega)
  simpa only [cellTest_7936, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
