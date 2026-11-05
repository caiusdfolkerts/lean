module
prelude
public import RootedSixExtra01GrowthCacheData

/- RootedSixExtra01GrowthCacheCells000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_0 (i : Nat) := cellTest (i+0)
theorem cellTest_0_block_0 : Interval cellTest_0 0 8 :=
  interval_of_check cellTest_0 0 8 (by decide +kernel)

theorem cellTest_0_block_1 : Interval cellTest_0 8 16 :=
  interval_of_check cellTest_0 8 8 (by decide +kernel)

theorem cellTest_0_block_2 : Interval cellTest_0 16 24 :=
  interval_of_check cellTest_0 16 8 (by decide +kernel)

theorem cellTest_0_block_3 : Interval cellTest_0 24 32 :=
  interval_of_check cellTest_0 24 8 (by decide +kernel)

theorem cellTest_0_block_4 : Interval cellTest_0 32 40 :=
  interval_of_check cellTest_0 32 8 (by decide +kernel)

theorem cellTest_0_block_5 : Interval cellTest_0 40 48 :=
  interval_of_check cellTest_0 40 8 (by decide +kernel)

theorem cellTest_0_block_6 : Interval cellTest_0 48 56 :=
  interval_of_check cellTest_0 48 8 (by decide +kernel)

theorem cellTest_0_block_7 : Interval cellTest_0 56 64 :=
  interval_of_check cellTest_0 56 8 (by decide +kernel)

theorem cellTest_0_block_8 : Interval cellTest_0 64 72 :=
  interval_of_check cellTest_0 64 8 (by decide +kernel)

theorem cellTest_0_block_9 : Interval cellTest_0 72 80 :=
  interval_of_check cellTest_0 72 8 (by decide +kernel)

theorem cellTest_0_block_10 : Interval cellTest_0 80 88 :=
  interval_of_check cellTest_0 80 8 (by decide +kernel)

theorem cellTest_0_block_11 : Interval cellTest_0 88 96 :=
  interval_of_check cellTest_0 88 8 (by decide +kernel)

theorem cellTest_0_block_12 : Interval cellTest_0 96 104 :=
  interval_of_check cellTest_0 96 8 (by decide +kernel)

theorem cellTest_0_block_13 : Interval cellTest_0 104 112 :=
  interval_of_check cellTest_0 104 8 (by decide +kernel)

theorem cellTest_0_block_14 : Interval cellTest_0 112 120 :=
  interval_of_check cellTest_0 112 8 (by decide +kernel)

theorem cellTest_0_block_15 : Interval cellTest_0 120 128 :=
  interval_of_check cellTest_0 120 8 (by decide +kernel)

theorem cellTest_0_block_16 : Interval cellTest_0 128 136 :=
  interval_of_check cellTest_0 128 8 (by decide +kernel)

theorem cellTest_0_block_17 : Interval cellTest_0 136 144 :=
  interval_of_check cellTest_0 136 8 (by decide +kernel)

theorem cellTest_0_block_18 : Interval cellTest_0 144 152 :=
  interval_of_check cellTest_0 144 8 (by decide +kernel)

theorem cellTest_0_block_19 : Interval cellTest_0 152 160 :=
  interval_of_check cellTest_0 152 8 (by decide +kernel)

theorem cellTest_0_block_20 : Interval cellTest_0 160 168 :=
  interval_of_check cellTest_0 160 8 (by decide +kernel)

theorem cellTest_0_block_21 : Interval cellTest_0 168 176 :=
  interval_of_check cellTest_0 168 8 (by decide +kernel)

theorem cellTest_0_block_22 : Interval cellTest_0 176 184 :=
  interval_of_check cellTest_0 176 8 (by decide +kernel)

theorem cellTest_0_block_23 : Interval cellTest_0 184 192 :=
  interval_of_check cellTest_0 184 8 (by decide +kernel)

theorem cellTest_0_block_24 : Interval cellTest_0 192 200 :=
  interval_of_check cellTest_0 192 8 (by decide +kernel)

theorem cellTest_0_block_25 : Interval cellTest_0 200 208 :=
  interval_of_check cellTest_0 200 8 (by decide +kernel)

theorem cellTest_0_block_26 : Interval cellTest_0 208 216 :=
  interval_of_check cellTest_0 208 8 (by decide +kernel)

theorem cellTest_0_block_27 : Interval cellTest_0 216 224 :=
  interval_of_check cellTest_0 216 8 (by decide +kernel)

theorem cellTest_0_block_28 : Interval cellTest_0 224 232 :=
  interval_of_check cellTest_0 224 8 (by decide +kernel)

theorem cellTest_0_block_29 : Interval cellTest_0 232 240 :=
  interval_of_check cellTest_0 232 8 (by decide +kernel)

theorem cellTest_0_block_30 : Interval cellTest_0 240 248 :=
  interval_of_check cellTest_0 240 8 (by decide +kernel)

theorem cellTest_0_block_31 : Interval cellTest_0 248 256 :=
  interval_of_check cellTest_0 248 8 (by decide +kernel)

theorem cellTest_0_complete : Interval cellTest_0 0 256 :=
  (interval_append cellTest_0 0 128 256
  (interval_append cellTest_0 0 64 128
  (interval_append cellTest_0 0 32 64
  (interval_append cellTest_0 0 16 32
  (interval_append cellTest_0 0 8 16
  cellTest_0_block_0
  cellTest_0_block_1)
  (interval_append cellTest_0 16 24 32
  cellTest_0_block_2
  cellTest_0_block_3))
  (interval_append cellTest_0 32 48 64
  (interval_append cellTest_0 32 40 48
  cellTest_0_block_4
  cellTest_0_block_5)
  (interval_append cellTest_0 48 56 64
  cellTest_0_block_6
  cellTest_0_block_7)))
  (interval_append cellTest_0 64 96 128
  (interval_append cellTest_0 64 80 96
  (interval_append cellTest_0 64 72 80
  cellTest_0_block_8
  cellTest_0_block_9)
  (interval_append cellTest_0 80 88 96
  cellTest_0_block_10
  cellTest_0_block_11))
  (interval_append cellTest_0 96 112 128
  (interval_append cellTest_0 96 104 112
  cellTest_0_block_12
  cellTest_0_block_13)
  (interval_append cellTest_0 112 120 128
  cellTest_0_block_14
  cellTest_0_block_15))))
  (interval_append cellTest_0 128 192 256
  (interval_append cellTest_0 128 160 192
  (interval_append cellTest_0 128 144 160
  (interval_append cellTest_0 128 136 144
  cellTest_0_block_16
  cellTest_0_block_17)
  (interval_append cellTest_0 144 152 160
  cellTest_0_block_18
  cellTest_0_block_19))
  (interval_append cellTest_0 160 176 192
  (interval_append cellTest_0 160 168 176
  cellTest_0_block_20
  cellTest_0_block_21)
  (interval_append cellTest_0 176 184 192
  cellTest_0_block_22
  cellTest_0_block_23)))
  (interval_append cellTest_0 192 224 256
  (interval_append cellTest_0 192 208 224
  (interval_append cellTest_0 192 200 208
  cellTest_0_block_24
  cellTest_0_block_25)
  (interval_append cellTest_0 208 216 224
  cellTest_0_block_26
  cellTest_0_block_27))
  (interval_append cellTest_0 224 240 256
  (interval_append cellTest_0 224 232 240
  cellTest_0_block_28
  cellTest_0_block_29)
  (interval_append cellTest_0 240 248 256
  cellTest_0_block_30
  cellTest_0_block_31)))))
theorem cellTestInterval0 : Interval cellTest 0 256 := by
  intro i hlo hhi
  have h := cellTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [cellTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_256 (i : Nat) := cellTest (i+256)
theorem cellTest_256_block_0 : Interval cellTest_256 0 8 :=
  interval_of_check cellTest_256 0 8 (by decide +kernel)

theorem cellTest_256_block_1 : Interval cellTest_256 8 16 :=
  interval_of_check cellTest_256 8 8 (by decide +kernel)

theorem cellTest_256_block_2 : Interval cellTest_256 16 24 :=
  interval_of_check cellTest_256 16 8 (by decide +kernel)

theorem cellTest_256_block_3 : Interval cellTest_256 24 32 :=
  interval_of_check cellTest_256 24 8 (by decide +kernel)

theorem cellTest_256_block_4 : Interval cellTest_256 32 40 :=
  interval_of_check cellTest_256 32 8 (by decide +kernel)

theorem cellTest_256_block_5 : Interval cellTest_256 40 48 :=
  interval_of_check cellTest_256 40 8 (by decide +kernel)

theorem cellTest_256_block_6 : Interval cellTest_256 48 56 :=
  interval_of_check cellTest_256 48 8 (by decide +kernel)

theorem cellTest_256_block_7 : Interval cellTest_256 56 64 :=
  interval_of_check cellTest_256 56 8 (by decide +kernel)

theorem cellTest_256_block_8 : Interval cellTest_256 64 72 :=
  interval_of_check cellTest_256 64 8 (by decide +kernel)

theorem cellTest_256_block_9 : Interval cellTest_256 72 80 :=
  interval_of_check cellTest_256 72 8 (by decide +kernel)

theorem cellTest_256_block_10 : Interval cellTest_256 80 88 :=
  interval_of_check cellTest_256 80 8 (by decide +kernel)

theorem cellTest_256_block_11 : Interval cellTest_256 88 96 :=
  interval_of_check cellTest_256 88 8 (by decide +kernel)

theorem cellTest_256_block_12 : Interval cellTest_256 96 104 :=
  interval_of_check cellTest_256 96 8 (by decide +kernel)

theorem cellTest_256_block_13 : Interval cellTest_256 104 112 :=
  interval_of_check cellTest_256 104 8 (by decide +kernel)

theorem cellTest_256_block_14 : Interval cellTest_256 112 120 :=
  interval_of_check cellTest_256 112 8 (by decide +kernel)

theorem cellTest_256_block_15 : Interval cellTest_256 120 128 :=
  interval_of_check cellTest_256 120 8 (by decide +kernel)

theorem cellTest_256_block_16 : Interval cellTest_256 128 136 :=
  interval_of_check cellTest_256 128 8 (by decide +kernel)

theorem cellTest_256_block_17 : Interval cellTest_256 136 144 :=
  interval_of_check cellTest_256 136 8 (by decide +kernel)

theorem cellTest_256_block_18 : Interval cellTest_256 144 152 :=
  interval_of_check cellTest_256 144 8 (by decide +kernel)

theorem cellTest_256_block_19 : Interval cellTest_256 152 160 :=
  interval_of_check cellTest_256 152 8 (by decide +kernel)

theorem cellTest_256_block_20 : Interval cellTest_256 160 168 :=
  interval_of_check cellTest_256 160 8 (by decide +kernel)

theorem cellTest_256_block_21 : Interval cellTest_256 168 176 :=
  interval_of_check cellTest_256 168 8 (by decide +kernel)

theorem cellTest_256_block_22 : Interval cellTest_256 176 184 :=
  interval_of_check cellTest_256 176 8 (by decide +kernel)

theorem cellTest_256_block_23 : Interval cellTest_256 184 192 :=
  interval_of_check cellTest_256 184 8 (by decide +kernel)

theorem cellTest_256_block_24 : Interval cellTest_256 192 200 :=
  interval_of_check cellTest_256 192 8 (by decide +kernel)

theorem cellTest_256_block_25 : Interval cellTest_256 200 208 :=
  interval_of_check cellTest_256 200 8 (by decide +kernel)

theorem cellTest_256_block_26 : Interval cellTest_256 208 216 :=
  interval_of_check cellTest_256 208 8 (by decide +kernel)

theorem cellTest_256_block_27 : Interval cellTest_256 216 224 :=
  interval_of_check cellTest_256 216 8 (by decide +kernel)

theorem cellTest_256_block_28 : Interval cellTest_256 224 232 :=
  interval_of_check cellTest_256 224 8 (by decide +kernel)

theorem cellTest_256_block_29 : Interval cellTest_256 232 240 :=
  interval_of_check cellTest_256 232 8 (by decide +kernel)

theorem cellTest_256_block_30 : Interval cellTest_256 240 248 :=
  interval_of_check cellTest_256 240 8 (by decide +kernel)

theorem cellTest_256_block_31 : Interval cellTest_256 248 256 :=
  interval_of_check cellTest_256 248 8 (by decide +kernel)

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
theorem cellTestInterval256 : Interval cellTest 256 512 := by
  intro i hlo hhi
  have h := cellTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [cellTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_512 (i : Nat) := cellTest (i+512)
theorem cellTest_512_block_0 : Interval cellTest_512 0 8 :=
  interval_of_check cellTest_512 0 8 (by decide +kernel)

theorem cellTest_512_block_1 : Interval cellTest_512 8 16 :=
  interval_of_check cellTest_512 8 8 (by decide +kernel)

theorem cellTest_512_block_2 : Interval cellTest_512 16 24 :=
  interval_of_check cellTest_512 16 8 (by decide +kernel)

theorem cellTest_512_block_3 : Interval cellTest_512 24 32 :=
  interval_of_check cellTest_512 24 8 (by decide +kernel)

theorem cellTest_512_block_4 : Interval cellTest_512 32 40 :=
  interval_of_check cellTest_512 32 8 (by decide +kernel)

theorem cellTest_512_block_5 : Interval cellTest_512 40 48 :=
  interval_of_check cellTest_512 40 8 (by decide +kernel)

theorem cellTest_512_block_6 : Interval cellTest_512 48 56 :=
  interval_of_check cellTest_512 48 8 (by decide +kernel)

theorem cellTest_512_block_7 : Interval cellTest_512 56 64 :=
  interval_of_check cellTest_512 56 8 (by decide +kernel)

theorem cellTest_512_block_8 : Interval cellTest_512 64 72 :=
  interval_of_check cellTest_512 64 8 (by decide +kernel)

theorem cellTest_512_block_9 : Interval cellTest_512 72 80 :=
  interval_of_check cellTest_512 72 8 (by decide +kernel)

theorem cellTest_512_block_10 : Interval cellTest_512 80 88 :=
  interval_of_check cellTest_512 80 8 (by decide +kernel)

theorem cellTest_512_block_11 : Interval cellTest_512 88 96 :=
  interval_of_check cellTest_512 88 8 (by decide +kernel)

theorem cellTest_512_block_12 : Interval cellTest_512 96 104 :=
  interval_of_check cellTest_512 96 8 (by decide +kernel)

theorem cellTest_512_block_13 : Interval cellTest_512 104 112 :=
  interval_of_check cellTest_512 104 8 (by decide +kernel)

theorem cellTest_512_block_14 : Interval cellTest_512 112 120 :=
  interval_of_check cellTest_512 112 8 (by decide +kernel)

theorem cellTest_512_block_15 : Interval cellTest_512 120 128 :=
  interval_of_check cellTest_512 120 8 (by decide +kernel)

theorem cellTest_512_block_16 : Interval cellTest_512 128 136 :=
  interval_of_check cellTest_512 128 8 (by decide +kernel)

theorem cellTest_512_block_17 : Interval cellTest_512 136 144 :=
  interval_of_check cellTest_512 136 8 (by decide +kernel)

theorem cellTest_512_block_18 : Interval cellTest_512 144 152 :=
  interval_of_check cellTest_512 144 8 (by decide +kernel)

theorem cellTest_512_block_19 : Interval cellTest_512 152 160 :=
  interval_of_check cellTest_512 152 8 (by decide +kernel)

theorem cellTest_512_block_20 : Interval cellTest_512 160 168 :=
  interval_of_check cellTest_512 160 8 (by decide +kernel)

theorem cellTest_512_block_21 : Interval cellTest_512 168 176 :=
  interval_of_check cellTest_512 168 8 (by decide +kernel)

theorem cellTest_512_block_22 : Interval cellTest_512 176 184 :=
  interval_of_check cellTest_512 176 8 (by decide +kernel)

theorem cellTest_512_block_23 : Interval cellTest_512 184 192 :=
  interval_of_check cellTest_512 184 8 (by decide +kernel)

theorem cellTest_512_block_24 : Interval cellTest_512 192 200 :=
  interval_of_check cellTest_512 192 8 (by decide +kernel)

theorem cellTest_512_block_25 : Interval cellTest_512 200 208 :=
  interval_of_check cellTest_512 200 8 (by decide +kernel)

theorem cellTest_512_block_26 : Interval cellTest_512 208 216 :=
  interval_of_check cellTest_512 208 8 (by decide +kernel)

theorem cellTest_512_block_27 : Interval cellTest_512 216 224 :=
  interval_of_check cellTest_512 216 8 (by decide +kernel)

theorem cellTest_512_block_28 : Interval cellTest_512 224 232 :=
  interval_of_check cellTest_512 224 8 (by decide +kernel)

theorem cellTest_512_block_29 : Interval cellTest_512 232 240 :=
  interval_of_check cellTest_512 232 8 (by decide +kernel)

theorem cellTest_512_block_30 : Interval cellTest_512 240 248 :=
  interval_of_check cellTest_512 240 8 (by decide +kernel)

theorem cellTest_512_block_31 : Interval cellTest_512 248 256 :=
  interval_of_check cellTest_512 248 8 (by decide +kernel)

theorem cellTest_512_complete : Interval cellTest_512 0 256 :=
  (interval_append cellTest_512 0 128 256
  (interval_append cellTest_512 0 64 128
  (interval_append cellTest_512 0 32 64
  (interval_append cellTest_512 0 16 32
  (interval_append cellTest_512 0 8 16
  cellTest_512_block_0
  cellTest_512_block_1)
  (interval_append cellTest_512 16 24 32
  cellTest_512_block_2
  cellTest_512_block_3))
  (interval_append cellTest_512 32 48 64
  (interval_append cellTest_512 32 40 48
  cellTest_512_block_4
  cellTest_512_block_5)
  (interval_append cellTest_512 48 56 64
  cellTest_512_block_6
  cellTest_512_block_7)))
  (interval_append cellTest_512 64 96 128
  (interval_append cellTest_512 64 80 96
  (interval_append cellTest_512 64 72 80
  cellTest_512_block_8
  cellTest_512_block_9)
  (interval_append cellTest_512 80 88 96
  cellTest_512_block_10
  cellTest_512_block_11))
  (interval_append cellTest_512 96 112 128
  (interval_append cellTest_512 96 104 112
  cellTest_512_block_12
  cellTest_512_block_13)
  (interval_append cellTest_512 112 120 128
  cellTest_512_block_14
  cellTest_512_block_15))))
  (interval_append cellTest_512 128 192 256
  (interval_append cellTest_512 128 160 192
  (interval_append cellTest_512 128 144 160
  (interval_append cellTest_512 128 136 144
  cellTest_512_block_16
  cellTest_512_block_17)
  (interval_append cellTest_512 144 152 160
  cellTest_512_block_18
  cellTest_512_block_19))
  (interval_append cellTest_512 160 176 192
  (interval_append cellTest_512 160 168 176
  cellTest_512_block_20
  cellTest_512_block_21)
  (interval_append cellTest_512 176 184 192
  cellTest_512_block_22
  cellTest_512_block_23)))
  (interval_append cellTest_512 192 224 256
  (interval_append cellTest_512 192 208 224
  (interval_append cellTest_512 192 200 208
  cellTest_512_block_24
  cellTest_512_block_25)
  (interval_append cellTest_512 208 216 224
  cellTest_512_block_26
  cellTest_512_block_27))
  (interval_append cellTest_512 224 240 256
  (interval_append cellTest_512 224 232 240
  cellTest_512_block_28
  cellTest_512_block_29)
  (interval_append cellTest_512 240 248 256
  cellTest_512_block_30
  cellTest_512_block_31)))))
theorem cellTestInterval512 : Interval cellTest 512 768 := by
  intro i hlo hhi
  have h := cellTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [cellTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_768 (i : Nat) := cellTest (i+768)
theorem cellTest_768_block_0 : Interval cellTest_768 0 8 :=
  interval_of_check cellTest_768 0 8 (by decide +kernel)

theorem cellTest_768_block_1 : Interval cellTest_768 8 16 :=
  interval_of_check cellTest_768 8 8 (by decide +kernel)

theorem cellTest_768_block_2 : Interval cellTest_768 16 24 :=
  interval_of_check cellTest_768 16 8 (by decide +kernel)

theorem cellTest_768_block_3 : Interval cellTest_768 24 32 :=
  interval_of_check cellTest_768 24 8 (by decide +kernel)

theorem cellTest_768_block_4 : Interval cellTest_768 32 40 :=
  interval_of_check cellTest_768 32 8 (by decide +kernel)

theorem cellTest_768_block_5 : Interval cellTest_768 40 48 :=
  interval_of_check cellTest_768 40 8 (by decide +kernel)

theorem cellTest_768_block_6 : Interval cellTest_768 48 56 :=
  interval_of_check cellTest_768 48 8 (by decide +kernel)

theorem cellTest_768_block_7 : Interval cellTest_768 56 64 :=
  interval_of_check cellTest_768 56 8 (by decide +kernel)

theorem cellTest_768_block_8 : Interval cellTest_768 64 72 :=
  interval_of_check cellTest_768 64 8 (by decide +kernel)

theorem cellTest_768_block_9 : Interval cellTest_768 72 80 :=
  interval_of_check cellTest_768 72 8 (by decide +kernel)

theorem cellTest_768_block_10 : Interval cellTest_768 80 88 :=
  interval_of_check cellTest_768 80 8 (by decide +kernel)

theorem cellTest_768_block_11 : Interval cellTest_768 88 96 :=
  interval_of_check cellTest_768 88 8 (by decide +kernel)

theorem cellTest_768_block_12 : Interval cellTest_768 96 104 :=
  interval_of_check cellTest_768 96 8 (by decide +kernel)

theorem cellTest_768_block_13 : Interval cellTest_768 104 112 :=
  interval_of_check cellTest_768 104 8 (by decide +kernel)

theorem cellTest_768_block_14 : Interval cellTest_768 112 120 :=
  interval_of_check cellTest_768 112 8 (by decide +kernel)

theorem cellTest_768_block_15 : Interval cellTest_768 120 128 :=
  interval_of_check cellTest_768 120 8 (by decide +kernel)

theorem cellTest_768_block_16 : Interval cellTest_768 128 136 :=
  interval_of_check cellTest_768 128 8 (by decide +kernel)

theorem cellTest_768_block_17 : Interval cellTest_768 136 144 :=
  interval_of_check cellTest_768 136 8 (by decide +kernel)

theorem cellTest_768_block_18 : Interval cellTest_768 144 152 :=
  interval_of_check cellTest_768 144 8 (by decide +kernel)

theorem cellTest_768_block_19 : Interval cellTest_768 152 160 :=
  interval_of_check cellTest_768 152 8 (by decide +kernel)

theorem cellTest_768_block_20 : Interval cellTest_768 160 168 :=
  interval_of_check cellTest_768 160 8 (by decide +kernel)

theorem cellTest_768_block_21 : Interval cellTest_768 168 176 :=
  interval_of_check cellTest_768 168 8 (by decide +kernel)

theorem cellTest_768_block_22 : Interval cellTest_768 176 184 :=
  interval_of_check cellTest_768 176 8 (by decide +kernel)

theorem cellTest_768_block_23 : Interval cellTest_768 184 192 :=
  interval_of_check cellTest_768 184 8 (by decide +kernel)

theorem cellTest_768_block_24 : Interval cellTest_768 192 200 :=
  interval_of_check cellTest_768 192 8 (by decide +kernel)

theorem cellTest_768_block_25 : Interval cellTest_768 200 208 :=
  interval_of_check cellTest_768 200 8 (by decide +kernel)

theorem cellTest_768_block_26 : Interval cellTest_768 208 216 :=
  interval_of_check cellTest_768 208 8 (by decide +kernel)

theorem cellTest_768_block_27 : Interval cellTest_768 216 224 :=
  interval_of_check cellTest_768 216 8 (by decide +kernel)

theorem cellTest_768_block_28 : Interval cellTest_768 224 232 :=
  interval_of_check cellTest_768 224 8 (by decide +kernel)

theorem cellTest_768_block_29 : Interval cellTest_768 232 240 :=
  interval_of_check cellTest_768 232 8 (by decide +kernel)

theorem cellTest_768_block_30 : Interval cellTest_768 240 248 :=
  interval_of_check cellTest_768 240 8 (by decide +kernel)

theorem cellTest_768_block_31 : Interval cellTest_768 248 256 :=
  interval_of_check cellTest_768 248 8 (by decide +kernel)

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

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_1024 (i : Nat) := cellTest (i+1024)
theorem cellTest_1024_block_0 : Interval cellTest_1024 0 8 :=
  interval_of_check cellTest_1024 0 8 (by decide +kernel)

theorem cellTest_1024_block_1 : Interval cellTest_1024 8 16 :=
  interval_of_check cellTest_1024 8 8 (by decide +kernel)

theorem cellTest_1024_block_2 : Interval cellTest_1024 16 24 :=
  interval_of_check cellTest_1024 16 8 (by decide +kernel)

theorem cellTest_1024_block_3 : Interval cellTest_1024 24 32 :=
  interval_of_check cellTest_1024 24 8 (by decide +kernel)

theorem cellTest_1024_block_4 : Interval cellTest_1024 32 40 :=
  interval_of_check cellTest_1024 32 8 (by decide +kernel)

theorem cellTest_1024_block_5 : Interval cellTest_1024 40 48 :=
  interval_of_check cellTest_1024 40 8 (by decide +kernel)

theorem cellTest_1024_block_6 : Interval cellTest_1024 48 56 :=
  interval_of_check cellTest_1024 48 8 (by decide +kernel)

theorem cellTest_1024_block_7 : Interval cellTest_1024 56 64 :=
  interval_of_check cellTest_1024 56 8 (by decide +kernel)

theorem cellTest_1024_block_8 : Interval cellTest_1024 64 72 :=
  interval_of_check cellTest_1024 64 8 (by decide +kernel)

theorem cellTest_1024_block_9 : Interval cellTest_1024 72 80 :=
  interval_of_check cellTest_1024 72 8 (by decide +kernel)

theorem cellTest_1024_block_10 : Interval cellTest_1024 80 88 :=
  interval_of_check cellTest_1024 80 8 (by decide +kernel)

theorem cellTest_1024_block_11 : Interval cellTest_1024 88 96 :=
  interval_of_check cellTest_1024 88 8 (by decide +kernel)

theorem cellTest_1024_block_12 : Interval cellTest_1024 96 104 :=
  interval_of_check cellTest_1024 96 8 (by decide +kernel)

theorem cellTest_1024_block_13 : Interval cellTest_1024 104 112 :=
  interval_of_check cellTest_1024 104 8 (by decide +kernel)

theorem cellTest_1024_block_14 : Interval cellTest_1024 112 120 :=
  interval_of_check cellTest_1024 112 8 (by decide +kernel)

theorem cellTest_1024_block_15 : Interval cellTest_1024 120 128 :=
  interval_of_check cellTest_1024 120 8 (by decide +kernel)

theorem cellTest_1024_block_16 : Interval cellTest_1024 128 136 :=
  interval_of_check cellTest_1024 128 8 (by decide +kernel)

theorem cellTest_1024_block_17 : Interval cellTest_1024 136 144 :=
  interval_of_check cellTest_1024 136 8 (by decide +kernel)

theorem cellTest_1024_block_18 : Interval cellTest_1024 144 152 :=
  interval_of_check cellTest_1024 144 8 (by decide +kernel)

theorem cellTest_1024_block_19 : Interval cellTest_1024 152 160 :=
  interval_of_check cellTest_1024 152 8 (by decide +kernel)

theorem cellTest_1024_block_20 : Interval cellTest_1024 160 168 :=
  interval_of_check cellTest_1024 160 8 (by decide +kernel)

theorem cellTest_1024_block_21 : Interval cellTest_1024 168 176 :=
  interval_of_check cellTest_1024 168 8 (by decide +kernel)

theorem cellTest_1024_block_22 : Interval cellTest_1024 176 184 :=
  interval_of_check cellTest_1024 176 8 (by decide +kernel)

theorem cellTest_1024_block_23 : Interval cellTest_1024 184 192 :=
  interval_of_check cellTest_1024 184 8 (by decide +kernel)

theorem cellTest_1024_block_24 : Interval cellTest_1024 192 200 :=
  interval_of_check cellTest_1024 192 8 (by decide +kernel)

theorem cellTest_1024_block_25 : Interval cellTest_1024 200 208 :=
  interval_of_check cellTest_1024 200 8 (by decide +kernel)

theorem cellTest_1024_block_26 : Interval cellTest_1024 208 216 :=
  interval_of_check cellTest_1024 208 8 (by decide +kernel)

theorem cellTest_1024_block_27 : Interval cellTest_1024 216 224 :=
  interval_of_check cellTest_1024 216 8 (by decide +kernel)

theorem cellTest_1024_block_28 : Interval cellTest_1024 224 232 :=
  interval_of_check cellTest_1024 224 8 (by decide +kernel)

theorem cellTest_1024_block_29 : Interval cellTest_1024 232 240 :=
  interval_of_check cellTest_1024 232 8 (by decide +kernel)

theorem cellTest_1024_block_30 : Interval cellTest_1024 240 248 :=
  interval_of_check cellTest_1024 240 8 (by decide +kernel)

theorem cellTest_1024_block_31 : Interval cellTest_1024 248 256 :=
  interval_of_check cellTest_1024 248 8 (by decide +kernel)

theorem cellTest_1024_complete : Interval cellTest_1024 0 256 :=
  (interval_append cellTest_1024 0 128 256
  (interval_append cellTest_1024 0 64 128
  (interval_append cellTest_1024 0 32 64
  (interval_append cellTest_1024 0 16 32
  (interval_append cellTest_1024 0 8 16
  cellTest_1024_block_0
  cellTest_1024_block_1)
  (interval_append cellTest_1024 16 24 32
  cellTest_1024_block_2
  cellTest_1024_block_3))
  (interval_append cellTest_1024 32 48 64
  (interval_append cellTest_1024 32 40 48
  cellTest_1024_block_4
  cellTest_1024_block_5)
  (interval_append cellTest_1024 48 56 64
  cellTest_1024_block_6
  cellTest_1024_block_7)))
  (interval_append cellTest_1024 64 96 128
  (interval_append cellTest_1024 64 80 96
  (interval_append cellTest_1024 64 72 80
  cellTest_1024_block_8
  cellTest_1024_block_9)
  (interval_append cellTest_1024 80 88 96
  cellTest_1024_block_10
  cellTest_1024_block_11))
  (interval_append cellTest_1024 96 112 128
  (interval_append cellTest_1024 96 104 112
  cellTest_1024_block_12
  cellTest_1024_block_13)
  (interval_append cellTest_1024 112 120 128
  cellTest_1024_block_14
  cellTest_1024_block_15))))
  (interval_append cellTest_1024 128 192 256
  (interval_append cellTest_1024 128 160 192
  (interval_append cellTest_1024 128 144 160
  (interval_append cellTest_1024 128 136 144
  cellTest_1024_block_16
  cellTest_1024_block_17)
  (interval_append cellTest_1024 144 152 160
  cellTest_1024_block_18
  cellTest_1024_block_19))
  (interval_append cellTest_1024 160 176 192
  (interval_append cellTest_1024 160 168 176
  cellTest_1024_block_20
  cellTest_1024_block_21)
  (interval_append cellTest_1024 176 184 192
  cellTest_1024_block_22
  cellTest_1024_block_23)))
  (interval_append cellTest_1024 192 224 256
  (interval_append cellTest_1024 192 208 224
  (interval_append cellTest_1024 192 200 208
  cellTest_1024_block_24
  cellTest_1024_block_25)
  (interval_append cellTest_1024 208 216 224
  cellTest_1024_block_26
  cellTest_1024_block_27))
  (interval_append cellTest_1024 224 240 256
  (interval_append cellTest_1024 224 232 240
  cellTest_1024_block_28
  cellTest_1024_block_29)
  (interval_append cellTest_1024 240 248 256
  cellTest_1024_block_30
  cellTest_1024_block_31)))))
theorem cellTestInterval1024 : Interval cellTest 1024 1280 := by
  intro i hlo hhi
  have h := cellTest_1024_complete (i-1024) (Nat.zero_le _) (by omega)
  simpa only [cellTest_1024, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_1280 (i : Nat) := cellTest (i+1280)
theorem cellTest_1280_block_0 : Interval cellTest_1280 0 8 :=
  interval_of_check cellTest_1280 0 8 (by decide +kernel)

theorem cellTest_1280_block_1 : Interval cellTest_1280 8 16 :=
  interval_of_check cellTest_1280 8 8 (by decide +kernel)

theorem cellTest_1280_block_2 : Interval cellTest_1280 16 24 :=
  interval_of_check cellTest_1280 16 8 (by decide +kernel)

theorem cellTest_1280_block_3 : Interval cellTest_1280 24 32 :=
  interval_of_check cellTest_1280 24 8 (by decide +kernel)

theorem cellTest_1280_block_4 : Interval cellTest_1280 32 40 :=
  interval_of_check cellTest_1280 32 8 (by decide +kernel)

theorem cellTest_1280_block_5 : Interval cellTest_1280 40 48 :=
  interval_of_check cellTest_1280 40 8 (by decide +kernel)

theorem cellTest_1280_block_6 : Interval cellTest_1280 48 56 :=
  interval_of_check cellTest_1280 48 8 (by decide +kernel)

theorem cellTest_1280_block_7 : Interval cellTest_1280 56 64 :=
  interval_of_check cellTest_1280 56 8 (by decide +kernel)

theorem cellTest_1280_block_8 : Interval cellTest_1280 64 72 :=
  interval_of_check cellTest_1280 64 8 (by decide +kernel)

theorem cellTest_1280_block_9 : Interval cellTest_1280 72 80 :=
  interval_of_check cellTest_1280 72 8 (by decide +kernel)

theorem cellTest_1280_block_10 : Interval cellTest_1280 80 88 :=
  interval_of_check cellTest_1280 80 8 (by decide +kernel)

theorem cellTest_1280_block_11 : Interval cellTest_1280 88 96 :=
  interval_of_check cellTest_1280 88 8 (by decide +kernel)

theorem cellTest_1280_block_12 : Interval cellTest_1280 96 104 :=
  interval_of_check cellTest_1280 96 8 (by decide +kernel)

theorem cellTest_1280_block_13 : Interval cellTest_1280 104 112 :=
  interval_of_check cellTest_1280 104 8 (by decide +kernel)

theorem cellTest_1280_block_14 : Interval cellTest_1280 112 120 :=
  interval_of_check cellTest_1280 112 8 (by decide +kernel)

theorem cellTest_1280_block_15 : Interval cellTest_1280 120 128 :=
  interval_of_check cellTest_1280 120 8 (by decide +kernel)

theorem cellTest_1280_block_16 : Interval cellTest_1280 128 136 :=
  interval_of_check cellTest_1280 128 8 (by decide +kernel)

theorem cellTest_1280_block_17 : Interval cellTest_1280 136 144 :=
  interval_of_check cellTest_1280 136 8 (by decide +kernel)

theorem cellTest_1280_block_18 : Interval cellTest_1280 144 152 :=
  interval_of_check cellTest_1280 144 8 (by decide +kernel)

theorem cellTest_1280_block_19 : Interval cellTest_1280 152 160 :=
  interval_of_check cellTest_1280 152 8 (by decide +kernel)

theorem cellTest_1280_block_20 : Interval cellTest_1280 160 168 :=
  interval_of_check cellTest_1280 160 8 (by decide +kernel)

theorem cellTest_1280_block_21 : Interval cellTest_1280 168 176 :=
  interval_of_check cellTest_1280 168 8 (by decide +kernel)

theorem cellTest_1280_block_22 : Interval cellTest_1280 176 184 :=
  interval_of_check cellTest_1280 176 8 (by decide +kernel)

theorem cellTest_1280_block_23 : Interval cellTest_1280 184 192 :=
  interval_of_check cellTest_1280 184 8 (by decide +kernel)

theorem cellTest_1280_block_24 : Interval cellTest_1280 192 200 :=
  interval_of_check cellTest_1280 192 8 (by decide +kernel)

theorem cellTest_1280_block_25 : Interval cellTest_1280 200 208 :=
  interval_of_check cellTest_1280 200 8 (by decide +kernel)

theorem cellTest_1280_block_26 : Interval cellTest_1280 208 216 :=
  interval_of_check cellTest_1280 208 8 (by decide +kernel)

theorem cellTest_1280_block_27 : Interval cellTest_1280 216 224 :=
  interval_of_check cellTest_1280 216 8 (by decide +kernel)

theorem cellTest_1280_block_28 : Interval cellTest_1280 224 232 :=
  interval_of_check cellTest_1280 224 8 (by decide +kernel)

theorem cellTest_1280_block_29 : Interval cellTest_1280 232 240 :=
  interval_of_check cellTest_1280 232 8 (by decide +kernel)

theorem cellTest_1280_block_30 : Interval cellTest_1280 240 248 :=
  interval_of_check cellTest_1280 240 8 (by decide +kernel)

theorem cellTest_1280_block_31 : Interval cellTest_1280 248 256 :=
  interval_of_check cellTest_1280 248 8 (by decide +kernel)

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

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_1536 (i : Nat) := cellTest (i+1536)
theorem cellTest_1536_block_0 : Interval cellTest_1536 0 8 :=
  interval_of_check cellTest_1536 0 8 (by decide +kernel)

theorem cellTest_1536_block_1 : Interval cellTest_1536 8 16 :=
  interval_of_check cellTest_1536 8 8 (by decide +kernel)

theorem cellTest_1536_block_2 : Interval cellTest_1536 16 24 :=
  interval_of_check cellTest_1536 16 8 (by decide +kernel)

theorem cellTest_1536_block_3 : Interval cellTest_1536 24 32 :=
  interval_of_check cellTest_1536 24 8 (by decide +kernel)

theorem cellTest_1536_block_4 : Interval cellTest_1536 32 40 :=
  interval_of_check cellTest_1536 32 8 (by decide +kernel)

theorem cellTest_1536_block_5 : Interval cellTest_1536 40 48 :=
  interval_of_check cellTest_1536 40 8 (by decide +kernel)

theorem cellTest_1536_block_6 : Interval cellTest_1536 48 56 :=
  interval_of_check cellTest_1536 48 8 (by decide +kernel)

theorem cellTest_1536_block_7 : Interval cellTest_1536 56 64 :=
  interval_of_check cellTest_1536 56 8 (by decide +kernel)

theorem cellTest_1536_block_8 : Interval cellTest_1536 64 72 :=
  interval_of_check cellTest_1536 64 8 (by decide +kernel)

theorem cellTest_1536_block_9 : Interval cellTest_1536 72 80 :=
  interval_of_check cellTest_1536 72 8 (by decide +kernel)

theorem cellTest_1536_block_10 : Interval cellTest_1536 80 88 :=
  interval_of_check cellTest_1536 80 8 (by decide +kernel)

theorem cellTest_1536_block_11 : Interval cellTest_1536 88 96 :=
  interval_of_check cellTest_1536 88 8 (by decide +kernel)

theorem cellTest_1536_block_12 : Interval cellTest_1536 96 104 :=
  interval_of_check cellTest_1536 96 8 (by decide +kernel)

theorem cellTest_1536_block_13 : Interval cellTest_1536 104 112 :=
  interval_of_check cellTest_1536 104 8 (by decide +kernel)

theorem cellTest_1536_block_14 : Interval cellTest_1536 112 120 :=
  interval_of_check cellTest_1536 112 8 (by decide +kernel)

theorem cellTest_1536_block_15 : Interval cellTest_1536 120 128 :=
  interval_of_check cellTest_1536 120 8 (by decide +kernel)

theorem cellTest_1536_block_16 : Interval cellTest_1536 128 136 :=
  interval_of_check cellTest_1536 128 8 (by decide +kernel)

theorem cellTest_1536_block_17 : Interval cellTest_1536 136 144 :=
  interval_of_check cellTest_1536 136 8 (by decide +kernel)

theorem cellTest_1536_block_18 : Interval cellTest_1536 144 152 :=
  interval_of_check cellTest_1536 144 8 (by decide +kernel)

theorem cellTest_1536_block_19 : Interval cellTest_1536 152 160 :=
  interval_of_check cellTest_1536 152 8 (by decide +kernel)

theorem cellTest_1536_block_20 : Interval cellTest_1536 160 168 :=
  interval_of_check cellTest_1536 160 8 (by decide +kernel)

theorem cellTest_1536_block_21 : Interval cellTest_1536 168 176 :=
  interval_of_check cellTest_1536 168 8 (by decide +kernel)

theorem cellTest_1536_block_22 : Interval cellTest_1536 176 184 :=
  interval_of_check cellTest_1536 176 8 (by decide +kernel)

theorem cellTest_1536_block_23 : Interval cellTest_1536 184 192 :=
  interval_of_check cellTest_1536 184 8 (by decide +kernel)

theorem cellTest_1536_block_24 : Interval cellTest_1536 192 200 :=
  interval_of_check cellTest_1536 192 8 (by decide +kernel)

theorem cellTest_1536_block_25 : Interval cellTest_1536 200 208 :=
  interval_of_check cellTest_1536 200 8 (by decide +kernel)

theorem cellTest_1536_block_26 : Interval cellTest_1536 208 216 :=
  interval_of_check cellTest_1536 208 8 (by decide +kernel)

theorem cellTest_1536_block_27 : Interval cellTest_1536 216 224 :=
  interval_of_check cellTest_1536 216 8 (by decide +kernel)

theorem cellTest_1536_block_28 : Interval cellTest_1536 224 232 :=
  interval_of_check cellTest_1536 224 8 (by decide +kernel)

theorem cellTest_1536_block_29 : Interval cellTest_1536 232 240 :=
  interval_of_check cellTest_1536 232 8 (by decide +kernel)

theorem cellTest_1536_block_30 : Interval cellTest_1536 240 248 :=
  interval_of_check cellTest_1536 240 8 (by decide +kernel)

theorem cellTest_1536_block_31 : Interval cellTest_1536 248 256 :=
  interval_of_check cellTest_1536 248 8 (by decide +kernel)

theorem cellTest_1536_complete : Interval cellTest_1536 0 256 :=
  (interval_append cellTest_1536 0 128 256
  (interval_append cellTest_1536 0 64 128
  (interval_append cellTest_1536 0 32 64
  (interval_append cellTest_1536 0 16 32
  (interval_append cellTest_1536 0 8 16
  cellTest_1536_block_0
  cellTest_1536_block_1)
  (interval_append cellTest_1536 16 24 32
  cellTest_1536_block_2
  cellTest_1536_block_3))
  (interval_append cellTest_1536 32 48 64
  (interval_append cellTest_1536 32 40 48
  cellTest_1536_block_4
  cellTest_1536_block_5)
  (interval_append cellTest_1536 48 56 64
  cellTest_1536_block_6
  cellTest_1536_block_7)))
  (interval_append cellTest_1536 64 96 128
  (interval_append cellTest_1536 64 80 96
  (interval_append cellTest_1536 64 72 80
  cellTest_1536_block_8
  cellTest_1536_block_9)
  (interval_append cellTest_1536 80 88 96
  cellTest_1536_block_10
  cellTest_1536_block_11))
  (interval_append cellTest_1536 96 112 128
  (interval_append cellTest_1536 96 104 112
  cellTest_1536_block_12
  cellTest_1536_block_13)
  (interval_append cellTest_1536 112 120 128
  cellTest_1536_block_14
  cellTest_1536_block_15))))
  (interval_append cellTest_1536 128 192 256
  (interval_append cellTest_1536 128 160 192
  (interval_append cellTest_1536 128 144 160
  (interval_append cellTest_1536 128 136 144
  cellTest_1536_block_16
  cellTest_1536_block_17)
  (interval_append cellTest_1536 144 152 160
  cellTest_1536_block_18
  cellTest_1536_block_19))
  (interval_append cellTest_1536 160 176 192
  (interval_append cellTest_1536 160 168 176
  cellTest_1536_block_20
  cellTest_1536_block_21)
  (interval_append cellTest_1536 176 184 192
  cellTest_1536_block_22
  cellTest_1536_block_23)))
  (interval_append cellTest_1536 192 224 256
  (interval_append cellTest_1536 192 208 224
  (interval_append cellTest_1536 192 200 208
  cellTest_1536_block_24
  cellTest_1536_block_25)
  (interval_append cellTest_1536 208 216 224
  cellTest_1536_block_26
  cellTest_1536_block_27))
  (interval_append cellTest_1536 224 240 256
  (interval_append cellTest_1536 224 232 240
  cellTest_1536_block_28
  cellTest_1536_block_29)
  (interval_append cellTest_1536 240 248 256
  cellTest_1536_block_30
  cellTest_1536_block_31)))))
theorem cellTestInterval1536 : Interval cellTest 1536 1792 := by
  intro i hlo hhi
  have h := cellTest_1536_complete (i-1536) (Nat.zero_le _) (by omega)
  simpa only [cellTest_1536, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_1792 (i : Nat) := cellTest (i+1792)
theorem cellTest_1792_block_0 : Interval cellTest_1792 0 8 :=
  interval_of_check cellTest_1792 0 8 (by decide +kernel)

theorem cellTest_1792_block_1 : Interval cellTest_1792 8 16 :=
  interval_of_check cellTest_1792 8 8 (by decide +kernel)

theorem cellTest_1792_block_2 : Interval cellTest_1792 16 24 :=
  interval_of_check cellTest_1792 16 8 (by decide +kernel)

theorem cellTest_1792_block_3 : Interval cellTest_1792 24 32 :=
  interval_of_check cellTest_1792 24 8 (by decide +kernel)

theorem cellTest_1792_block_4 : Interval cellTest_1792 32 40 :=
  interval_of_check cellTest_1792 32 8 (by decide +kernel)

theorem cellTest_1792_block_5 : Interval cellTest_1792 40 48 :=
  interval_of_check cellTest_1792 40 8 (by decide +kernel)

theorem cellTest_1792_block_6 : Interval cellTest_1792 48 56 :=
  interval_of_check cellTest_1792 48 8 (by decide +kernel)

theorem cellTest_1792_block_7 : Interval cellTest_1792 56 64 :=
  interval_of_check cellTest_1792 56 8 (by decide +kernel)

theorem cellTest_1792_block_8 : Interval cellTest_1792 64 72 :=
  interval_of_check cellTest_1792 64 8 (by decide +kernel)

theorem cellTest_1792_block_9 : Interval cellTest_1792 72 80 :=
  interval_of_check cellTest_1792 72 8 (by decide +kernel)

theorem cellTest_1792_block_10 : Interval cellTest_1792 80 88 :=
  interval_of_check cellTest_1792 80 8 (by decide +kernel)

theorem cellTest_1792_block_11 : Interval cellTest_1792 88 96 :=
  interval_of_check cellTest_1792 88 8 (by decide +kernel)

theorem cellTest_1792_block_12 : Interval cellTest_1792 96 104 :=
  interval_of_check cellTest_1792 96 8 (by decide +kernel)

theorem cellTest_1792_block_13 : Interval cellTest_1792 104 112 :=
  interval_of_check cellTest_1792 104 8 (by decide +kernel)

theorem cellTest_1792_block_14 : Interval cellTest_1792 112 120 :=
  interval_of_check cellTest_1792 112 8 (by decide +kernel)

theorem cellTest_1792_block_15 : Interval cellTest_1792 120 128 :=
  interval_of_check cellTest_1792 120 8 (by decide +kernel)

theorem cellTest_1792_block_16 : Interval cellTest_1792 128 136 :=
  interval_of_check cellTest_1792 128 8 (by decide +kernel)

theorem cellTest_1792_block_17 : Interval cellTest_1792 136 144 :=
  interval_of_check cellTest_1792 136 8 (by decide +kernel)

theorem cellTest_1792_block_18 : Interval cellTest_1792 144 152 :=
  interval_of_check cellTest_1792 144 8 (by decide +kernel)

theorem cellTest_1792_block_19 : Interval cellTest_1792 152 160 :=
  interval_of_check cellTest_1792 152 8 (by decide +kernel)

theorem cellTest_1792_block_20 : Interval cellTest_1792 160 168 :=
  interval_of_check cellTest_1792 160 8 (by decide +kernel)

theorem cellTest_1792_block_21 : Interval cellTest_1792 168 176 :=
  interval_of_check cellTest_1792 168 8 (by decide +kernel)

theorem cellTest_1792_block_22 : Interval cellTest_1792 176 184 :=
  interval_of_check cellTest_1792 176 8 (by decide +kernel)

theorem cellTest_1792_block_23 : Interval cellTest_1792 184 192 :=
  interval_of_check cellTest_1792 184 8 (by decide +kernel)

theorem cellTest_1792_block_24 : Interval cellTest_1792 192 200 :=
  interval_of_check cellTest_1792 192 8 (by decide +kernel)

theorem cellTest_1792_block_25 : Interval cellTest_1792 200 208 :=
  interval_of_check cellTest_1792 200 8 (by decide +kernel)

theorem cellTest_1792_block_26 : Interval cellTest_1792 208 216 :=
  interval_of_check cellTest_1792 208 8 (by decide +kernel)

theorem cellTest_1792_block_27 : Interval cellTest_1792 216 224 :=
  interval_of_check cellTest_1792 216 8 (by decide +kernel)

theorem cellTest_1792_block_28 : Interval cellTest_1792 224 232 :=
  interval_of_check cellTest_1792 224 8 (by decide +kernel)

theorem cellTest_1792_block_29 : Interval cellTest_1792 232 240 :=
  interval_of_check cellTest_1792 232 8 (by decide +kernel)

theorem cellTest_1792_block_30 : Interval cellTest_1792 240 248 :=
  interval_of_check cellTest_1792 240 8 (by decide +kernel)

theorem cellTest_1792_block_31 : Interval cellTest_1792 248 256 :=
  interval_of_check cellTest_1792 248 8 (by decide +kernel)

theorem cellTest_1792_complete : Interval cellTest_1792 0 256 :=
  (interval_append cellTest_1792 0 128 256
  (interval_append cellTest_1792 0 64 128
  (interval_append cellTest_1792 0 32 64
  (interval_append cellTest_1792 0 16 32
  (interval_append cellTest_1792 0 8 16
  cellTest_1792_block_0
  cellTest_1792_block_1)
  (interval_append cellTest_1792 16 24 32
  cellTest_1792_block_2
  cellTest_1792_block_3))
  (interval_append cellTest_1792 32 48 64
  (interval_append cellTest_1792 32 40 48
  cellTest_1792_block_4
  cellTest_1792_block_5)
  (interval_append cellTest_1792 48 56 64
  cellTest_1792_block_6
  cellTest_1792_block_7)))
  (interval_append cellTest_1792 64 96 128
  (interval_append cellTest_1792 64 80 96
  (interval_append cellTest_1792 64 72 80
  cellTest_1792_block_8
  cellTest_1792_block_9)
  (interval_append cellTest_1792 80 88 96
  cellTest_1792_block_10
  cellTest_1792_block_11))
  (interval_append cellTest_1792 96 112 128
  (interval_append cellTest_1792 96 104 112
  cellTest_1792_block_12
  cellTest_1792_block_13)
  (interval_append cellTest_1792 112 120 128
  cellTest_1792_block_14
  cellTest_1792_block_15))))
  (interval_append cellTest_1792 128 192 256
  (interval_append cellTest_1792 128 160 192
  (interval_append cellTest_1792 128 144 160
  (interval_append cellTest_1792 128 136 144
  cellTest_1792_block_16
  cellTest_1792_block_17)
  (interval_append cellTest_1792 144 152 160
  cellTest_1792_block_18
  cellTest_1792_block_19))
  (interval_append cellTest_1792 160 176 192
  (interval_append cellTest_1792 160 168 176
  cellTest_1792_block_20
  cellTest_1792_block_21)
  (interval_append cellTest_1792 176 184 192
  cellTest_1792_block_22
  cellTest_1792_block_23)))
  (interval_append cellTest_1792 192 224 256
  (interval_append cellTest_1792 192 208 224
  (interval_append cellTest_1792 192 200 208
  cellTest_1792_block_24
  cellTest_1792_block_25)
  (interval_append cellTest_1792 208 216 224
  cellTest_1792_block_26
  cellTest_1792_block_27))
  (interval_append cellTest_1792 224 240 256
  (interval_append cellTest_1792 224 232 240
  cellTest_1792_block_28
  cellTest_1792_block_29)
  (interval_append cellTest_1792 240 248 256
  cellTest_1792_block_30
  cellTest_1792_block_31)))))
theorem cellTestInterval1792 : Interval cellTest 1792 2048 := by
  intro i hlo hhi
  have h := cellTest_1792_complete (i-1792) (Nat.zero_le _) (by omega)
  simpa only [cellTest_1792, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_2048 (i : Nat) := cellTest (i+2048)
theorem cellTest_2048_block_0 : Interval cellTest_2048 0 8 :=
  interval_of_check cellTest_2048 0 8 (by decide +kernel)

theorem cellTest_2048_block_1 : Interval cellTest_2048 8 16 :=
  interval_of_check cellTest_2048 8 8 (by decide +kernel)

theorem cellTest_2048_block_2 : Interval cellTest_2048 16 24 :=
  interval_of_check cellTest_2048 16 8 (by decide +kernel)

theorem cellTest_2048_block_3 : Interval cellTest_2048 24 32 :=
  interval_of_check cellTest_2048 24 8 (by decide +kernel)

theorem cellTest_2048_block_4 : Interval cellTest_2048 32 40 :=
  interval_of_check cellTest_2048 32 8 (by decide +kernel)

theorem cellTest_2048_block_5 : Interval cellTest_2048 40 48 :=
  interval_of_check cellTest_2048 40 8 (by decide +kernel)

theorem cellTest_2048_block_6 : Interval cellTest_2048 48 56 :=
  interval_of_check cellTest_2048 48 8 (by decide +kernel)

theorem cellTest_2048_block_7 : Interval cellTest_2048 56 64 :=
  interval_of_check cellTest_2048 56 8 (by decide +kernel)

theorem cellTest_2048_block_8 : Interval cellTest_2048 64 72 :=
  interval_of_check cellTest_2048 64 8 (by decide +kernel)

theorem cellTest_2048_block_9 : Interval cellTest_2048 72 80 :=
  interval_of_check cellTest_2048 72 8 (by decide +kernel)

theorem cellTest_2048_block_10 : Interval cellTest_2048 80 88 :=
  interval_of_check cellTest_2048 80 8 (by decide +kernel)

theorem cellTest_2048_block_11 : Interval cellTest_2048 88 96 :=
  interval_of_check cellTest_2048 88 8 (by decide +kernel)

theorem cellTest_2048_block_12 : Interval cellTest_2048 96 104 :=
  interval_of_check cellTest_2048 96 8 (by decide +kernel)

theorem cellTest_2048_block_13 : Interval cellTest_2048 104 112 :=
  interval_of_check cellTest_2048 104 8 (by decide +kernel)

theorem cellTest_2048_block_14 : Interval cellTest_2048 112 120 :=
  interval_of_check cellTest_2048 112 8 (by decide +kernel)

theorem cellTest_2048_block_15 : Interval cellTest_2048 120 128 :=
  interval_of_check cellTest_2048 120 8 (by decide +kernel)

theorem cellTest_2048_block_16 : Interval cellTest_2048 128 136 :=
  interval_of_check cellTest_2048 128 8 (by decide +kernel)

theorem cellTest_2048_block_17 : Interval cellTest_2048 136 144 :=
  interval_of_check cellTest_2048 136 8 (by decide +kernel)

theorem cellTest_2048_block_18 : Interval cellTest_2048 144 152 :=
  interval_of_check cellTest_2048 144 8 (by decide +kernel)

theorem cellTest_2048_block_19 : Interval cellTest_2048 152 160 :=
  interval_of_check cellTest_2048 152 8 (by decide +kernel)

theorem cellTest_2048_block_20 : Interval cellTest_2048 160 168 :=
  interval_of_check cellTest_2048 160 8 (by decide +kernel)

theorem cellTest_2048_block_21 : Interval cellTest_2048 168 176 :=
  interval_of_check cellTest_2048 168 8 (by decide +kernel)

theorem cellTest_2048_block_22 : Interval cellTest_2048 176 184 :=
  interval_of_check cellTest_2048 176 8 (by decide +kernel)

theorem cellTest_2048_block_23 : Interval cellTest_2048 184 192 :=
  interval_of_check cellTest_2048 184 8 (by decide +kernel)

theorem cellTest_2048_block_24 : Interval cellTest_2048 192 200 :=
  interval_of_check cellTest_2048 192 8 (by decide +kernel)

theorem cellTest_2048_block_25 : Interval cellTest_2048 200 208 :=
  interval_of_check cellTest_2048 200 8 (by decide +kernel)

theorem cellTest_2048_block_26 : Interval cellTest_2048 208 216 :=
  interval_of_check cellTest_2048 208 8 (by decide +kernel)

theorem cellTest_2048_block_27 : Interval cellTest_2048 216 224 :=
  interval_of_check cellTest_2048 216 8 (by decide +kernel)

theorem cellTest_2048_block_28 : Interval cellTest_2048 224 232 :=
  interval_of_check cellTest_2048 224 8 (by decide +kernel)

theorem cellTest_2048_block_29 : Interval cellTest_2048 232 240 :=
  interval_of_check cellTest_2048 232 8 (by decide +kernel)

theorem cellTest_2048_block_30 : Interval cellTest_2048 240 248 :=
  interval_of_check cellTest_2048 240 8 (by decide +kernel)

theorem cellTest_2048_block_31 : Interval cellTest_2048 248 256 :=
  interval_of_check cellTest_2048 248 8 (by decide +kernel)

theorem cellTest_2048_complete : Interval cellTest_2048 0 256 :=
  (interval_append cellTest_2048 0 128 256
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
  (interval_append cellTest_2048 128 192 256
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
  (interval_append cellTest_2048 192 224 256
  (interval_append cellTest_2048 192 208 224
  (interval_append cellTest_2048 192 200 208
  cellTest_2048_block_24
  cellTest_2048_block_25)
  (interval_append cellTest_2048 208 216 224
  cellTest_2048_block_26
  cellTest_2048_block_27))
  (interval_append cellTest_2048 224 240 256
  (interval_append cellTest_2048 224 232 240
  cellTest_2048_block_28
  cellTest_2048_block_29)
  (interval_append cellTest_2048 240 248 256
  cellTest_2048_block_30
  cellTest_2048_block_31)))))
theorem cellTestInterval2048 : Interval cellTest 2048 2304 := by
  intro i hlo hhi
  have h := cellTest_2048_complete (i-2048) (Nat.zero_le _) (by omega)
  simpa only [cellTest_2048, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_2304 (i : Nat) := cellTest (i+2304)
theorem cellTest_2304_block_0 : Interval cellTest_2304 0 8 :=
  interval_of_check cellTest_2304 0 8 (by decide +kernel)

theorem cellTest_2304_block_1 : Interval cellTest_2304 8 16 :=
  interval_of_check cellTest_2304 8 8 (by decide +kernel)

theorem cellTest_2304_block_2 : Interval cellTest_2304 16 24 :=
  interval_of_check cellTest_2304 16 8 (by decide +kernel)

theorem cellTest_2304_block_3 : Interval cellTest_2304 24 32 :=
  interval_of_check cellTest_2304 24 8 (by decide +kernel)

theorem cellTest_2304_block_4 : Interval cellTest_2304 32 40 :=
  interval_of_check cellTest_2304 32 8 (by decide +kernel)

theorem cellTest_2304_block_5 : Interval cellTest_2304 40 48 :=
  interval_of_check cellTest_2304 40 8 (by decide +kernel)

theorem cellTest_2304_block_6 : Interval cellTest_2304 48 56 :=
  interval_of_check cellTest_2304 48 8 (by decide +kernel)

theorem cellTest_2304_block_7 : Interval cellTest_2304 56 64 :=
  interval_of_check cellTest_2304 56 8 (by decide +kernel)

theorem cellTest_2304_block_8 : Interval cellTest_2304 64 72 :=
  interval_of_check cellTest_2304 64 8 (by decide +kernel)

theorem cellTest_2304_block_9 : Interval cellTest_2304 72 80 :=
  interval_of_check cellTest_2304 72 8 (by decide +kernel)

theorem cellTest_2304_block_10 : Interval cellTest_2304 80 88 :=
  interval_of_check cellTest_2304 80 8 (by decide +kernel)

theorem cellTest_2304_block_11 : Interval cellTest_2304 88 96 :=
  interval_of_check cellTest_2304 88 8 (by decide +kernel)

theorem cellTest_2304_block_12 : Interval cellTest_2304 96 104 :=
  interval_of_check cellTest_2304 96 8 (by decide +kernel)

theorem cellTest_2304_block_13 : Interval cellTest_2304 104 112 :=
  interval_of_check cellTest_2304 104 8 (by decide +kernel)

theorem cellTest_2304_block_14 : Interval cellTest_2304 112 120 :=
  interval_of_check cellTest_2304 112 8 (by decide +kernel)

theorem cellTest_2304_block_15 : Interval cellTest_2304 120 128 :=
  interval_of_check cellTest_2304 120 8 (by decide +kernel)

theorem cellTest_2304_block_16 : Interval cellTest_2304 128 136 :=
  interval_of_check cellTest_2304 128 8 (by decide +kernel)

theorem cellTest_2304_block_17 : Interval cellTest_2304 136 144 :=
  interval_of_check cellTest_2304 136 8 (by decide +kernel)

theorem cellTest_2304_block_18 : Interval cellTest_2304 144 152 :=
  interval_of_check cellTest_2304 144 8 (by decide +kernel)

theorem cellTest_2304_block_19 : Interval cellTest_2304 152 160 :=
  interval_of_check cellTest_2304 152 8 (by decide +kernel)

theorem cellTest_2304_block_20 : Interval cellTest_2304 160 168 :=
  interval_of_check cellTest_2304 160 8 (by decide +kernel)

theorem cellTest_2304_block_21 : Interval cellTest_2304 168 176 :=
  interval_of_check cellTest_2304 168 8 (by decide +kernel)

theorem cellTest_2304_block_22 : Interval cellTest_2304 176 184 :=
  interval_of_check cellTest_2304 176 8 (by decide +kernel)

theorem cellTest_2304_block_23 : Interval cellTest_2304 184 192 :=
  interval_of_check cellTest_2304 184 8 (by decide +kernel)

theorem cellTest_2304_block_24 : Interval cellTest_2304 192 200 :=
  interval_of_check cellTest_2304 192 8 (by decide +kernel)

theorem cellTest_2304_block_25 : Interval cellTest_2304 200 208 :=
  interval_of_check cellTest_2304 200 8 (by decide +kernel)

theorem cellTest_2304_block_26 : Interval cellTest_2304 208 216 :=
  interval_of_check cellTest_2304 208 8 (by decide +kernel)

theorem cellTest_2304_block_27 : Interval cellTest_2304 216 224 :=
  interval_of_check cellTest_2304 216 8 (by decide +kernel)

theorem cellTest_2304_block_28 : Interval cellTest_2304 224 232 :=
  interval_of_check cellTest_2304 224 8 (by decide +kernel)

theorem cellTest_2304_block_29 : Interval cellTest_2304 232 240 :=
  interval_of_check cellTest_2304 232 8 (by decide +kernel)

theorem cellTest_2304_block_30 : Interval cellTest_2304 240 248 :=
  interval_of_check cellTest_2304 240 8 (by decide +kernel)

theorem cellTest_2304_block_31 : Interval cellTest_2304 248 256 :=
  interval_of_check cellTest_2304 248 8 (by decide +kernel)

theorem cellTest_2304_complete : Interval cellTest_2304 0 256 :=
  (interval_append cellTest_2304 0 128 256
  (interval_append cellTest_2304 0 64 128
  (interval_append cellTest_2304 0 32 64
  (interval_append cellTest_2304 0 16 32
  (interval_append cellTest_2304 0 8 16
  cellTest_2304_block_0
  cellTest_2304_block_1)
  (interval_append cellTest_2304 16 24 32
  cellTest_2304_block_2
  cellTest_2304_block_3))
  (interval_append cellTest_2304 32 48 64
  (interval_append cellTest_2304 32 40 48
  cellTest_2304_block_4
  cellTest_2304_block_5)
  (interval_append cellTest_2304 48 56 64
  cellTest_2304_block_6
  cellTest_2304_block_7)))
  (interval_append cellTest_2304 64 96 128
  (interval_append cellTest_2304 64 80 96
  (interval_append cellTest_2304 64 72 80
  cellTest_2304_block_8
  cellTest_2304_block_9)
  (interval_append cellTest_2304 80 88 96
  cellTest_2304_block_10
  cellTest_2304_block_11))
  (interval_append cellTest_2304 96 112 128
  (interval_append cellTest_2304 96 104 112
  cellTest_2304_block_12
  cellTest_2304_block_13)
  (interval_append cellTest_2304 112 120 128
  cellTest_2304_block_14
  cellTest_2304_block_15))))
  (interval_append cellTest_2304 128 192 256
  (interval_append cellTest_2304 128 160 192
  (interval_append cellTest_2304 128 144 160
  (interval_append cellTest_2304 128 136 144
  cellTest_2304_block_16
  cellTest_2304_block_17)
  (interval_append cellTest_2304 144 152 160
  cellTest_2304_block_18
  cellTest_2304_block_19))
  (interval_append cellTest_2304 160 176 192
  (interval_append cellTest_2304 160 168 176
  cellTest_2304_block_20
  cellTest_2304_block_21)
  (interval_append cellTest_2304 176 184 192
  cellTest_2304_block_22
  cellTest_2304_block_23)))
  (interval_append cellTest_2304 192 224 256
  (interval_append cellTest_2304 192 208 224
  (interval_append cellTest_2304 192 200 208
  cellTest_2304_block_24
  cellTest_2304_block_25)
  (interval_append cellTest_2304 208 216 224
  cellTest_2304_block_26
  cellTest_2304_block_27))
  (interval_append cellTest_2304 224 240 256
  (interval_append cellTest_2304 224 232 240
  cellTest_2304_block_28
  cellTest_2304_block_29)
  (interval_append cellTest_2304 240 248 256
  cellTest_2304_block_30
  cellTest_2304_block_31)))))
theorem cellTestInterval2304 : Interval cellTest 2304 2560 := by
  intro i hlo hhi
  have h := cellTest_2304_complete (i-2304) (Nat.zero_le _) (by omega)
  simpa only [cellTest_2304, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells010 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_2560 (i : Nat) := cellTest (i+2560)
theorem cellTest_2560_block_0 : Interval cellTest_2560 0 8 :=
  interval_of_check cellTest_2560 0 8 (by decide +kernel)

theorem cellTest_2560_block_1 : Interval cellTest_2560 8 16 :=
  interval_of_check cellTest_2560 8 8 (by decide +kernel)

theorem cellTest_2560_block_2 : Interval cellTest_2560 16 24 :=
  interval_of_check cellTest_2560 16 8 (by decide +kernel)

theorem cellTest_2560_block_3 : Interval cellTest_2560 24 32 :=
  interval_of_check cellTest_2560 24 8 (by decide +kernel)

theorem cellTest_2560_block_4 : Interval cellTest_2560 32 40 :=
  interval_of_check cellTest_2560 32 8 (by decide +kernel)

theorem cellTest_2560_block_5 : Interval cellTest_2560 40 48 :=
  interval_of_check cellTest_2560 40 8 (by decide +kernel)

theorem cellTest_2560_block_6 : Interval cellTest_2560 48 56 :=
  interval_of_check cellTest_2560 48 8 (by decide +kernel)

theorem cellTest_2560_block_7 : Interval cellTest_2560 56 64 :=
  interval_of_check cellTest_2560 56 8 (by decide +kernel)

theorem cellTest_2560_block_8 : Interval cellTest_2560 64 72 :=
  interval_of_check cellTest_2560 64 8 (by decide +kernel)

theorem cellTest_2560_block_9 : Interval cellTest_2560 72 80 :=
  interval_of_check cellTest_2560 72 8 (by decide +kernel)

theorem cellTest_2560_block_10 : Interval cellTest_2560 80 88 :=
  interval_of_check cellTest_2560 80 8 (by decide +kernel)

theorem cellTest_2560_block_11 : Interval cellTest_2560 88 96 :=
  interval_of_check cellTest_2560 88 8 (by decide +kernel)

theorem cellTest_2560_block_12 : Interval cellTest_2560 96 104 :=
  interval_of_check cellTest_2560 96 8 (by decide +kernel)

theorem cellTest_2560_block_13 : Interval cellTest_2560 104 112 :=
  interval_of_check cellTest_2560 104 8 (by decide +kernel)

theorem cellTest_2560_block_14 : Interval cellTest_2560 112 120 :=
  interval_of_check cellTest_2560 112 8 (by decide +kernel)

theorem cellTest_2560_block_15 : Interval cellTest_2560 120 128 :=
  interval_of_check cellTest_2560 120 8 (by decide +kernel)

theorem cellTest_2560_block_16 : Interval cellTest_2560 128 136 :=
  interval_of_check cellTest_2560 128 8 (by decide +kernel)

theorem cellTest_2560_block_17 : Interval cellTest_2560 136 144 :=
  interval_of_check cellTest_2560 136 8 (by decide +kernel)

theorem cellTest_2560_block_18 : Interval cellTest_2560 144 152 :=
  interval_of_check cellTest_2560 144 8 (by decide +kernel)

theorem cellTest_2560_block_19 : Interval cellTest_2560 152 160 :=
  interval_of_check cellTest_2560 152 8 (by decide +kernel)

theorem cellTest_2560_block_20 : Interval cellTest_2560 160 168 :=
  interval_of_check cellTest_2560 160 8 (by decide +kernel)

theorem cellTest_2560_block_21 : Interval cellTest_2560 168 176 :=
  interval_of_check cellTest_2560 168 8 (by decide +kernel)

theorem cellTest_2560_block_22 : Interval cellTest_2560 176 184 :=
  interval_of_check cellTest_2560 176 8 (by decide +kernel)

theorem cellTest_2560_block_23 : Interval cellTest_2560 184 192 :=
  interval_of_check cellTest_2560 184 8 (by decide +kernel)

theorem cellTest_2560_block_24 : Interval cellTest_2560 192 200 :=
  interval_of_check cellTest_2560 192 8 (by decide +kernel)

theorem cellTest_2560_block_25 : Interval cellTest_2560 200 208 :=
  interval_of_check cellTest_2560 200 8 (by decide +kernel)

theorem cellTest_2560_block_26 : Interval cellTest_2560 208 216 :=
  interval_of_check cellTest_2560 208 8 (by decide +kernel)

theorem cellTest_2560_block_27 : Interval cellTest_2560 216 224 :=
  interval_of_check cellTest_2560 216 8 (by decide +kernel)

theorem cellTest_2560_block_28 : Interval cellTest_2560 224 232 :=
  interval_of_check cellTest_2560 224 8 (by decide +kernel)

theorem cellTest_2560_block_29 : Interval cellTest_2560 232 240 :=
  interval_of_check cellTest_2560 232 8 (by decide +kernel)

theorem cellTest_2560_block_30 : Interval cellTest_2560 240 248 :=
  interval_of_check cellTest_2560 240 8 (by decide +kernel)

theorem cellTest_2560_block_31 : Interval cellTest_2560 248 256 :=
  interval_of_check cellTest_2560 248 8 (by decide +kernel)

theorem cellTest_2560_complete : Interval cellTest_2560 0 256 :=
  (interval_append cellTest_2560 0 128 256
  (interval_append cellTest_2560 0 64 128
  (interval_append cellTest_2560 0 32 64
  (interval_append cellTest_2560 0 16 32
  (interval_append cellTest_2560 0 8 16
  cellTest_2560_block_0
  cellTest_2560_block_1)
  (interval_append cellTest_2560 16 24 32
  cellTest_2560_block_2
  cellTest_2560_block_3))
  (interval_append cellTest_2560 32 48 64
  (interval_append cellTest_2560 32 40 48
  cellTest_2560_block_4
  cellTest_2560_block_5)
  (interval_append cellTest_2560 48 56 64
  cellTest_2560_block_6
  cellTest_2560_block_7)))
  (interval_append cellTest_2560 64 96 128
  (interval_append cellTest_2560 64 80 96
  (interval_append cellTest_2560 64 72 80
  cellTest_2560_block_8
  cellTest_2560_block_9)
  (interval_append cellTest_2560 80 88 96
  cellTest_2560_block_10
  cellTest_2560_block_11))
  (interval_append cellTest_2560 96 112 128
  (interval_append cellTest_2560 96 104 112
  cellTest_2560_block_12
  cellTest_2560_block_13)
  (interval_append cellTest_2560 112 120 128
  cellTest_2560_block_14
  cellTest_2560_block_15))))
  (interval_append cellTest_2560 128 192 256
  (interval_append cellTest_2560 128 160 192
  (interval_append cellTest_2560 128 144 160
  (interval_append cellTest_2560 128 136 144
  cellTest_2560_block_16
  cellTest_2560_block_17)
  (interval_append cellTest_2560 144 152 160
  cellTest_2560_block_18
  cellTest_2560_block_19))
  (interval_append cellTest_2560 160 176 192
  (interval_append cellTest_2560 160 168 176
  cellTest_2560_block_20
  cellTest_2560_block_21)
  (interval_append cellTest_2560 176 184 192
  cellTest_2560_block_22
  cellTest_2560_block_23)))
  (interval_append cellTest_2560 192 224 256
  (interval_append cellTest_2560 192 208 224
  (interval_append cellTest_2560 192 200 208
  cellTest_2560_block_24
  cellTest_2560_block_25)
  (interval_append cellTest_2560 208 216 224
  cellTest_2560_block_26
  cellTest_2560_block_27))
  (interval_append cellTest_2560 224 240 256
  (interval_append cellTest_2560 224 232 240
  cellTest_2560_block_28
  cellTest_2560_block_29)
  (interval_append cellTest_2560 240 248 256
  cellTest_2560_block_30
  cellTest_2560_block_31)))))
theorem cellTestInterval2560 : Interval cellTest 2560 2816 := by
  intro i hlo hhi
  have h := cellTest_2560_complete (i-2560) (Nat.zero_le _) (by omega)
  simpa only [cellTest_2560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells011 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_2816 (i : Nat) := cellTest (i+2816)
theorem cellTest_2816_block_0 : Interval cellTest_2816 0 8 :=
  interval_of_check cellTest_2816 0 8 (by decide +kernel)

theorem cellTest_2816_block_1 : Interval cellTest_2816 8 16 :=
  interval_of_check cellTest_2816 8 8 (by decide +kernel)

theorem cellTest_2816_block_2 : Interval cellTest_2816 16 24 :=
  interval_of_check cellTest_2816 16 8 (by decide +kernel)

theorem cellTest_2816_block_3 : Interval cellTest_2816 24 32 :=
  interval_of_check cellTest_2816 24 8 (by decide +kernel)

theorem cellTest_2816_block_4 : Interval cellTest_2816 32 40 :=
  interval_of_check cellTest_2816 32 8 (by decide +kernel)

theorem cellTest_2816_block_5 : Interval cellTest_2816 40 48 :=
  interval_of_check cellTest_2816 40 8 (by decide +kernel)

theorem cellTest_2816_block_6 : Interval cellTest_2816 48 56 :=
  interval_of_check cellTest_2816 48 8 (by decide +kernel)

theorem cellTest_2816_block_7 : Interval cellTest_2816 56 64 :=
  interval_of_check cellTest_2816 56 8 (by decide +kernel)

theorem cellTest_2816_block_8 : Interval cellTest_2816 64 72 :=
  interval_of_check cellTest_2816 64 8 (by decide +kernel)

theorem cellTest_2816_block_9 : Interval cellTest_2816 72 80 :=
  interval_of_check cellTest_2816 72 8 (by decide +kernel)

theorem cellTest_2816_block_10 : Interval cellTest_2816 80 88 :=
  interval_of_check cellTest_2816 80 8 (by decide +kernel)

theorem cellTest_2816_block_11 : Interval cellTest_2816 88 96 :=
  interval_of_check cellTest_2816 88 8 (by decide +kernel)

theorem cellTest_2816_block_12 : Interval cellTest_2816 96 104 :=
  interval_of_check cellTest_2816 96 8 (by decide +kernel)

theorem cellTest_2816_block_13 : Interval cellTest_2816 104 112 :=
  interval_of_check cellTest_2816 104 8 (by decide +kernel)

theorem cellTest_2816_block_14 : Interval cellTest_2816 112 120 :=
  interval_of_check cellTest_2816 112 8 (by decide +kernel)

theorem cellTest_2816_block_15 : Interval cellTest_2816 120 128 :=
  interval_of_check cellTest_2816 120 8 (by decide +kernel)

theorem cellTest_2816_block_16 : Interval cellTest_2816 128 136 :=
  interval_of_check cellTest_2816 128 8 (by decide +kernel)

theorem cellTest_2816_block_17 : Interval cellTest_2816 136 144 :=
  interval_of_check cellTest_2816 136 8 (by decide +kernel)

theorem cellTest_2816_block_18 : Interval cellTest_2816 144 152 :=
  interval_of_check cellTest_2816 144 8 (by decide +kernel)

theorem cellTest_2816_block_19 : Interval cellTest_2816 152 160 :=
  interval_of_check cellTest_2816 152 8 (by decide +kernel)

theorem cellTest_2816_block_20 : Interval cellTest_2816 160 168 :=
  interval_of_check cellTest_2816 160 8 (by decide +kernel)

theorem cellTest_2816_block_21 : Interval cellTest_2816 168 176 :=
  interval_of_check cellTest_2816 168 8 (by decide +kernel)

theorem cellTest_2816_block_22 : Interval cellTest_2816 176 184 :=
  interval_of_check cellTest_2816 176 8 (by decide +kernel)

theorem cellTest_2816_block_23 : Interval cellTest_2816 184 192 :=
  interval_of_check cellTest_2816 184 8 (by decide +kernel)

theorem cellTest_2816_block_24 : Interval cellTest_2816 192 200 :=
  interval_of_check cellTest_2816 192 8 (by decide +kernel)

theorem cellTest_2816_block_25 : Interval cellTest_2816 200 208 :=
  interval_of_check cellTest_2816 200 8 (by decide +kernel)

theorem cellTest_2816_block_26 : Interval cellTest_2816 208 216 :=
  interval_of_check cellTest_2816 208 8 (by decide +kernel)

theorem cellTest_2816_block_27 : Interval cellTest_2816 216 224 :=
  interval_of_check cellTest_2816 216 8 (by decide +kernel)

theorem cellTest_2816_block_28 : Interval cellTest_2816 224 232 :=
  interval_of_check cellTest_2816 224 8 (by decide +kernel)

theorem cellTest_2816_block_29 : Interval cellTest_2816 232 240 :=
  interval_of_check cellTest_2816 232 8 (by decide +kernel)

theorem cellTest_2816_block_30 : Interval cellTest_2816 240 248 :=
  interval_of_check cellTest_2816 240 8 (by decide +kernel)

theorem cellTest_2816_block_31 : Interval cellTest_2816 248 256 :=
  interval_of_check cellTest_2816 248 8 (by decide +kernel)

theorem cellTest_2816_complete : Interval cellTest_2816 0 256 :=
  (interval_append cellTest_2816 0 128 256
  (interval_append cellTest_2816 0 64 128
  (interval_append cellTest_2816 0 32 64
  (interval_append cellTest_2816 0 16 32
  (interval_append cellTest_2816 0 8 16
  cellTest_2816_block_0
  cellTest_2816_block_1)
  (interval_append cellTest_2816 16 24 32
  cellTest_2816_block_2
  cellTest_2816_block_3))
  (interval_append cellTest_2816 32 48 64
  (interval_append cellTest_2816 32 40 48
  cellTest_2816_block_4
  cellTest_2816_block_5)
  (interval_append cellTest_2816 48 56 64
  cellTest_2816_block_6
  cellTest_2816_block_7)))
  (interval_append cellTest_2816 64 96 128
  (interval_append cellTest_2816 64 80 96
  (interval_append cellTest_2816 64 72 80
  cellTest_2816_block_8
  cellTest_2816_block_9)
  (interval_append cellTest_2816 80 88 96
  cellTest_2816_block_10
  cellTest_2816_block_11))
  (interval_append cellTest_2816 96 112 128
  (interval_append cellTest_2816 96 104 112
  cellTest_2816_block_12
  cellTest_2816_block_13)
  (interval_append cellTest_2816 112 120 128
  cellTest_2816_block_14
  cellTest_2816_block_15))))
  (interval_append cellTest_2816 128 192 256
  (interval_append cellTest_2816 128 160 192
  (interval_append cellTest_2816 128 144 160
  (interval_append cellTest_2816 128 136 144
  cellTest_2816_block_16
  cellTest_2816_block_17)
  (interval_append cellTest_2816 144 152 160
  cellTest_2816_block_18
  cellTest_2816_block_19))
  (interval_append cellTest_2816 160 176 192
  (interval_append cellTest_2816 160 168 176
  cellTest_2816_block_20
  cellTest_2816_block_21)
  (interval_append cellTest_2816 176 184 192
  cellTest_2816_block_22
  cellTest_2816_block_23)))
  (interval_append cellTest_2816 192 224 256
  (interval_append cellTest_2816 192 208 224
  (interval_append cellTest_2816 192 200 208
  cellTest_2816_block_24
  cellTest_2816_block_25)
  (interval_append cellTest_2816 208 216 224
  cellTest_2816_block_26
  cellTest_2816_block_27))
  (interval_append cellTest_2816 224 240 256
  (interval_append cellTest_2816 224 232 240
  cellTest_2816_block_28
  cellTest_2816_block_29)
  (interval_append cellTest_2816 240 248 256
  cellTest_2816_block_30
  cellTest_2816_block_31)))))
theorem cellTestInterval2816 : Interval cellTest 2816 3072 := by
  intro i hlo hhi
  have h := cellTest_2816_complete (i-2816) (Nat.zero_le _) (by omega)
  simpa only [cellTest_2816, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells012 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_3072 (i : Nat) := cellTest (i+3072)
theorem cellTest_3072_block_0 : Interval cellTest_3072 0 8 :=
  interval_of_check cellTest_3072 0 8 (by decide +kernel)

theorem cellTest_3072_block_1 : Interval cellTest_3072 8 16 :=
  interval_of_check cellTest_3072 8 8 (by decide +kernel)

theorem cellTest_3072_block_2 : Interval cellTest_3072 16 24 :=
  interval_of_check cellTest_3072 16 8 (by decide +kernel)

theorem cellTest_3072_block_3 : Interval cellTest_3072 24 32 :=
  interval_of_check cellTest_3072 24 8 (by decide +kernel)

theorem cellTest_3072_block_4 : Interval cellTest_3072 32 40 :=
  interval_of_check cellTest_3072 32 8 (by decide +kernel)

theorem cellTest_3072_block_5 : Interval cellTest_3072 40 48 :=
  interval_of_check cellTest_3072 40 8 (by decide +kernel)

theorem cellTest_3072_block_6 : Interval cellTest_3072 48 56 :=
  interval_of_check cellTest_3072 48 8 (by decide +kernel)

theorem cellTest_3072_block_7 : Interval cellTest_3072 56 64 :=
  interval_of_check cellTest_3072 56 8 (by decide +kernel)

theorem cellTest_3072_block_8 : Interval cellTest_3072 64 72 :=
  interval_of_check cellTest_3072 64 8 (by decide +kernel)

theorem cellTest_3072_block_9 : Interval cellTest_3072 72 78 :=
  interval_of_check cellTest_3072 72 6 (by decide +kernel)

theorem cellTest_3072_complete : Interval cellTest_3072 0 78 :=
  (interval_append cellTest_3072 0 40 78
  (interval_append cellTest_3072 0 16 40
  (interval_append cellTest_3072 0 8 16
  cellTest_3072_block_0
  cellTest_3072_block_1)
  (interval_append cellTest_3072 16 24 40
  cellTest_3072_block_2
  (interval_append cellTest_3072 24 32 40
  cellTest_3072_block_3
  cellTest_3072_block_4)))
  (interval_append cellTest_3072 40 56 78
  (interval_append cellTest_3072 40 48 56
  cellTest_3072_block_5
  cellTest_3072_block_6)
  (interval_append cellTest_3072 56 64 78
  cellTest_3072_block_7
  (interval_append cellTest_3072 64 72 78
  cellTest_3072_block_8
  cellTest_3072_block_9))))
theorem cellTestInterval3072 : Interval cellTest 3072 3150 := by
  intro i hlo hhi
  have h := cellTest_3072_complete (i-3072) (Nat.zero_le _) (by omega)
  simpa only [cellTest_3072, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheBad000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheBad001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheBad002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
