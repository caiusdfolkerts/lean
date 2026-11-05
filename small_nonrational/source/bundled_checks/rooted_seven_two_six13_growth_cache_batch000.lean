module
prelude
public import RootedSevenTwoSix13GrowthCacheData

/- RootedSevenTwoSix13GrowthCacheCells000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheCells001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheCells002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheCells003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheCells004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheCells005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheCells006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheCells007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

theorem cellTest_1792_block_30 : Interval cellTest_1792 240 246 :=
  interval_of_check cellTest_1792 240 6 (by decide +kernel)

theorem cellTest_1792_complete : Interval cellTest_1792 0 246 :=
  (interval_append cellTest_1792 0 120 246
  (interval_append cellTest_1792 0 56 120
  (interval_append cellTest_1792 0 24 56
  (interval_append cellTest_1792 0 8 24
  cellTest_1792_block_0
  (interval_append cellTest_1792 8 16 24
  cellTest_1792_block_1
  cellTest_1792_block_2))
  (interval_append cellTest_1792 24 40 56
  (interval_append cellTest_1792 24 32 40
  cellTest_1792_block_3
  cellTest_1792_block_4)
  (interval_append cellTest_1792 40 48 56
  cellTest_1792_block_5
  cellTest_1792_block_6)))
  (interval_append cellTest_1792 56 88 120
  (interval_append cellTest_1792 56 72 88
  (interval_append cellTest_1792 56 64 72
  cellTest_1792_block_7
  cellTest_1792_block_8)
  (interval_append cellTest_1792 72 80 88
  cellTest_1792_block_9
  cellTest_1792_block_10))
  (interval_append cellTest_1792 88 104 120
  (interval_append cellTest_1792 88 96 104
  cellTest_1792_block_11
  cellTest_1792_block_12)
  (interval_append cellTest_1792 104 112 120
  cellTest_1792_block_13
  cellTest_1792_block_14))))
  (interval_append cellTest_1792 120 184 246
  (interval_append cellTest_1792 120 152 184
  (interval_append cellTest_1792 120 136 152
  (interval_append cellTest_1792 120 128 136
  cellTest_1792_block_15
  cellTest_1792_block_16)
  (interval_append cellTest_1792 136 144 152
  cellTest_1792_block_17
  cellTest_1792_block_18))
  (interval_append cellTest_1792 152 168 184
  (interval_append cellTest_1792 152 160 168
  cellTest_1792_block_19
  cellTest_1792_block_20)
  (interval_append cellTest_1792 168 176 184
  cellTest_1792_block_21
  cellTest_1792_block_22)))
  (interval_append cellTest_1792 184 216 246
  (interval_append cellTest_1792 184 200 216
  (interval_append cellTest_1792 184 192 200
  cellTest_1792_block_23
  cellTest_1792_block_24)
  (interval_append cellTest_1792 200 208 216
  cellTest_1792_block_25
  cellTest_1792_block_26))
  (interval_append cellTest_1792 216 232 246
  (interval_append cellTest_1792 216 224 232
  cellTest_1792_block_27
  cellTest_1792_block_28)
  (interval_append cellTest_1792 232 240 246
  cellTest_1792_block_29
  cellTest_1792_block_30)))))
theorem cellTestInterval1792 : Interval cellTest 1792 2038 := by
  intro i hlo hhi
  have h := cellTest_1792_complete (i-1792) (Nat.zero_le _) (by omega)
  simpa only [cellTest_1792, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheBad000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheBad001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheBad002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheBad003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheBad004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheBad005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
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

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheBad006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_1536 (i : Nat) := badTest (i+1536)
theorem badTest_1536_block_0 : Interval badTest_1536 0 8 :=
  interval_of_check badTest_1536 0 8 (by decide +kernel)

theorem badTest_1536_block_1 : Interval badTest_1536 8 16 :=
  interval_of_check badTest_1536 8 8 (by decide +kernel)

theorem badTest_1536_block_2 : Interval badTest_1536 16 24 :=
  interval_of_check badTest_1536 16 8 (by decide +kernel)

theorem badTest_1536_block_3 : Interval badTest_1536 24 32 :=
  interval_of_check badTest_1536 24 8 (by decide +kernel)

theorem badTest_1536_block_4 : Interval badTest_1536 32 40 :=
  interval_of_check badTest_1536 32 8 (by decide +kernel)

theorem badTest_1536_block_5 : Interval badTest_1536 40 48 :=
  interval_of_check badTest_1536 40 8 (by decide +kernel)

theorem badTest_1536_block_6 : Interval badTest_1536 48 56 :=
  interval_of_check badTest_1536 48 8 (by decide +kernel)

theorem badTest_1536_block_7 : Interval badTest_1536 56 64 :=
  interval_of_check badTest_1536 56 8 (by decide +kernel)

theorem badTest_1536_block_8 : Interval badTest_1536 64 72 :=
  interval_of_check badTest_1536 64 8 (by decide +kernel)

theorem badTest_1536_block_9 : Interval badTest_1536 72 80 :=
  interval_of_check badTest_1536 72 8 (by decide +kernel)

theorem badTest_1536_block_10 : Interval badTest_1536 80 88 :=
  interval_of_check badTest_1536 80 8 (by decide +kernel)

theorem badTest_1536_block_11 : Interval badTest_1536 88 96 :=
  interval_of_check badTest_1536 88 8 (by decide +kernel)

theorem badTest_1536_block_12 : Interval badTest_1536 96 104 :=
  interval_of_check badTest_1536 96 8 (by decide +kernel)

theorem badTest_1536_block_13 : Interval badTest_1536 104 112 :=
  interval_of_check badTest_1536 104 8 (by decide +kernel)

theorem badTest_1536_block_14 : Interval badTest_1536 112 120 :=
  interval_of_check badTest_1536 112 8 (by decide +kernel)

theorem badTest_1536_block_15 : Interval badTest_1536 120 128 :=
  interval_of_check badTest_1536 120 8 (by decide +kernel)

theorem badTest_1536_block_16 : Interval badTest_1536 128 136 :=
  interval_of_check badTest_1536 128 8 (by decide +kernel)

theorem badTest_1536_block_17 : Interval badTest_1536 136 144 :=
  interval_of_check badTest_1536 136 8 (by decide +kernel)

theorem badTest_1536_block_18 : Interval badTest_1536 144 152 :=
  interval_of_check badTest_1536 144 8 (by decide +kernel)

theorem badTest_1536_block_19 : Interval badTest_1536 152 160 :=
  interval_of_check badTest_1536 152 8 (by decide +kernel)

theorem badTest_1536_block_20 : Interval badTest_1536 160 168 :=
  interval_of_check badTest_1536 160 8 (by decide +kernel)

theorem badTest_1536_block_21 : Interval badTest_1536 168 176 :=
  interval_of_check badTest_1536 168 8 (by decide +kernel)

theorem badTest_1536_block_22 : Interval badTest_1536 176 184 :=
  interval_of_check badTest_1536 176 8 (by decide +kernel)

theorem badTest_1536_block_23 : Interval badTest_1536 184 192 :=
  interval_of_check badTest_1536 184 8 (by decide +kernel)

theorem badTest_1536_block_24 : Interval badTest_1536 192 200 :=
  interval_of_check badTest_1536 192 8 (by decide +kernel)

theorem badTest_1536_block_25 : Interval badTest_1536 200 208 :=
  interval_of_check badTest_1536 200 8 (by decide +kernel)

theorem badTest_1536_block_26 : Interval badTest_1536 208 216 :=
  interval_of_check badTest_1536 208 8 (by decide +kernel)

theorem badTest_1536_block_27 : Interval badTest_1536 216 224 :=
  interval_of_check badTest_1536 216 8 (by decide +kernel)

theorem badTest_1536_block_28 : Interval badTest_1536 224 232 :=
  interval_of_check badTest_1536 224 8 (by decide +kernel)

theorem badTest_1536_block_29 : Interval badTest_1536 232 240 :=
  interval_of_check badTest_1536 232 8 (by decide +kernel)

theorem badTest_1536_block_30 : Interval badTest_1536 240 248 :=
  interval_of_check badTest_1536 240 8 (by decide +kernel)

theorem badTest_1536_block_31 : Interval badTest_1536 248 256 :=
  interval_of_check badTest_1536 248 8 (by decide +kernel)

theorem badTest_1536_complete : Interval badTest_1536 0 256 :=
  (interval_append badTest_1536 0 128 256
  (interval_append badTest_1536 0 64 128
  (interval_append badTest_1536 0 32 64
  (interval_append badTest_1536 0 16 32
  (interval_append badTest_1536 0 8 16
  badTest_1536_block_0
  badTest_1536_block_1)
  (interval_append badTest_1536 16 24 32
  badTest_1536_block_2
  badTest_1536_block_3))
  (interval_append badTest_1536 32 48 64
  (interval_append badTest_1536 32 40 48
  badTest_1536_block_4
  badTest_1536_block_5)
  (interval_append badTest_1536 48 56 64
  badTest_1536_block_6
  badTest_1536_block_7)))
  (interval_append badTest_1536 64 96 128
  (interval_append badTest_1536 64 80 96
  (interval_append badTest_1536 64 72 80
  badTest_1536_block_8
  badTest_1536_block_9)
  (interval_append badTest_1536 80 88 96
  badTest_1536_block_10
  badTest_1536_block_11))
  (interval_append badTest_1536 96 112 128
  (interval_append badTest_1536 96 104 112
  badTest_1536_block_12
  badTest_1536_block_13)
  (interval_append badTest_1536 112 120 128
  badTest_1536_block_14
  badTest_1536_block_15))))
  (interval_append badTest_1536 128 192 256
  (interval_append badTest_1536 128 160 192
  (interval_append badTest_1536 128 144 160
  (interval_append badTest_1536 128 136 144
  badTest_1536_block_16
  badTest_1536_block_17)
  (interval_append badTest_1536 144 152 160
  badTest_1536_block_18
  badTest_1536_block_19))
  (interval_append badTest_1536 160 176 192
  (interval_append badTest_1536 160 168 176
  badTest_1536_block_20
  badTest_1536_block_21)
  (interval_append badTest_1536 176 184 192
  badTest_1536_block_22
  badTest_1536_block_23)))
  (interval_append badTest_1536 192 224 256
  (interval_append badTest_1536 192 208 224
  (interval_append badTest_1536 192 200 208
  badTest_1536_block_24
  badTest_1536_block_25)
  (interval_append badTest_1536 208 216 224
  badTest_1536_block_26
  badTest_1536_block_27))
  (interval_append badTest_1536 224 240 256
  (interval_append badTest_1536 224 232 240
  badTest_1536_block_28
  badTest_1536_block_29)
  (interval_append badTest_1536 240 248 256
  badTest_1536_block_30
  badTest_1536_block_31)))))
theorem badTestInterval1536 : Interval badTest 1536 1792 := by
  intro i hlo hhi
  have h := badTest_1536_complete (i-1536) (Nat.zero_le _) (by omega)
  simpa only [badTest_1536, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
/- RootedSevenTwoSix13GrowthCacheBad007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_1792 (i : Nat) := badTest (i+1792)
theorem badTest_1792_block_0 : Interval badTest_1792 0 8 :=
  interval_of_check badTest_1792 0 8 (by decide +kernel)

theorem badTest_1792_block_1 : Interval badTest_1792 8 16 :=
  interval_of_check badTest_1792 8 8 (by decide +kernel)

theorem badTest_1792_block_2 : Interval badTest_1792 16 24 :=
  interval_of_check badTest_1792 16 8 (by decide +kernel)

theorem badTest_1792_block_3 : Interval badTest_1792 24 32 :=
  interval_of_check badTest_1792 24 8 (by decide +kernel)

theorem badTest_1792_block_4 : Interval badTest_1792 32 40 :=
  interval_of_check badTest_1792 32 8 (by decide +kernel)

theorem badTest_1792_block_5 : Interval badTest_1792 40 48 :=
  interval_of_check badTest_1792 40 8 (by decide +kernel)

theorem badTest_1792_block_6 : Interval badTest_1792 48 56 :=
  interval_of_check badTest_1792 48 8 (by decide +kernel)

theorem badTest_1792_block_7 : Interval badTest_1792 56 64 :=
  interval_of_check badTest_1792 56 8 (by decide +kernel)

theorem badTest_1792_block_8 : Interval badTest_1792 64 72 :=
  interval_of_check badTest_1792 64 8 (by decide +kernel)

theorem badTest_1792_block_9 : Interval badTest_1792 72 80 :=
  interval_of_check badTest_1792 72 8 (by decide +kernel)

theorem badTest_1792_block_10 : Interval badTest_1792 80 88 :=
  interval_of_check badTest_1792 80 8 (by decide +kernel)

theorem badTest_1792_block_11 : Interval badTest_1792 88 96 :=
  interval_of_check badTest_1792 88 8 (by decide +kernel)

theorem badTest_1792_block_12 : Interval badTest_1792 96 104 :=
  interval_of_check badTest_1792 96 8 (by decide +kernel)

theorem badTest_1792_block_13 : Interval badTest_1792 104 112 :=
  interval_of_check badTest_1792 104 8 (by decide +kernel)

theorem badTest_1792_block_14 : Interval badTest_1792 112 120 :=
  interval_of_check badTest_1792 112 8 (by decide +kernel)

theorem badTest_1792_block_15 : Interval badTest_1792 120 128 :=
  interval_of_check badTest_1792 120 8 (by decide +kernel)

theorem badTest_1792_block_16 : Interval badTest_1792 128 136 :=
  interval_of_check badTest_1792 128 8 (by decide +kernel)

theorem badTest_1792_block_17 : Interval badTest_1792 136 144 :=
  interval_of_check badTest_1792 136 8 (by decide +kernel)

theorem badTest_1792_block_18 : Interval badTest_1792 144 152 :=
  interval_of_check badTest_1792 144 8 (by decide +kernel)

theorem badTest_1792_block_19 : Interval badTest_1792 152 160 :=
  interval_of_check badTest_1792 152 8 (by decide +kernel)

theorem badTest_1792_block_20 : Interval badTest_1792 160 168 :=
  interval_of_check badTest_1792 160 8 (by decide +kernel)

theorem badTest_1792_block_21 : Interval badTest_1792 168 176 :=
  interval_of_check badTest_1792 168 8 (by decide +kernel)

theorem badTest_1792_block_22 : Interval badTest_1792 176 184 :=
  interval_of_check badTest_1792 176 8 (by decide +kernel)

theorem badTest_1792_block_23 : Interval badTest_1792 184 192 :=
  interval_of_check badTest_1792 184 8 (by decide +kernel)

theorem badTest_1792_block_24 : Interval badTest_1792 192 200 :=
  interval_of_check badTest_1792 192 8 (by decide +kernel)

theorem badTest_1792_block_25 : Interval badTest_1792 200 208 :=
  interval_of_check badTest_1792 200 8 (by decide +kernel)

theorem badTest_1792_block_26 : Interval badTest_1792 208 216 :=
  interval_of_check badTest_1792 208 8 (by decide +kernel)

theorem badTest_1792_block_27 : Interval badTest_1792 216 224 :=
  interval_of_check badTest_1792 216 8 (by decide +kernel)

theorem badTest_1792_block_28 : Interval badTest_1792 224 232 :=
  interval_of_check badTest_1792 224 8 (by decide +kernel)

theorem badTest_1792_block_29 : Interval badTest_1792 232 240 :=
  interval_of_check badTest_1792 232 8 (by decide +kernel)

theorem badTest_1792_block_30 : Interval badTest_1792 240 246 :=
  interval_of_check badTest_1792 240 6 (by decide +kernel)

theorem badTest_1792_complete : Interval badTest_1792 0 246 :=
  (interval_append badTest_1792 0 120 246
  (interval_append badTest_1792 0 56 120
  (interval_append badTest_1792 0 24 56
  (interval_append badTest_1792 0 8 24
  badTest_1792_block_0
  (interval_append badTest_1792 8 16 24
  badTest_1792_block_1
  badTest_1792_block_2))
  (interval_append badTest_1792 24 40 56
  (interval_append badTest_1792 24 32 40
  badTest_1792_block_3
  badTest_1792_block_4)
  (interval_append badTest_1792 40 48 56
  badTest_1792_block_5
  badTest_1792_block_6)))
  (interval_append badTest_1792 56 88 120
  (interval_append badTest_1792 56 72 88
  (interval_append badTest_1792 56 64 72
  badTest_1792_block_7
  badTest_1792_block_8)
  (interval_append badTest_1792 72 80 88
  badTest_1792_block_9
  badTest_1792_block_10))
  (interval_append badTest_1792 88 104 120
  (interval_append badTest_1792 88 96 104
  badTest_1792_block_11
  badTest_1792_block_12)
  (interval_append badTest_1792 104 112 120
  badTest_1792_block_13
  badTest_1792_block_14))))
  (interval_append badTest_1792 120 184 246
  (interval_append badTest_1792 120 152 184
  (interval_append badTest_1792 120 136 152
  (interval_append badTest_1792 120 128 136
  badTest_1792_block_15
  badTest_1792_block_16)
  (interval_append badTest_1792 136 144 152
  badTest_1792_block_17
  badTest_1792_block_18))
  (interval_append badTest_1792 152 168 184
  (interval_append badTest_1792 152 160 168
  badTest_1792_block_19
  badTest_1792_block_20)
  (interval_append badTest_1792 168 176 184
  badTest_1792_block_21
  badTest_1792_block_22)))
  (interval_append badTest_1792 184 216 246
  (interval_append badTest_1792 184 200 216
  (interval_append badTest_1792 184 192 200
  badTest_1792_block_23
  badTest_1792_block_24)
  (interval_append badTest_1792 200 208 216
  badTest_1792_block_25
  badTest_1792_block_26))
  (interval_append badTest_1792 216 232 246
  (interval_append badTest_1792 216 224 232
  badTest_1792_block_27
  badTest_1792_block_28)
  (interval_append badTest_1792 232 240 246
  badTest_1792_block_29
  badTest_1792_block_30)))))
theorem badTestInterval1792 : Interval badTest 1792 2038 := by
  intro i hlo hhi
  have h := badTest_1792_complete (i-1792) (Nat.zero_le _) (by omega)
  simpa only [badTest_1792, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13

end
end
