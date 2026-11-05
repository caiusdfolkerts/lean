module
prelude
public import RootedSevenPure020GrowthCacheData

/- RootedSevenPure020GrowthCacheCells000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheCells001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheCells002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
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

theorem cellTest_512_block_9 : Interval cellTest_512 72 74 :=
  interval_of_check cellTest_512 72 2 (by decide +kernel)

theorem cellTest_512_complete : Interval cellTest_512 0 74 :=
  (interval_append cellTest_512 0 40 74
  (interval_append cellTest_512 0 16 40
  (interval_append cellTest_512 0 8 16
  cellTest_512_block_0
  cellTest_512_block_1)
  (interval_append cellTest_512 16 24 40
  cellTest_512_block_2
  (interval_append cellTest_512 24 32 40
  cellTest_512_block_3
  cellTest_512_block_4)))
  (interval_append cellTest_512 40 56 74
  (interval_append cellTest_512 40 48 56
  cellTest_512_block_5
  cellTest_512_block_6)
  (interval_append cellTest_512 56 64 74
  cellTest_512_block_7
  (interval_append cellTest_512 64 72 74
  cellTest_512_block_8
  cellTest_512_block_9))))
theorem cellTestInterval512 : Interval cellTest 512 586 := by
  intro i hlo hhi
  have h := cellTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [cellTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheBad000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheBad001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
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

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheBad002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
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

theorem badTest_512_block_9 : Interval badTest_512 72 74 :=
  interval_of_check badTest_512 72 2 (by decide +kernel)

theorem badTest_512_complete : Interval badTest_512 0 74 :=
  (interval_append badTest_512 0 40 74
  (interval_append badTest_512 0 16 40
  (interval_append badTest_512 0 8 16
  badTest_512_block_0
  badTest_512_block_1)
  (interval_append badTest_512 16 24 40
  badTest_512_block_2
  (interval_append badTest_512 24 32 40
  badTest_512_block_3
  badTest_512_block_4)))
  (interval_append badTest_512 40 56 74
  (interval_append badTest_512 40 48 56
  badTest_512_block_5
  badTest_512_block_6)
  (interval_append badTest_512 56 64 74
  badTest_512_block_7
  (interval_append badTest_512 64 72 74
  badTest_512_block_8
  badTest_512_block_9))))
theorem badTestInterval512 : Interval badTest 512 586 := by
  intro i hlo hhi
  have h := badTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [badTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheRidges000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_0 (i : Nat) := ridgeTest (i+0)
theorem ridgeTest_0_block_0 : Interval ridgeTest_0 0 8 :=
  interval_of_check ridgeTest_0 0 8 (by decide +kernel)

theorem ridgeTest_0_block_1 : Interval ridgeTest_0 8 16 :=
  interval_of_check ridgeTest_0 8 8 (by decide +kernel)

theorem ridgeTest_0_block_2 : Interval ridgeTest_0 16 24 :=
  interval_of_check ridgeTest_0 16 8 (by decide +kernel)

theorem ridgeTest_0_block_3 : Interval ridgeTest_0 24 32 :=
  interval_of_check ridgeTest_0 24 8 (by decide +kernel)

theorem ridgeTest_0_block_4 : Interval ridgeTest_0 32 40 :=
  interval_of_check ridgeTest_0 32 8 (by decide +kernel)

theorem ridgeTest_0_block_5 : Interval ridgeTest_0 40 48 :=
  interval_of_check ridgeTest_0 40 8 (by decide +kernel)

theorem ridgeTest_0_block_6 : Interval ridgeTest_0 48 56 :=
  interval_of_check ridgeTest_0 48 8 (by decide +kernel)

theorem ridgeTest_0_block_7 : Interval ridgeTest_0 56 64 :=
  interval_of_check ridgeTest_0 56 8 (by decide +kernel)

theorem ridgeTest_0_block_8 : Interval ridgeTest_0 64 72 :=
  interval_of_check ridgeTest_0 64 8 (by decide +kernel)

theorem ridgeTest_0_block_9 : Interval ridgeTest_0 72 80 :=
  interval_of_check ridgeTest_0 72 8 (by decide +kernel)

theorem ridgeTest_0_block_10 : Interval ridgeTest_0 80 88 :=
  interval_of_check ridgeTest_0 80 8 (by decide +kernel)

theorem ridgeTest_0_block_11 : Interval ridgeTest_0 88 96 :=
  interval_of_check ridgeTest_0 88 8 (by decide +kernel)

theorem ridgeTest_0_block_12 : Interval ridgeTest_0 96 104 :=
  interval_of_check ridgeTest_0 96 8 (by decide +kernel)

theorem ridgeTest_0_block_13 : Interval ridgeTest_0 104 112 :=
  interval_of_check ridgeTest_0 104 8 (by decide +kernel)

theorem ridgeTest_0_block_14 : Interval ridgeTest_0 112 120 :=
  interval_of_check ridgeTest_0 112 8 (by decide +kernel)

theorem ridgeTest_0_block_15 : Interval ridgeTest_0 120 128 :=
  interval_of_check ridgeTest_0 120 8 (by decide +kernel)

theorem ridgeTest_0_complete : Interval ridgeTest_0 0 128 :=
  (interval_append ridgeTest_0 0 64 128
  (interval_append ridgeTest_0 0 32 64
  (interval_append ridgeTest_0 0 16 32
  (interval_append ridgeTest_0 0 8 16
  ridgeTest_0_block_0
  ridgeTest_0_block_1)
  (interval_append ridgeTest_0 16 24 32
  ridgeTest_0_block_2
  ridgeTest_0_block_3))
  (interval_append ridgeTest_0 32 48 64
  (interval_append ridgeTest_0 32 40 48
  ridgeTest_0_block_4
  ridgeTest_0_block_5)
  (interval_append ridgeTest_0 48 56 64
  ridgeTest_0_block_6
  ridgeTest_0_block_7)))
  (interval_append ridgeTest_0 64 96 128
  (interval_append ridgeTest_0 64 80 96
  (interval_append ridgeTest_0 64 72 80
  ridgeTest_0_block_8
  ridgeTest_0_block_9)
  (interval_append ridgeTest_0 80 88 96
  ridgeTest_0_block_10
  ridgeTest_0_block_11))
  (interval_append ridgeTest_0 96 112 128
  (interval_append ridgeTest_0 96 104 112
  ridgeTest_0_block_12
  ridgeTest_0_block_13)
  (interval_append ridgeTest_0 112 120 128
  ridgeTest_0_block_14
  ridgeTest_0_block_15))))
theorem ridgeTestInterval0 : Interval ridgeTest 0 128 := by
  intro i hlo hhi
  have h := ridgeTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheRidges001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_128 (i : Nat) := ridgeTest (i+128)
theorem ridgeTest_128_block_0 : Interval ridgeTest_128 0 8 :=
  interval_of_check ridgeTest_128 0 8 (by decide +kernel)

theorem ridgeTest_128_block_1 : Interval ridgeTest_128 8 16 :=
  interval_of_check ridgeTest_128 8 8 (by decide +kernel)

theorem ridgeTest_128_block_2 : Interval ridgeTest_128 16 24 :=
  interval_of_check ridgeTest_128 16 8 (by decide +kernel)

theorem ridgeTest_128_block_3 : Interval ridgeTest_128 24 32 :=
  interval_of_check ridgeTest_128 24 8 (by decide +kernel)

theorem ridgeTest_128_block_4 : Interval ridgeTest_128 32 40 :=
  interval_of_check ridgeTest_128 32 8 (by decide +kernel)

theorem ridgeTest_128_block_5 : Interval ridgeTest_128 40 48 :=
  interval_of_check ridgeTest_128 40 8 (by decide +kernel)

theorem ridgeTest_128_block_6 : Interval ridgeTest_128 48 56 :=
  interval_of_check ridgeTest_128 48 8 (by decide +kernel)

theorem ridgeTest_128_block_7 : Interval ridgeTest_128 56 64 :=
  interval_of_check ridgeTest_128 56 8 (by decide +kernel)

theorem ridgeTest_128_block_8 : Interval ridgeTest_128 64 72 :=
  interval_of_check ridgeTest_128 64 8 (by decide +kernel)

theorem ridgeTest_128_block_9 : Interval ridgeTest_128 72 80 :=
  interval_of_check ridgeTest_128 72 8 (by decide +kernel)

theorem ridgeTest_128_block_10 : Interval ridgeTest_128 80 88 :=
  interval_of_check ridgeTest_128 80 8 (by decide +kernel)

theorem ridgeTest_128_block_11 : Interval ridgeTest_128 88 96 :=
  interval_of_check ridgeTest_128 88 8 (by decide +kernel)

theorem ridgeTest_128_block_12 : Interval ridgeTest_128 96 104 :=
  interval_of_check ridgeTest_128 96 8 (by decide +kernel)

theorem ridgeTest_128_block_13 : Interval ridgeTest_128 104 112 :=
  interval_of_check ridgeTest_128 104 8 (by decide +kernel)

theorem ridgeTest_128_block_14 : Interval ridgeTest_128 112 120 :=
  interval_of_check ridgeTest_128 112 8 (by decide +kernel)

theorem ridgeTest_128_block_15 : Interval ridgeTest_128 120 128 :=
  interval_of_check ridgeTest_128 120 8 (by decide +kernel)

theorem ridgeTest_128_complete : Interval ridgeTest_128 0 128 :=
  (interval_append ridgeTest_128 0 64 128
  (interval_append ridgeTest_128 0 32 64
  (interval_append ridgeTest_128 0 16 32
  (interval_append ridgeTest_128 0 8 16
  ridgeTest_128_block_0
  ridgeTest_128_block_1)
  (interval_append ridgeTest_128 16 24 32
  ridgeTest_128_block_2
  ridgeTest_128_block_3))
  (interval_append ridgeTest_128 32 48 64
  (interval_append ridgeTest_128 32 40 48
  ridgeTest_128_block_4
  ridgeTest_128_block_5)
  (interval_append ridgeTest_128 48 56 64
  ridgeTest_128_block_6
  ridgeTest_128_block_7)))
  (interval_append ridgeTest_128 64 96 128
  (interval_append ridgeTest_128 64 80 96
  (interval_append ridgeTest_128 64 72 80
  ridgeTest_128_block_8
  ridgeTest_128_block_9)
  (interval_append ridgeTest_128 80 88 96
  ridgeTest_128_block_10
  ridgeTest_128_block_11))
  (interval_append ridgeTest_128 96 112 128
  (interval_append ridgeTest_128 96 104 112
  ridgeTest_128_block_12
  ridgeTest_128_block_13)
  (interval_append ridgeTest_128 112 120 128
  ridgeTest_128_block_14
  ridgeTest_128_block_15))))
theorem ridgeTestInterval128 : Interval ridgeTest 128 256 := by
  intro i hlo hhi
  have h := ridgeTest_128_complete (i-128) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheRidges002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_256 (i : Nat) := ridgeTest (i+256)
theorem ridgeTest_256_block_0 : Interval ridgeTest_256 0 8 :=
  interval_of_check ridgeTest_256 0 8 (by decide +kernel)

theorem ridgeTest_256_block_1 : Interval ridgeTest_256 8 16 :=
  interval_of_check ridgeTest_256 8 8 (by decide +kernel)

theorem ridgeTest_256_block_2 : Interval ridgeTest_256 16 24 :=
  interval_of_check ridgeTest_256 16 8 (by decide +kernel)

theorem ridgeTest_256_block_3 : Interval ridgeTest_256 24 32 :=
  interval_of_check ridgeTest_256 24 8 (by decide +kernel)

theorem ridgeTest_256_block_4 : Interval ridgeTest_256 32 40 :=
  interval_of_check ridgeTest_256 32 8 (by decide +kernel)

theorem ridgeTest_256_block_5 : Interval ridgeTest_256 40 48 :=
  interval_of_check ridgeTest_256 40 8 (by decide +kernel)

theorem ridgeTest_256_block_6 : Interval ridgeTest_256 48 56 :=
  interval_of_check ridgeTest_256 48 8 (by decide +kernel)

theorem ridgeTest_256_block_7 : Interval ridgeTest_256 56 64 :=
  interval_of_check ridgeTest_256 56 8 (by decide +kernel)

theorem ridgeTest_256_block_8 : Interval ridgeTest_256 64 72 :=
  interval_of_check ridgeTest_256 64 8 (by decide +kernel)

theorem ridgeTest_256_block_9 : Interval ridgeTest_256 72 80 :=
  interval_of_check ridgeTest_256 72 8 (by decide +kernel)

theorem ridgeTest_256_block_10 : Interval ridgeTest_256 80 88 :=
  interval_of_check ridgeTest_256 80 8 (by decide +kernel)

theorem ridgeTest_256_block_11 : Interval ridgeTest_256 88 96 :=
  interval_of_check ridgeTest_256 88 8 (by decide +kernel)

theorem ridgeTest_256_block_12 : Interval ridgeTest_256 96 104 :=
  interval_of_check ridgeTest_256 96 8 (by decide +kernel)

theorem ridgeTest_256_block_13 : Interval ridgeTest_256 104 112 :=
  interval_of_check ridgeTest_256 104 8 (by decide +kernel)

theorem ridgeTest_256_block_14 : Interval ridgeTest_256 112 120 :=
  interval_of_check ridgeTest_256 112 8 (by decide +kernel)

theorem ridgeTest_256_block_15 : Interval ridgeTest_256 120 128 :=
  interval_of_check ridgeTest_256 120 8 (by decide +kernel)

theorem ridgeTest_256_complete : Interval ridgeTest_256 0 128 :=
  (interval_append ridgeTest_256 0 64 128
  (interval_append ridgeTest_256 0 32 64
  (interval_append ridgeTest_256 0 16 32
  (interval_append ridgeTest_256 0 8 16
  ridgeTest_256_block_0
  ridgeTest_256_block_1)
  (interval_append ridgeTest_256 16 24 32
  ridgeTest_256_block_2
  ridgeTest_256_block_3))
  (interval_append ridgeTest_256 32 48 64
  (interval_append ridgeTest_256 32 40 48
  ridgeTest_256_block_4
  ridgeTest_256_block_5)
  (interval_append ridgeTest_256 48 56 64
  ridgeTest_256_block_6
  ridgeTest_256_block_7)))
  (interval_append ridgeTest_256 64 96 128
  (interval_append ridgeTest_256 64 80 96
  (interval_append ridgeTest_256 64 72 80
  ridgeTest_256_block_8
  ridgeTest_256_block_9)
  (interval_append ridgeTest_256 80 88 96
  ridgeTest_256_block_10
  ridgeTest_256_block_11))
  (interval_append ridgeTest_256 96 112 128
  (interval_append ridgeTest_256 96 104 112
  ridgeTest_256_block_12
  ridgeTest_256_block_13)
  (interval_append ridgeTest_256 112 120 128
  ridgeTest_256_block_14
  ridgeTest_256_block_15))))
theorem ridgeTestInterval256 : Interval ridgeTest 256 384 := by
  intro i hlo hhi
  have h := ridgeTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheRidges003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_384 (i : Nat) := ridgeTest (i+384)
theorem ridgeTest_384_block_0 : Interval ridgeTest_384 0 8 :=
  interval_of_check ridgeTest_384 0 8 (by decide +kernel)

theorem ridgeTest_384_block_1 : Interval ridgeTest_384 8 16 :=
  interval_of_check ridgeTest_384 8 8 (by decide +kernel)

theorem ridgeTest_384_block_2 : Interval ridgeTest_384 16 24 :=
  interval_of_check ridgeTest_384 16 8 (by decide +kernel)

theorem ridgeTest_384_block_3 : Interval ridgeTest_384 24 32 :=
  interval_of_check ridgeTest_384 24 8 (by decide +kernel)

theorem ridgeTest_384_block_4 : Interval ridgeTest_384 32 40 :=
  interval_of_check ridgeTest_384 32 8 (by decide +kernel)

theorem ridgeTest_384_block_5 : Interval ridgeTest_384 40 48 :=
  interval_of_check ridgeTest_384 40 8 (by decide +kernel)

theorem ridgeTest_384_block_6 : Interval ridgeTest_384 48 56 :=
  interval_of_check ridgeTest_384 48 8 (by decide +kernel)

theorem ridgeTest_384_block_7 : Interval ridgeTest_384 56 64 :=
  interval_of_check ridgeTest_384 56 8 (by decide +kernel)

theorem ridgeTest_384_block_8 : Interval ridgeTest_384 64 72 :=
  interval_of_check ridgeTest_384 64 8 (by decide +kernel)

theorem ridgeTest_384_block_9 : Interval ridgeTest_384 72 80 :=
  interval_of_check ridgeTest_384 72 8 (by decide +kernel)

theorem ridgeTest_384_block_10 : Interval ridgeTest_384 80 88 :=
  interval_of_check ridgeTest_384 80 8 (by decide +kernel)

theorem ridgeTest_384_block_11 : Interval ridgeTest_384 88 96 :=
  interval_of_check ridgeTest_384 88 8 (by decide +kernel)

theorem ridgeTest_384_block_12 : Interval ridgeTest_384 96 104 :=
  interval_of_check ridgeTest_384 96 8 (by decide +kernel)

theorem ridgeTest_384_block_13 : Interval ridgeTest_384 104 112 :=
  interval_of_check ridgeTest_384 104 8 (by decide +kernel)

theorem ridgeTest_384_block_14 : Interval ridgeTest_384 112 120 :=
  interval_of_check ridgeTest_384 112 8 (by decide +kernel)

theorem ridgeTest_384_block_15 : Interval ridgeTest_384 120 128 :=
  interval_of_check ridgeTest_384 120 8 (by decide +kernel)

theorem ridgeTest_384_complete : Interval ridgeTest_384 0 128 :=
  (interval_append ridgeTest_384 0 64 128
  (interval_append ridgeTest_384 0 32 64
  (interval_append ridgeTest_384 0 16 32
  (interval_append ridgeTest_384 0 8 16
  ridgeTest_384_block_0
  ridgeTest_384_block_1)
  (interval_append ridgeTest_384 16 24 32
  ridgeTest_384_block_2
  ridgeTest_384_block_3))
  (interval_append ridgeTest_384 32 48 64
  (interval_append ridgeTest_384 32 40 48
  ridgeTest_384_block_4
  ridgeTest_384_block_5)
  (interval_append ridgeTest_384 48 56 64
  ridgeTest_384_block_6
  ridgeTest_384_block_7)))
  (interval_append ridgeTest_384 64 96 128
  (interval_append ridgeTest_384 64 80 96
  (interval_append ridgeTest_384 64 72 80
  ridgeTest_384_block_8
  ridgeTest_384_block_9)
  (interval_append ridgeTest_384 80 88 96
  ridgeTest_384_block_10
  ridgeTest_384_block_11))
  (interval_append ridgeTest_384 96 112 128
  (interval_append ridgeTest_384 96 104 112
  ridgeTest_384_block_12
  ridgeTest_384_block_13)
  (interval_append ridgeTest_384 112 120 128
  ridgeTest_384_block_14
  ridgeTest_384_block_15))))
theorem ridgeTestInterval384 : Interval ridgeTest 384 512 := by
  intro i hlo hhi
  have h := ridgeTest_384_complete (i-384) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_384, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheRidges004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_512 (i : Nat) := ridgeTest (i+512)
theorem ridgeTest_512_block_0 : Interval ridgeTest_512 0 8 :=
  interval_of_check ridgeTest_512 0 8 (by decide +kernel)

theorem ridgeTest_512_block_1 : Interval ridgeTest_512 8 16 :=
  interval_of_check ridgeTest_512 8 8 (by decide +kernel)

theorem ridgeTest_512_block_2 : Interval ridgeTest_512 16 24 :=
  interval_of_check ridgeTest_512 16 8 (by decide +kernel)

theorem ridgeTest_512_block_3 : Interval ridgeTest_512 24 32 :=
  interval_of_check ridgeTest_512 24 8 (by decide +kernel)

theorem ridgeTest_512_block_4 : Interval ridgeTest_512 32 40 :=
  interval_of_check ridgeTest_512 32 8 (by decide +kernel)

theorem ridgeTest_512_block_5 : Interval ridgeTest_512 40 48 :=
  interval_of_check ridgeTest_512 40 8 (by decide +kernel)

theorem ridgeTest_512_block_6 : Interval ridgeTest_512 48 56 :=
  interval_of_check ridgeTest_512 48 8 (by decide +kernel)

theorem ridgeTest_512_block_7 : Interval ridgeTest_512 56 64 :=
  interval_of_check ridgeTest_512 56 8 (by decide +kernel)

theorem ridgeTest_512_block_8 : Interval ridgeTest_512 64 72 :=
  interval_of_check ridgeTest_512 64 8 (by decide +kernel)

theorem ridgeTest_512_block_9 : Interval ridgeTest_512 72 80 :=
  interval_of_check ridgeTest_512 72 8 (by decide +kernel)

theorem ridgeTest_512_block_10 : Interval ridgeTest_512 80 88 :=
  interval_of_check ridgeTest_512 80 8 (by decide +kernel)

theorem ridgeTest_512_block_11 : Interval ridgeTest_512 88 96 :=
  interval_of_check ridgeTest_512 88 8 (by decide +kernel)

theorem ridgeTest_512_block_12 : Interval ridgeTest_512 96 104 :=
  interval_of_check ridgeTest_512 96 8 (by decide +kernel)

theorem ridgeTest_512_block_13 : Interval ridgeTest_512 104 112 :=
  interval_of_check ridgeTest_512 104 8 (by decide +kernel)

theorem ridgeTest_512_block_14 : Interval ridgeTest_512 112 120 :=
  interval_of_check ridgeTest_512 112 8 (by decide +kernel)

theorem ridgeTest_512_block_15 : Interval ridgeTest_512 120 128 :=
  interval_of_check ridgeTest_512 120 8 (by decide +kernel)

theorem ridgeTest_512_complete : Interval ridgeTest_512 0 128 :=
  (interval_append ridgeTest_512 0 64 128
  (interval_append ridgeTest_512 0 32 64
  (interval_append ridgeTest_512 0 16 32
  (interval_append ridgeTest_512 0 8 16
  ridgeTest_512_block_0
  ridgeTest_512_block_1)
  (interval_append ridgeTest_512 16 24 32
  ridgeTest_512_block_2
  ridgeTest_512_block_3))
  (interval_append ridgeTest_512 32 48 64
  (interval_append ridgeTest_512 32 40 48
  ridgeTest_512_block_4
  ridgeTest_512_block_5)
  (interval_append ridgeTest_512 48 56 64
  ridgeTest_512_block_6
  ridgeTest_512_block_7)))
  (interval_append ridgeTest_512 64 96 128
  (interval_append ridgeTest_512 64 80 96
  (interval_append ridgeTest_512 64 72 80
  ridgeTest_512_block_8
  ridgeTest_512_block_9)
  (interval_append ridgeTest_512 80 88 96
  ridgeTest_512_block_10
  ridgeTest_512_block_11))
  (interval_append ridgeTest_512 96 112 128
  (interval_append ridgeTest_512 96 104 112
  ridgeTest_512_block_12
  ridgeTest_512_block_13)
  (interval_append ridgeTest_512 112 120 128
  ridgeTest_512_block_14
  ridgeTest_512_block_15))))
theorem ridgeTestInterval512 : Interval ridgeTest 512 640 := by
  intro i hlo hhi
  have h := ridgeTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheRidges005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_640 (i : Nat) := ridgeTest (i+640)
theorem ridgeTest_640_block_0 : Interval ridgeTest_640 0 8 :=
  interval_of_check ridgeTest_640 0 8 (by decide +kernel)

theorem ridgeTest_640_block_1 : Interval ridgeTest_640 8 16 :=
  interval_of_check ridgeTest_640 8 8 (by decide +kernel)

theorem ridgeTest_640_block_2 : Interval ridgeTest_640 16 24 :=
  interval_of_check ridgeTest_640 16 8 (by decide +kernel)

theorem ridgeTest_640_block_3 : Interval ridgeTest_640 24 32 :=
  interval_of_check ridgeTest_640 24 8 (by decide +kernel)

theorem ridgeTest_640_block_4 : Interval ridgeTest_640 32 40 :=
  interval_of_check ridgeTest_640 32 8 (by decide +kernel)

theorem ridgeTest_640_block_5 : Interval ridgeTest_640 40 48 :=
  interval_of_check ridgeTest_640 40 8 (by decide +kernel)

theorem ridgeTest_640_block_6 : Interval ridgeTest_640 48 56 :=
  interval_of_check ridgeTest_640 48 8 (by decide +kernel)

theorem ridgeTest_640_block_7 : Interval ridgeTest_640 56 64 :=
  interval_of_check ridgeTest_640 56 8 (by decide +kernel)

theorem ridgeTest_640_block_8 : Interval ridgeTest_640 64 72 :=
  interval_of_check ridgeTest_640 64 8 (by decide +kernel)

theorem ridgeTest_640_block_9 : Interval ridgeTest_640 72 80 :=
  interval_of_check ridgeTest_640 72 8 (by decide +kernel)

theorem ridgeTest_640_block_10 : Interval ridgeTest_640 80 88 :=
  interval_of_check ridgeTest_640 80 8 (by decide +kernel)

theorem ridgeTest_640_block_11 : Interval ridgeTest_640 88 96 :=
  interval_of_check ridgeTest_640 88 8 (by decide +kernel)

theorem ridgeTest_640_block_12 : Interval ridgeTest_640 96 104 :=
  interval_of_check ridgeTest_640 96 8 (by decide +kernel)

theorem ridgeTest_640_block_13 : Interval ridgeTest_640 104 112 :=
  interval_of_check ridgeTest_640 104 8 (by decide +kernel)

theorem ridgeTest_640_block_14 : Interval ridgeTest_640 112 120 :=
  interval_of_check ridgeTest_640 112 8 (by decide +kernel)

theorem ridgeTest_640_block_15 : Interval ridgeTest_640 120 128 :=
  interval_of_check ridgeTest_640 120 8 (by decide +kernel)

theorem ridgeTest_640_complete : Interval ridgeTest_640 0 128 :=
  (interval_append ridgeTest_640 0 64 128
  (interval_append ridgeTest_640 0 32 64
  (interval_append ridgeTest_640 0 16 32
  (interval_append ridgeTest_640 0 8 16
  ridgeTest_640_block_0
  ridgeTest_640_block_1)
  (interval_append ridgeTest_640 16 24 32
  ridgeTest_640_block_2
  ridgeTest_640_block_3))
  (interval_append ridgeTest_640 32 48 64
  (interval_append ridgeTest_640 32 40 48
  ridgeTest_640_block_4
  ridgeTest_640_block_5)
  (interval_append ridgeTest_640 48 56 64
  ridgeTest_640_block_6
  ridgeTest_640_block_7)))
  (interval_append ridgeTest_640 64 96 128
  (interval_append ridgeTest_640 64 80 96
  (interval_append ridgeTest_640 64 72 80
  ridgeTest_640_block_8
  ridgeTest_640_block_9)
  (interval_append ridgeTest_640 80 88 96
  ridgeTest_640_block_10
  ridgeTest_640_block_11))
  (interval_append ridgeTest_640 96 112 128
  (interval_append ridgeTest_640 96 104 112
  ridgeTest_640_block_12
  ridgeTest_640_block_13)
  (interval_append ridgeTest_640 112 120 128
  ridgeTest_640_block_14
  ridgeTest_640_block_15))))
theorem ridgeTestInterval640 : Interval ridgeTest 640 768 := by
  intro i hlo hhi
  have h := ridgeTest_640_complete (i-640) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheRidges006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_768 (i : Nat) := ridgeTest (i+768)
theorem ridgeTest_768_block_0 : Interval ridgeTest_768 0 8 :=
  interval_of_check ridgeTest_768 0 8 (by decide +kernel)

theorem ridgeTest_768_block_1 : Interval ridgeTest_768 8 16 :=
  interval_of_check ridgeTest_768 8 8 (by decide +kernel)

theorem ridgeTest_768_block_2 : Interval ridgeTest_768 16 24 :=
  interval_of_check ridgeTest_768 16 8 (by decide +kernel)

theorem ridgeTest_768_block_3 : Interval ridgeTest_768 24 32 :=
  interval_of_check ridgeTest_768 24 8 (by decide +kernel)

theorem ridgeTest_768_block_4 : Interval ridgeTest_768 32 40 :=
  interval_of_check ridgeTest_768 32 8 (by decide +kernel)

theorem ridgeTest_768_block_5 : Interval ridgeTest_768 40 48 :=
  interval_of_check ridgeTest_768 40 8 (by decide +kernel)

theorem ridgeTest_768_block_6 : Interval ridgeTest_768 48 56 :=
  interval_of_check ridgeTest_768 48 8 (by decide +kernel)

theorem ridgeTest_768_block_7 : Interval ridgeTest_768 56 64 :=
  interval_of_check ridgeTest_768 56 8 (by decide +kernel)

theorem ridgeTest_768_block_8 : Interval ridgeTest_768 64 72 :=
  interval_of_check ridgeTest_768 64 8 (by decide +kernel)

theorem ridgeTest_768_block_9 : Interval ridgeTest_768 72 80 :=
  interval_of_check ridgeTest_768 72 8 (by decide +kernel)

theorem ridgeTest_768_block_10 : Interval ridgeTest_768 80 88 :=
  interval_of_check ridgeTest_768 80 8 (by decide +kernel)

theorem ridgeTest_768_block_11 : Interval ridgeTest_768 88 96 :=
  interval_of_check ridgeTest_768 88 8 (by decide +kernel)

theorem ridgeTest_768_block_12 : Interval ridgeTest_768 96 104 :=
  interval_of_check ridgeTest_768 96 8 (by decide +kernel)

theorem ridgeTest_768_block_13 : Interval ridgeTest_768 104 112 :=
  interval_of_check ridgeTest_768 104 8 (by decide +kernel)

theorem ridgeTest_768_block_14 : Interval ridgeTest_768 112 120 :=
  interval_of_check ridgeTest_768 112 8 (by decide +kernel)

theorem ridgeTest_768_block_15 : Interval ridgeTest_768 120 128 :=
  interval_of_check ridgeTest_768 120 8 (by decide +kernel)

theorem ridgeTest_768_complete : Interval ridgeTest_768 0 128 :=
  (interval_append ridgeTest_768 0 64 128
  (interval_append ridgeTest_768 0 32 64
  (interval_append ridgeTest_768 0 16 32
  (interval_append ridgeTest_768 0 8 16
  ridgeTest_768_block_0
  ridgeTest_768_block_1)
  (interval_append ridgeTest_768 16 24 32
  ridgeTest_768_block_2
  ridgeTest_768_block_3))
  (interval_append ridgeTest_768 32 48 64
  (interval_append ridgeTest_768 32 40 48
  ridgeTest_768_block_4
  ridgeTest_768_block_5)
  (interval_append ridgeTest_768 48 56 64
  ridgeTest_768_block_6
  ridgeTest_768_block_7)))
  (interval_append ridgeTest_768 64 96 128
  (interval_append ridgeTest_768 64 80 96
  (interval_append ridgeTest_768 64 72 80
  ridgeTest_768_block_8
  ridgeTest_768_block_9)
  (interval_append ridgeTest_768 80 88 96
  ridgeTest_768_block_10
  ridgeTest_768_block_11))
  (interval_append ridgeTest_768 96 112 128
  (interval_append ridgeTest_768 96 104 112
  ridgeTest_768_block_12
  ridgeTest_768_block_13)
  (interval_append ridgeTest_768 112 120 128
  ridgeTest_768_block_14
  ridgeTest_768_block_15))))
theorem ridgeTestInterval768 : Interval ridgeTest 768 896 := by
  intro i hlo hhi
  have h := ridgeTest_768_complete (i-768) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheRidges007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_896 (i : Nat) := ridgeTest (i+896)
theorem ridgeTest_896_block_0 : Interval ridgeTest_896 0 8 :=
  interval_of_check ridgeTest_896 0 8 (by decide +kernel)

theorem ridgeTest_896_block_1 : Interval ridgeTest_896 8 16 :=
  interval_of_check ridgeTest_896 8 8 (by decide +kernel)

theorem ridgeTest_896_block_2 : Interval ridgeTest_896 16 24 :=
  interval_of_check ridgeTest_896 16 8 (by decide +kernel)

theorem ridgeTest_896_block_3 : Interval ridgeTest_896 24 32 :=
  interval_of_check ridgeTest_896 24 8 (by decide +kernel)

theorem ridgeTest_896_block_4 : Interval ridgeTest_896 32 40 :=
  interval_of_check ridgeTest_896 32 8 (by decide +kernel)

theorem ridgeTest_896_block_5 : Interval ridgeTest_896 40 48 :=
  interval_of_check ridgeTest_896 40 8 (by decide +kernel)

theorem ridgeTest_896_block_6 : Interval ridgeTest_896 48 56 :=
  interval_of_check ridgeTest_896 48 8 (by decide +kernel)

theorem ridgeTest_896_block_7 : Interval ridgeTest_896 56 64 :=
  interval_of_check ridgeTest_896 56 8 (by decide +kernel)

theorem ridgeTest_896_block_8 : Interval ridgeTest_896 64 72 :=
  interval_of_check ridgeTest_896 64 8 (by decide +kernel)

theorem ridgeTest_896_block_9 : Interval ridgeTest_896 72 80 :=
  interval_of_check ridgeTest_896 72 8 (by decide +kernel)

theorem ridgeTest_896_block_10 : Interval ridgeTest_896 80 88 :=
  interval_of_check ridgeTest_896 80 8 (by decide +kernel)

theorem ridgeTest_896_block_11 : Interval ridgeTest_896 88 96 :=
  interval_of_check ridgeTest_896 88 8 (by decide +kernel)

theorem ridgeTest_896_block_12 : Interval ridgeTest_896 96 104 :=
  interval_of_check ridgeTest_896 96 8 (by decide +kernel)

theorem ridgeTest_896_block_13 : Interval ridgeTest_896 104 112 :=
  interval_of_check ridgeTest_896 104 8 (by decide +kernel)

theorem ridgeTest_896_block_14 : Interval ridgeTest_896 112 120 :=
  interval_of_check ridgeTest_896 112 8 (by decide +kernel)

theorem ridgeTest_896_block_15 : Interval ridgeTest_896 120 128 :=
  interval_of_check ridgeTest_896 120 8 (by decide +kernel)

theorem ridgeTest_896_complete : Interval ridgeTest_896 0 128 :=
  (interval_append ridgeTest_896 0 64 128
  (interval_append ridgeTest_896 0 32 64
  (interval_append ridgeTest_896 0 16 32
  (interval_append ridgeTest_896 0 8 16
  ridgeTest_896_block_0
  ridgeTest_896_block_1)
  (interval_append ridgeTest_896 16 24 32
  ridgeTest_896_block_2
  ridgeTest_896_block_3))
  (interval_append ridgeTest_896 32 48 64
  (interval_append ridgeTest_896 32 40 48
  ridgeTest_896_block_4
  ridgeTest_896_block_5)
  (interval_append ridgeTest_896 48 56 64
  ridgeTest_896_block_6
  ridgeTest_896_block_7)))
  (interval_append ridgeTest_896 64 96 128
  (interval_append ridgeTest_896 64 80 96
  (interval_append ridgeTest_896 64 72 80
  ridgeTest_896_block_8
  ridgeTest_896_block_9)
  (interval_append ridgeTest_896 80 88 96
  ridgeTest_896_block_10
  ridgeTest_896_block_11))
  (interval_append ridgeTest_896 96 112 128
  (interval_append ridgeTest_896 96 104 112
  ridgeTest_896_block_12
  ridgeTest_896_block_13)
  (interval_append ridgeTest_896 112 120 128
  ridgeTest_896_block_14
  ridgeTest_896_block_15))))
theorem ridgeTestInterval896 : Interval ridgeTest 896 1024 := by
  intro i hlo hhi
  have h := ridgeTest_896_complete (i-896) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_0 (i : Nat) := wellFormedTest (i+0)
theorem wellFormedTest_0_block_0 : Interval wellFormedTest_0 0 16 :=
  interval_of_check wellFormedTest_0 0 16 (by decide +kernel)

theorem wellFormedTest_0_block_1 : Interval wellFormedTest_0 16 32 :=
  interval_of_check wellFormedTest_0 16 16 (by decide +kernel)

theorem wellFormedTest_0_block_2 : Interval wellFormedTest_0 32 48 :=
  interval_of_check wellFormedTest_0 32 16 (by decide +kernel)

theorem wellFormedTest_0_block_3 : Interval wellFormedTest_0 48 64 :=
  interval_of_check wellFormedTest_0 48 16 (by decide +kernel)

theorem wellFormedTest_0_block_4 : Interval wellFormedTest_0 64 80 :=
  interval_of_check wellFormedTest_0 64 16 (by decide +kernel)

theorem wellFormedTest_0_block_5 : Interval wellFormedTest_0 80 96 :=
  interval_of_check wellFormedTest_0 80 16 (by decide +kernel)

theorem wellFormedTest_0_block_6 : Interval wellFormedTest_0 96 112 :=
  interval_of_check wellFormedTest_0 96 16 (by decide +kernel)

theorem wellFormedTest_0_block_7 : Interval wellFormedTest_0 112 128 :=
  interval_of_check wellFormedTest_0 112 16 (by decide +kernel)

theorem wellFormedTest_0_block_8 : Interval wellFormedTest_0 128 144 :=
  interval_of_check wellFormedTest_0 128 16 (by decide +kernel)

theorem wellFormedTest_0_block_9 : Interval wellFormedTest_0 144 160 :=
  interval_of_check wellFormedTest_0 144 16 (by decide +kernel)

theorem wellFormedTest_0_block_10 : Interval wellFormedTest_0 160 176 :=
  interval_of_check wellFormedTest_0 160 16 (by decide +kernel)

theorem wellFormedTest_0_block_11 : Interval wellFormedTest_0 176 192 :=
  interval_of_check wellFormedTest_0 176 16 (by decide +kernel)

theorem wellFormedTest_0_block_12 : Interval wellFormedTest_0 192 208 :=
  interval_of_check wellFormedTest_0 192 16 (by decide +kernel)

theorem wellFormedTest_0_block_13 : Interval wellFormedTest_0 208 224 :=
  interval_of_check wellFormedTest_0 208 16 (by decide +kernel)

theorem wellFormedTest_0_block_14 : Interval wellFormedTest_0 224 240 :=
  interval_of_check wellFormedTest_0 224 16 (by decide +kernel)

theorem wellFormedTest_0_block_15 : Interval wellFormedTest_0 240 256 :=
  interval_of_check wellFormedTest_0 240 16 (by decide +kernel)

theorem wellFormedTest_0_complete : Interval wellFormedTest_0 0 256 :=
  (interval_append wellFormedTest_0 0 128 256
  (interval_append wellFormedTest_0 0 64 128
  (interval_append wellFormedTest_0 0 32 64
  (interval_append wellFormedTest_0 0 16 32
  wellFormedTest_0_block_0
  wellFormedTest_0_block_1)
  (interval_append wellFormedTest_0 32 48 64
  wellFormedTest_0_block_2
  wellFormedTest_0_block_3))
  (interval_append wellFormedTest_0 64 96 128
  (interval_append wellFormedTest_0 64 80 96
  wellFormedTest_0_block_4
  wellFormedTest_0_block_5)
  (interval_append wellFormedTest_0 96 112 128
  wellFormedTest_0_block_6
  wellFormedTest_0_block_7)))
  (interval_append wellFormedTest_0 128 192 256
  (interval_append wellFormedTest_0 128 160 192
  (interval_append wellFormedTest_0 128 144 160
  wellFormedTest_0_block_8
  wellFormedTest_0_block_9)
  (interval_append wellFormedTest_0 160 176 192
  wellFormedTest_0_block_10
  wellFormedTest_0_block_11))
  (interval_append wellFormedTest_0 192 224 256
  (interval_append wellFormedTest_0 192 208 224
  wellFormedTest_0_block_12
  wellFormedTest_0_block_13)
  (interval_append wellFormedTest_0 224 240 256
  wellFormedTest_0_block_14
  wellFormedTest_0_block_15))))
theorem wellFormedTestInterval0 : Interval wellFormedTest 0 256 := by
  intro i hlo hhi
  have h := wellFormedTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
/- RootedSevenPure020GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure020
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_256 (i : Nat) := wellFormedTest (i+256)
theorem wellFormedTest_256_block_0 : Interval wellFormedTest_256 0 16 :=
  interval_of_check wellFormedTest_256 0 16 (by decide +kernel)

theorem wellFormedTest_256_block_1 : Interval wellFormedTest_256 16 32 :=
  interval_of_check wellFormedTest_256 16 16 (by decide +kernel)

theorem wellFormedTest_256_block_2 : Interval wellFormedTest_256 32 48 :=
  interval_of_check wellFormedTest_256 32 16 (by decide +kernel)

theorem wellFormedTest_256_block_3 : Interval wellFormedTest_256 48 64 :=
  interval_of_check wellFormedTest_256 48 16 (by decide +kernel)

theorem wellFormedTest_256_block_4 : Interval wellFormedTest_256 64 80 :=
  interval_of_check wellFormedTest_256 64 16 (by decide +kernel)

theorem wellFormedTest_256_block_5 : Interval wellFormedTest_256 80 96 :=
  interval_of_check wellFormedTest_256 80 16 (by decide +kernel)

theorem wellFormedTest_256_block_6 : Interval wellFormedTest_256 96 112 :=
  interval_of_check wellFormedTest_256 96 16 (by decide +kernel)

theorem wellFormedTest_256_block_7 : Interval wellFormedTest_256 112 128 :=
  interval_of_check wellFormedTest_256 112 16 (by decide +kernel)

theorem wellFormedTest_256_block_8 : Interval wellFormedTest_256 128 144 :=
  interval_of_check wellFormedTest_256 128 16 (by decide +kernel)

theorem wellFormedTest_256_block_9 : Interval wellFormedTest_256 144 160 :=
  interval_of_check wellFormedTest_256 144 16 (by decide +kernel)

theorem wellFormedTest_256_block_10 : Interval wellFormedTest_256 160 176 :=
  interval_of_check wellFormedTest_256 160 16 (by decide +kernel)

theorem wellFormedTest_256_block_11 : Interval wellFormedTest_256 176 192 :=
  interval_of_check wellFormedTest_256 176 16 (by decide +kernel)

theorem wellFormedTest_256_block_12 : Interval wellFormedTest_256 192 208 :=
  interval_of_check wellFormedTest_256 192 16 (by decide +kernel)

theorem wellFormedTest_256_block_13 : Interval wellFormedTest_256 208 224 :=
  interval_of_check wellFormedTest_256 208 16 (by decide +kernel)

theorem wellFormedTest_256_block_14 : Interval wellFormedTest_256 224 240 :=
  interval_of_check wellFormedTest_256 224 16 (by decide +kernel)

theorem wellFormedTest_256_block_15 : Interval wellFormedTest_256 240 256 :=
  interval_of_check wellFormedTest_256 240 16 (by decide +kernel)

theorem wellFormedTest_256_complete : Interval wellFormedTest_256 0 256 :=
  (interval_append wellFormedTest_256 0 128 256
  (interval_append wellFormedTest_256 0 64 128
  (interval_append wellFormedTest_256 0 32 64
  (interval_append wellFormedTest_256 0 16 32
  wellFormedTest_256_block_0
  wellFormedTest_256_block_1)
  (interval_append wellFormedTest_256 32 48 64
  wellFormedTest_256_block_2
  wellFormedTest_256_block_3))
  (interval_append wellFormedTest_256 64 96 128
  (interval_append wellFormedTest_256 64 80 96
  wellFormedTest_256_block_4
  wellFormedTest_256_block_5)
  (interval_append wellFormedTest_256 96 112 128
  wellFormedTest_256_block_6
  wellFormedTest_256_block_7)))
  (interval_append wellFormedTest_256 128 192 256
  (interval_append wellFormedTest_256 128 160 192
  (interval_append wellFormedTest_256 128 144 160
  wellFormedTest_256_block_8
  wellFormedTest_256_block_9)
  (interval_append wellFormedTest_256 160 176 192
  wellFormedTest_256_block_10
  wellFormedTest_256_block_11))
  (interval_append wellFormedTest_256 192 224 256
  (interval_append wellFormedTest_256 192 208 224
  wellFormedTest_256_block_12
  wellFormedTest_256_block_13)
  (interval_append wellFormedTest_256 224 240 256
  wellFormedTest_256_block_14
  wellFormedTest_256_block_15))))
theorem wellFormedTestInterval256 : Interval wellFormedTest 256 512 := by
  intro i hlo hhi
  have h := wellFormedTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure020

end
end
