module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheCells080 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_20480 (i : Nat) := cellTest (i+20480)
theorem cellTest_20480_block_0 : Interval cellTest_20480 0 8 :=
  interval_of_check cellTest_20480 0 8 (by decide +kernel)

theorem cellTest_20480_block_1 : Interval cellTest_20480 8 16 :=
  interval_of_check cellTest_20480 8 8 (by decide +kernel)

theorem cellTest_20480_block_2 : Interval cellTest_20480 16 24 :=
  interval_of_check cellTest_20480 16 8 (by decide +kernel)

theorem cellTest_20480_block_3 : Interval cellTest_20480 24 32 :=
  interval_of_check cellTest_20480 24 8 (by decide +kernel)

theorem cellTest_20480_block_4 : Interval cellTest_20480 32 40 :=
  interval_of_check cellTest_20480 32 8 (by decide +kernel)

theorem cellTest_20480_block_5 : Interval cellTest_20480 40 48 :=
  interval_of_check cellTest_20480 40 8 (by decide +kernel)

theorem cellTest_20480_block_6 : Interval cellTest_20480 48 56 :=
  interval_of_check cellTest_20480 48 8 (by decide +kernel)

theorem cellTest_20480_block_7 : Interval cellTest_20480 56 64 :=
  interval_of_check cellTest_20480 56 8 (by decide +kernel)

theorem cellTest_20480_block_8 : Interval cellTest_20480 64 72 :=
  interval_of_check cellTest_20480 64 8 (by decide +kernel)

theorem cellTest_20480_block_9 : Interval cellTest_20480 72 80 :=
  interval_of_check cellTest_20480 72 8 (by decide +kernel)

theorem cellTest_20480_block_10 : Interval cellTest_20480 80 88 :=
  interval_of_check cellTest_20480 80 8 (by decide +kernel)

theorem cellTest_20480_block_11 : Interval cellTest_20480 88 96 :=
  interval_of_check cellTest_20480 88 8 (by decide +kernel)

theorem cellTest_20480_block_12 : Interval cellTest_20480 96 104 :=
  interval_of_check cellTest_20480 96 8 (by decide +kernel)

theorem cellTest_20480_block_13 : Interval cellTest_20480 104 112 :=
  interval_of_check cellTest_20480 104 8 (by decide +kernel)

theorem cellTest_20480_block_14 : Interval cellTest_20480 112 120 :=
  interval_of_check cellTest_20480 112 8 (by decide +kernel)

theorem cellTest_20480_block_15 : Interval cellTest_20480 120 128 :=
  interval_of_check cellTest_20480 120 8 (by decide +kernel)

theorem cellTest_20480_block_16 : Interval cellTest_20480 128 136 :=
  interval_of_check cellTest_20480 128 8 (by decide +kernel)

theorem cellTest_20480_block_17 : Interval cellTest_20480 136 144 :=
  interval_of_check cellTest_20480 136 8 (by decide +kernel)

theorem cellTest_20480_block_18 : Interval cellTest_20480 144 152 :=
  interval_of_check cellTest_20480 144 8 (by decide +kernel)

theorem cellTest_20480_block_19 : Interval cellTest_20480 152 160 :=
  interval_of_check cellTest_20480 152 8 (by decide +kernel)

theorem cellTest_20480_block_20 : Interval cellTest_20480 160 168 :=
  interval_of_check cellTest_20480 160 8 (by decide +kernel)

theorem cellTest_20480_block_21 : Interval cellTest_20480 168 176 :=
  interval_of_check cellTest_20480 168 8 (by decide +kernel)

theorem cellTest_20480_block_22 : Interval cellTest_20480 176 184 :=
  interval_of_check cellTest_20480 176 8 (by decide +kernel)

theorem cellTest_20480_block_23 : Interval cellTest_20480 184 192 :=
  interval_of_check cellTest_20480 184 8 (by decide +kernel)

theorem cellTest_20480_block_24 : Interval cellTest_20480 192 200 :=
  interval_of_check cellTest_20480 192 8 (by decide +kernel)

theorem cellTest_20480_block_25 : Interval cellTest_20480 200 208 :=
  interval_of_check cellTest_20480 200 8 (by decide +kernel)

theorem cellTest_20480_block_26 : Interval cellTest_20480 208 216 :=
  interval_of_check cellTest_20480 208 8 (by decide +kernel)

theorem cellTest_20480_block_27 : Interval cellTest_20480 216 224 :=
  interval_of_check cellTest_20480 216 8 (by decide +kernel)

theorem cellTest_20480_block_28 : Interval cellTest_20480 224 232 :=
  interval_of_check cellTest_20480 224 8 (by decide +kernel)

theorem cellTest_20480_block_29 : Interval cellTest_20480 232 240 :=
  interval_of_check cellTest_20480 232 8 (by decide +kernel)

theorem cellTest_20480_block_30 : Interval cellTest_20480 240 248 :=
  interval_of_check cellTest_20480 240 8 (by decide +kernel)

theorem cellTest_20480_block_31 : Interval cellTest_20480 248 256 :=
  interval_of_check cellTest_20480 248 8 (by decide +kernel)

theorem cellTest_20480_complete : Interval cellTest_20480 0 256 :=
  (interval_append cellTest_20480 0 128 256
  (interval_append cellTest_20480 0 64 128
  (interval_append cellTest_20480 0 32 64
  (interval_append cellTest_20480 0 16 32
  (interval_append cellTest_20480 0 8 16
  cellTest_20480_block_0
  cellTest_20480_block_1)
  (interval_append cellTest_20480 16 24 32
  cellTest_20480_block_2
  cellTest_20480_block_3))
  (interval_append cellTest_20480 32 48 64
  (interval_append cellTest_20480 32 40 48
  cellTest_20480_block_4
  cellTest_20480_block_5)
  (interval_append cellTest_20480 48 56 64
  cellTest_20480_block_6
  cellTest_20480_block_7)))
  (interval_append cellTest_20480 64 96 128
  (interval_append cellTest_20480 64 80 96
  (interval_append cellTest_20480 64 72 80
  cellTest_20480_block_8
  cellTest_20480_block_9)
  (interval_append cellTest_20480 80 88 96
  cellTest_20480_block_10
  cellTest_20480_block_11))
  (interval_append cellTest_20480 96 112 128
  (interval_append cellTest_20480 96 104 112
  cellTest_20480_block_12
  cellTest_20480_block_13)
  (interval_append cellTest_20480 112 120 128
  cellTest_20480_block_14
  cellTest_20480_block_15))))
  (interval_append cellTest_20480 128 192 256
  (interval_append cellTest_20480 128 160 192
  (interval_append cellTest_20480 128 144 160
  (interval_append cellTest_20480 128 136 144
  cellTest_20480_block_16
  cellTest_20480_block_17)
  (interval_append cellTest_20480 144 152 160
  cellTest_20480_block_18
  cellTest_20480_block_19))
  (interval_append cellTest_20480 160 176 192
  (interval_append cellTest_20480 160 168 176
  cellTest_20480_block_20
  cellTest_20480_block_21)
  (interval_append cellTest_20480 176 184 192
  cellTest_20480_block_22
  cellTest_20480_block_23)))
  (interval_append cellTest_20480 192 224 256
  (interval_append cellTest_20480 192 208 224
  (interval_append cellTest_20480 192 200 208
  cellTest_20480_block_24
  cellTest_20480_block_25)
  (interval_append cellTest_20480 208 216 224
  cellTest_20480_block_26
  cellTest_20480_block_27))
  (interval_append cellTest_20480 224 240 256
  (interval_append cellTest_20480 224 232 240
  cellTest_20480_block_28
  cellTest_20480_block_29)
  (interval_append cellTest_20480 240 248 256
  cellTest_20480_block_30
  cellTest_20480_block_31)))))
theorem cellTestInterval20480 : Interval cellTest 20480 20736 := by
  intro i hlo hhi
  have h := cellTest_20480_complete (i-20480) (Nat.zero_le _) (by omega)
  simpa only [cellTest_20480, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells081 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_20736 (i : Nat) := cellTest (i+20736)
theorem cellTest_20736_block_0 : Interval cellTest_20736 0 8 :=
  interval_of_check cellTest_20736 0 8 (by decide +kernel)

theorem cellTest_20736_block_1 : Interval cellTest_20736 8 16 :=
  interval_of_check cellTest_20736 8 8 (by decide +kernel)

theorem cellTest_20736_block_2 : Interval cellTest_20736 16 24 :=
  interval_of_check cellTest_20736 16 8 (by decide +kernel)

theorem cellTest_20736_block_3 : Interval cellTest_20736 24 32 :=
  interval_of_check cellTest_20736 24 8 (by decide +kernel)

theorem cellTest_20736_block_4 : Interval cellTest_20736 32 40 :=
  interval_of_check cellTest_20736 32 8 (by decide +kernel)

theorem cellTest_20736_block_5 : Interval cellTest_20736 40 48 :=
  interval_of_check cellTest_20736 40 8 (by decide +kernel)

theorem cellTest_20736_block_6 : Interval cellTest_20736 48 56 :=
  interval_of_check cellTest_20736 48 8 (by decide +kernel)

theorem cellTest_20736_block_7 : Interval cellTest_20736 56 64 :=
  interval_of_check cellTest_20736 56 8 (by decide +kernel)

theorem cellTest_20736_block_8 : Interval cellTest_20736 64 72 :=
  interval_of_check cellTest_20736 64 8 (by decide +kernel)

theorem cellTest_20736_block_9 : Interval cellTest_20736 72 80 :=
  interval_of_check cellTest_20736 72 8 (by decide +kernel)

theorem cellTest_20736_block_10 : Interval cellTest_20736 80 88 :=
  interval_of_check cellTest_20736 80 8 (by decide +kernel)

theorem cellTest_20736_block_11 : Interval cellTest_20736 88 96 :=
  interval_of_check cellTest_20736 88 8 (by decide +kernel)

theorem cellTest_20736_block_12 : Interval cellTest_20736 96 104 :=
  interval_of_check cellTest_20736 96 8 (by decide +kernel)

theorem cellTest_20736_block_13 : Interval cellTest_20736 104 112 :=
  interval_of_check cellTest_20736 104 8 (by decide +kernel)

theorem cellTest_20736_block_14 : Interval cellTest_20736 112 120 :=
  interval_of_check cellTest_20736 112 8 (by decide +kernel)

theorem cellTest_20736_block_15 : Interval cellTest_20736 120 128 :=
  interval_of_check cellTest_20736 120 8 (by decide +kernel)

theorem cellTest_20736_block_16 : Interval cellTest_20736 128 136 :=
  interval_of_check cellTest_20736 128 8 (by decide +kernel)

theorem cellTest_20736_block_17 : Interval cellTest_20736 136 144 :=
  interval_of_check cellTest_20736 136 8 (by decide +kernel)

theorem cellTest_20736_block_18 : Interval cellTest_20736 144 152 :=
  interval_of_check cellTest_20736 144 8 (by decide +kernel)

theorem cellTest_20736_block_19 : Interval cellTest_20736 152 160 :=
  interval_of_check cellTest_20736 152 8 (by decide +kernel)

theorem cellTest_20736_block_20 : Interval cellTest_20736 160 168 :=
  interval_of_check cellTest_20736 160 8 (by decide +kernel)

theorem cellTest_20736_block_21 : Interval cellTest_20736 168 176 :=
  interval_of_check cellTest_20736 168 8 (by decide +kernel)

theorem cellTest_20736_block_22 : Interval cellTest_20736 176 184 :=
  interval_of_check cellTest_20736 176 8 (by decide +kernel)

theorem cellTest_20736_block_23 : Interval cellTest_20736 184 192 :=
  interval_of_check cellTest_20736 184 8 (by decide +kernel)

theorem cellTest_20736_block_24 : Interval cellTest_20736 192 200 :=
  interval_of_check cellTest_20736 192 8 (by decide +kernel)

theorem cellTest_20736_block_25 : Interval cellTest_20736 200 208 :=
  interval_of_check cellTest_20736 200 8 (by decide +kernel)

theorem cellTest_20736_block_26 : Interval cellTest_20736 208 216 :=
  interval_of_check cellTest_20736 208 8 (by decide +kernel)

theorem cellTest_20736_block_27 : Interval cellTest_20736 216 224 :=
  interval_of_check cellTest_20736 216 8 (by decide +kernel)

theorem cellTest_20736_block_28 : Interval cellTest_20736 224 232 :=
  interval_of_check cellTest_20736 224 8 (by decide +kernel)

theorem cellTest_20736_block_29 : Interval cellTest_20736 232 240 :=
  interval_of_check cellTest_20736 232 8 (by decide +kernel)

theorem cellTest_20736_block_30 : Interval cellTest_20736 240 248 :=
  interval_of_check cellTest_20736 240 8 (by decide +kernel)

theorem cellTest_20736_block_31 : Interval cellTest_20736 248 256 :=
  interval_of_check cellTest_20736 248 8 (by decide +kernel)

theorem cellTest_20736_complete : Interval cellTest_20736 0 256 :=
  (interval_append cellTest_20736 0 128 256
  (interval_append cellTest_20736 0 64 128
  (interval_append cellTest_20736 0 32 64
  (interval_append cellTest_20736 0 16 32
  (interval_append cellTest_20736 0 8 16
  cellTest_20736_block_0
  cellTest_20736_block_1)
  (interval_append cellTest_20736 16 24 32
  cellTest_20736_block_2
  cellTest_20736_block_3))
  (interval_append cellTest_20736 32 48 64
  (interval_append cellTest_20736 32 40 48
  cellTest_20736_block_4
  cellTest_20736_block_5)
  (interval_append cellTest_20736 48 56 64
  cellTest_20736_block_6
  cellTest_20736_block_7)))
  (interval_append cellTest_20736 64 96 128
  (interval_append cellTest_20736 64 80 96
  (interval_append cellTest_20736 64 72 80
  cellTest_20736_block_8
  cellTest_20736_block_9)
  (interval_append cellTest_20736 80 88 96
  cellTest_20736_block_10
  cellTest_20736_block_11))
  (interval_append cellTest_20736 96 112 128
  (interval_append cellTest_20736 96 104 112
  cellTest_20736_block_12
  cellTest_20736_block_13)
  (interval_append cellTest_20736 112 120 128
  cellTest_20736_block_14
  cellTest_20736_block_15))))
  (interval_append cellTest_20736 128 192 256
  (interval_append cellTest_20736 128 160 192
  (interval_append cellTest_20736 128 144 160
  (interval_append cellTest_20736 128 136 144
  cellTest_20736_block_16
  cellTest_20736_block_17)
  (interval_append cellTest_20736 144 152 160
  cellTest_20736_block_18
  cellTest_20736_block_19))
  (interval_append cellTest_20736 160 176 192
  (interval_append cellTest_20736 160 168 176
  cellTest_20736_block_20
  cellTest_20736_block_21)
  (interval_append cellTest_20736 176 184 192
  cellTest_20736_block_22
  cellTest_20736_block_23)))
  (interval_append cellTest_20736 192 224 256
  (interval_append cellTest_20736 192 208 224
  (interval_append cellTest_20736 192 200 208
  cellTest_20736_block_24
  cellTest_20736_block_25)
  (interval_append cellTest_20736 208 216 224
  cellTest_20736_block_26
  cellTest_20736_block_27))
  (interval_append cellTest_20736 224 240 256
  (interval_append cellTest_20736 224 232 240
  cellTest_20736_block_28
  cellTest_20736_block_29)
  (interval_append cellTest_20736 240 248 256
  cellTest_20736_block_30
  cellTest_20736_block_31)))))
theorem cellTestInterval20736 : Interval cellTest 20736 20992 := by
  intro i hlo hhi
  have h := cellTest_20736_complete (i-20736) (Nat.zero_le _) (by omega)
  simpa only [cellTest_20736, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells082 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_20992 (i : Nat) := cellTest (i+20992)
theorem cellTest_20992_block_0 : Interval cellTest_20992 0 8 :=
  interval_of_check cellTest_20992 0 8 (by decide +kernel)

theorem cellTest_20992_block_1 : Interval cellTest_20992 8 16 :=
  interval_of_check cellTest_20992 8 8 (by decide +kernel)

theorem cellTest_20992_block_2 : Interval cellTest_20992 16 24 :=
  interval_of_check cellTest_20992 16 8 (by decide +kernel)

theorem cellTest_20992_block_3 : Interval cellTest_20992 24 32 :=
  interval_of_check cellTest_20992 24 8 (by decide +kernel)

theorem cellTest_20992_block_4 : Interval cellTest_20992 32 40 :=
  interval_of_check cellTest_20992 32 8 (by decide +kernel)

theorem cellTest_20992_block_5 : Interval cellTest_20992 40 48 :=
  interval_of_check cellTest_20992 40 8 (by decide +kernel)

theorem cellTest_20992_block_6 : Interval cellTest_20992 48 56 :=
  interval_of_check cellTest_20992 48 8 (by decide +kernel)

theorem cellTest_20992_block_7 : Interval cellTest_20992 56 64 :=
  interval_of_check cellTest_20992 56 8 (by decide +kernel)

theorem cellTest_20992_block_8 : Interval cellTest_20992 64 72 :=
  interval_of_check cellTest_20992 64 8 (by decide +kernel)

theorem cellTest_20992_block_9 : Interval cellTest_20992 72 80 :=
  interval_of_check cellTest_20992 72 8 (by decide +kernel)

theorem cellTest_20992_block_10 : Interval cellTest_20992 80 88 :=
  interval_of_check cellTest_20992 80 8 (by decide +kernel)

theorem cellTest_20992_block_11 : Interval cellTest_20992 88 96 :=
  interval_of_check cellTest_20992 88 8 (by decide +kernel)

theorem cellTest_20992_block_12 : Interval cellTest_20992 96 104 :=
  interval_of_check cellTest_20992 96 8 (by decide +kernel)

theorem cellTest_20992_block_13 : Interval cellTest_20992 104 112 :=
  interval_of_check cellTest_20992 104 8 (by decide +kernel)

theorem cellTest_20992_block_14 : Interval cellTest_20992 112 120 :=
  interval_of_check cellTest_20992 112 8 (by decide +kernel)

theorem cellTest_20992_block_15 : Interval cellTest_20992 120 128 :=
  interval_of_check cellTest_20992 120 8 (by decide +kernel)

theorem cellTest_20992_block_16 : Interval cellTest_20992 128 136 :=
  interval_of_check cellTest_20992 128 8 (by decide +kernel)

theorem cellTest_20992_block_17 : Interval cellTest_20992 136 144 :=
  interval_of_check cellTest_20992 136 8 (by decide +kernel)

theorem cellTest_20992_block_18 : Interval cellTest_20992 144 152 :=
  interval_of_check cellTest_20992 144 8 (by decide +kernel)

theorem cellTest_20992_block_19 : Interval cellTest_20992 152 160 :=
  interval_of_check cellTest_20992 152 8 (by decide +kernel)

theorem cellTest_20992_block_20 : Interval cellTest_20992 160 168 :=
  interval_of_check cellTest_20992 160 8 (by decide +kernel)

theorem cellTest_20992_block_21 : Interval cellTest_20992 168 176 :=
  interval_of_check cellTest_20992 168 8 (by decide +kernel)

theorem cellTest_20992_block_22 : Interval cellTest_20992 176 184 :=
  interval_of_check cellTest_20992 176 8 (by decide +kernel)

theorem cellTest_20992_block_23 : Interval cellTest_20992 184 192 :=
  interval_of_check cellTest_20992 184 8 (by decide +kernel)

theorem cellTest_20992_block_24 : Interval cellTest_20992 192 200 :=
  interval_of_check cellTest_20992 192 8 (by decide +kernel)

theorem cellTest_20992_block_25 : Interval cellTest_20992 200 208 :=
  interval_of_check cellTest_20992 200 8 (by decide +kernel)

theorem cellTest_20992_block_26 : Interval cellTest_20992 208 216 :=
  interval_of_check cellTest_20992 208 8 (by decide +kernel)

theorem cellTest_20992_block_27 : Interval cellTest_20992 216 224 :=
  interval_of_check cellTest_20992 216 8 (by decide +kernel)

theorem cellTest_20992_block_28 : Interval cellTest_20992 224 232 :=
  interval_of_check cellTest_20992 224 8 (by decide +kernel)

theorem cellTest_20992_block_29 : Interval cellTest_20992 232 240 :=
  interval_of_check cellTest_20992 232 8 (by decide +kernel)

theorem cellTest_20992_block_30 : Interval cellTest_20992 240 248 :=
  interval_of_check cellTest_20992 240 8 (by decide +kernel)

theorem cellTest_20992_block_31 : Interval cellTest_20992 248 256 :=
  interval_of_check cellTest_20992 248 8 (by decide +kernel)

theorem cellTest_20992_complete : Interval cellTest_20992 0 256 :=
  (interval_append cellTest_20992 0 128 256
  (interval_append cellTest_20992 0 64 128
  (interval_append cellTest_20992 0 32 64
  (interval_append cellTest_20992 0 16 32
  (interval_append cellTest_20992 0 8 16
  cellTest_20992_block_0
  cellTest_20992_block_1)
  (interval_append cellTest_20992 16 24 32
  cellTest_20992_block_2
  cellTest_20992_block_3))
  (interval_append cellTest_20992 32 48 64
  (interval_append cellTest_20992 32 40 48
  cellTest_20992_block_4
  cellTest_20992_block_5)
  (interval_append cellTest_20992 48 56 64
  cellTest_20992_block_6
  cellTest_20992_block_7)))
  (interval_append cellTest_20992 64 96 128
  (interval_append cellTest_20992 64 80 96
  (interval_append cellTest_20992 64 72 80
  cellTest_20992_block_8
  cellTest_20992_block_9)
  (interval_append cellTest_20992 80 88 96
  cellTest_20992_block_10
  cellTest_20992_block_11))
  (interval_append cellTest_20992 96 112 128
  (interval_append cellTest_20992 96 104 112
  cellTest_20992_block_12
  cellTest_20992_block_13)
  (interval_append cellTest_20992 112 120 128
  cellTest_20992_block_14
  cellTest_20992_block_15))))
  (interval_append cellTest_20992 128 192 256
  (interval_append cellTest_20992 128 160 192
  (interval_append cellTest_20992 128 144 160
  (interval_append cellTest_20992 128 136 144
  cellTest_20992_block_16
  cellTest_20992_block_17)
  (interval_append cellTest_20992 144 152 160
  cellTest_20992_block_18
  cellTest_20992_block_19))
  (interval_append cellTest_20992 160 176 192
  (interval_append cellTest_20992 160 168 176
  cellTest_20992_block_20
  cellTest_20992_block_21)
  (interval_append cellTest_20992 176 184 192
  cellTest_20992_block_22
  cellTest_20992_block_23)))
  (interval_append cellTest_20992 192 224 256
  (interval_append cellTest_20992 192 208 224
  (interval_append cellTest_20992 192 200 208
  cellTest_20992_block_24
  cellTest_20992_block_25)
  (interval_append cellTest_20992 208 216 224
  cellTest_20992_block_26
  cellTest_20992_block_27))
  (interval_append cellTest_20992 224 240 256
  (interval_append cellTest_20992 224 232 240
  cellTest_20992_block_28
  cellTest_20992_block_29)
  (interval_append cellTest_20992 240 248 256
  cellTest_20992_block_30
  cellTest_20992_block_31)))))
theorem cellTestInterval20992 : Interval cellTest 20992 21248 := by
  intro i hlo hhi
  have h := cellTest_20992_complete (i-20992) (Nat.zero_le _) (by omega)
  simpa only [cellTest_20992, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells083 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_21248 (i : Nat) := cellTest (i+21248)
theorem cellTest_21248_block_0 : Interval cellTest_21248 0 8 :=
  interval_of_check cellTest_21248 0 8 (by decide +kernel)

theorem cellTest_21248_block_1 : Interval cellTest_21248 8 16 :=
  interval_of_check cellTest_21248 8 8 (by decide +kernel)

theorem cellTest_21248_block_2 : Interval cellTest_21248 16 24 :=
  interval_of_check cellTest_21248 16 8 (by decide +kernel)

theorem cellTest_21248_block_3 : Interval cellTest_21248 24 32 :=
  interval_of_check cellTest_21248 24 8 (by decide +kernel)

theorem cellTest_21248_block_4 : Interval cellTest_21248 32 40 :=
  interval_of_check cellTest_21248 32 8 (by decide +kernel)

theorem cellTest_21248_block_5 : Interval cellTest_21248 40 48 :=
  interval_of_check cellTest_21248 40 8 (by decide +kernel)

theorem cellTest_21248_block_6 : Interval cellTest_21248 48 56 :=
  interval_of_check cellTest_21248 48 8 (by decide +kernel)

theorem cellTest_21248_block_7 : Interval cellTest_21248 56 64 :=
  interval_of_check cellTest_21248 56 8 (by decide +kernel)

theorem cellTest_21248_block_8 : Interval cellTest_21248 64 72 :=
  interval_of_check cellTest_21248 64 8 (by decide +kernel)

theorem cellTest_21248_block_9 : Interval cellTest_21248 72 80 :=
  interval_of_check cellTest_21248 72 8 (by decide +kernel)

theorem cellTest_21248_block_10 : Interval cellTest_21248 80 88 :=
  interval_of_check cellTest_21248 80 8 (by decide +kernel)

theorem cellTest_21248_block_11 : Interval cellTest_21248 88 96 :=
  interval_of_check cellTest_21248 88 8 (by decide +kernel)

theorem cellTest_21248_block_12 : Interval cellTest_21248 96 104 :=
  interval_of_check cellTest_21248 96 8 (by decide +kernel)

theorem cellTest_21248_block_13 : Interval cellTest_21248 104 112 :=
  interval_of_check cellTest_21248 104 8 (by decide +kernel)

theorem cellTest_21248_block_14 : Interval cellTest_21248 112 120 :=
  interval_of_check cellTest_21248 112 8 (by decide +kernel)

theorem cellTest_21248_block_15 : Interval cellTest_21248 120 128 :=
  interval_of_check cellTest_21248 120 8 (by decide +kernel)

theorem cellTest_21248_block_16 : Interval cellTest_21248 128 136 :=
  interval_of_check cellTest_21248 128 8 (by decide +kernel)

theorem cellTest_21248_block_17 : Interval cellTest_21248 136 144 :=
  interval_of_check cellTest_21248 136 8 (by decide +kernel)

theorem cellTest_21248_block_18 : Interval cellTest_21248 144 152 :=
  interval_of_check cellTest_21248 144 8 (by decide +kernel)

theorem cellTest_21248_block_19 : Interval cellTest_21248 152 160 :=
  interval_of_check cellTest_21248 152 8 (by decide +kernel)

theorem cellTest_21248_block_20 : Interval cellTest_21248 160 168 :=
  interval_of_check cellTest_21248 160 8 (by decide +kernel)

theorem cellTest_21248_block_21 : Interval cellTest_21248 168 176 :=
  interval_of_check cellTest_21248 168 8 (by decide +kernel)

theorem cellTest_21248_block_22 : Interval cellTest_21248 176 184 :=
  interval_of_check cellTest_21248 176 8 (by decide +kernel)

theorem cellTest_21248_block_23 : Interval cellTest_21248 184 192 :=
  interval_of_check cellTest_21248 184 8 (by decide +kernel)

theorem cellTest_21248_block_24 : Interval cellTest_21248 192 200 :=
  interval_of_check cellTest_21248 192 8 (by decide +kernel)

theorem cellTest_21248_block_25 : Interval cellTest_21248 200 208 :=
  interval_of_check cellTest_21248 200 8 (by decide +kernel)

theorem cellTest_21248_block_26 : Interval cellTest_21248 208 216 :=
  interval_of_check cellTest_21248 208 8 (by decide +kernel)

theorem cellTest_21248_block_27 : Interval cellTest_21248 216 224 :=
  interval_of_check cellTest_21248 216 8 (by decide +kernel)

theorem cellTest_21248_block_28 : Interval cellTest_21248 224 232 :=
  interval_of_check cellTest_21248 224 8 (by decide +kernel)

theorem cellTest_21248_block_29 : Interval cellTest_21248 232 240 :=
  interval_of_check cellTest_21248 232 8 (by decide +kernel)

theorem cellTest_21248_block_30 : Interval cellTest_21248 240 248 :=
  interval_of_check cellTest_21248 240 8 (by decide +kernel)

theorem cellTest_21248_block_31 : Interval cellTest_21248 248 256 :=
  interval_of_check cellTest_21248 248 8 (by decide +kernel)

theorem cellTest_21248_complete : Interval cellTest_21248 0 256 :=
  (interval_append cellTest_21248 0 128 256
  (interval_append cellTest_21248 0 64 128
  (interval_append cellTest_21248 0 32 64
  (interval_append cellTest_21248 0 16 32
  (interval_append cellTest_21248 0 8 16
  cellTest_21248_block_0
  cellTest_21248_block_1)
  (interval_append cellTest_21248 16 24 32
  cellTest_21248_block_2
  cellTest_21248_block_3))
  (interval_append cellTest_21248 32 48 64
  (interval_append cellTest_21248 32 40 48
  cellTest_21248_block_4
  cellTest_21248_block_5)
  (interval_append cellTest_21248 48 56 64
  cellTest_21248_block_6
  cellTest_21248_block_7)))
  (interval_append cellTest_21248 64 96 128
  (interval_append cellTest_21248 64 80 96
  (interval_append cellTest_21248 64 72 80
  cellTest_21248_block_8
  cellTest_21248_block_9)
  (interval_append cellTest_21248 80 88 96
  cellTest_21248_block_10
  cellTest_21248_block_11))
  (interval_append cellTest_21248 96 112 128
  (interval_append cellTest_21248 96 104 112
  cellTest_21248_block_12
  cellTest_21248_block_13)
  (interval_append cellTest_21248 112 120 128
  cellTest_21248_block_14
  cellTest_21248_block_15))))
  (interval_append cellTest_21248 128 192 256
  (interval_append cellTest_21248 128 160 192
  (interval_append cellTest_21248 128 144 160
  (interval_append cellTest_21248 128 136 144
  cellTest_21248_block_16
  cellTest_21248_block_17)
  (interval_append cellTest_21248 144 152 160
  cellTest_21248_block_18
  cellTest_21248_block_19))
  (interval_append cellTest_21248 160 176 192
  (interval_append cellTest_21248 160 168 176
  cellTest_21248_block_20
  cellTest_21248_block_21)
  (interval_append cellTest_21248 176 184 192
  cellTest_21248_block_22
  cellTest_21248_block_23)))
  (interval_append cellTest_21248 192 224 256
  (interval_append cellTest_21248 192 208 224
  (interval_append cellTest_21248 192 200 208
  cellTest_21248_block_24
  cellTest_21248_block_25)
  (interval_append cellTest_21248 208 216 224
  cellTest_21248_block_26
  cellTest_21248_block_27))
  (interval_append cellTest_21248 224 240 256
  (interval_append cellTest_21248 224 232 240
  cellTest_21248_block_28
  cellTest_21248_block_29)
  (interval_append cellTest_21248 240 248 256
  cellTest_21248_block_30
  cellTest_21248_block_31)))))
theorem cellTestInterval21248 : Interval cellTest 21248 21504 := by
  intro i hlo hhi
  have h := cellTest_21248_complete (i-21248) (Nat.zero_le _) (by omega)
  simpa only [cellTest_21248, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells084 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_21504 (i : Nat) := cellTest (i+21504)
theorem cellTest_21504_block_0 : Interval cellTest_21504 0 8 :=
  interval_of_check cellTest_21504 0 8 (by decide +kernel)

theorem cellTest_21504_block_1 : Interval cellTest_21504 8 16 :=
  interval_of_check cellTest_21504 8 8 (by decide +kernel)

theorem cellTest_21504_block_2 : Interval cellTest_21504 16 24 :=
  interval_of_check cellTest_21504 16 8 (by decide +kernel)

theorem cellTest_21504_block_3 : Interval cellTest_21504 24 32 :=
  interval_of_check cellTest_21504 24 8 (by decide +kernel)

theorem cellTest_21504_block_4 : Interval cellTest_21504 32 40 :=
  interval_of_check cellTest_21504 32 8 (by decide +kernel)

theorem cellTest_21504_block_5 : Interval cellTest_21504 40 48 :=
  interval_of_check cellTest_21504 40 8 (by decide +kernel)

theorem cellTest_21504_block_6 : Interval cellTest_21504 48 56 :=
  interval_of_check cellTest_21504 48 8 (by decide +kernel)

theorem cellTest_21504_block_7 : Interval cellTest_21504 56 64 :=
  interval_of_check cellTest_21504 56 8 (by decide +kernel)

theorem cellTest_21504_block_8 : Interval cellTest_21504 64 72 :=
  interval_of_check cellTest_21504 64 8 (by decide +kernel)

theorem cellTest_21504_block_9 : Interval cellTest_21504 72 80 :=
  interval_of_check cellTest_21504 72 8 (by decide +kernel)

theorem cellTest_21504_block_10 : Interval cellTest_21504 80 88 :=
  interval_of_check cellTest_21504 80 8 (by decide +kernel)

theorem cellTest_21504_block_11 : Interval cellTest_21504 88 96 :=
  interval_of_check cellTest_21504 88 8 (by decide +kernel)

theorem cellTest_21504_block_12 : Interval cellTest_21504 96 104 :=
  interval_of_check cellTest_21504 96 8 (by decide +kernel)

theorem cellTest_21504_block_13 : Interval cellTest_21504 104 112 :=
  interval_of_check cellTest_21504 104 8 (by decide +kernel)

theorem cellTest_21504_block_14 : Interval cellTest_21504 112 120 :=
  interval_of_check cellTest_21504 112 8 (by decide +kernel)

theorem cellTest_21504_block_15 : Interval cellTest_21504 120 128 :=
  interval_of_check cellTest_21504 120 8 (by decide +kernel)

theorem cellTest_21504_block_16 : Interval cellTest_21504 128 136 :=
  interval_of_check cellTest_21504 128 8 (by decide +kernel)

theorem cellTest_21504_block_17 : Interval cellTest_21504 136 144 :=
  interval_of_check cellTest_21504 136 8 (by decide +kernel)

theorem cellTest_21504_block_18 : Interval cellTest_21504 144 152 :=
  interval_of_check cellTest_21504 144 8 (by decide +kernel)

theorem cellTest_21504_block_19 : Interval cellTest_21504 152 160 :=
  interval_of_check cellTest_21504 152 8 (by decide +kernel)

theorem cellTest_21504_block_20 : Interval cellTest_21504 160 168 :=
  interval_of_check cellTest_21504 160 8 (by decide +kernel)

theorem cellTest_21504_block_21 : Interval cellTest_21504 168 176 :=
  interval_of_check cellTest_21504 168 8 (by decide +kernel)

theorem cellTest_21504_block_22 : Interval cellTest_21504 176 184 :=
  interval_of_check cellTest_21504 176 8 (by decide +kernel)

theorem cellTest_21504_block_23 : Interval cellTest_21504 184 192 :=
  interval_of_check cellTest_21504 184 8 (by decide +kernel)

theorem cellTest_21504_block_24 : Interval cellTest_21504 192 200 :=
  interval_of_check cellTest_21504 192 8 (by decide +kernel)

theorem cellTest_21504_block_25 : Interval cellTest_21504 200 208 :=
  interval_of_check cellTest_21504 200 8 (by decide +kernel)

theorem cellTest_21504_block_26 : Interval cellTest_21504 208 216 :=
  interval_of_check cellTest_21504 208 8 (by decide +kernel)

theorem cellTest_21504_block_27 : Interval cellTest_21504 216 224 :=
  interval_of_check cellTest_21504 216 8 (by decide +kernel)

theorem cellTest_21504_block_28 : Interval cellTest_21504 224 232 :=
  interval_of_check cellTest_21504 224 8 (by decide +kernel)

theorem cellTest_21504_block_29 : Interval cellTest_21504 232 240 :=
  interval_of_check cellTest_21504 232 8 (by decide +kernel)

theorem cellTest_21504_block_30 : Interval cellTest_21504 240 248 :=
  interval_of_check cellTest_21504 240 8 (by decide +kernel)

theorem cellTest_21504_block_31 : Interval cellTest_21504 248 256 :=
  interval_of_check cellTest_21504 248 8 (by decide +kernel)

theorem cellTest_21504_complete : Interval cellTest_21504 0 256 :=
  (interval_append cellTest_21504 0 128 256
  (interval_append cellTest_21504 0 64 128
  (interval_append cellTest_21504 0 32 64
  (interval_append cellTest_21504 0 16 32
  (interval_append cellTest_21504 0 8 16
  cellTest_21504_block_0
  cellTest_21504_block_1)
  (interval_append cellTest_21504 16 24 32
  cellTest_21504_block_2
  cellTest_21504_block_3))
  (interval_append cellTest_21504 32 48 64
  (interval_append cellTest_21504 32 40 48
  cellTest_21504_block_4
  cellTest_21504_block_5)
  (interval_append cellTest_21504 48 56 64
  cellTest_21504_block_6
  cellTest_21504_block_7)))
  (interval_append cellTest_21504 64 96 128
  (interval_append cellTest_21504 64 80 96
  (interval_append cellTest_21504 64 72 80
  cellTest_21504_block_8
  cellTest_21504_block_9)
  (interval_append cellTest_21504 80 88 96
  cellTest_21504_block_10
  cellTest_21504_block_11))
  (interval_append cellTest_21504 96 112 128
  (interval_append cellTest_21504 96 104 112
  cellTest_21504_block_12
  cellTest_21504_block_13)
  (interval_append cellTest_21504 112 120 128
  cellTest_21504_block_14
  cellTest_21504_block_15))))
  (interval_append cellTest_21504 128 192 256
  (interval_append cellTest_21504 128 160 192
  (interval_append cellTest_21504 128 144 160
  (interval_append cellTest_21504 128 136 144
  cellTest_21504_block_16
  cellTest_21504_block_17)
  (interval_append cellTest_21504 144 152 160
  cellTest_21504_block_18
  cellTest_21504_block_19))
  (interval_append cellTest_21504 160 176 192
  (interval_append cellTest_21504 160 168 176
  cellTest_21504_block_20
  cellTest_21504_block_21)
  (interval_append cellTest_21504 176 184 192
  cellTest_21504_block_22
  cellTest_21504_block_23)))
  (interval_append cellTest_21504 192 224 256
  (interval_append cellTest_21504 192 208 224
  (interval_append cellTest_21504 192 200 208
  cellTest_21504_block_24
  cellTest_21504_block_25)
  (interval_append cellTest_21504 208 216 224
  cellTest_21504_block_26
  cellTest_21504_block_27))
  (interval_append cellTest_21504 224 240 256
  (interval_append cellTest_21504 224 232 240
  cellTest_21504_block_28
  cellTest_21504_block_29)
  (interval_append cellTest_21504 240 248 256
  cellTest_21504_block_30
  cellTest_21504_block_31)))))
theorem cellTestInterval21504 : Interval cellTest 21504 21760 := by
  intro i hlo hhi
  have h := cellTest_21504_complete (i-21504) (Nat.zero_le _) (by omega)
  simpa only [cellTest_21504, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells085 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_21760 (i : Nat) := cellTest (i+21760)
theorem cellTest_21760_block_0 : Interval cellTest_21760 0 8 :=
  interval_of_check cellTest_21760 0 8 (by decide +kernel)

theorem cellTest_21760_block_1 : Interval cellTest_21760 8 16 :=
  interval_of_check cellTest_21760 8 8 (by decide +kernel)

theorem cellTest_21760_block_2 : Interval cellTest_21760 16 24 :=
  interval_of_check cellTest_21760 16 8 (by decide +kernel)

theorem cellTest_21760_block_3 : Interval cellTest_21760 24 32 :=
  interval_of_check cellTest_21760 24 8 (by decide +kernel)

theorem cellTest_21760_block_4 : Interval cellTest_21760 32 40 :=
  interval_of_check cellTest_21760 32 8 (by decide +kernel)

theorem cellTest_21760_block_5 : Interval cellTest_21760 40 48 :=
  interval_of_check cellTest_21760 40 8 (by decide +kernel)

theorem cellTest_21760_block_6 : Interval cellTest_21760 48 56 :=
  interval_of_check cellTest_21760 48 8 (by decide +kernel)

theorem cellTest_21760_block_7 : Interval cellTest_21760 56 64 :=
  interval_of_check cellTest_21760 56 8 (by decide +kernel)

theorem cellTest_21760_block_8 : Interval cellTest_21760 64 72 :=
  interval_of_check cellTest_21760 64 8 (by decide +kernel)

theorem cellTest_21760_block_9 : Interval cellTest_21760 72 80 :=
  interval_of_check cellTest_21760 72 8 (by decide +kernel)

theorem cellTest_21760_block_10 : Interval cellTest_21760 80 88 :=
  interval_of_check cellTest_21760 80 8 (by decide +kernel)

theorem cellTest_21760_block_11 : Interval cellTest_21760 88 96 :=
  interval_of_check cellTest_21760 88 8 (by decide +kernel)

theorem cellTest_21760_block_12 : Interval cellTest_21760 96 104 :=
  interval_of_check cellTest_21760 96 8 (by decide +kernel)

theorem cellTest_21760_block_13 : Interval cellTest_21760 104 112 :=
  interval_of_check cellTest_21760 104 8 (by decide +kernel)

theorem cellTest_21760_block_14 : Interval cellTest_21760 112 120 :=
  interval_of_check cellTest_21760 112 8 (by decide +kernel)

theorem cellTest_21760_block_15 : Interval cellTest_21760 120 128 :=
  interval_of_check cellTest_21760 120 8 (by decide +kernel)

theorem cellTest_21760_block_16 : Interval cellTest_21760 128 136 :=
  interval_of_check cellTest_21760 128 8 (by decide +kernel)

theorem cellTest_21760_block_17 : Interval cellTest_21760 136 144 :=
  interval_of_check cellTest_21760 136 8 (by decide +kernel)

theorem cellTest_21760_block_18 : Interval cellTest_21760 144 152 :=
  interval_of_check cellTest_21760 144 8 (by decide +kernel)

theorem cellTest_21760_block_19 : Interval cellTest_21760 152 160 :=
  interval_of_check cellTest_21760 152 8 (by decide +kernel)

theorem cellTest_21760_block_20 : Interval cellTest_21760 160 168 :=
  interval_of_check cellTest_21760 160 8 (by decide +kernel)

theorem cellTest_21760_block_21 : Interval cellTest_21760 168 176 :=
  interval_of_check cellTest_21760 168 8 (by decide +kernel)

theorem cellTest_21760_block_22 : Interval cellTest_21760 176 184 :=
  interval_of_check cellTest_21760 176 8 (by decide +kernel)

theorem cellTest_21760_block_23 : Interval cellTest_21760 184 192 :=
  interval_of_check cellTest_21760 184 8 (by decide +kernel)

theorem cellTest_21760_block_24 : Interval cellTest_21760 192 200 :=
  interval_of_check cellTest_21760 192 8 (by decide +kernel)

theorem cellTest_21760_block_25 : Interval cellTest_21760 200 208 :=
  interval_of_check cellTest_21760 200 8 (by decide +kernel)

theorem cellTest_21760_block_26 : Interval cellTest_21760 208 216 :=
  interval_of_check cellTest_21760 208 8 (by decide +kernel)

theorem cellTest_21760_complete : Interval cellTest_21760 0 216 :=
  (interval_append cellTest_21760 0 104 216
  (interval_append cellTest_21760 0 48 104
  (interval_append cellTest_21760 0 24 48
  (interval_append cellTest_21760 0 8 24
  cellTest_21760_block_0
  (interval_append cellTest_21760 8 16 24
  cellTest_21760_block_1
  cellTest_21760_block_2))
  (interval_append cellTest_21760 24 32 48
  cellTest_21760_block_3
  (interval_append cellTest_21760 32 40 48
  cellTest_21760_block_4
  cellTest_21760_block_5)))
  (interval_append cellTest_21760 48 72 104
  (interval_append cellTest_21760 48 56 72
  cellTest_21760_block_6
  (interval_append cellTest_21760 56 64 72
  cellTest_21760_block_7
  cellTest_21760_block_8))
  (interval_append cellTest_21760 72 88 104
  (interval_append cellTest_21760 72 80 88
  cellTest_21760_block_9
  cellTest_21760_block_10)
  (interval_append cellTest_21760 88 96 104
  cellTest_21760_block_11
  cellTest_21760_block_12))))
  (interval_append cellTest_21760 104 160 216
  (interval_append cellTest_21760 104 128 160
  (interval_append cellTest_21760 104 112 128
  cellTest_21760_block_13
  (interval_append cellTest_21760 112 120 128
  cellTest_21760_block_14
  cellTest_21760_block_15))
  (interval_append cellTest_21760 128 144 160
  (interval_append cellTest_21760 128 136 144
  cellTest_21760_block_16
  cellTest_21760_block_17)
  (interval_append cellTest_21760 144 152 160
  cellTest_21760_block_18
  cellTest_21760_block_19)))
  (interval_append cellTest_21760 160 184 216
  (interval_append cellTest_21760 160 168 184
  cellTest_21760_block_20
  (interval_append cellTest_21760 168 176 184
  cellTest_21760_block_21
  cellTest_21760_block_22))
  (interval_append cellTest_21760 184 200 216
  (interval_append cellTest_21760 184 192 200
  cellTest_21760_block_23
  cellTest_21760_block_24)
  (interval_append cellTest_21760 200 208 216
  cellTest_21760_block_25
  cellTest_21760_block_26)))))
theorem cellTestInterval21760 : Interval cellTest 21760 21976 := by
  intro i hlo hhi
  have h := cellTest_21760_complete (i-21760) (Nat.zero_le _) (by omega)
  simpa only [cellTest_21760, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

theorem badTest_1792_block_30 : Interval badTest_1792 240 248 :=
  interval_of_check badTest_1792 240 8 (by decide +kernel)

theorem badTest_1792_block_31 : Interval badTest_1792 248 256 :=
  interval_of_check badTest_1792 248 8 (by decide +kernel)

theorem badTest_1792_complete : Interval badTest_1792 0 256 :=
  (interval_append badTest_1792 0 128 256
  (interval_append badTest_1792 0 64 128
  (interval_append badTest_1792 0 32 64
  (interval_append badTest_1792 0 16 32
  (interval_append badTest_1792 0 8 16
  badTest_1792_block_0
  badTest_1792_block_1)
  (interval_append badTest_1792 16 24 32
  badTest_1792_block_2
  badTest_1792_block_3))
  (interval_append badTest_1792 32 48 64
  (interval_append badTest_1792 32 40 48
  badTest_1792_block_4
  badTest_1792_block_5)
  (interval_append badTest_1792 48 56 64
  badTest_1792_block_6
  badTest_1792_block_7)))
  (interval_append badTest_1792 64 96 128
  (interval_append badTest_1792 64 80 96
  (interval_append badTest_1792 64 72 80
  badTest_1792_block_8
  badTest_1792_block_9)
  (interval_append badTest_1792 80 88 96
  badTest_1792_block_10
  badTest_1792_block_11))
  (interval_append badTest_1792 96 112 128
  (interval_append badTest_1792 96 104 112
  badTest_1792_block_12
  badTest_1792_block_13)
  (interval_append badTest_1792 112 120 128
  badTest_1792_block_14
  badTest_1792_block_15))))
  (interval_append badTest_1792 128 192 256
  (interval_append badTest_1792 128 160 192
  (interval_append badTest_1792 128 144 160
  (interval_append badTest_1792 128 136 144
  badTest_1792_block_16
  badTest_1792_block_17)
  (interval_append badTest_1792 144 152 160
  badTest_1792_block_18
  badTest_1792_block_19))
  (interval_append badTest_1792 160 176 192
  (interval_append badTest_1792 160 168 176
  badTest_1792_block_20
  badTest_1792_block_21)
  (interval_append badTest_1792 176 184 192
  badTest_1792_block_22
  badTest_1792_block_23)))
  (interval_append badTest_1792 192 224 256
  (interval_append badTest_1792 192 208 224
  (interval_append badTest_1792 192 200 208
  badTest_1792_block_24
  badTest_1792_block_25)
  (interval_append badTest_1792 208 216 224
  badTest_1792_block_26
  badTest_1792_block_27))
  (interval_append badTest_1792 224 240 256
  (interval_append badTest_1792 224 232 240
  badTest_1792_block_28
  badTest_1792_block_29)
  (interval_append badTest_1792 240 248 256
  badTest_1792_block_30
  badTest_1792_block_31)))))
theorem badTestInterval1792 : Interval badTest 1792 2048 := by
  intro i hlo hhi
  have h := badTest_1792_complete (i-1792) (Nat.zero_le _) (by omega)
  simpa only [badTest_1792, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_2048 (i : Nat) := badTest (i+2048)
theorem badTest_2048_block_0 : Interval badTest_2048 0 8 :=
  interval_of_check badTest_2048 0 8 (by decide +kernel)

theorem badTest_2048_block_1 : Interval badTest_2048 8 16 :=
  interval_of_check badTest_2048 8 8 (by decide +kernel)

theorem badTest_2048_block_2 : Interval badTest_2048 16 24 :=
  interval_of_check badTest_2048 16 8 (by decide +kernel)

theorem badTest_2048_block_3 : Interval badTest_2048 24 32 :=
  interval_of_check badTest_2048 24 8 (by decide +kernel)

theorem badTest_2048_block_4 : Interval badTest_2048 32 40 :=
  interval_of_check badTest_2048 32 8 (by decide +kernel)

theorem badTest_2048_block_5 : Interval badTest_2048 40 48 :=
  interval_of_check badTest_2048 40 8 (by decide +kernel)

theorem badTest_2048_block_6 : Interval badTest_2048 48 56 :=
  interval_of_check badTest_2048 48 8 (by decide +kernel)

theorem badTest_2048_block_7 : Interval badTest_2048 56 64 :=
  interval_of_check badTest_2048 56 8 (by decide +kernel)

theorem badTest_2048_block_8 : Interval badTest_2048 64 72 :=
  interval_of_check badTest_2048 64 8 (by decide +kernel)

theorem badTest_2048_block_9 : Interval badTest_2048 72 80 :=
  interval_of_check badTest_2048 72 8 (by decide +kernel)

theorem badTest_2048_block_10 : Interval badTest_2048 80 88 :=
  interval_of_check badTest_2048 80 8 (by decide +kernel)

theorem badTest_2048_block_11 : Interval badTest_2048 88 96 :=
  interval_of_check badTest_2048 88 8 (by decide +kernel)

theorem badTest_2048_block_12 : Interval badTest_2048 96 104 :=
  interval_of_check badTest_2048 96 8 (by decide +kernel)

theorem badTest_2048_block_13 : Interval badTest_2048 104 112 :=
  interval_of_check badTest_2048 104 8 (by decide +kernel)

theorem badTest_2048_block_14 : Interval badTest_2048 112 120 :=
  interval_of_check badTest_2048 112 8 (by decide +kernel)

theorem badTest_2048_block_15 : Interval badTest_2048 120 128 :=
  interval_of_check badTest_2048 120 8 (by decide +kernel)

theorem badTest_2048_block_16 : Interval badTest_2048 128 136 :=
  interval_of_check badTest_2048 128 8 (by decide +kernel)

theorem badTest_2048_block_17 : Interval badTest_2048 136 144 :=
  interval_of_check badTest_2048 136 8 (by decide +kernel)

theorem badTest_2048_block_18 : Interval badTest_2048 144 152 :=
  interval_of_check badTest_2048 144 8 (by decide +kernel)

theorem badTest_2048_block_19 : Interval badTest_2048 152 160 :=
  interval_of_check badTest_2048 152 8 (by decide +kernel)

theorem badTest_2048_block_20 : Interval badTest_2048 160 168 :=
  interval_of_check badTest_2048 160 8 (by decide +kernel)

theorem badTest_2048_block_21 : Interval badTest_2048 168 176 :=
  interval_of_check badTest_2048 168 8 (by decide +kernel)

theorem badTest_2048_block_22 : Interval badTest_2048 176 184 :=
  interval_of_check badTest_2048 176 8 (by decide +kernel)

theorem badTest_2048_block_23 : Interval badTest_2048 184 192 :=
  interval_of_check badTest_2048 184 8 (by decide +kernel)

theorem badTest_2048_block_24 : Interval badTest_2048 192 200 :=
  interval_of_check badTest_2048 192 8 (by decide +kernel)

theorem badTest_2048_block_25 : Interval badTest_2048 200 208 :=
  interval_of_check badTest_2048 200 8 (by decide +kernel)

theorem badTest_2048_block_26 : Interval badTest_2048 208 216 :=
  interval_of_check badTest_2048 208 8 (by decide +kernel)

theorem badTest_2048_block_27 : Interval badTest_2048 216 224 :=
  interval_of_check badTest_2048 216 8 (by decide +kernel)

theorem badTest_2048_block_28 : Interval badTest_2048 224 232 :=
  interval_of_check badTest_2048 224 8 (by decide +kernel)

theorem badTest_2048_block_29 : Interval badTest_2048 232 240 :=
  interval_of_check badTest_2048 232 8 (by decide +kernel)

theorem badTest_2048_block_30 : Interval badTest_2048 240 248 :=
  interval_of_check badTest_2048 240 8 (by decide +kernel)

theorem badTest_2048_block_31 : Interval badTest_2048 248 256 :=
  interval_of_check badTest_2048 248 8 (by decide +kernel)

theorem badTest_2048_complete : Interval badTest_2048 0 256 :=
  (interval_append badTest_2048 0 128 256
  (interval_append badTest_2048 0 64 128
  (interval_append badTest_2048 0 32 64
  (interval_append badTest_2048 0 16 32
  (interval_append badTest_2048 0 8 16
  badTest_2048_block_0
  badTest_2048_block_1)
  (interval_append badTest_2048 16 24 32
  badTest_2048_block_2
  badTest_2048_block_3))
  (interval_append badTest_2048 32 48 64
  (interval_append badTest_2048 32 40 48
  badTest_2048_block_4
  badTest_2048_block_5)
  (interval_append badTest_2048 48 56 64
  badTest_2048_block_6
  badTest_2048_block_7)))
  (interval_append badTest_2048 64 96 128
  (interval_append badTest_2048 64 80 96
  (interval_append badTest_2048 64 72 80
  badTest_2048_block_8
  badTest_2048_block_9)
  (interval_append badTest_2048 80 88 96
  badTest_2048_block_10
  badTest_2048_block_11))
  (interval_append badTest_2048 96 112 128
  (interval_append badTest_2048 96 104 112
  badTest_2048_block_12
  badTest_2048_block_13)
  (interval_append badTest_2048 112 120 128
  badTest_2048_block_14
  badTest_2048_block_15))))
  (interval_append badTest_2048 128 192 256
  (interval_append badTest_2048 128 160 192
  (interval_append badTest_2048 128 144 160
  (interval_append badTest_2048 128 136 144
  badTest_2048_block_16
  badTest_2048_block_17)
  (interval_append badTest_2048 144 152 160
  badTest_2048_block_18
  badTest_2048_block_19))
  (interval_append badTest_2048 160 176 192
  (interval_append badTest_2048 160 168 176
  badTest_2048_block_20
  badTest_2048_block_21)
  (interval_append badTest_2048 176 184 192
  badTest_2048_block_22
  badTest_2048_block_23)))
  (interval_append badTest_2048 192 224 256
  (interval_append badTest_2048 192 208 224
  (interval_append badTest_2048 192 200 208
  badTest_2048_block_24
  badTest_2048_block_25)
  (interval_append badTest_2048 208 216 224
  badTest_2048_block_26
  badTest_2048_block_27))
  (interval_append badTest_2048 224 240 256
  (interval_append badTest_2048 224 232 240
  badTest_2048_block_28
  badTest_2048_block_29)
  (interval_append badTest_2048 240 248 256
  badTest_2048_block_30
  badTest_2048_block_31)))))
theorem badTestInterval2048 : Interval badTest 2048 2304 := by
  intro i hlo hhi
  have h := badTest_2048_complete (i-2048) (Nat.zero_le _) (by omega)
  simpa only [badTest_2048, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_2304 (i : Nat) := badTest (i+2304)
theorem badTest_2304_block_0 : Interval badTest_2304 0 8 :=
  interval_of_check badTest_2304 0 8 (by decide +kernel)

theorem badTest_2304_block_1 : Interval badTest_2304 8 16 :=
  interval_of_check badTest_2304 8 8 (by decide +kernel)

theorem badTest_2304_block_2 : Interval badTest_2304 16 24 :=
  interval_of_check badTest_2304 16 8 (by decide +kernel)

theorem badTest_2304_block_3 : Interval badTest_2304 24 32 :=
  interval_of_check badTest_2304 24 8 (by decide +kernel)

theorem badTest_2304_block_4 : Interval badTest_2304 32 40 :=
  interval_of_check badTest_2304 32 8 (by decide +kernel)

theorem badTest_2304_block_5 : Interval badTest_2304 40 48 :=
  interval_of_check badTest_2304 40 8 (by decide +kernel)

theorem badTest_2304_block_6 : Interval badTest_2304 48 56 :=
  interval_of_check badTest_2304 48 8 (by decide +kernel)

theorem badTest_2304_block_7 : Interval badTest_2304 56 64 :=
  interval_of_check badTest_2304 56 8 (by decide +kernel)

theorem badTest_2304_block_8 : Interval badTest_2304 64 72 :=
  interval_of_check badTest_2304 64 8 (by decide +kernel)

theorem badTest_2304_block_9 : Interval badTest_2304 72 80 :=
  interval_of_check badTest_2304 72 8 (by decide +kernel)

theorem badTest_2304_block_10 : Interval badTest_2304 80 88 :=
  interval_of_check badTest_2304 80 8 (by decide +kernel)

theorem badTest_2304_block_11 : Interval badTest_2304 88 96 :=
  interval_of_check badTest_2304 88 8 (by decide +kernel)

theorem badTest_2304_block_12 : Interval badTest_2304 96 104 :=
  interval_of_check badTest_2304 96 8 (by decide +kernel)

theorem badTest_2304_block_13 : Interval badTest_2304 104 112 :=
  interval_of_check badTest_2304 104 8 (by decide +kernel)

theorem badTest_2304_block_14 : Interval badTest_2304 112 120 :=
  interval_of_check badTest_2304 112 8 (by decide +kernel)

theorem badTest_2304_block_15 : Interval badTest_2304 120 128 :=
  interval_of_check badTest_2304 120 8 (by decide +kernel)

theorem badTest_2304_block_16 : Interval badTest_2304 128 136 :=
  interval_of_check badTest_2304 128 8 (by decide +kernel)

theorem badTest_2304_block_17 : Interval badTest_2304 136 144 :=
  interval_of_check badTest_2304 136 8 (by decide +kernel)

theorem badTest_2304_block_18 : Interval badTest_2304 144 152 :=
  interval_of_check badTest_2304 144 8 (by decide +kernel)

theorem badTest_2304_block_19 : Interval badTest_2304 152 160 :=
  interval_of_check badTest_2304 152 8 (by decide +kernel)

theorem badTest_2304_block_20 : Interval badTest_2304 160 168 :=
  interval_of_check badTest_2304 160 8 (by decide +kernel)

theorem badTest_2304_block_21 : Interval badTest_2304 168 176 :=
  interval_of_check badTest_2304 168 8 (by decide +kernel)

theorem badTest_2304_block_22 : Interval badTest_2304 176 184 :=
  interval_of_check badTest_2304 176 8 (by decide +kernel)

theorem badTest_2304_block_23 : Interval badTest_2304 184 192 :=
  interval_of_check badTest_2304 184 8 (by decide +kernel)

theorem badTest_2304_block_24 : Interval badTest_2304 192 200 :=
  interval_of_check badTest_2304 192 8 (by decide +kernel)

theorem badTest_2304_block_25 : Interval badTest_2304 200 208 :=
  interval_of_check badTest_2304 200 8 (by decide +kernel)

theorem badTest_2304_block_26 : Interval badTest_2304 208 216 :=
  interval_of_check badTest_2304 208 8 (by decide +kernel)

theorem badTest_2304_block_27 : Interval badTest_2304 216 224 :=
  interval_of_check badTest_2304 216 8 (by decide +kernel)

theorem badTest_2304_block_28 : Interval badTest_2304 224 232 :=
  interval_of_check badTest_2304 224 8 (by decide +kernel)

theorem badTest_2304_block_29 : Interval badTest_2304 232 240 :=
  interval_of_check badTest_2304 232 8 (by decide +kernel)

theorem badTest_2304_block_30 : Interval badTest_2304 240 248 :=
  interval_of_check badTest_2304 240 8 (by decide +kernel)

theorem badTest_2304_block_31 : Interval badTest_2304 248 256 :=
  interval_of_check badTest_2304 248 8 (by decide +kernel)

theorem badTest_2304_complete : Interval badTest_2304 0 256 :=
  (interval_append badTest_2304 0 128 256
  (interval_append badTest_2304 0 64 128
  (interval_append badTest_2304 0 32 64
  (interval_append badTest_2304 0 16 32
  (interval_append badTest_2304 0 8 16
  badTest_2304_block_0
  badTest_2304_block_1)
  (interval_append badTest_2304 16 24 32
  badTest_2304_block_2
  badTest_2304_block_3))
  (interval_append badTest_2304 32 48 64
  (interval_append badTest_2304 32 40 48
  badTest_2304_block_4
  badTest_2304_block_5)
  (interval_append badTest_2304 48 56 64
  badTest_2304_block_6
  badTest_2304_block_7)))
  (interval_append badTest_2304 64 96 128
  (interval_append badTest_2304 64 80 96
  (interval_append badTest_2304 64 72 80
  badTest_2304_block_8
  badTest_2304_block_9)
  (interval_append badTest_2304 80 88 96
  badTest_2304_block_10
  badTest_2304_block_11))
  (interval_append badTest_2304 96 112 128
  (interval_append badTest_2304 96 104 112
  badTest_2304_block_12
  badTest_2304_block_13)
  (interval_append badTest_2304 112 120 128
  badTest_2304_block_14
  badTest_2304_block_15))))
  (interval_append badTest_2304 128 192 256
  (interval_append badTest_2304 128 160 192
  (interval_append badTest_2304 128 144 160
  (interval_append badTest_2304 128 136 144
  badTest_2304_block_16
  badTest_2304_block_17)
  (interval_append badTest_2304 144 152 160
  badTest_2304_block_18
  badTest_2304_block_19))
  (interval_append badTest_2304 160 176 192
  (interval_append badTest_2304 160 168 176
  badTest_2304_block_20
  badTest_2304_block_21)
  (interval_append badTest_2304 176 184 192
  badTest_2304_block_22
  badTest_2304_block_23)))
  (interval_append badTest_2304 192 224 256
  (interval_append badTest_2304 192 208 224
  (interval_append badTest_2304 192 200 208
  badTest_2304_block_24
  badTest_2304_block_25)
  (interval_append badTest_2304 208 216 224
  badTest_2304_block_26
  badTest_2304_block_27))
  (interval_append badTest_2304 224 240 256
  (interval_append badTest_2304 224 232 240
  badTest_2304_block_28
  badTest_2304_block_29)
  (interval_append badTest_2304 240 248 256
  badTest_2304_block_30
  badTest_2304_block_31)))))
theorem badTestInterval2304 : Interval badTest 2304 2560 := by
  intro i hlo hhi
  have h := badTest_2304_complete (i-2304) (Nat.zero_le _) (by omega)
  simpa only [badTest_2304, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
