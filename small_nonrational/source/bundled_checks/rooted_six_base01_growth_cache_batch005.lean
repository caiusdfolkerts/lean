module
prelude
public import RootedSixBase01GrowthCacheData

/- RootedSixBase01GrowthCacheBad020 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_5120 (i : Nat) := badTest (i+5120)
theorem badTest_5120_block_0 : Interval badTest_5120 0 8 :=
  interval_of_check badTest_5120 0 8 (by decide +kernel)

theorem badTest_5120_block_1 : Interval badTest_5120 8 16 :=
  interval_of_check badTest_5120 8 8 (by decide +kernel)

theorem badTest_5120_block_2 : Interval badTest_5120 16 24 :=
  interval_of_check badTest_5120 16 8 (by decide +kernel)

theorem badTest_5120_block_3 : Interval badTest_5120 24 32 :=
  interval_of_check badTest_5120 24 8 (by decide +kernel)

theorem badTest_5120_block_4 : Interval badTest_5120 32 40 :=
  interval_of_check badTest_5120 32 8 (by decide +kernel)

theorem badTest_5120_block_5 : Interval badTest_5120 40 48 :=
  interval_of_check badTest_5120 40 8 (by decide +kernel)

theorem badTest_5120_block_6 : Interval badTest_5120 48 56 :=
  interval_of_check badTest_5120 48 8 (by decide +kernel)

theorem badTest_5120_block_7 : Interval badTest_5120 56 64 :=
  interval_of_check badTest_5120 56 8 (by decide +kernel)

theorem badTest_5120_block_8 : Interval badTest_5120 64 72 :=
  interval_of_check badTest_5120 64 8 (by decide +kernel)

theorem badTest_5120_block_9 : Interval badTest_5120 72 80 :=
  interval_of_check badTest_5120 72 8 (by decide +kernel)

theorem badTest_5120_block_10 : Interval badTest_5120 80 88 :=
  interval_of_check badTest_5120 80 8 (by decide +kernel)

theorem badTest_5120_block_11 : Interval badTest_5120 88 96 :=
  interval_of_check badTest_5120 88 8 (by decide +kernel)

theorem badTest_5120_block_12 : Interval badTest_5120 96 104 :=
  interval_of_check badTest_5120 96 8 (by decide +kernel)

theorem badTest_5120_block_13 : Interval badTest_5120 104 112 :=
  interval_of_check badTest_5120 104 8 (by decide +kernel)

theorem badTest_5120_block_14 : Interval badTest_5120 112 120 :=
  interval_of_check badTest_5120 112 8 (by decide +kernel)

theorem badTest_5120_block_15 : Interval badTest_5120 120 128 :=
  interval_of_check badTest_5120 120 8 (by decide +kernel)

theorem badTest_5120_block_16 : Interval badTest_5120 128 136 :=
  interval_of_check badTest_5120 128 8 (by decide +kernel)

theorem badTest_5120_block_17 : Interval badTest_5120 136 144 :=
  interval_of_check badTest_5120 136 8 (by decide +kernel)

theorem badTest_5120_block_18 : Interval badTest_5120 144 152 :=
  interval_of_check badTest_5120 144 8 (by decide +kernel)

theorem badTest_5120_block_19 : Interval badTest_5120 152 160 :=
  interval_of_check badTest_5120 152 8 (by decide +kernel)

theorem badTest_5120_block_20 : Interval badTest_5120 160 168 :=
  interval_of_check badTest_5120 160 8 (by decide +kernel)

theorem badTest_5120_block_21 : Interval badTest_5120 168 176 :=
  interval_of_check badTest_5120 168 8 (by decide +kernel)

theorem badTest_5120_block_22 : Interval badTest_5120 176 184 :=
  interval_of_check badTest_5120 176 8 (by decide +kernel)

theorem badTest_5120_block_23 : Interval badTest_5120 184 192 :=
  interval_of_check badTest_5120 184 8 (by decide +kernel)

theorem badTest_5120_block_24 : Interval badTest_5120 192 200 :=
  interval_of_check badTest_5120 192 8 (by decide +kernel)

theorem badTest_5120_block_25 : Interval badTest_5120 200 208 :=
  interval_of_check badTest_5120 200 8 (by decide +kernel)

theorem badTest_5120_block_26 : Interval badTest_5120 208 216 :=
  interval_of_check badTest_5120 208 8 (by decide +kernel)

theorem badTest_5120_block_27 : Interval badTest_5120 216 224 :=
  interval_of_check badTest_5120 216 8 (by decide +kernel)

theorem badTest_5120_block_28 : Interval badTest_5120 224 232 :=
  interval_of_check badTest_5120 224 8 (by decide +kernel)

theorem badTest_5120_block_29 : Interval badTest_5120 232 240 :=
  interval_of_check badTest_5120 232 8 (by decide +kernel)

theorem badTest_5120_block_30 : Interval badTest_5120 240 248 :=
  interval_of_check badTest_5120 240 8 (by decide +kernel)

theorem badTest_5120_block_31 : Interval badTest_5120 248 256 :=
  interval_of_check badTest_5120 248 8 (by decide +kernel)

theorem badTest_5120_complete : Interval badTest_5120 0 256 :=
  (interval_append badTest_5120 0 128 256
  (interval_append badTest_5120 0 64 128
  (interval_append badTest_5120 0 32 64
  (interval_append badTest_5120 0 16 32
  (interval_append badTest_5120 0 8 16
  badTest_5120_block_0
  badTest_5120_block_1)
  (interval_append badTest_5120 16 24 32
  badTest_5120_block_2
  badTest_5120_block_3))
  (interval_append badTest_5120 32 48 64
  (interval_append badTest_5120 32 40 48
  badTest_5120_block_4
  badTest_5120_block_5)
  (interval_append badTest_5120 48 56 64
  badTest_5120_block_6
  badTest_5120_block_7)))
  (interval_append badTest_5120 64 96 128
  (interval_append badTest_5120 64 80 96
  (interval_append badTest_5120 64 72 80
  badTest_5120_block_8
  badTest_5120_block_9)
  (interval_append badTest_5120 80 88 96
  badTest_5120_block_10
  badTest_5120_block_11))
  (interval_append badTest_5120 96 112 128
  (interval_append badTest_5120 96 104 112
  badTest_5120_block_12
  badTest_5120_block_13)
  (interval_append badTest_5120 112 120 128
  badTest_5120_block_14
  badTest_5120_block_15))))
  (interval_append badTest_5120 128 192 256
  (interval_append badTest_5120 128 160 192
  (interval_append badTest_5120 128 144 160
  (interval_append badTest_5120 128 136 144
  badTest_5120_block_16
  badTest_5120_block_17)
  (interval_append badTest_5120 144 152 160
  badTest_5120_block_18
  badTest_5120_block_19))
  (interval_append badTest_5120 160 176 192
  (interval_append badTest_5120 160 168 176
  badTest_5120_block_20
  badTest_5120_block_21)
  (interval_append badTest_5120 176 184 192
  badTest_5120_block_22
  badTest_5120_block_23)))
  (interval_append badTest_5120 192 224 256
  (interval_append badTest_5120 192 208 224
  (interval_append badTest_5120 192 200 208
  badTest_5120_block_24
  badTest_5120_block_25)
  (interval_append badTest_5120 208 216 224
  badTest_5120_block_26
  badTest_5120_block_27))
  (interval_append badTest_5120 224 240 256
  (interval_append badTest_5120 224 232 240
  badTest_5120_block_28
  badTest_5120_block_29)
  (interval_append badTest_5120 240 248 256
  badTest_5120_block_30
  badTest_5120_block_31)))))
theorem badTestInterval5120 : Interval badTest 5120 5376 := by
  intro i hlo hhi
  have h := badTest_5120_complete (i-5120) (Nat.zero_le _) (by omega)
  simpa only [badTest_5120, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad021 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_5376 (i : Nat) := badTest (i+5376)
theorem badTest_5376_block_0 : Interval badTest_5376 0 8 :=
  interval_of_check badTest_5376 0 8 (by decide +kernel)

theorem badTest_5376_block_1 : Interval badTest_5376 8 16 :=
  interval_of_check badTest_5376 8 8 (by decide +kernel)

theorem badTest_5376_block_2 : Interval badTest_5376 16 24 :=
  interval_of_check badTest_5376 16 8 (by decide +kernel)

theorem badTest_5376_block_3 : Interval badTest_5376 24 32 :=
  interval_of_check badTest_5376 24 8 (by decide +kernel)

theorem badTest_5376_block_4 : Interval badTest_5376 32 40 :=
  interval_of_check badTest_5376 32 8 (by decide +kernel)

theorem badTest_5376_block_5 : Interval badTest_5376 40 48 :=
  interval_of_check badTest_5376 40 8 (by decide +kernel)

theorem badTest_5376_block_6 : Interval badTest_5376 48 56 :=
  interval_of_check badTest_5376 48 8 (by decide +kernel)

theorem badTest_5376_block_7 : Interval badTest_5376 56 64 :=
  interval_of_check badTest_5376 56 8 (by decide +kernel)

theorem badTest_5376_block_8 : Interval badTest_5376 64 72 :=
  interval_of_check badTest_5376 64 8 (by decide +kernel)

theorem badTest_5376_block_9 : Interval badTest_5376 72 80 :=
  interval_of_check badTest_5376 72 8 (by decide +kernel)

theorem badTest_5376_block_10 : Interval badTest_5376 80 88 :=
  interval_of_check badTest_5376 80 8 (by decide +kernel)

theorem badTest_5376_block_11 : Interval badTest_5376 88 96 :=
  interval_of_check badTest_5376 88 8 (by decide +kernel)

theorem badTest_5376_block_12 : Interval badTest_5376 96 104 :=
  interval_of_check badTest_5376 96 8 (by decide +kernel)

theorem badTest_5376_block_13 : Interval badTest_5376 104 112 :=
  interval_of_check badTest_5376 104 8 (by decide +kernel)

theorem badTest_5376_block_14 : Interval badTest_5376 112 120 :=
  interval_of_check badTest_5376 112 8 (by decide +kernel)

theorem badTest_5376_block_15 : Interval badTest_5376 120 128 :=
  interval_of_check badTest_5376 120 8 (by decide +kernel)

theorem badTest_5376_block_16 : Interval badTest_5376 128 136 :=
  interval_of_check badTest_5376 128 8 (by decide +kernel)

theorem badTest_5376_block_17 : Interval badTest_5376 136 144 :=
  interval_of_check badTest_5376 136 8 (by decide +kernel)

theorem badTest_5376_block_18 : Interval badTest_5376 144 152 :=
  interval_of_check badTest_5376 144 8 (by decide +kernel)

theorem badTest_5376_block_19 : Interval badTest_5376 152 160 :=
  interval_of_check badTest_5376 152 8 (by decide +kernel)

theorem badTest_5376_block_20 : Interval badTest_5376 160 168 :=
  interval_of_check badTest_5376 160 8 (by decide +kernel)

theorem badTest_5376_block_21 : Interval badTest_5376 168 176 :=
  interval_of_check badTest_5376 168 8 (by decide +kernel)

theorem badTest_5376_block_22 : Interval badTest_5376 176 184 :=
  interval_of_check badTest_5376 176 8 (by decide +kernel)

theorem badTest_5376_block_23 : Interval badTest_5376 184 192 :=
  interval_of_check badTest_5376 184 8 (by decide +kernel)

theorem badTest_5376_block_24 : Interval badTest_5376 192 200 :=
  interval_of_check badTest_5376 192 8 (by decide +kernel)

theorem badTest_5376_block_25 : Interval badTest_5376 200 208 :=
  interval_of_check badTest_5376 200 8 (by decide +kernel)

theorem badTest_5376_block_26 : Interval badTest_5376 208 216 :=
  interval_of_check badTest_5376 208 8 (by decide +kernel)

theorem badTest_5376_block_27 : Interval badTest_5376 216 224 :=
  interval_of_check badTest_5376 216 8 (by decide +kernel)

theorem badTest_5376_block_28 : Interval badTest_5376 224 232 :=
  interval_of_check badTest_5376 224 8 (by decide +kernel)

theorem badTest_5376_block_29 : Interval badTest_5376 232 240 :=
  interval_of_check badTest_5376 232 8 (by decide +kernel)

theorem badTest_5376_block_30 : Interval badTest_5376 240 248 :=
  interval_of_check badTest_5376 240 8 (by decide +kernel)

theorem badTest_5376_block_31 : Interval badTest_5376 248 256 :=
  interval_of_check badTest_5376 248 8 (by decide +kernel)

theorem badTest_5376_complete : Interval badTest_5376 0 256 :=
  (interval_append badTest_5376 0 128 256
  (interval_append badTest_5376 0 64 128
  (interval_append badTest_5376 0 32 64
  (interval_append badTest_5376 0 16 32
  (interval_append badTest_5376 0 8 16
  badTest_5376_block_0
  badTest_5376_block_1)
  (interval_append badTest_5376 16 24 32
  badTest_5376_block_2
  badTest_5376_block_3))
  (interval_append badTest_5376 32 48 64
  (interval_append badTest_5376 32 40 48
  badTest_5376_block_4
  badTest_5376_block_5)
  (interval_append badTest_5376 48 56 64
  badTest_5376_block_6
  badTest_5376_block_7)))
  (interval_append badTest_5376 64 96 128
  (interval_append badTest_5376 64 80 96
  (interval_append badTest_5376 64 72 80
  badTest_5376_block_8
  badTest_5376_block_9)
  (interval_append badTest_5376 80 88 96
  badTest_5376_block_10
  badTest_5376_block_11))
  (interval_append badTest_5376 96 112 128
  (interval_append badTest_5376 96 104 112
  badTest_5376_block_12
  badTest_5376_block_13)
  (interval_append badTest_5376 112 120 128
  badTest_5376_block_14
  badTest_5376_block_15))))
  (interval_append badTest_5376 128 192 256
  (interval_append badTest_5376 128 160 192
  (interval_append badTest_5376 128 144 160
  (interval_append badTest_5376 128 136 144
  badTest_5376_block_16
  badTest_5376_block_17)
  (interval_append badTest_5376 144 152 160
  badTest_5376_block_18
  badTest_5376_block_19))
  (interval_append badTest_5376 160 176 192
  (interval_append badTest_5376 160 168 176
  badTest_5376_block_20
  badTest_5376_block_21)
  (interval_append badTest_5376 176 184 192
  badTest_5376_block_22
  badTest_5376_block_23)))
  (interval_append badTest_5376 192 224 256
  (interval_append badTest_5376 192 208 224
  (interval_append badTest_5376 192 200 208
  badTest_5376_block_24
  badTest_5376_block_25)
  (interval_append badTest_5376 208 216 224
  badTest_5376_block_26
  badTest_5376_block_27))
  (interval_append badTest_5376 224 240 256
  (interval_append badTest_5376 224 232 240
  badTest_5376_block_28
  badTest_5376_block_29)
  (interval_append badTest_5376 240 248 256
  badTest_5376_block_30
  badTest_5376_block_31)))))
theorem badTestInterval5376 : Interval badTest 5376 5632 := by
  intro i hlo hhi
  have h := badTest_5376_complete (i-5376) (Nat.zero_le _) (by omega)
  simpa only [badTest_5376, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad022 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_5632 (i : Nat) := badTest (i+5632)
theorem badTest_5632_block_0 : Interval badTest_5632 0 8 :=
  interval_of_check badTest_5632 0 8 (by decide +kernel)

theorem badTest_5632_block_1 : Interval badTest_5632 8 16 :=
  interval_of_check badTest_5632 8 8 (by decide +kernel)

theorem badTest_5632_block_2 : Interval badTest_5632 16 24 :=
  interval_of_check badTest_5632 16 8 (by decide +kernel)

theorem badTest_5632_block_3 : Interval badTest_5632 24 32 :=
  interval_of_check badTest_5632 24 8 (by decide +kernel)

theorem badTest_5632_block_4 : Interval badTest_5632 32 40 :=
  interval_of_check badTest_5632 32 8 (by decide +kernel)

theorem badTest_5632_block_5 : Interval badTest_5632 40 48 :=
  interval_of_check badTest_5632 40 8 (by decide +kernel)

theorem badTest_5632_block_6 : Interval badTest_5632 48 56 :=
  interval_of_check badTest_5632 48 8 (by decide +kernel)

theorem badTest_5632_block_7 : Interval badTest_5632 56 64 :=
  interval_of_check badTest_5632 56 8 (by decide +kernel)

theorem badTest_5632_block_8 : Interval badTest_5632 64 72 :=
  interval_of_check badTest_5632 64 8 (by decide +kernel)

theorem badTest_5632_block_9 : Interval badTest_5632 72 80 :=
  interval_of_check badTest_5632 72 8 (by decide +kernel)

theorem badTest_5632_block_10 : Interval badTest_5632 80 88 :=
  interval_of_check badTest_5632 80 8 (by decide +kernel)

theorem badTest_5632_block_11 : Interval badTest_5632 88 96 :=
  interval_of_check badTest_5632 88 8 (by decide +kernel)

theorem badTest_5632_block_12 : Interval badTest_5632 96 104 :=
  interval_of_check badTest_5632 96 8 (by decide +kernel)

theorem badTest_5632_block_13 : Interval badTest_5632 104 112 :=
  interval_of_check badTest_5632 104 8 (by decide +kernel)

theorem badTest_5632_block_14 : Interval badTest_5632 112 120 :=
  interval_of_check badTest_5632 112 8 (by decide +kernel)

theorem badTest_5632_block_15 : Interval badTest_5632 120 128 :=
  interval_of_check badTest_5632 120 8 (by decide +kernel)

theorem badTest_5632_block_16 : Interval badTest_5632 128 136 :=
  interval_of_check badTest_5632 128 8 (by decide +kernel)

theorem badTest_5632_block_17 : Interval badTest_5632 136 144 :=
  interval_of_check badTest_5632 136 8 (by decide +kernel)

theorem badTest_5632_block_18 : Interval badTest_5632 144 152 :=
  interval_of_check badTest_5632 144 8 (by decide +kernel)

theorem badTest_5632_block_19 : Interval badTest_5632 152 160 :=
  interval_of_check badTest_5632 152 8 (by decide +kernel)

theorem badTest_5632_block_20 : Interval badTest_5632 160 168 :=
  interval_of_check badTest_5632 160 8 (by decide +kernel)

theorem badTest_5632_block_21 : Interval badTest_5632 168 176 :=
  interval_of_check badTest_5632 168 8 (by decide +kernel)

theorem badTest_5632_block_22 : Interval badTest_5632 176 184 :=
  interval_of_check badTest_5632 176 8 (by decide +kernel)

theorem badTest_5632_block_23 : Interval badTest_5632 184 192 :=
  interval_of_check badTest_5632 184 8 (by decide +kernel)

theorem badTest_5632_block_24 : Interval badTest_5632 192 200 :=
  interval_of_check badTest_5632 192 8 (by decide +kernel)

theorem badTest_5632_block_25 : Interval badTest_5632 200 208 :=
  interval_of_check badTest_5632 200 8 (by decide +kernel)

theorem badTest_5632_block_26 : Interval badTest_5632 208 216 :=
  interval_of_check badTest_5632 208 8 (by decide +kernel)

theorem badTest_5632_block_27 : Interval badTest_5632 216 224 :=
  interval_of_check badTest_5632 216 8 (by decide +kernel)

theorem badTest_5632_block_28 : Interval badTest_5632 224 232 :=
  interval_of_check badTest_5632 224 8 (by decide +kernel)

theorem badTest_5632_block_29 : Interval badTest_5632 232 240 :=
  interval_of_check badTest_5632 232 8 (by decide +kernel)

theorem badTest_5632_block_30 : Interval badTest_5632 240 248 :=
  interval_of_check badTest_5632 240 8 (by decide +kernel)

theorem badTest_5632_block_31 : Interval badTest_5632 248 256 :=
  interval_of_check badTest_5632 248 8 (by decide +kernel)

theorem badTest_5632_complete : Interval badTest_5632 0 256 :=
  (interval_append badTest_5632 0 128 256
  (interval_append badTest_5632 0 64 128
  (interval_append badTest_5632 0 32 64
  (interval_append badTest_5632 0 16 32
  (interval_append badTest_5632 0 8 16
  badTest_5632_block_0
  badTest_5632_block_1)
  (interval_append badTest_5632 16 24 32
  badTest_5632_block_2
  badTest_5632_block_3))
  (interval_append badTest_5632 32 48 64
  (interval_append badTest_5632 32 40 48
  badTest_5632_block_4
  badTest_5632_block_5)
  (interval_append badTest_5632 48 56 64
  badTest_5632_block_6
  badTest_5632_block_7)))
  (interval_append badTest_5632 64 96 128
  (interval_append badTest_5632 64 80 96
  (interval_append badTest_5632 64 72 80
  badTest_5632_block_8
  badTest_5632_block_9)
  (interval_append badTest_5632 80 88 96
  badTest_5632_block_10
  badTest_5632_block_11))
  (interval_append badTest_5632 96 112 128
  (interval_append badTest_5632 96 104 112
  badTest_5632_block_12
  badTest_5632_block_13)
  (interval_append badTest_5632 112 120 128
  badTest_5632_block_14
  badTest_5632_block_15))))
  (interval_append badTest_5632 128 192 256
  (interval_append badTest_5632 128 160 192
  (interval_append badTest_5632 128 144 160
  (interval_append badTest_5632 128 136 144
  badTest_5632_block_16
  badTest_5632_block_17)
  (interval_append badTest_5632 144 152 160
  badTest_5632_block_18
  badTest_5632_block_19))
  (interval_append badTest_5632 160 176 192
  (interval_append badTest_5632 160 168 176
  badTest_5632_block_20
  badTest_5632_block_21)
  (interval_append badTest_5632 176 184 192
  badTest_5632_block_22
  badTest_5632_block_23)))
  (interval_append badTest_5632 192 224 256
  (interval_append badTest_5632 192 208 224
  (interval_append badTest_5632 192 200 208
  badTest_5632_block_24
  badTest_5632_block_25)
  (interval_append badTest_5632 208 216 224
  badTest_5632_block_26
  badTest_5632_block_27))
  (interval_append badTest_5632 224 240 256
  (interval_append badTest_5632 224 232 240
  badTest_5632_block_28
  badTest_5632_block_29)
  (interval_append badTest_5632 240 248 256
  badTest_5632_block_30
  badTest_5632_block_31)))))
theorem badTestInterval5632 : Interval badTest 5632 5888 := by
  intro i hlo hhi
  have h := badTest_5632_complete (i-5632) (Nat.zero_le _) (by omega)
  simpa only [badTest_5632, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad023 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_5888 (i : Nat) := badTest (i+5888)
theorem badTest_5888_block_0 : Interval badTest_5888 0 8 :=
  interval_of_check badTest_5888 0 8 (by decide +kernel)

theorem badTest_5888_block_1 : Interval badTest_5888 8 16 :=
  interval_of_check badTest_5888 8 8 (by decide +kernel)

theorem badTest_5888_block_2 : Interval badTest_5888 16 24 :=
  interval_of_check badTest_5888 16 8 (by decide +kernel)

theorem badTest_5888_block_3 : Interval badTest_5888 24 32 :=
  interval_of_check badTest_5888 24 8 (by decide +kernel)

theorem badTest_5888_block_4 : Interval badTest_5888 32 40 :=
  interval_of_check badTest_5888 32 8 (by decide +kernel)

theorem badTest_5888_block_5 : Interval badTest_5888 40 48 :=
  interval_of_check badTest_5888 40 8 (by decide +kernel)

theorem badTest_5888_block_6 : Interval badTest_5888 48 56 :=
  interval_of_check badTest_5888 48 8 (by decide +kernel)

theorem badTest_5888_block_7 : Interval badTest_5888 56 64 :=
  interval_of_check badTest_5888 56 8 (by decide +kernel)

theorem badTest_5888_block_8 : Interval badTest_5888 64 72 :=
  interval_of_check badTest_5888 64 8 (by decide +kernel)

theorem badTest_5888_block_9 : Interval badTest_5888 72 80 :=
  interval_of_check badTest_5888 72 8 (by decide +kernel)

theorem badTest_5888_block_10 : Interval badTest_5888 80 88 :=
  interval_of_check badTest_5888 80 8 (by decide +kernel)

theorem badTest_5888_block_11 : Interval badTest_5888 88 96 :=
  interval_of_check badTest_5888 88 8 (by decide +kernel)

theorem badTest_5888_block_12 : Interval badTest_5888 96 104 :=
  interval_of_check badTest_5888 96 8 (by decide +kernel)

theorem badTest_5888_block_13 : Interval badTest_5888 104 112 :=
  interval_of_check badTest_5888 104 8 (by decide +kernel)

theorem badTest_5888_block_14 : Interval badTest_5888 112 120 :=
  interval_of_check badTest_5888 112 8 (by decide +kernel)

theorem badTest_5888_block_15 : Interval badTest_5888 120 128 :=
  interval_of_check badTest_5888 120 8 (by decide +kernel)

theorem badTest_5888_block_16 : Interval badTest_5888 128 136 :=
  interval_of_check badTest_5888 128 8 (by decide +kernel)

theorem badTest_5888_block_17 : Interval badTest_5888 136 144 :=
  interval_of_check badTest_5888 136 8 (by decide +kernel)

theorem badTest_5888_block_18 : Interval badTest_5888 144 152 :=
  interval_of_check badTest_5888 144 8 (by decide +kernel)

theorem badTest_5888_block_19 : Interval badTest_5888 152 160 :=
  interval_of_check badTest_5888 152 8 (by decide +kernel)

theorem badTest_5888_block_20 : Interval badTest_5888 160 168 :=
  interval_of_check badTest_5888 160 8 (by decide +kernel)

theorem badTest_5888_block_21 : Interval badTest_5888 168 176 :=
  interval_of_check badTest_5888 168 8 (by decide +kernel)

theorem badTest_5888_block_22 : Interval badTest_5888 176 184 :=
  interval_of_check badTest_5888 176 8 (by decide +kernel)

theorem badTest_5888_block_23 : Interval badTest_5888 184 192 :=
  interval_of_check badTest_5888 184 8 (by decide +kernel)

theorem badTest_5888_block_24 : Interval badTest_5888 192 200 :=
  interval_of_check badTest_5888 192 8 (by decide +kernel)

theorem badTest_5888_block_25 : Interval badTest_5888 200 208 :=
  interval_of_check badTest_5888 200 8 (by decide +kernel)

theorem badTest_5888_block_26 : Interval badTest_5888 208 216 :=
  interval_of_check badTest_5888 208 8 (by decide +kernel)

theorem badTest_5888_block_27 : Interval badTest_5888 216 224 :=
  interval_of_check badTest_5888 216 8 (by decide +kernel)

theorem badTest_5888_block_28 : Interval badTest_5888 224 232 :=
  interval_of_check badTest_5888 224 8 (by decide +kernel)

theorem badTest_5888_block_29 : Interval badTest_5888 232 240 :=
  interval_of_check badTest_5888 232 8 (by decide +kernel)

theorem badTest_5888_block_30 : Interval badTest_5888 240 248 :=
  interval_of_check badTest_5888 240 8 (by decide +kernel)

theorem badTest_5888_block_31 : Interval badTest_5888 248 256 :=
  interval_of_check badTest_5888 248 8 (by decide +kernel)

theorem badTest_5888_complete : Interval badTest_5888 0 256 :=
  (interval_append badTest_5888 0 128 256
  (interval_append badTest_5888 0 64 128
  (interval_append badTest_5888 0 32 64
  (interval_append badTest_5888 0 16 32
  (interval_append badTest_5888 0 8 16
  badTest_5888_block_0
  badTest_5888_block_1)
  (interval_append badTest_5888 16 24 32
  badTest_5888_block_2
  badTest_5888_block_3))
  (interval_append badTest_5888 32 48 64
  (interval_append badTest_5888 32 40 48
  badTest_5888_block_4
  badTest_5888_block_5)
  (interval_append badTest_5888 48 56 64
  badTest_5888_block_6
  badTest_5888_block_7)))
  (interval_append badTest_5888 64 96 128
  (interval_append badTest_5888 64 80 96
  (interval_append badTest_5888 64 72 80
  badTest_5888_block_8
  badTest_5888_block_9)
  (interval_append badTest_5888 80 88 96
  badTest_5888_block_10
  badTest_5888_block_11))
  (interval_append badTest_5888 96 112 128
  (interval_append badTest_5888 96 104 112
  badTest_5888_block_12
  badTest_5888_block_13)
  (interval_append badTest_5888 112 120 128
  badTest_5888_block_14
  badTest_5888_block_15))))
  (interval_append badTest_5888 128 192 256
  (interval_append badTest_5888 128 160 192
  (interval_append badTest_5888 128 144 160
  (interval_append badTest_5888 128 136 144
  badTest_5888_block_16
  badTest_5888_block_17)
  (interval_append badTest_5888 144 152 160
  badTest_5888_block_18
  badTest_5888_block_19))
  (interval_append badTest_5888 160 176 192
  (interval_append badTest_5888 160 168 176
  badTest_5888_block_20
  badTest_5888_block_21)
  (interval_append badTest_5888 176 184 192
  badTest_5888_block_22
  badTest_5888_block_23)))
  (interval_append badTest_5888 192 224 256
  (interval_append badTest_5888 192 208 224
  (interval_append badTest_5888 192 200 208
  badTest_5888_block_24
  badTest_5888_block_25)
  (interval_append badTest_5888 208 216 224
  badTest_5888_block_26
  badTest_5888_block_27))
  (interval_append badTest_5888 224 240 256
  (interval_append badTest_5888 224 232 240
  badTest_5888_block_28
  badTest_5888_block_29)
  (interval_append badTest_5888 240 248 256
  badTest_5888_block_30
  badTest_5888_block_31)))))
theorem badTestInterval5888 : Interval badTest 5888 6144 := by
  intro i hlo hhi
  have h := badTest_5888_complete (i-5888) (Nat.zero_le _) (by omega)
  simpa only [badTest_5888, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad024 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_6144 (i : Nat) := badTest (i+6144)
theorem badTest_6144_block_0 : Interval badTest_6144 0 8 :=
  interval_of_check badTest_6144 0 8 (by decide +kernel)

theorem badTest_6144_block_1 : Interval badTest_6144 8 16 :=
  interval_of_check badTest_6144 8 8 (by decide +kernel)

theorem badTest_6144_block_2 : Interval badTest_6144 16 24 :=
  interval_of_check badTest_6144 16 8 (by decide +kernel)

theorem badTest_6144_block_3 : Interval badTest_6144 24 32 :=
  interval_of_check badTest_6144 24 8 (by decide +kernel)

theorem badTest_6144_block_4 : Interval badTest_6144 32 40 :=
  interval_of_check badTest_6144 32 8 (by decide +kernel)

theorem badTest_6144_block_5 : Interval badTest_6144 40 48 :=
  interval_of_check badTest_6144 40 8 (by decide +kernel)

theorem badTest_6144_block_6 : Interval badTest_6144 48 56 :=
  interval_of_check badTest_6144 48 8 (by decide +kernel)

theorem badTest_6144_block_7 : Interval badTest_6144 56 64 :=
  interval_of_check badTest_6144 56 8 (by decide +kernel)

theorem badTest_6144_block_8 : Interval badTest_6144 64 72 :=
  interval_of_check badTest_6144 64 8 (by decide +kernel)

theorem badTest_6144_block_9 : Interval badTest_6144 72 80 :=
  interval_of_check badTest_6144 72 8 (by decide +kernel)

theorem badTest_6144_block_10 : Interval badTest_6144 80 88 :=
  interval_of_check badTest_6144 80 8 (by decide +kernel)

theorem badTest_6144_block_11 : Interval badTest_6144 88 96 :=
  interval_of_check badTest_6144 88 8 (by decide +kernel)

theorem badTest_6144_block_12 : Interval badTest_6144 96 104 :=
  interval_of_check badTest_6144 96 8 (by decide +kernel)

theorem badTest_6144_block_13 : Interval badTest_6144 104 112 :=
  interval_of_check badTest_6144 104 8 (by decide +kernel)

theorem badTest_6144_block_14 : Interval badTest_6144 112 120 :=
  interval_of_check badTest_6144 112 8 (by decide +kernel)

theorem badTest_6144_block_15 : Interval badTest_6144 120 128 :=
  interval_of_check badTest_6144 120 8 (by decide +kernel)

theorem badTest_6144_block_16 : Interval badTest_6144 128 136 :=
  interval_of_check badTest_6144 128 8 (by decide +kernel)

theorem badTest_6144_block_17 : Interval badTest_6144 136 144 :=
  interval_of_check badTest_6144 136 8 (by decide +kernel)

theorem badTest_6144_block_18 : Interval badTest_6144 144 152 :=
  interval_of_check badTest_6144 144 8 (by decide +kernel)

theorem badTest_6144_block_19 : Interval badTest_6144 152 160 :=
  interval_of_check badTest_6144 152 8 (by decide +kernel)

theorem badTest_6144_block_20 : Interval badTest_6144 160 168 :=
  interval_of_check badTest_6144 160 8 (by decide +kernel)

theorem badTest_6144_block_21 : Interval badTest_6144 168 176 :=
  interval_of_check badTest_6144 168 8 (by decide +kernel)

theorem badTest_6144_block_22 : Interval badTest_6144 176 184 :=
  interval_of_check badTest_6144 176 8 (by decide +kernel)

theorem badTest_6144_block_23 : Interval badTest_6144 184 192 :=
  interval_of_check badTest_6144 184 8 (by decide +kernel)

theorem badTest_6144_block_24 : Interval badTest_6144 192 200 :=
  interval_of_check badTest_6144 192 8 (by decide +kernel)

theorem badTest_6144_block_25 : Interval badTest_6144 200 208 :=
  interval_of_check badTest_6144 200 8 (by decide +kernel)

theorem badTest_6144_block_26 : Interval badTest_6144 208 216 :=
  interval_of_check badTest_6144 208 8 (by decide +kernel)

theorem badTest_6144_block_27 : Interval badTest_6144 216 224 :=
  interval_of_check badTest_6144 216 8 (by decide +kernel)

theorem badTest_6144_block_28 : Interval badTest_6144 224 232 :=
  interval_of_check badTest_6144 224 8 (by decide +kernel)

theorem badTest_6144_block_29 : Interval badTest_6144 232 240 :=
  interval_of_check badTest_6144 232 8 (by decide +kernel)

theorem badTest_6144_block_30 : Interval badTest_6144 240 248 :=
  interval_of_check badTest_6144 240 8 (by decide +kernel)

theorem badTest_6144_block_31 : Interval badTest_6144 248 256 :=
  interval_of_check badTest_6144 248 8 (by decide +kernel)

theorem badTest_6144_complete : Interval badTest_6144 0 256 :=
  (interval_append badTest_6144 0 128 256
  (interval_append badTest_6144 0 64 128
  (interval_append badTest_6144 0 32 64
  (interval_append badTest_6144 0 16 32
  (interval_append badTest_6144 0 8 16
  badTest_6144_block_0
  badTest_6144_block_1)
  (interval_append badTest_6144 16 24 32
  badTest_6144_block_2
  badTest_6144_block_3))
  (interval_append badTest_6144 32 48 64
  (interval_append badTest_6144 32 40 48
  badTest_6144_block_4
  badTest_6144_block_5)
  (interval_append badTest_6144 48 56 64
  badTest_6144_block_6
  badTest_6144_block_7)))
  (interval_append badTest_6144 64 96 128
  (interval_append badTest_6144 64 80 96
  (interval_append badTest_6144 64 72 80
  badTest_6144_block_8
  badTest_6144_block_9)
  (interval_append badTest_6144 80 88 96
  badTest_6144_block_10
  badTest_6144_block_11))
  (interval_append badTest_6144 96 112 128
  (interval_append badTest_6144 96 104 112
  badTest_6144_block_12
  badTest_6144_block_13)
  (interval_append badTest_6144 112 120 128
  badTest_6144_block_14
  badTest_6144_block_15))))
  (interval_append badTest_6144 128 192 256
  (interval_append badTest_6144 128 160 192
  (interval_append badTest_6144 128 144 160
  (interval_append badTest_6144 128 136 144
  badTest_6144_block_16
  badTest_6144_block_17)
  (interval_append badTest_6144 144 152 160
  badTest_6144_block_18
  badTest_6144_block_19))
  (interval_append badTest_6144 160 176 192
  (interval_append badTest_6144 160 168 176
  badTest_6144_block_20
  badTest_6144_block_21)
  (interval_append badTest_6144 176 184 192
  badTest_6144_block_22
  badTest_6144_block_23)))
  (interval_append badTest_6144 192 224 256
  (interval_append badTest_6144 192 208 224
  (interval_append badTest_6144 192 200 208
  badTest_6144_block_24
  badTest_6144_block_25)
  (interval_append badTest_6144 208 216 224
  badTest_6144_block_26
  badTest_6144_block_27))
  (interval_append badTest_6144 224 240 256
  (interval_append badTest_6144 224 232 240
  badTest_6144_block_28
  badTest_6144_block_29)
  (interval_append badTest_6144 240 248 256
  badTest_6144_block_30
  badTest_6144_block_31)))))
theorem badTestInterval6144 : Interval badTest 6144 6400 := by
  intro i hlo hhi
  have h := badTest_6144_complete (i-6144) (Nat.zero_le _) (by omega)
  simpa only [badTest_6144, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad025 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_6400 (i : Nat) := badTest (i+6400)
theorem badTest_6400_block_0 : Interval badTest_6400 0 8 :=
  interval_of_check badTest_6400 0 8 (by decide +kernel)

theorem badTest_6400_block_1 : Interval badTest_6400 8 16 :=
  interval_of_check badTest_6400 8 8 (by decide +kernel)

theorem badTest_6400_block_2 : Interval badTest_6400 16 24 :=
  interval_of_check badTest_6400 16 8 (by decide +kernel)

theorem badTest_6400_block_3 : Interval badTest_6400 24 32 :=
  interval_of_check badTest_6400 24 8 (by decide +kernel)

theorem badTest_6400_block_4 : Interval badTest_6400 32 40 :=
  interval_of_check badTest_6400 32 8 (by decide +kernel)

theorem badTest_6400_block_5 : Interval badTest_6400 40 48 :=
  interval_of_check badTest_6400 40 8 (by decide +kernel)

theorem badTest_6400_block_6 : Interval badTest_6400 48 56 :=
  interval_of_check badTest_6400 48 8 (by decide +kernel)

theorem badTest_6400_block_7 : Interval badTest_6400 56 64 :=
  interval_of_check badTest_6400 56 8 (by decide +kernel)

theorem badTest_6400_block_8 : Interval badTest_6400 64 72 :=
  interval_of_check badTest_6400 64 8 (by decide +kernel)

theorem badTest_6400_block_9 : Interval badTest_6400 72 80 :=
  interval_of_check badTest_6400 72 8 (by decide +kernel)

theorem badTest_6400_block_10 : Interval badTest_6400 80 88 :=
  interval_of_check badTest_6400 80 8 (by decide +kernel)

theorem badTest_6400_block_11 : Interval badTest_6400 88 96 :=
  interval_of_check badTest_6400 88 8 (by decide +kernel)

theorem badTest_6400_block_12 : Interval badTest_6400 96 104 :=
  interval_of_check badTest_6400 96 8 (by decide +kernel)

theorem badTest_6400_block_13 : Interval badTest_6400 104 112 :=
  interval_of_check badTest_6400 104 8 (by decide +kernel)

theorem badTest_6400_block_14 : Interval badTest_6400 112 120 :=
  interval_of_check badTest_6400 112 8 (by decide +kernel)

theorem badTest_6400_block_15 : Interval badTest_6400 120 128 :=
  interval_of_check badTest_6400 120 8 (by decide +kernel)

theorem badTest_6400_block_16 : Interval badTest_6400 128 136 :=
  interval_of_check badTest_6400 128 8 (by decide +kernel)

theorem badTest_6400_block_17 : Interval badTest_6400 136 144 :=
  interval_of_check badTest_6400 136 8 (by decide +kernel)

theorem badTest_6400_block_18 : Interval badTest_6400 144 152 :=
  interval_of_check badTest_6400 144 8 (by decide +kernel)

theorem badTest_6400_block_19 : Interval badTest_6400 152 160 :=
  interval_of_check badTest_6400 152 8 (by decide +kernel)

theorem badTest_6400_block_20 : Interval badTest_6400 160 168 :=
  interval_of_check badTest_6400 160 8 (by decide +kernel)

theorem badTest_6400_block_21 : Interval badTest_6400 168 176 :=
  interval_of_check badTest_6400 168 8 (by decide +kernel)

theorem badTest_6400_block_22 : Interval badTest_6400 176 184 :=
  interval_of_check badTest_6400 176 8 (by decide +kernel)

theorem badTest_6400_block_23 : Interval badTest_6400 184 192 :=
  interval_of_check badTest_6400 184 8 (by decide +kernel)

theorem badTest_6400_block_24 : Interval badTest_6400 192 200 :=
  interval_of_check badTest_6400 192 8 (by decide +kernel)

theorem badTest_6400_block_25 : Interval badTest_6400 200 208 :=
  interval_of_check badTest_6400 200 8 (by decide +kernel)

theorem badTest_6400_block_26 : Interval badTest_6400 208 216 :=
  interval_of_check badTest_6400 208 8 (by decide +kernel)

theorem badTest_6400_block_27 : Interval badTest_6400 216 224 :=
  interval_of_check badTest_6400 216 8 (by decide +kernel)

theorem badTest_6400_block_28 : Interval badTest_6400 224 232 :=
  interval_of_check badTest_6400 224 8 (by decide +kernel)

theorem badTest_6400_block_29 : Interval badTest_6400 232 240 :=
  interval_of_check badTest_6400 232 8 (by decide +kernel)

theorem badTest_6400_block_30 : Interval badTest_6400 240 248 :=
  interval_of_check badTest_6400 240 8 (by decide +kernel)

theorem badTest_6400_block_31 : Interval badTest_6400 248 256 :=
  interval_of_check badTest_6400 248 8 (by decide +kernel)

theorem badTest_6400_complete : Interval badTest_6400 0 256 :=
  (interval_append badTest_6400 0 128 256
  (interval_append badTest_6400 0 64 128
  (interval_append badTest_6400 0 32 64
  (interval_append badTest_6400 0 16 32
  (interval_append badTest_6400 0 8 16
  badTest_6400_block_0
  badTest_6400_block_1)
  (interval_append badTest_6400 16 24 32
  badTest_6400_block_2
  badTest_6400_block_3))
  (interval_append badTest_6400 32 48 64
  (interval_append badTest_6400 32 40 48
  badTest_6400_block_4
  badTest_6400_block_5)
  (interval_append badTest_6400 48 56 64
  badTest_6400_block_6
  badTest_6400_block_7)))
  (interval_append badTest_6400 64 96 128
  (interval_append badTest_6400 64 80 96
  (interval_append badTest_6400 64 72 80
  badTest_6400_block_8
  badTest_6400_block_9)
  (interval_append badTest_6400 80 88 96
  badTest_6400_block_10
  badTest_6400_block_11))
  (interval_append badTest_6400 96 112 128
  (interval_append badTest_6400 96 104 112
  badTest_6400_block_12
  badTest_6400_block_13)
  (interval_append badTest_6400 112 120 128
  badTest_6400_block_14
  badTest_6400_block_15))))
  (interval_append badTest_6400 128 192 256
  (interval_append badTest_6400 128 160 192
  (interval_append badTest_6400 128 144 160
  (interval_append badTest_6400 128 136 144
  badTest_6400_block_16
  badTest_6400_block_17)
  (interval_append badTest_6400 144 152 160
  badTest_6400_block_18
  badTest_6400_block_19))
  (interval_append badTest_6400 160 176 192
  (interval_append badTest_6400 160 168 176
  badTest_6400_block_20
  badTest_6400_block_21)
  (interval_append badTest_6400 176 184 192
  badTest_6400_block_22
  badTest_6400_block_23)))
  (interval_append badTest_6400 192 224 256
  (interval_append badTest_6400 192 208 224
  (interval_append badTest_6400 192 200 208
  badTest_6400_block_24
  badTest_6400_block_25)
  (interval_append badTest_6400 208 216 224
  badTest_6400_block_26
  badTest_6400_block_27))
  (interval_append badTest_6400 224 240 256
  (interval_append badTest_6400 224 232 240
  badTest_6400_block_28
  badTest_6400_block_29)
  (interval_append badTest_6400 240 248 256
  badTest_6400_block_30
  badTest_6400_block_31)))))
theorem badTestInterval6400 : Interval badTest 6400 6656 := by
  intro i hlo hhi
  have h := badTest_6400_complete (i-6400) (Nat.zero_le _) (by omega)
  simpa only [badTest_6400, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad026 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_6656 (i : Nat) := badTest (i+6656)
theorem badTest_6656_block_0 : Interval badTest_6656 0 8 :=
  interval_of_check badTest_6656 0 8 (by decide +kernel)

theorem badTest_6656_block_1 : Interval badTest_6656 8 16 :=
  interval_of_check badTest_6656 8 8 (by decide +kernel)

theorem badTest_6656_block_2 : Interval badTest_6656 16 24 :=
  interval_of_check badTest_6656 16 8 (by decide +kernel)

theorem badTest_6656_block_3 : Interval badTest_6656 24 32 :=
  interval_of_check badTest_6656 24 8 (by decide +kernel)

theorem badTest_6656_block_4 : Interval badTest_6656 32 40 :=
  interval_of_check badTest_6656 32 8 (by decide +kernel)

theorem badTest_6656_block_5 : Interval badTest_6656 40 48 :=
  interval_of_check badTest_6656 40 8 (by decide +kernel)

theorem badTest_6656_block_6 : Interval badTest_6656 48 56 :=
  interval_of_check badTest_6656 48 8 (by decide +kernel)

theorem badTest_6656_block_7 : Interval badTest_6656 56 64 :=
  interval_of_check badTest_6656 56 8 (by decide +kernel)

theorem badTest_6656_block_8 : Interval badTest_6656 64 72 :=
  interval_of_check badTest_6656 64 8 (by decide +kernel)

theorem badTest_6656_block_9 : Interval badTest_6656 72 80 :=
  interval_of_check badTest_6656 72 8 (by decide +kernel)

theorem badTest_6656_block_10 : Interval badTest_6656 80 88 :=
  interval_of_check badTest_6656 80 8 (by decide +kernel)

theorem badTest_6656_block_11 : Interval badTest_6656 88 96 :=
  interval_of_check badTest_6656 88 8 (by decide +kernel)

theorem badTest_6656_block_12 : Interval badTest_6656 96 104 :=
  interval_of_check badTest_6656 96 8 (by decide +kernel)

theorem badTest_6656_block_13 : Interval badTest_6656 104 112 :=
  interval_of_check badTest_6656 104 8 (by decide +kernel)

theorem badTest_6656_block_14 : Interval badTest_6656 112 120 :=
  interval_of_check badTest_6656 112 8 (by decide +kernel)

theorem badTest_6656_block_15 : Interval badTest_6656 120 128 :=
  interval_of_check badTest_6656 120 8 (by decide +kernel)

theorem badTest_6656_block_16 : Interval badTest_6656 128 136 :=
  interval_of_check badTest_6656 128 8 (by decide +kernel)

theorem badTest_6656_block_17 : Interval badTest_6656 136 144 :=
  interval_of_check badTest_6656 136 8 (by decide +kernel)

theorem badTest_6656_block_18 : Interval badTest_6656 144 152 :=
  interval_of_check badTest_6656 144 8 (by decide +kernel)

theorem badTest_6656_block_19 : Interval badTest_6656 152 160 :=
  interval_of_check badTest_6656 152 8 (by decide +kernel)

theorem badTest_6656_block_20 : Interval badTest_6656 160 168 :=
  interval_of_check badTest_6656 160 8 (by decide +kernel)

theorem badTest_6656_block_21 : Interval badTest_6656 168 176 :=
  interval_of_check badTest_6656 168 8 (by decide +kernel)

theorem badTest_6656_block_22 : Interval badTest_6656 176 184 :=
  interval_of_check badTest_6656 176 8 (by decide +kernel)

theorem badTest_6656_block_23 : Interval badTest_6656 184 192 :=
  interval_of_check badTest_6656 184 8 (by decide +kernel)

theorem badTest_6656_block_24 : Interval badTest_6656 192 200 :=
  interval_of_check badTest_6656 192 8 (by decide +kernel)

theorem badTest_6656_block_25 : Interval badTest_6656 200 208 :=
  interval_of_check badTest_6656 200 8 (by decide +kernel)

theorem badTest_6656_block_26 : Interval badTest_6656 208 216 :=
  interval_of_check badTest_6656 208 8 (by decide +kernel)

theorem badTest_6656_block_27 : Interval badTest_6656 216 224 :=
  interval_of_check badTest_6656 216 8 (by decide +kernel)

theorem badTest_6656_block_28 : Interval badTest_6656 224 232 :=
  interval_of_check badTest_6656 224 8 (by decide +kernel)

theorem badTest_6656_block_29 : Interval badTest_6656 232 240 :=
  interval_of_check badTest_6656 232 8 (by decide +kernel)

theorem badTest_6656_block_30 : Interval badTest_6656 240 248 :=
  interval_of_check badTest_6656 240 8 (by decide +kernel)

theorem badTest_6656_block_31 : Interval badTest_6656 248 256 :=
  interval_of_check badTest_6656 248 8 (by decide +kernel)

theorem badTest_6656_complete : Interval badTest_6656 0 256 :=
  (interval_append badTest_6656 0 128 256
  (interval_append badTest_6656 0 64 128
  (interval_append badTest_6656 0 32 64
  (interval_append badTest_6656 0 16 32
  (interval_append badTest_6656 0 8 16
  badTest_6656_block_0
  badTest_6656_block_1)
  (interval_append badTest_6656 16 24 32
  badTest_6656_block_2
  badTest_6656_block_3))
  (interval_append badTest_6656 32 48 64
  (interval_append badTest_6656 32 40 48
  badTest_6656_block_4
  badTest_6656_block_5)
  (interval_append badTest_6656 48 56 64
  badTest_6656_block_6
  badTest_6656_block_7)))
  (interval_append badTest_6656 64 96 128
  (interval_append badTest_6656 64 80 96
  (interval_append badTest_6656 64 72 80
  badTest_6656_block_8
  badTest_6656_block_9)
  (interval_append badTest_6656 80 88 96
  badTest_6656_block_10
  badTest_6656_block_11))
  (interval_append badTest_6656 96 112 128
  (interval_append badTest_6656 96 104 112
  badTest_6656_block_12
  badTest_6656_block_13)
  (interval_append badTest_6656 112 120 128
  badTest_6656_block_14
  badTest_6656_block_15))))
  (interval_append badTest_6656 128 192 256
  (interval_append badTest_6656 128 160 192
  (interval_append badTest_6656 128 144 160
  (interval_append badTest_6656 128 136 144
  badTest_6656_block_16
  badTest_6656_block_17)
  (interval_append badTest_6656 144 152 160
  badTest_6656_block_18
  badTest_6656_block_19))
  (interval_append badTest_6656 160 176 192
  (interval_append badTest_6656 160 168 176
  badTest_6656_block_20
  badTest_6656_block_21)
  (interval_append badTest_6656 176 184 192
  badTest_6656_block_22
  badTest_6656_block_23)))
  (interval_append badTest_6656 192 224 256
  (interval_append badTest_6656 192 208 224
  (interval_append badTest_6656 192 200 208
  badTest_6656_block_24
  badTest_6656_block_25)
  (interval_append badTest_6656 208 216 224
  badTest_6656_block_26
  badTest_6656_block_27))
  (interval_append badTest_6656 224 240 256
  (interval_append badTest_6656 224 232 240
  badTest_6656_block_28
  badTest_6656_block_29)
  (interval_append badTest_6656 240 248 256
  badTest_6656_block_30
  badTest_6656_block_31)))))
theorem badTestInterval6656 : Interval badTest 6656 6912 := by
  intro i hlo hhi
  have h := badTest_6656_complete (i-6656) (Nat.zero_le _) (by omega)
  simpa only [badTest_6656, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad027 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_6912 (i : Nat) := badTest (i+6912)
theorem badTest_6912_block_0 : Interval badTest_6912 0 8 :=
  interval_of_check badTest_6912 0 8 (by decide +kernel)

theorem badTest_6912_block_1 : Interval badTest_6912 8 16 :=
  interval_of_check badTest_6912 8 8 (by decide +kernel)

theorem badTest_6912_block_2 : Interval badTest_6912 16 24 :=
  interval_of_check badTest_6912 16 8 (by decide +kernel)

theorem badTest_6912_block_3 : Interval badTest_6912 24 32 :=
  interval_of_check badTest_6912 24 8 (by decide +kernel)

theorem badTest_6912_block_4 : Interval badTest_6912 32 40 :=
  interval_of_check badTest_6912 32 8 (by decide +kernel)

theorem badTest_6912_block_5 : Interval badTest_6912 40 48 :=
  interval_of_check badTest_6912 40 8 (by decide +kernel)

theorem badTest_6912_block_6 : Interval badTest_6912 48 56 :=
  interval_of_check badTest_6912 48 8 (by decide +kernel)

theorem badTest_6912_block_7 : Interval badTest_6912 56 64 :=
  interval_of_check badTest_6912 56 8 (by decide +kernel)

theorem badTest_6912_block_8 : Interval badTest_6912 64 72 :=
  interval_of_check badTest_6912 64 8 (by decide +kernel)

theorem badTest_6912_block_9 : Interval badTest_6912 72 80 :=
  interval_of_check badTest_6912 72 8 (by decide +kernel)

theorem badTest_6912_block_10 : Interval badTest_6912 80 88 :=
  interval_of_check badTest_6912 80 8 (by decide +kernel)

theorem badTest_6912_block_11 : Interval badTest_6912 88 96 :=
  interval_of_check badTest_6912 88 8 (by decide +kernel)

theorem badTest_6912_block_12 : Interval badTest_6912 96 104 :=
  interval_of_check badTest_6912 96 8 (by decide +kernel)

theorem badTest_6912_block_13 : Interval badTest_6912 104 112 :=
  interval_of_check badTest_6912 104 8 (by decide +kernel)

theorem badTest_6912_block_14 : Interval badTest_6912 112 120 :=
  interval_of_check badTest_6912 112 8 (by decide +kernel)

theorem badTest_6912_block_15 : Interval badTest_6912 120 128 :=
  interval_of_check badTest_6912 120 8 (by decide +kernel)

theorem badTest_6912_block_16 : Interval badTest_6912 128 136 :=
  interval_of_check badTest_6912 128 8 (by decide +kernel)

theorem badTest_6912_block_17 : Interval badTest_6912 136 144 :=
  interval_of_check badTest_6912 136 8 (by decide +kernel)

theorem badTest_6912_block_18 : Interval badTest_6912 144 152 :=
  interval_of_check badTest_6912 144 8 (by decide +kernel)

theorem badTest_6912_block_19 : Interval badTest_6912 152 160 :=
  interval_of_check badTest_6912 152 8 (by decide +kernel)

theorem badTest_6912_block_20 : Interval badTest_6912 160 168 :=
  interval_of_check badTest_6912 160 8 (by decide +kernel)

theorem badTest_6912_block_21 : Interval badTest_6912 168 176 :=
  interval_of_check badTest_6912 168 8 (by decide +kernel)

theorem badTest_6912_block_22 : Interval badTest_6912 176 184 :=
  interval_of_check badTest_6912 176 8 (by decide +kernel)

theorem badTest_6912_block_23 : Interval badTest_6912 184 192 :=
  interval_of_check badTest_6912 184 8 (by decide +kernel)

theorem badTest_6912_block_24 : Interval badTest_6912 192 200 :=
  interval_of_check badTest_6912 192 8 (by decide +kernel)

theorem badTest_6912_block_25 : Interval badTest_6912 200 208 :=
  interval_of_check badTest_6912 200 8 (by decide +kernel)

theorem badTest_6912_block_26 : Interval badTest_6912 208 216 :=
  interval_of_check badTest_6912 208 8 (by decide +kernel)

theorem badTest_6912_block_27 : Interval badTest_6912 216 224 :=
  interval_of_check badTest_6912 216 8 (by decide +kernel)

theorem badTest_6912_block_28 : Interval badTest_6912 224 232 :=
  interval_of_check badTest_6912 224 8 (by decide +kernel)

theorem badTest_6912_block_29 : Interval badTest_6912 232 240 :=
  interval_of_check badTest_6912 232 8 (by decide +kernel)

theorem badTest_6912_block_30 : Interval badTest_6912 240 248 :=
  interval_of_check badTest_6912 240 8 (by decide +kernel)

theorem badTest_6912_block_31 : Interval badTest_6912 248 256 :=
  interval_of_check badTest_6912 248 8 (by decide +kernel)

theorem badTest_6912_complete : Interval badTest_6912 0 256 :=
  (interval_append badTest_6912 0 128 256
  (interval_append badTest_6912 0 64 128
  (interval_append badTest_6912 0 32 64
  (interval_append badTest_6912 0 16 32
  (interval_append badTest_6912 0 8 16
  badTest_6912_block_0
  badTest_6912_block_1)
  (interval_append badTest_6912 16 24 32
  badTest_6912_block_2
  badTest_6912_block_3))
  (interval_append badTest_6912 32 48 64
  (interval_append badTest_6912 32 40 48
  badTest_6912_block_4
  badTest_6912_block_5)
  (interval_append badTest_6912 48 56 64
  badTest_6912_block_6
  badTest_6912_block_7)))
  (interval_append badTest_6912 64 96 128
  (interval_append badTest_6912 64 80 96
  (interval_append badTest_6912 64 72 80
  badTest_6912_block_8
  badTest_6912_block_9)
  (interval_append badTest_6912 80 88 96
  badTest_6912_block_10
  badTest_6912_block_11))
  (interval_append badTest_6912 96 112 128
  (interval_append badTest_6912 96 104 112
  badTest_6912_block_12
  badTest_6912_block_13)
  (interval_append badTest_6912 112 120 128
  badTest_6912_block_14
  badTest_6912_block_15))))
  (interval_append badTest_6912 128 192 256
  (interval_append badTest_6912 128 160 192
  (interval_append badTest_6912 128 144 160
  (interval_append badTest_6912 128 136 144
  badTest_6912_block_16
  badTest_6912_block_17)
  (interval_append badTest_6912 144 152 160
  badTest_6912_block_18
  badTest_6912_block_19))
  (interval_append badTest_6912 160 176 192
  (interval_append badTest_6912 160 168 176
  badTest_6912_block_20
  badTest_6912_block_21)
  (interval_append badTest_6912 176 184 192
  badTest_6912_block_22
  badTest_6912_block_23)))
  (interval_append badTest_6912 192 224 256
  (interval_append badTest_6912 192 208 224
  (interval_append badTest_6912 192 200 208
  badTest_6912_block_24
  badTest_6912_block_25)
  (interval_append badTest_6912 208 216 224
  badTest_6912_block_26
  badTest_6912_block_27))
  (interval_append badTest_6912 224 240 256
  (interval_append badTest_6912 224 232 240
  badTest_6912_block_28
  badTest_6912_block_29)
  (interval_append badTest_6912 240 248 256
  badTest_6912_block_30
  badTest_6912_block_31)))))
theorem badTestInterval6912 : Interval badTest 6912 7168 := by
  intro i hlo hhi
  have h := badTest_6912_complete (i-6912) (Nat.zero_le _) (by omega)
  simpa only [badTest_6912, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad028 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_7168 (i : Nat) := badTest (i+7168)
theorem badTest_7168_block_0 : Interval badTest_7168 0 8 :=
  interval_of_check badTest_7168 0 8 (by decide +kernel)

theorem badTest_7168_block_1 : Interval badTest_7168 8 16 :=
  interval_of_check badTest_7168 8 8 (by decide +kernel)

theorem badTest_7168_block_2 : Interval badTest_7168 16 24 :=
  interval_of_check badTest_7168 16 8 (by decide +kernel)

theorem badTest_7168_block_3 : Interval badTest_7168 24 32 :=
  interval_of_check badTest_7168 24 8 (by decide +kernel)

theorem badTest_7168_block_4 : Interval badTest_7168 32 40 :=
  interval_of_check badTest_7168 32 8 (by decide +kernel)

theorem badTest_7168_block_5 : Interval badTest_7168 40 48 :=
  interval_of_check badTest_7168 40 8 (by decide +kernel)

theorem badTest_7168_block_6 : Interval badTest_7168 48 56 :=
  interval_of_check badTest_7168 48 8 (by decide +kernel)

theorem badTest_7168_block_7 : Interval badTest_7168 56 64 :=
  interval_of_check badTest_7168 56 8 (by decide +kernel)

theorem badTest_7168_block_8 : Interval badTest_7168 64 72 :=
  interval_of_check badTest_7168 64 8 (by decide +kernel)

theorem badTest_7168_block_9 : Interval badTest_7168 72 80 :=
  interval_of_check badTest_7168 72 8 (by decide +kernel)

theorem badTest_7168_block_10 : Interval badTest_7168 80 88 :=
  interval_of_check badTest_7168 80 8 (by decide +kernel)

theorem badTest_7168_block_11 : Interval badTest_7168 88 96 :=
  interval_of_check badTest_7168 88 8 (by decide +kernel)

theorem badTest_7168_block_12 : Interval badTest_7168 96 104 :=
  interval_of_check badTest_7168 96 8 (by decide +kernel)

theorem badTest_7168_block_13 : Interval badTest_7168 104 112 :=
  interval_of_check badTest_7168 104 8 (by decide +kernel)

theorem badTest_7168_block_14 : Interval badTest_7168 112 120 :=
  interval_of_check badTest_7168 112 8 (by decide +kernel)

theorem badTest_7168_block_15 : Interval badTest_7168 120 128 :=
  interval_of_check badTest_7168 120 8 (by decide +kernel)

theorem badTest_7168_block_16 : Interval badTest_7168 128 136 :=
  interval_of_check badTest_7168 128 8 (by decide +kernel)

theorem badTest_7168_block_17 : Interval badTest_7168 136 144 :=
  interval_of_check badTest_7168 136 8 (by decide +kernel)

theorem badTest_7168_block_18 : Interval badTest_7168 144 152 :=
  interval_of_check badTest_7168 144 8 (by decide +kernel)

theorem badTest_7168_block_19 : Interval badTest_7168 152 160 :=
  interval_of_check badTest_7168 152 8 (by decide +kernel)

theorem badTest_7168_block_20 : Interval badTest_7168 160 168 :=
  interval_of_check badTest_7168 160 8 (by decide +kernel)

theorem badTest_7168_block_21 : Interval badTest_7168 168 176 :=
  interval_of_check badTest_7168 168 8 (by decide +kernel)

theorem badTest_7168_block_22 : Interval badTest_7168 176 184 :=
  interval_of_check badTest_7168 176 8 (by decide +kernel)

theorem badTest_7168_block_23 : Interval badTest_7168 184 192 :=
  interval_of_check badTest_7168 184 8 (by decide +kernel)

theorem badTest_7168_block_24 : Interval badTest_7168 192 200 :=
  interval_of_check badTest_7168 192 8 (by decide +kernel)

theorem badTest_7168_block_25 : Interval badTest_7168 200 208 :=
  interval_of_check badTest_7168 200 8 (by decide +kernel)

theorem badTest_7168_block_26 : Interval badTest_7168 208 216 :=
  interval_of_check badTest_7168 208 8 (by decide +kernel)

theorem badTest_7168_block_27 : Interval badTest_7168 216 224 :=
  interval_of_check badTest_7168 216 8 (by decide +kernel)

theorem badTest_7168_block_28 : Interval badTest_7168 224 232 :=
  interval_of_check badTest_7168 224 8 (by decide +kernel)

theorem badTest_7168_block_29 : Interval badTest_7168 232 240 :=
  interval_of_check badTest_7168 232 8 (by decide +kernel)

theorem badTest_7168_block_30 : Interval badTest_7168 240 248 :=
  interval_of_check badTest_7168 240 8 (by decide +kernel)

theorem badTest_7168_block_31 : Interval badTest_7168 248 256 :=
  interval_of_check badTest_7168 248 8 (by decide +kernel)

theorem badTest_7168_complete : Interval badTest_7168 0 256 :=
  (interval_append badTest_7168 0 128 256
  (interval_append badTest_7168 0 64 128
  (interval_append badTest_7168 0 32 64
  (interval_append badTest_7168 0 16 32
  (interval_append badTest_7168 0 8 16
  badTest_7168_block_0
  badTest_7168_block_1)
  (interval_append badTest_7168 16 24 32
  badTest_7168_block_2
  badTest_7168_block_3))
  (interval_append badTest_7168 32 48 64
  (interval_append badTest_7168 32 40 48
  badTest_7168_block_4
  badTest_7168_block_5)
  (interval_append badTest_7168 48 56 64
  badTest_7168_block_6
  badTest_7168_block_7)))
  (interval_append badTest_7168 64 96 128
  (interval_append badTest_7168 64 80 96
  (interval_append badTest_7168 64 72 80
  badTest_7168_block_8
  badTest_7168_block_9)
  (interval_append badTest_7168 80 88 96
  badTest_7168_block_10
  badTest_7168_block_11))
  (interval_append badTest_7168 96 112 128
  (interval_append badTest_7168 96 104 112
  badTest_7168_block_12
  badTest_7168_block_13)
  (interval_append badTest_7168 112 120 128
  badTest_7168_block_14
  badTest_7168_block_15))))
  (interval_append badTest_7168 128 192 256
  (interval_append badTest_7168 128 160 192
  (interval_append badTest_7168 128 144 160
  (interval_append badTest_7168 128 136 144
  badTest_7168_block_16
  badTest_7168_block_17)
  (interval_append badTest_7168 144 152 160
  badTest_7168_block_18
  badTest_7168_block_19))
  (interval_append badTest_7168 160 176 192
  (interval_append badTest_7168 160 168 176
  badTest_7168_block_20
  badTest_7168_block_21)
  (interval_append badTest_7168 176 184 192
  badTest_7168_block_22
  badTest_7168_block_23)))
  (interval_append badTest_7168 192 224 256
  (interval_append badTest_7168 192 208 224
  (interval_append badTest_7168 192 200 208
  badTest_7168_block_24
  badTest_7168_block_25)
  (interval_append badTest_7168 208 216 224
  badTest_7168_block_26
  badTest_7168_block_27))
  (interval_append badTest_7168 224 240 256
  (interval_append badTest_7168 224 232 240
  badTest_7168_block_28
  badTest_7168_block_29)
  (interval_append badTest_7168 240 248 256
  badTest_7168_block_30
  badTest_7168_block_31)))))
theorem badTestInterval7168 : Interval badTest 7168 7424 := by
  intro i hlo hhi
  have h := badTest_7168_complete (i-7168) (Nat.zero_le _) (by omega)
  simpa only [badTest_7168, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad029 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_7424 (i : Nat) := badTest (i+7424)
theorem badTest_7424_block_0 : Interval badTest_7424 0 8 :=
  interval_of_check badTest_7424 0 8 (by decide +kernel)

theorem badTest_7424_block_1 : Interval badTest_7424 8 16 :=
  interval_of_check badTest_7424 8 8 (by decide +kernel)

theorem badTest_7424_block_2 : Interval badTest_7424 16 24 :=
  interval_of_check badTest_7424 16 8 (by decide +kernel)

theorem badTest_7424_block_3 : Interval badTest_7424 24 32 :=
  interval_of_check badTest_7424 24 8 (by decide +kernel)

theorem badTest_7424_block_4 : Interval badTest_7424 32 40 :=
  interval_of_check badTest_7424 32 8 (by decide +kernel)

theorem badTest_7424_block_5 : Interval badTest_7424 40 48 :=
  interval_of_check badTest_7424 40 8 (by decide +kernel)

theorem badTest_7424_block_6 : Interval badTest_7424 48 56 :=
  interval_of_check badTest_7424 48 8 (by decide +kernel)

theorem badTest_7424_block_7 : Interval badTest_7424 56 64 :=
  interval_of_check badTest_7424 56 8 (by decide +kernel)

theorem badTest_7424_block_8 : Interval badTest_7424 64 72 :=
  interval_of_check badTest_7424 64 8 (by decide +kernel)

theorem badTest_7424_block_9 : Interval badTest_7424 72 80 :=
  interval_of_check badTest_7424 72 8 (by decide +kernel)

theorem badTest_7424_block_10 : Interval badTest_7424 80 88 :=
  interval_of_check badTest_7424 80 8 (by decide +kernel)

theorem badTest_7424_block_11 : Interval badTest_7424 88 96 :=
  interval_of_check badTest_7424 88 8 (by decide +kernel)

theorem badTest_7424_block_12 : Interval badTest_7424 96 104 :=
  interval_of_check badTest_7424 96 8 (by decide +kernel)

theorem badTest_7424_block_13 : Interval badTest_7424 104 112 :=
  interval_of_check badTest_7424 104 8 (by decide +kernel)

theorem badTest_7424_block_14 : Interval badTest_7424 112 120 :=
  interval_of_check badTest_7424 112 8 (by decide +kernel)

theorem badTest_7424_block_15 : Interval badTest_7424 120 128 :=
  interval_of_check badTest_7424 120 8 (by decide +kernel)

theorem badTest_7424_block_16 : Interval badTest_7424 128 136 :=
  interval_of_check badTest_7424 128 8 (by decide +kernel)

theorem badTest_7424_block_17 : Interval badTest_7424 136 144 :=
  interval_of_check badTest_7424 136 8 (by decide +kernel)

theorem badTest_7424_block_18 : Interval badTest_7424 144 152 :=
  interval_of_check badTest_7424 144 8 (by decide +kernel)

theorem badTest_7424_block_19 : Interval badTest_7424 152 160 :=
  interval_of_check badTest_7424 152 8 (by decide +kernel)

theorem badTest_7424_block_20 : Interval badTest_7424 160 168 :=
  interval_of_check badTest_7424 160 8 (by decide +kernel)

theorem badTest_7424_block_21 : Interval badTest_7424 168 176 :=
  interval_of_check badTest_7424 168 8 (by decide +kernel)

theorem badTest_7424_block_22 : Interval badTest_7424 176 184 :=
  interval_of_check badTest_7424 176 8 (by decide +kernel)

theorem badTest_7424_block_23 : Interval badTest_7424 184 192 :=
  interval_of_check badTest_7424 184 8 (by decide +kernel)

theorem badTest_7424_block_24 : Interval badTest_7424 192 200 :=
  interval_of_check badTest_7424 192 8 (by decide +kernel)

theorem badTest_7424_block_25 : Interval badTest_7424 200 208 :=
  interval_of_check badTest_7424 200 8 (by decide +kernel)

theorem badTest_7424_block_26 : Interval badTest_7424 208 216 :=
  interval_of_check badTest_7424 208 8 (by decide +kernel)

theorem badTest_7424_block_27 : Interval badTest_7424 216 224 :=
  interval_of_check badTest_7424 216 8 (by decide +kernel)

theorem badTest_7424_block_28 : Interval badTest_7424 224 232 :=
  interval_of_check badTest_7424 224 8 (by decide +kernel)

theorem badTest_7424_block_29 : Interval badTest_7424 232 240 :=
  interval_of_check badTest_7424 232 8 (by decide +kernel)

theorem badTest_7424_block_30 : Interval badTest_7424 240 248 :=
  interval_of_check badTest_7424 240 8 (by decide +kernel)

theorem badTest_7424_block_31 : Interval badTest_7424 248 256 :=
  interval_of_check badTest_7424 248 8 (by decide +kernel)

theorem badTest_7424_complete : Interval badTest_7424 0 256 :=
  (interval_append badTest_7424 0 128 256
  (interval_append badTest_7424 0 64 128
  (interval_append badTest_7424 0 32 64
  (interval_append badTest_7424 0 16 32
  (interval_append badTest_7424 0 8 16
  badTest_7424_block_0
  badTest_7424_block_1)
  (interval_append badTest_7424 16 24 32
  badTest_7424_block_2
  badTest_7424_block_3))
  (interval_append badTest_7424 32 48 64
  (interval_append badTest_7424 32 40 48
  badTest_7424_block_4
  badTest_7424_block_5)
  (interval_append badTest_7424 48 56 64
  badTest_7424_block_6
  badTest_7424_block_7)))
  (interval_append badTest_7424 64 96 128
  (interval_append badTest_7424 64 80 96
  (interval_append badTest_7424 64 72 80
  badTest_7424_block_8
  badTest_7424_block_9)
  (interval_append badTest_7424 80 88 96
  badTest_7424_block_10
  badTest_7424_block_11))
  (interval_append badTest_7424 96 112 128
  (interval_append badTest_7424 96 104 112
  badTest_7424_block_12
  badTest_7424_block_13)
  (interval_append badTest_7424 112 120 128
  badTest_7424_block_14
  badTest_7424_block_15))))
  (interval_append badTest_7424 128 192 256
  (interval_append badTest_7424 128 160 192
  (interval_append badTest_7424 128 144 160
  (interval_append badTest_7424 128 136 144
  badTest_7424_block_16
  badTest_7424_block_17)
  (interval_append badTest_7424 144 152 160
  badTest_7424_block_18
  badTest_7424_block_19))
  (interval_append badTest_7424 160 176 192
  (interval_append badTest_7424 160 168 176
  badTest_7424_block_20
  badTest_7424_block_21)
  (interval_append badTest_7424 176 184 192
  badTest_7424_block_22
  badTest_7424_block_23)))
  (interval_append badTest_7424 192 224 256
  (interval_append badTest_7424 192 208 224
  (interval_append badTest_7424 192 200 208
  badTest_7424_block_24
  badTest_7424_block_25)
  (interval_append badTest_7424 208 216 224
  badTest_7424_block_26
  badTest_7424_block_27))
  (interval_append badTest_7424 224 240 256
  (interval_append badTest_7424 224 232 240
  badTest_7424_block_28
  badTest_7424_block_29)
  (interval_append badTest_7424 240 248 256
  badTest_7424_block_30
  badTest_7424_block_31)))))
theorem badTestInterval7424 : Interval badTest 7424 7680 := by
  intro i hlo hhi
  have h := badTest_7424_complete (i-7424) (Nat.zero_le _) (by omega)
  simpa only [badTest_7424, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad030 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_7680 (i : Nat) := badTest (i+7680)
theorem badTest_7680_block_0 : Interval badTest_7680 0 8 :=
  interval_of_check badTest_7680 0 8 (by decide +kernel)

theorem badTest_7680_block_1 : Interval badTest_7680 8 16 :=
  interval_of_check badTest_7680 8 8 (by decide +kernel)

theorem badTest_7680_block_2 : Interval badTest_7680 16 24 :=
  interval_of_check badTest_7680 16 8 (by decide +kernel)

theorem badTest_7680_block_3 : Interval badTest_7680 24 32 :=
  interval_of_check badTest_7680 24 8 (by decide +kernel)

theorem badTest_7680_block_4 : Interval badTest_7680 32 40 :=
  interval_of_check badTest_7680 32 8 (by decide +kernel)

theorem badTest_7680_block_5 : Interval badTest_7680 40 48 :=
  interval_of_check badTest_7680 40 8 (by decide +kernel)

theorem badTest_7680_block_6 : Interval badTest_7680 48 56 :=
  interval_of_check badTest_7680 48 8 (by decide +kernel)

theorem badTest_7680_block_7 : Interval badTest_7680 56 64 :=
  interval_of_check badTest_7680 56 8 (by decide +kernel)

theorem badTest_7680_block_8 : Interval badTest_7680 64 72 :=
  interval_of_check badTest_7680 64 8 (by decide +kernel)

theorem badTest_7680_block_9 : Interval badTest_7680 72 80 :=
  interval_of_check badTest_7680 72 8 (by decide +kernel)

theorem badTest_7680_block_10 : Interval badTest_7680 80 88 :=
  interval_of_check badTest_7680 80 8 (by decide +kernel)

theorem badTest_7680_block_11 : Interval badTest_7680 88 96 :=
  interval_of_check badTest_7680 88 8 (by decide +kernel)

theorem badTest_7680_block_12 : Interval badTest_7680 96 104 :=
  interval_of_check badTest_7680 96 8 (by decide +kernel)

theorem badTest_7680_block_13 : Interval badTest_7680 104 112 :=
  interval_of_check badTest_7680 104 8 (by decide +kernel)

theorem badTest_7680_block_14 : Interval badTest_7680 112 120 :=
  interval_of_check badTest_7680 112 8 (by decide +kernel)

theorem badTest_7680_block_15 : Interval badTest_7680 120 128 :=
  interval_of_check badTest_7680 120 8 (by decide +kernel)

theorem badTest_7680_block_16 : Interval badTest_7680 128 136 :=
  interval_of_check badTest_7680 128 8 (by decide +kernel)

theorem badTest_7680_block_17 : Interval badTest_7680 136 144 :=
  interval_of_check badTest_7680 136 8 (by decide +kernel)

theorem badTest_7680_block_18 : Interval badTest_7680 144 152 :=
  interval_of_check badTest_7680 144 8 (by decide +kernel)

theorem badTest_7680_block_19 : Interval badTest_7680 152 160 :=
  interval_of_check badTest_7680 152 8 (by decide +kernel)

theorem badTest_7680_block_20 : Interval badTest_7680 160 168 :=
  interval_of_check badTest_7680 160 8 (by decide +kernel)

theorem badTest_7680_block_21 : Interval badTest_7680 168 176 :=
  interval_of_check badTest_7680 168 8 (by decide +kernel)

theorem badTest_7680_block_22 : Interval badTest_7680 176 184 :=
  interval_of_check badTest_7680 176 8 (by decide +kernel)

theorem badTest_7680_block_23 : Interval badTest_7680 184 192 :=
  interval_of_check badTest_7680 184 8 (by decide +kernel)

theorem badTest_7680_block_24 : Interval badTest_7680 192 200 :=
  interval_of_check badTest_7680 192 8 (by decide +kernel)

theorem badTest_7680_block_25 : Interval badTest_7680 200 208 :=
  interval_of_check badTest_7680 200 8 (by decide +kernel)

theorem badTest_7680_block_26 : Interval badTest_7680 208 216 :=
  interval_of_check badTest_7680 208 8 (by decide +kernel)

theorem badTest_7680_block_27 : Interval badTest_7680 216 224 :=
  interval_of_check badTest_7680 216 8 (by decide +kernel)

theorem badTest_7680_block_28 : Interval badTest_7680 224 232 :=
  interval_of_check badTest_7680 224 8 (by decide +kernel)

theorem badTest_7680_block_29 : Interval badTest_7680 232 240 :=
  interval_of_check badTest_7680 232 8 (by decide +kernel)

theorem badTest_7680_block_30 : Interval badTest_7680 240 248 :=
  interval_of_check badTest_7680 240 8 (by decide +kernel)

theorem badTest_7680_block_31 : Interval badTest_7680 248 256 :=
  interval_of_check badTest_7680 248 8 (by decide +kernel)

theorem badTest_7680_complete : Interval badTest_7680 0 256 :=
  (interval_append badTest_7680 0 128 256
  (interval_append badTest_7680 0 64 128
  (interval_append badTest_7680 0 32 64
  (interval_append badTest_7680 0 16 32
  (interval_append badTest_7680 0 8 16
  badTest_7680_block_0
  badTest_7680_block_1)
  (interval_append badTest_7680 16 24 32
  badTest_7680_block_2
  badTest_7680_block_3))
  (interval_append badTest_7680 32 48 64
  (interval_append badTest_7680 32 40 48
  badTest_7680_block_4
  badTest_7680_block_5)
  (interval_append badTest_7680 48 56 64
  badTest_7680_block_6
  badTest_7680_block_7)))
  (interval_append badTest_7680 64 96 128
  (interval_append badTest_7680 64 80 96
  (interval_append badTest_7680 64 72 80
  badTest_7680_block_8
  badTest_7680_block_9)
  (interval_append badTest_7680 80 88 96
  badTest_7680_block_10
  badTest_7680_block_11))
  (interval_append badTest_7680 96 112 128
  (interval_append badTest_7680 96 104 112
  badTest_7680_block_12
  badTest_7680_block_13)
  (interval_append badTest_7680 112 120 128
  badTest_7680_block_14
  badTest_7680_block_15))))
  (interval_append badTest_7680 128 192 256
  (interval_append badTest_7680 128 160 192
  (interval_append badTest_7680 128 144 160
  (interval_append badTest_7680 128 136 144
  badTest_7680_block_16
  badTest_7680_block_17)
  (interval_append badTest_7680 144 152 160
  badTest_7680_block_18
  badTest_7680_block_19))
  (interval_append badTest_7680 160 176 192
  (interval_append badTest_7680 160 168 176
  badTest_7680_block_20
  badTest_7680_block_21)
  (interval_append badTest_7680 176 184 192
  badTest_7680_block_22
  badTest_7680_block_23)))
  (interval_append badTest_7680 192 224 256
  (interval_append badTest_7680 192 208 224
  (interval_append badTest_7680 192 200 208
  badTest_7680_block_24
  badTest_7680_block_25)
  (interval_append badTest_7680 208 216 224
  badTest_7680_block_26
  badTest_7680_block_27))
  (interval_append badTest_7680 224 240 256
  (interval_append badTest_7680 224 232 240
  badTest_7680_block_28
  badTest_7680_block_29)
  (interval_append badTest_7680 240 248 256
  badTest_7680_block_30
  badTest_7680_block_31)))))
theorem badTestInterval7680 : Interval badTest 7680 7936 := by
  intro i hlo hhi
  have h := badTest_7680_complete (i-7680) (Nat.zero_le _) (by omega)
  simpa only [badTest_7680, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad031 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_7936 (i : Nat) := badTest (i+7936)
theorem badTest_7936_block_0 : Interval badTest_7936 0 8 :=
  interval_of_check badTest_7936 0 8 (by decide +kernel)

theorem badTest_7936_block_1 : Interval badTest_7936 8 16 :=
  interval_of_check badTest_7936 8 8 (by decide +kernel)

theorem badTest_7936_block_2 : Interval badTest_7936 16 24 :=
  interval_of_check badTest_7936 16 8 (by decide +kernel)

theorem badTest_7936_block_3 : Interval badTest_7936 24 32 :=
  interval_of_check badTest_7936 24 8 (by decide +kernel)

theorem badTest_7936_block_4 : Interval badTest_7936 32 40 :=
  interval_of_check badTest_7936 32 8 (by decide +kernel)

theorem badTest_7936_block_5 : Interval badTest_7936 40 48 :=
  interval_of_check badTest_7936 40 8 (by decide +kernel)

theorem badTest_7936_block_6 : Interval badTest_7936 48 56 :=
  interval_of_check badTest_7936 48 8 (by decide +kernel)

theorem badTest_7936_block_7 : Interval badTest_7936 56 64 :=
  interval_of_check badTest_7936 56 8 (by decide +kernel)

theorem badTest_7936_block_8 : Interval badTest_7936 64 72 :=
  interval_of_check badTest_7936 64 8 (by decide +kernel)

theorem badTest_7936_block_9 : Interval badTest_7936 72 80 :=
  interval_of_check badTest_7936 72 8 (by decide +kernel)

theorem badTest_7936_block_10 : Interval badTest_7936 80 88 :=
  interval_of_check badTest_7936 80 8 (by decide +kernel)

theorem badTest_7936_block_11 : Interval badTest_7936 88 96 :=
  interval_of_check badTest_7936 88 8 (by decide +kernel)

theorem badTest_7936_block_12 : Interval badTest_7936 96 104 :=
  interval_of_check badTest_7936 96 8 (by decide +kernel)

theorem badTest_7936_block_13 : Interval badTest_7936 104 112 :=
  interval_of_check badTest_7936 104 8 (by decide +kernel)

theorem badTest_7936_block_14 : Interval badTest_7936 112 120 :=
  interval_of_check badTest_7936 112 8 (by decide +kernel)

theorem badTest_7936_block_15 : Interval badTest_7936 120 128 :=
  interval_of_check badTest_7936 120 8 (by decide +kernel)

theorem badTest_7936_block_16 : Interval badTest_7936 128 136 :=
  interval_of_check badTest_7936 128 8 (by decide +kernel)

theorem badTest_7936_block_17 : Interval badTest_7936 136 144 :=
  interval_of_check badTest_7936 136 8 (by decide +kernel)

theorem badTest_7936_block_18 : Interval badTest_7936 144 152 :=
  interval_of_check badTest_7936 144 8 (by decide +kernel)

theorem badTest_7936_block_19 : Interval badTest_7936 152 160 :=
  interval_of_check badTest_7936 152 8 (by decide +kernel)

theorem badTest_7936_block_20 : Interval badTest_7936 160 168 :=
  interval_of_check badTest_7936 160 8 (by decide +kernel)

theorem badTest_7936_block_21 : Interval badTest_7936 168 176 :=
  interval_of_check badTest_7936 168 8 (by decide +kernel)

theorem badTest_7936_block_22 : Interval badTest_7936 176 184 :=
  interval_of_check badTest_7936 176 8 (by decide +kernel)

theorem badTest_7936_block_23 : Interval badTest_7936 184 192 :=
  interval_of_check badTest_7936 184 8 (by decide +kernel)

theorem badTest_7936_block_24 : Interval badTest_7936 192 200 :=
  interval_of_check badTest_7936 192 8 (by decide +kernel)

theorem badTest_7936_block_25 : Interval badTest_7936 200 208 :=
  interval_of_check badTest_7936 200 8 (by decide +kernel)

theorem badTest_7936_block_26 : Interval badTest_7936 208 216 :=
  interval_of_check badTest_7936 208 8 (by decide +kernel)

theorem badTest_7936_block_27 : Interval badTest_7936 216 224 :=
  interval_of_check badTest_7936 216 8 (by decide +kernel)

theorem badTest_7936_block_28 : Interval badTest_7936 224 232 :=
  interval_of_check badTest_7936 224 8 (by decide +kernel)

theorem badTest_7936_block_29 : Interval badTest_7936 232 240 :=
  interval_of_check badTest_7936 232 8 (by decide +kernel)

theorem badTest_7936_block_30 : Interval badTest_7936 240 248 :=
  interval_of_check badTest_7936 240 8 (by decide +kernel)

theorem badTest_7936_block_31 : Interval badTest_7936 248 256 :=
  interval_of_check badTest_7936 248 8 (by decide +kernel)

theorem badTest_7936_complete : Interval badTest_7936 0 256 :=
  (interval_append badTest_7936 0 128 256
  (interval_append badTest_7936 0 64 128
  (interval_append badTest_7936 0 32 64
  (interval_append badTest_7936 0 16 32
  (interval_append badTest_7936 0 8 16
  badTest_7936_block_0
  badTest_7936_block_1)
  (interval_append badTest_7936 16 24 32
  badTest_7936_block_2
  badTest_7936_block_3))
  (interval_append badTest_7936 32 48 64
  (interval_append badTest_7936 32 40 48
  badTest_7936_block_4
  badTest_7936_block_5)
  (interval_append badTest_7936 48 56 64
  badTest_7936_block_6
  badTest_7936_block_7)))
  (interval_append badTest_7936 64 96 128
  (interval_append badTest_7936 64 80 96
  (interval_append badTest_7936 64 72 80
  badTest_7936_block_8
  badTest_7936_block_9)
  (interval_append badTest_7936 80 88 96
  badTest_7936_block_10
  badTest_7936_block_11))
  (interval_append badTest_7936 96 112 128
  (interval_append badTest_7936 96 104 112
  badTest_7936_block_12
  badTest_7936_block_13)
  (interval_append badTest_7936 112 120 128
  badTest_7936_block_14
  badTest_7936_block_15))))
  (interval_append badTest_7936 128 192 256
  (interval_append badTest_7936 128 160 192
  (interval_append badTest_7936 128 144 160
  (interval_append badTest_7936 128 136 144
  badTest_7936_block_16
  badTest_7936_block_17)
  (interval_append badTest_7936 144 152 160
  badTest_7936_block_18
  badTest_7936_block_19))
  (interval_append badTest_7936 160 176 192
  (interval_append badTest_7936 160 168 176
  badTest_7936_block_20
  badTest_7936_block_21)
  (interval_append badTest_7936 176 184 192
  badTest_7936_block_22
  badTest_7936_block_23)))
  (interval_append badTest_7936 192 224 256
  (interval_append badTest_7936 192 208 224
  (interval_append badTest_7936 192 200 208
  badTest_7936_block_24
  badTest_7936_block_25)
  (interval_append badTest_7936 208 216 224
  badTest_7936_block_26
  badTest_7936_block_27))
  (interval_append badTest_7936 224 240 256
  (interval_append badTest_7936 224 232 240
  badTest_7936_block_28
  badTest_7936_block_29)
  (interval_append badTest_7936 240 248 256
  badTest_7936_block_30
  badTest_7936_block_31)))))
theorem badTestInterval7936 : Interval badTest 7936 8192 := by
  intro i hlo hhi
  have h := badTest_7936_complete (i-7936) (Nat.zero_le _) (by omega)
  simpa only [badTest_7936, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad032 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_8192 (i : Nat) := badTest (i+8192)
theorem badTest_8192_block_0 : Interval badTest_8192 0 8 :=
  interval_of_check badTest_8192 0 8 (by decide +kernel)

theorem badTest_8192_block_1 : Interval badTest_8192 8 16 :=
  interval_of_check badTest_8192 8 8 (by decide +kernel)

theorem badTest_8192_block_2 : Interval badTest_8192 16 24 :=
  interval_of_check badTest_8192 16 8 (by decide +kernel)

theorem badTest_8192_block_3 : Interval badTest_8192 24 32 :=
  interval_of_check badTest_8192 24 8 (by decide +kernel)

theorem badTest_8192_block_4 : Interval badTest_8192 32 40 :=
  interval_of_check badTest_8192 32 8 (by decide +kernel)

theorem badTest_8192_block_5 : Interval badTest_8192 40 48 :=
  interval_of_check badTest_8192 40 8 (by decide +kernel)

theorem badTest_8192_block_6 : Interval badTest_8192 48 56 :=
  interval_of_check badTest_8192 48 8 (by decide +kernel)

theorem badTest_8192_block_7 : Interval badTest_8192 56 64 :=
  interval_of_check badTest_8192 56 8 (by decide +kernel)

theorem badTest_8192_block_8 : Interval badTest_8192 64 72 :=
  interval_of_check badTest_8192 64 8 (by decide +kernel)

theorem badTest_8192_block_9 : Interval badTest_8192 72 80 :=
  interval_of_check badTest_8192 72 8 (by decide +kernel)

theorem badTest_8192_block_10 : Interval badTest_8192 80 88 :=
  interval_of_check badTest_8192 80 8 (by decide +kernel)

theorem badTest_8192_block_11 : Interval badTest_8192 88 96 :=
  interval_of_check badTest_8192 88 8 (by decide +kernel)

theorem badTest_8192_block_12 : Interval badTest_8192 96 104 :=
  interval_of_check badTest_8192 96 8 (by decide +kernel)

theorem badTest_8192_block_13 : Interval badTest_8192 104 112 :=
  interval_of_check badTest_8192 104 8 (by decide +kernel)

theorem badTest_8192_block_14 : Interval badTest_8192 112 120 :=
  interval_of_check badTest_8192 112 8 (by decide +kernel)

theorem badTest_8192_block_15 : Interval badTest_8192 120 128 :=
  interval_of_check badTest_8192 120 8 (by decide +kernel)

theorem badTest_8192_block_16 : Interval badTest_8192 128 136 :=
  interval_of_check badTest_8192 128 8 (by decide +kernel)

theorem badTest_8192_block_17 : Interval badTest_8192 136 144 :=
  interval_of_check badTest_8192 136 8 (by decide +kernel)

theorem badTest_8192_block_18 : Interval badTest_8192 144 152 :=
  interval_of_check badTest_8192 144 8 (by decide +kernel)

theorem badTest_8192_block_19 : Interval badTest_8192 152 160 :=
  interval_of_check badTest_8192 152 8 (by decide +kernel)

theorem badTest_8192_block_20 : Interval badTest_8192 160 168 :=
  interval_of_check badTest_8192 160 8 (by decide +kernel)

theorem badTest_8192_block_21 : Interval badTest_8192 168 176 :=
  interval_of_check badTest_8192 168 8 (by decide +kernel)

theorem badTest_8192_block_22 : Interval badTest_8192 176 184 :=
  interval_of_check badTest_8192 176 8 (by decide +kernel)

theorem badTest_8192_block_23 : Interval badTest_8192 184 192 :=
  interval_of_check badTest_8192 184 8 (by decide +kernel)

theorem badTest_8192_block_24 : Interval badTest_8192 192 200 :=
  interval_of_check badTest_8192 192 8 (by decide +kernel)

theorem badTest_8192_block_25 : Interval badTest_8192 200 208 :=
  interval_of_check badTest_8192 200 8 (by decide +kernel)

theorem badTest_8192_block_26 : Interval badTest_8192 208 216 :=
  interval_of_check badTest_8192 208 8 (by decide +kernel)

theorem badTest_8192_block_27 : Interval badTest_8192 216 224 :=
  interval_of_check badTest_8192 216 8 (by decide +kernel)

theorem badTest_8192_block_28 : Interval badTest_8192 224 232 :=
  interval_of_check badTest_8192 224 8 (by decide +kernel)

theorem badTest_8192_block_29 : Interval badTest_8192 232 240 :=
  interval_of_check badTest_8192 232 8 (by decide +kernel)

theorem badTest_8192_block_30 : Interval badTest_8192 240 248 :=
  interval_of_check badTest_8192 240 8 (by decide +kernel)

theorem badTest_8192_block_31 : Interval badTest_8192 248 256 :=
  interval_of_check badTest_8192 248 8 (by decide +kernel)

theorem badTest_8192_complete : Interval badTest_8192 0 256 :=
  (interval_append badTest_8192 0 128 256
  (interval_append badTest_8192 0 64 128
  (interval_append badTest_8192 0 32 64
  (interval_append badTest_8192 0 16 32
  (interval_append badTest_8192 0 8 16
  badTest_8192_block_0
  badTest_8192_block_1)
  (interval_append badTest_8192 16 24 32
  badTest_8192_block_2
  badTest_8192_block_3))
  (interval_append badTest_8192 32 48 64
  (interval_append badTest_8192 32 40 48
  badTest_8192_block_4
  badTest_8192_block_5)
  (interval_append badTest_8192 48 56 64
  badTest_8192_block_6
  badTest_8192_block_7)))
  (interval_append badTest_8192 64 96 128
  (interval_append badTest_8192 64 80 96
  (interval_append badTest_8192 64 72 80
  badTest_8192_block_8
  badTest_8192_block_9)
  (interval_append badTest_8192 80 88 96
  badTest_8192_block_10
  badTest_8192_block_11))
  (interval_append badTest_8192 96 112 128
  (interval_append badTest_8192 96 104 112
  badTest_8192_block_12
  badTest_8192_block_13)
  (interval_append badTest_8192 112 120 128
  badTest_8192_block_14
  badTest_8192_block_15))))
  (interval_append badTest_8192 128 192 256
  (interval_append badTest_8192 128 160 192
  (interval_append badTest_8192 128 144 160
  (interval_append badTest_8192 128 136 144
  badTest_8192_block_16
  badTest_8192_block_17)
  (interval_append badTest_8192 144 152 160
  badTest_8192_block_18
  badTest_8192_block_19))
  (interval_append badTest_8192 160 176 192
  (interval_append badTest_8192 160 168 176
  badTest_8192_block_20
  badTest_8192_block_21)
  (interval_append badTest_8192 176 184 192
  badTest_8192_block_22
  badTest_8192_block_23)))
  (interval_append badTest_8192 192 224 256
  (interval_append badTest_8192 192 208 224
  (interval_append badTest_8192 192 200 208
  badTest_8192_block_24
  badTest_8192_block_25)
  (interval_append badTest_8192 208 216 224
  badTest_8192_block_26
  badTest_8192_block_27))
  (interval_append badTest_8192 224 240 256
  (interval_append badTest_8192 224 232 240
  badTest_8192_block_28
  badTest_8192_block_29)
  (interval_append badTest_8192 240 248 256
  badTest_8192_block_30
  badTest_8192_block_31)))))
theorem badTestInterval8192 : Interval badTest 8192 8448 := by
  intro i hlo hhi
  have h := badTest_8192_complete (i-8192) (Nat.zero_le _) (by omega)
  simpa only [badTest_8192, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad033 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_8448 (i : Nat) := badTest (i+8448)
theorem badTest_8448_block_0 : Interval badTest_8448 0 8 :=
  interval_of_check badTest_8448 0 8 (by decide +kernel)

theorem badTest_8448_block_1 : Interval badTest_8448 8 16 :=
  interval_of_check badTest_8448 8 8 (by decide +kernel)

theorem badTest_8448_block_2 : Interval badTest_8448 16 24 :=
  interval_of_check badTest_8448 16 8 (by decide +kernel)

theorem badTest_8448_block_3 : Interval badTest_8448 24 32 :=
  interval_of_check badTest_8448 24 8 (by decide +kernel)

theorem badTest_8448_block_4 : Interval badTest_8448 32 40 :=
  interval_of_check badTest_8448 32 8 (by decide +kernel)

theorem badTest_8448_block_5 : Interval badTest_8448 40 48 :=
  interval_of_check badTest_8448 40 8 (by decide +kernel)

theorem badTest_8448_block_6 : Interval badTest_8448 48 56 :=
  interval_of_check badTest_8448 48 8 (by decide +kernel)

theorem badTest_8448_block_7 : Interval badTest_8448 56 64 :=
  interval_of_check badTest_8448 56 8 (by decide +kernel)

theorem badTest_8448_block_8 : Interval badTest_8448 64 72 :=
  interval_of_check badTest_8448 64 8 (by decide +kernel)

theorem badTest_8448_block_9 : Interval badTest_8448 72 80 :=
  interval_of_check badTest_8448 72 8 (by decide +kernel)

theorem badTest_8448_block_10 : Interval badTest_8448 80 88 :=
  interval_of_check badTest_8448 80 8 (by decide +kernel)

theorem badTest_8448_block_11 : Interval badTest_8448 88 96 :=
  interval_of_check badTest_8448 88 8 (by decide +kernel)

theorem badTest_8448_block_12 : Interval badTest_8448 96 104 :=
  interval_of_check badTest_8448 96 8 (by decide +kernel)

theorem badTest_8448_block_13 : Interval badTest_8448 104 112 :=
  interval_of_check badTest_8448 104 8 (by decide +kernel)

theorem badTest_8448_block_14 : Interval badTest_8448 112 120 :=
  interval_of_check badTest_8448 112 8 (by decide +kernel)

theorem badTest_8448_block_15 : Interval badTest_8448 120 128 :=
  interval_of_check badTest_8448 120 8 (by decide +kernel)

theorem badTest_8448_block_16 : Interval badTest_8448 128 136 :=
  interval_of_check badTest_8448 128 8 (by decide +kernel)

theorem badTest_8448_block_17 : Interval badTest_8448 136 144 :=
  interval_of_check badTest_8448 136 8 (by decide +kernel)

theorem badTest_8448_block_18 : Interval badTest_8448 144 152 :=
  interval_of_check badTest_8448 144 8 (by decide +kernel)

theorem badTest_8448_block_19 : Interval badTest_8448 152 160 :=
  interval_of_check badTest_8448 152 8 (by decide +kernel)

theorem badTest_8448_block_20 : Interval badTest_8448 160 168 :=
  interval_of_check badTest_8448 160 8 (by decide +kernel)

theorem badTest_8448_block_21 : Interval badTest_8448 168 176 :=
  interval_of_check badTest_8448 168 8 (by decide +kernel)

theorem badTest_8448_block_22 : Interval badTest_8448 176 184 :=
  interval_of_check badTest_8448 176 8 (by decide +kernel)

theorem badTest_8448_block_23 : Interval badTest_8448 184 192 :=
  interval_of_check badTest_8448 184 8 (by decide +kernel)

theorem badTest_8448_block_24 : Interval badTest_8448 192 200 :=
  interval_of_check badTest_8448 192 8 (by decide +kernel)

theorem badTest_8448_block_25 : Interval badTest_8448 200 208 :=
  interval_of_check badTest_8448 200 8 (by decide +kernel)

theorem badTest_8448_block_26 : Interval badTest_8448 208 216 :=
  interval_of_check badTest_8448 208 8 (by decide +kernel)

theorem badTest_8448_block_27 : Interval badTest_8448 216 224 :=
  interval_of_check badTest_8448 216 8 (by decide +kernel)

theorem badTest_8448_block_28 : Interval badTest_8448 224 232 :=
  interval_of_check badTest_8448 224 8 (by decide +kernel)

theorem badTest_8448_block_29 : Interval badTest_8448 232 240 :=
  interval_of_check badTest_8448 232 8 (by decide +kernel)

theorem badTest_8448_block_30 : Interval badTest_8448 240 248 :=
  interval_of_check badTest_8448 240 8 (by decide +kernel)

theorem badTest_8448_block_31 : Interval badTest_8448 248 256 :=
  interval_of_check badTest_8448 248 8 (by decide +kernel)

theorem badTest_8448_complete : Interval badTest_8448 0 256 :=
  (interval_append badTest_8448 0 128 256
  (interval_append badTest_8448 0 64 128
  (interval_append badTest_8448 0 32 64
  (interval_append badTest_8448 0 16 32
  (interval_append badTest_8448 0 8 16
  badTest_8448_block_0
  badTest_8448_block_1)
  (interval_append badTest_8448 16 24 32
  badTest_8448_block_2
  badTest_8448_block_3))
  (interval_append badTest_8448 32 48 64
  (interval_append badTest_8448 32 40 48
  badTest_8448_block_4
  badTest_8448_block_5)
  (interval_append badTest_8448 48 56 64
  badTest_8448_block_6
  badTest_8448_block_7)))
  (interval_append badTest_8448 64 96 128
  (interval_append badTest_8448 64 80 96
  (interval_append badTest_8448 64 72 80
  badTest_8448_block_8
  badTest_8448_block_9)
  (interval_append badTest_8448 80 88 96
  badTest_8448_block_10
  badTest_8448_block_11))
  (interval_append badTest_8448 96 112 128
  (interval_append badTest_8448 96 104 112
  badTest_8448_block_12
  badTest_8448_block_13)
  (interval_append badTest_8448 112 120 128
  badTest_8448_block_14
  badTest_8448_block_15))))
  (interval_append badTest_8448 128 192 256
  (interval_append badTest_8448 128 160 192
  (interval_append badTest_8448 128 144 160
  (interval_append badTest_8448 128 136 144
  badTest_8448_block_16
  badTest_8448_block_17)
  (interval_append badTest_8448 144 152 160
  badTest_8448_block_18
  badTest_8448_block_19))
  (interval_append badTest_8448 160 176 192
  (interval_append badTest_8448 160 168 176
  badTest_8448_block_20
  badTest_8448_block_21)
  (interval_append badTest_8448 176 184 192
  badTest_8448_block_22
  badTest_8448_block_23)))
  (interval_append badTest_8448 192 224 256
  (interval_append badTest_8448 192 208 224
  (interval_append badTest_8448 192 200 208
  badTest_8448_block_24
  badTest_8448_block_25)
  (interval_append badTest_8448 208 216 224
  badTest_8448_block_26
  badTest_8448_block_27))
  (interval_append badTest_8448 224 240 256
  (interval_append badTest_8448 224 232 240
  badTest_8448_block_28
  badTest_8448_block_29)
  (interval_append badTest_8448 240 248 256
  badTest_8448_block_30
  badTest_8448_block_31)))))
theorem badTestInterval8448 : Interval badTest 8448 8704 := by
  intro i hlo hhi
  have h := badTest_8448_complete (i-8448) (Nat.zero_le _) (by omega)
  simpa only [badTest_8448, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad034 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_8704 (i : Nat) := badTest (i+8704)
theorem badTest_8704_block_0 : Interval badTest_8704 0 8 :=
  interval_of_check badTest_8704 0 8 (by decide +kernel)

theorem badTest_8704_block_1 : Interval badTest_8704 8 16 :=
  interval_of_check badTest_8704 8 8 (by decide +kernel)

theorem badTest_8704_block_2 : Interval badTest_8704 16 24 :=
  interval_of_check badTest_8704 16 8 (by decide +kernel)

theorem badTest_8704_block_3 : Interval badTest_8704 24 32 :=
  interval_of_check badTest_8704 24 8 (by decide +kernel)

theorem badTest_8704_block_4 : Interval badTest_8704 32 40 :=
  interval_of_check badTest_8704 32 8 (by decide +kernel)

theorem badTest_8704_block_5 : Interval badTest_8704 40 48 :=
  interval_of_check badTest_8704 40 8 (by decide +kernel)

theorem badTest_8704_block_6 : Interval badTest_8704 48 56 :=
  interval_of_check badTest_8704 48 8 (by decide +kernel)

theorem badTest_8704_block_7 : Interval badTest_8704 56 64 :=
  interval_of_check badTest_8704 56 8 (by decide +kernel)

theorem badTest_8704_block_8 : Interval badTest_8704 64 72 :=
  interval_of_check badTest_8704 64 8 (by decide +kernel)

theorem badTest_8704_block_9 : Interval badTest_8704 72 80 :=
  interval_of_check badTest_8704 72 8 (by decide +kernel)

theorem badTest_8704_block_10 : Interval badTest_8704 80 88 :=
  interval_of_check badTest_8704 80 8 (by decide +kernel)

theorem badTest_8704_block_11 : Interval badTest_8704 88 96 :=
  interval_of_check badTest_8704 88 8 (by decide +kernel)

theorem badTest_8704_block_12 : Interval badTest_8704 96 104 :=
  interval_of_check badTest_8704 96 8 (by decide +kernel)

theorem badTest_8704_block_13 : Interval badTest_8704 104 112 :=
  interval_of_check badTest_8704 104 8 (by decide +kernel)

theorem badTest_8704_block_14 : Interval badTest_8704 112 120 :=
  interval_of_check badTest_8704 112 8 (by decide +kernel)

theorem badTest_8704_block_15 : Interval badTest_8704 120 128 :=
  interval_of_check badTest_8704 120 8 (by decide +kernel)

theorem badTest_8704_block_16 : Interval badTest_8704 128 136 :=
  interval_of_check badTest_8704 128 8 (by decide +kernel)

theorem badTest_8704_block_17 : Interval badTest_8704 136 144 :=
  interval_of_check badTest_8704 136 8 (by decide +kernel)

theorem badTest_8704_block_18 : Interval badTest_8704 144 152 :=
  interval_of_check badTest_8704 144 8 (by decide +kernel)

theorem badTest_8704_block_19 : Interval badTest_8704 152 160 :=
  interval_of_check badTest_8704 152 8 (by decide +kernel)

theorem badTest_8704_block_20 : Interval badTest_8704 160 168 :=
  interval_of_check badTest_8704 160 8 (by decide +kernel)

theorem badTest_8704_block_21 : Interval badTest_8704 168 176 :=
  interval_of_check badTest_8704 168 8 (by decide +kernel)

theorem badTest_8704_block_22 : Interval badTest_8704 176 184 :=
  interval_of_check badTest_8704 176 8 (by decide +kernel)

theorem badTest_8704_block_23 : Interval badTest_8704 184 192 :=
  interval_of_check badTest_8704 184 8 (by decide +kernel)

theorem badTest_8704_block_24 : Interval badTest_8704 192 200 :=
  interval_of_check badTest_8704 192 8 (by decide +kernel)

theorem badTest_8704_block_25 : Interval badTest_8704 200 208 :=
  interval_of_check badTest_8704 200 8 (by decide +kernel)

theorem badTest_8704_block_26 : Interval badTest_8704 208 216 :=
  interval_of_check badTest_8704 208 8 (by decide +kernel)

theorem badTest_8704_block_27 : Interval badTest_8704 216 224 :=
  interval_of_check badTest_8704 216 8 (by decide +kernel)

theorem badTest_8704_block_28 : Interval badTest_8704 224 232 :=
  interval_of_check badTest_8704 224 8 (by decide +kernel)

theorem badTest_8704_block_29 : Interval badTest_8704 232 240 :=
  interval_of_check badTest_8704 232 8 (by decide +kernel)

theorem badTest_8704_block_30 : Interval badTest_8704 240 248 :=
  interval_of_check badTest_8704 240 8 (by decide +kernel)

theorem badTest_8704_block_31 : Interval badTest_8704 248 256 :=
  interval_of_check badTest_8704 248 8 (by decide +kernel)

theorem badTest_8704_complete : Interval badTest_8704 0 256 :=
  (interval_append badTest_8704 0 128 256
  (interval_append badTest_8704 0 64 128
  (interval_append badTest_8704 0 32 64
  (interval_append badTest_8704 0 16 32
  (interval_append badTest_8704 0 8 16
  badTest_8704_block_0
  badTest_8704_block_1)
  (interval_append badTest_8704 16 24 32
  badTest_8704_block_2
  badTest_8704_block_3))
  (interval_append badTest_8704 32 48 64
  (interval_append badTest_8704 32 40 48
  badTest_8704_block_4
  badTest_8704_block_5)
  (interval_append badTest_8704 48 56 64
  badTest_8704_block_6
  badTest_8704_block_7)))
  (interval_append badTest_8704 64 96 128
  (interval_append badTest_8704 64 80 96
  (interval_append badTest_8704 64 72 80
  badTest_8704_block_8
  badTest_8704_block_9)
  (interval_append badTest_8704 80 88 96
  badTest_8704_block_10
  badTest_8704_block_11))
  (interval_append badTest_8704 96 112 128
  (interval_append badTest_8704 96 104 112
  badTest_8704_block_12
  badTest_8704_block_13)
  (interval_append badTest_8704 112 120 128
  badTest_8704_block_14
  badTest_8704_block_15))))
  (interval_append badTest_8704 128 192 256
  (interval_append badTest_8704 128 160 192
  (interval_append badTest_8704 128 144 160
  (interval_append badTest_8704 128 136 144
  badTest_8704_block_16
  badTest_8704_block_17)
  (interval_append badTest_8704 144 152 160
  badTest_8704_block_18
  badTest_8704_block_19))
  (interval_append badTest_8704 160 176 192
  (interval_append badTest_8704 160 168 176
  badTest_8704_block_20
  badTest_8704_block_21)
  (interval_append badTest_8704 176 184 192
  badTest_8704_block_22
  badTest_8704_block_23)))
  (interval_append badTest_8704 192 224 256
  (interval_append badTest_8704 192 208 224
  (interval_append badTest_8704 192 200 208
  badTest_8704_block_24
  badTest_8704_block_25)
  (interval_append badTest_8704 208 216 224
  badTest_8704_block_26
  badTest_8704_block_27))
  (interval_append badTest_8704 224 240 256
  (interval_append badTest_8704 224 232 240
  badTest_8704_block_28
  badTest_8704_block_29)
  (interval_append badTest_8704 240 248 256
  badTest_8704_block_30
  badTest_8704_block_31)))))
theorem badTestInterval8704 : Interval badTest 8704 8960 := by
  intro i hlo hhi
  have h := badTest_8704_complete (i-8704) (Nat.zero_le _) (by omega)
  simpa only [badTest_8704, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad035 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_8960 (i : Nat) := badTest (i+8960)
theorem badTest_8960_block_0 : Interval badTest_8960 0 8 :=
  interval_of_check badTest_8960 0 8 (by decide +kernel)

theorem badTest_8960_block_1 : Interval badTest_8960 8 16 :=
  interval_of_check badTest_8960 8 8 (by decide +kernel)

theorem badTest_8960_block_2 : Interval badTest_8960 16 24 :=
  interval_of_check badTest_8960 16 8 (by decide +kernel)

theorem badTest_8960_block_3 : Interval badTest_8960 24 32 :=
  interval_of_check badTest_8960 24 8 (by decide +kernel)

theorem badTest_8960_block_4 : Interval badTest_8960 32 40 :=
  interval_of_check badTest_8960 32 8 (by decide +kernel)

theorem badTest_8960_block_5 : Interval badTest_8960 40 48 :=
  interval_of_check badTest_8960 40 8 (by decide +kernel)

theorem badTest_8960_block_6 : Interval badTest_8960 48 56 :=
  interval_of_check badTest_8960 48 8 (by decide +kernel)

theorem badTest_8960_block_7 : Interval badTest_8960 56 64 :=
  interval_of_check badTest_8960 56 8 (by decide +kernel)

theorem badTest_8960_block_8 : Interval badTest_8960 64 72 :=
  interval_of_check badTest_8960 64 8 (by decide +kernel)

theorem badTest_8960_block_9 : Interval badTest_8960 72 80 :=
  interval_of_check badTest_8960 72 8 (by decide +kernel)

theorem badTest_8960_block_10 : Interval badTest_8960 80 88 :=
  interval_of_check badTest_8960 80 8 (by decide +kernel)

theorem badTest_8960_block_11 : Interval badTest_8960 88 96 :=
  interval_of_check badTest_8960 88 8 (by decide +kernel)

theorem badTest_8960_block_12 : Interval badTest_8960 96 104 :=
  interval_of_check badTest_8960 96 8 (by decide +kernel)

theorem badTest_8960_block_13 : Interval badTest_8960 104 112 :=
  interval_of_check badTest_8960 104 8 (by decide +kernel)

theorem badTest_8960_block_14 : Interval badTest_8960 112 120 :=
  interval_of_check badTest_8960 112 8 (by decide +kernel)

theorem badTest_8960_block_15 : Interval badTest_8960 120 128 :=
  interval_of_check badTest_8960 120 8 (by decide +kernel)

theorem badTest_8960_block_16 : Interval badTest_8960 128 136 :=
  interval_of_check badTest_8960 128 8 (by decide +kernel)

theorem badTest_8960_block_17 : Interval badTest_8960 136 144 :=
  interval_of_check badTest_8960 136 8 (by decide +kernel)

theorem badTest_8960_block_18 : Interval badTest_8960 144 152 :=
  interval_of_check badTest_8960 144 8 (by decide +kernel)

theorem badTest_8960_block_19 : Interval badTest_8960 152 160 :=
  interval_of_check badTest_8960 152 8 (by decide +kernel)

theorem badTest_8960_block_20 : Interval badTest_8960 160 168 :=
  interval_of_check badTest_8960 160 8 (by decide +kernel)

theorem badTest_8960_block_21 : Interval badTest_8960 168 176 :=
  interval_of_check badTest_8960 168 8 (by decide +kernel)

theorem badTest_8960_block_22 : Interval badTest_8960 176 184 :=
  interval_of_check badTest_8960 176 8 (by decide +kernel)

theorem badTest_8960_block_23 : Interval badTest_8960 184 192 :=
  interval_of_check badTest_8960 184 8 (by decide +kernel)

theorem badTest_8960_block_24 : Interval badTest_8960 192 200 :=
  interval_of_check badTest_8960 192 8 (by decide +kernel)

theorem badTest_8960_block_25 : Interval badTest_8960 200 208 :=
  interval_of_check badTest_8960 200 8 (by decide +kernel)

theorem badTest_8960_block_26 : Interval badTest_8960 208 216 :=
  interval_of_check badTest_8960 208 8 (by decide +kernel)

theorem badTest_8960_block_27 : Interval badTest_8960 216 224 :=
  interval_of_check badTest_8960 216 8 (by decide +kernel)

theorem badTest_8960_block_28 : Interval badTest_8960 224 232 :=
  interval_of_check badTest_8960 224 8 (by decide +kernel)

theorem badTest_8960_block_29 : Interval badTest_8960 232 240 :=
  interval_of_check badTest_8960 232 8 (by decide +kernel)

theorem badTest_8960_block_30 : Interval badTest_8960 240 248 :=
  interval_of_check badTest_8960 240 8 (by decide +kernel)

theorem badTest_8960_block_31 : Interval badTest_8960 248 256 :=
  interval_of_check badTest_8960 248 8 (by decide +kernel)

theorem badTest_8960_complete : Interval badTest_8960 0 256 :=
  (interval_append badTest_8960 0 128 256
  (interval_append badTest_8960 0 64 128
  (interval_append badTest_8960 0 32 64
  (interval_append badTest_8960 0 16 32
  (interval_append badTest_8960 0 8 16
  badTest_8960_block_0
  badTest_8960_block_1)
  (interval_append badTest_8960 16 24 32
  badTest_8960_block_2
  badTest_8960_block_3))
  (interval_append badTest_8960 32 48 64
  (interval_append badTest_8960 32 40 48
  badTest_8960_block_4
  badTest_8960_block_5)
  (interval_append badTest_8960 48 56 64
  badTest_8960_block_6
  badTest_8960_block_7)))
  (interval_append badTest_8960 64 96 128
  (interval_append badTest_8960 64 80 96
  (interval_append badTest_8960 64 72 80
  badTest_8960_block_8
  badTest_8960_block_9)
  (interval_append badTest_8960 80 88 96
  badTest_8960_block_10
  badTest_8960_block_11))
  (interval_append badTest_8960 96 112 128
  (interval_append badTest_8960 96 104 112
  badTest_8960_block_12
  badTest_8960_block_13)
  (interval_append badTest_8960 112 120 128
  badTest_8960_block_14
  badTest_8960_block_15))))
  (interval_append badTest_8960 128 192 256
  (interval_append badTest_8960 128 160 192
  (interval_append badTest_8960 128 144 160
  (interval_append badTest_8960 128 136 144
  badTest_8960_block_16
  badTest_8960_block_17)
  (interval_append badTest_8960 144 152 160
  badTest_8960_block_18
  badTest_8960_block_19))
  (interval_append badTest_8960 160 176 192
  (interval_append badTest_8960 160 168 176
  badTest_8960_block_20
  badTest_8960_block_21)
  (interval_append badTest_8960 176 184 192
  badTest_8960_block_22
  badTest_8960_block_23)))
  (interval_append badTest_8960 192 224 256
  (interval_append badTest_8960 192 208 224
  (interval_append badTest_8960 192 200 208
  badTest_8960_block_24
  badTest_8960_block_25)
  (interval_append badTest_8960 208 216 224
  badTest_8960_block_26
  badTest_8960_block_27))
  (interval_append badTest_8960 224 240 256
  (interval_append badTest_8960 224 232 240
  badTest_8960_block_28
  badTest_8960_block_29)
  (interval_append badTest_8960 240 248 256
  badTest_8960_block_30
  badTest_8960_block_31)))))
theorem badTestInterval8960 : Interval badTest 8960 9216 := by
  intro i hlo hhi
  have h := badTest_8960_complete (i-8960) (Nat.zero_le _) (by omega)
  simpa only [badTest_8960, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
