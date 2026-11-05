module
prelude
public import RootedSixExtra02GrowthCacheData

/- RootedSixExtra02GrowthCacheBad022 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad023 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad024 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad025 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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

theorem badTest_6400_block_27 : Interval badTest_6400 216 220 :=
  interval_of_check badTest_6400 216 4 (by decide +kernel)

theorem badTest_6400_complete : Interval badTest_6400 0 220 :=
  (interval_append badTest_6400 0 112 220
  (interval_append badTest_6400 0 56 112
  (interval_append badTest_6400 0 24 56
  (interval_append badTest_6400 0 8 24
  badTest_6400_block_0
  (interval_append badTest_6400 8 16 24
  badTest_6400_block_1
  badTest_6400_block_2))
  (interval_append badTest_6400 24 40 56
  (interval_append badTest_6400 24 32 40
  badTest_6400_block_3
  badTest_6400_block_4)
  (interval_append badTest_6400 40 48 56
  badTest_6400_block_5
  badTest_6400_block_6)))
  (interval_append badTest_6400 56 80 112
  (interval_append badTest_6400 56 64 80
  badTest_6400_block_7
  (interval_append badTest_6400 64 72 80
  badTest_6400_block_8
  badTest_6400_block_9))
  (interval_append badTest_6400 80 96 112
  (interval_append badTest_6400 80 88 96
  badTest_6400_block_10
  badTest_6400_block_11)
  (interval_append badTest_6400 96 104 112
  badTest_6400_block_12
  badTest_6400_block_13))))
  (interval_append badTest_6400 112 168 220
  (interval_append badTest_6400 112 136 168
  (interval_append badTest_6400 112 120 136
  badTest_6400_block_14
  (interval_append badTest_6400 120 128 136
  badTest_6400_block_15
  badTest_6400_block_16))
  (interval_append badTest_6400 136 152 168
  (interval_append badTest_6400 136 144 152
  badTest_6400_block_17
  badTest_6400_block_18)
  (interval_append badTest_6400 152 160 168
  badTest_6400_block_19
  badTest_6400_block_20)))
  (interval_append badTest_6400 168 192 220
  (interval_append badTest_6400 168 176 192
  badTest_6400_block_21
  (interval_append badTest_6400 176 184 192
  badTest_6400_block_22
  badTest_6400_block_23))
  (interval_append badTest_6400 192 208 220
  (interval_append badTest_6400 192 200 208
  badTest_6400_block_24
  badTest_6400_block_25)
  (interval_append badTest_6400 208 216 220
  badTest_6400_block_26
  badTest_6400_block_27)))))
theorem badTestInterval6400 : Interval badTest 6400 6620 := by
  intro i hlo hhi
  have h := badTest_6400_complete (i-6400) (Nat.zero_le _) (by omega)
  simpa only [badTest_6400, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_512 (i : Nat) := wellFormedTest (i+512)
theorem wellFormedTest_512_block_0 : Interval wellFormedTest_512 0 16 :=
  interval_of_check wellFormedTest_512 0 16 (by decide +kernel)

theorem wellFormedTest_512_block_1 : Interval wellFormedTest_512 16 32 :=
  interval_of_check wellFormedTest_512 16 16 (by decide +kernel)

theorem wellFormedTest_512_block_2 : Interval wellFormedTest_512 32 48 :=
  interval_of_check wellFormedTest_512 32 16 (by decide +kernel)

theorem wellFormedTest_512_block_3 : Interval wellFormedTest_512 48 64 :=
  interval_of_check wellFormedTest_512 48 16 (by decide +kernel)

theorem wellFormedTest_512_block_4 : Interval wellFormedTest_512 64 80 :=
  interval_of_check wellFormedTest_512 64 16 (by decide +kernel)

theorem wellFormedTest_512_block_5 : Interval wellFormedTest_512 80 96 :=
  interval_of_check wellFormedTest_512 80 16 (by decide +kernel)

theorem wellFormedTest_512_block_6 : Interval wellFormedTest_512 96 112 :=
  interval_of_check wellFormedTest_512 96 16 (by decide +kernel)

theorem wellFormedTest_512_block_7 : Interval wellFormedTest_512 112 128 :=
  interval_of_check wellFormedTest_512 112 16 (by decide +kernel)

theorem wellFormedTest_512_block_8 : Interval wellFormedTest_512 128 144 :=
  interval_of_check wellFormedTest_512 128 16 (by decide +kernel)

theorem wellFormedTest_512_block_9 : Interval wellFormedTest_512 144 160 :=
  interval_of_check wellFormedTest_512 144 16 (by decide +kernel)

theorem wellFormedTest_512_block_10 : Interval wellFormedTest_512 160 176 :=
  interval_of_check wellFormedTest_512 160 16 (by decide +kernel)

theorem wellFormedTest_512_block_11 : Interval wellFormedTest_512 176 192 :=
  interval_of_check wellFormedTest_512 176 16 (by decide +kernel)

theorem wellFormedTest_512_block_12 : Interval wellFormedTest_512 192 208 :=
  interval_of_check wellFormedTest_512 192 16 (by decide +kernel)

theorem wellFormedTest_512_block_13 : Interval wellFormedTest_512 208 224 :=
  interval_of_check wellFormedTest_512 208 16 (by decide +kernel)

theorem wellFormedTest_512_block_14 : Interval wellFormedTest_512 224 240 :=
  interval_of_check wellFormedTest_512 224 16 (by decide +kernel)

theorem wellFormedTest_512_block_15 : Interval wellFormedTest_512 240 256 :=
  interval_of_check wellFormedTest_512 240 16 (by decide +kernel)

theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 256 :=
  (interval_append wellFormedTest_512 0 128 256
  (interval_append wellFormedTest_512 0 64 128
  (interval_append wellFormedTest_512 0 32 64
  (interval_append wellFormedTest_512 0 16 32
  wellFormedTest_512_block_0
  wellFormedTest_512_block_1)
  (interval_append wellFormedTest_512 32 48 64
  wellFormedTest_512_block_2
  wellFormedTest_512_block_3))
  (interval_append wellFormedTest_512 64 96 128
  (interval_append wellFormedTest_512 64 80 96
  wellFormedTest_512_block_4
  wellFormedTest_512_block_5)
  (interval_append wellFormedTest_512 96 112 128
  wellFormedTest_512_block_6
  wellFormedTest_512_block_7)))
  (interval_append wellFormedTest_512 128 192 256
  (interval_append wellFormedTest_512 128 160 192
  (interval_append wellFormedTest_512 128 144 160
  wellFormedTest_512_block_8
  wellFormedTest_512_block_9)
  (interval_append wellFormedTest_512 160 176 192
  wellFormedTest_512_block_10
  wellFormedTest_512_block_11))
  (interval_append wellFormedTest_512 192 224 256
  (interval_append wellFormedTest_512 192 208 224
  wellFormedTest_512_block_12
  wellFormedTest_512_block_13)
  (interval_append wellFormedTest_512 224 240 256
  wellFormedTest_512_block_14
  wellFormedTest_512_block_15))))
theorem wellFormedTestInterval512 : Interval wellFormedTest 512 768 := by
  intro i hlo hhi
  have h := wellFormedTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_768 (i : Nat) := wellFormedTest (i+768)
theorem wellFormedTest_768_block_0 : Interval wellFormedTest_768 0 16 :=
  interval_of_check wellFormedTest_768 0 16 (by decide +kernel)

theorem wellFormedTest_768_block_1 : Interval wellFormedTest_768 16 32 :=
  interval_of_check wellFormedTest_768 16 16 (by decide +kernel)

theorem wellFormedTest_768_block_2 : Interval wellFormedTest_768 32 48 :=
  interval_of_check wellFormedTest_768 32 16 (by decide +kernel)

theorem wellFormedTest_768_block_3 : Interval wellFormedTest_768 48 64 :=
  interval_of_check wellFormedTest_768 48 16 (by decide +kernel)

theorem wellFormedTest_768_block_4 : Interval wellFormedTest_768 64 80 :=
  interval_of_check wellFormedTest_768 64 16 (by decide +kernel)

theorem wellFormedTest_768_block_5 : Interval wellFormedTest_768 80 96 :=
  interval_of_check wellFormedTest_768 80 16 (by decide +kernel)

theorem wellFormedTest_768_block_6 : Interval wellFormedTest_768 96 112 :=
  interval_of_check wellFormedTest_768 96 16 (by decide +kernel)

theorem wellFormedTest_768_block_7 : Interval wellFormedTest_768 112 128 :=
  interval_of_check wellFormedTest_768 112 16 (by decide +kernel)

theorem wellFormedTest_768_block_8 : Interval wellFormedTest_768 128 144 :=
  interval_of_check wellFormedTest_768 128 16 (by decide +kernel)

theorem wellFormedTest_768_block_9 : Interval wellFormedTest_768 144 160 :=
  interval_of_check wellFormedTest_768 144 16 (by decide +kernel)

theorem wellFormedTest_768_block_10 : Interval wellFormedTest_768 160 176 :=
  interval_of_check wellFormedTest_768 160 16 (by decide +kernel)

theorem wellFormedTest_768_block_11 : Interval wellFormedTest_768 176 192 :=
  interval_of_check wellFormedTest_768 176 16 (by decide +kernel)

theorem wellFormedTest_768_block_12 : Interval wellFormedTest_768 192 208 :=
  interval_of_check wellFormedTest_768 192 16 (by decide +kernel)

theorem wellFormedTest_768_block_13 : Interval wellFormedTest_768 208 224 :=
  interval_of_check wellFormedTest_768 208 16 (by decide +kernel)

theorem wellFormedTest_768_block_14 : Interval wellFormedTest_768 224 240 :=
  interval_of_check wellFormedTest_768 224 16 (by decide +kernel)

theorem wellFormedTest_768_block_15 : Interval wellFormedTest_768 240 256 :=
  interval_of_check wellFormedTest_768 240 16 (by decide +kernel)

theorem wellFormedTest_768_complete : Interval wellFormedTest_768 0 256 :=
  (interval_append wellFormedTest_768 0 128 256
  (interval_append wellFormedTest_768 0 64 128
  (interval_append wellFormedTest_768 0 32 64
  (interval_append wellFormedTest_768 0 16 32
  wellFormedTest_768_block_0
  wellFormedTest_768_block_1)
  (interval_append wellFormedTest_768 32 48 64
  wellFormedTest_768_block_2
  wellFormedTest_768_block_3))
  (interval_append wellFormedTest_768 64 96 128
  (interval_append wellFormedTest_768 64 80 96
  wellFormedTest_768_block_4
  wellFormedTest_768_block_5)
  (interval_append wellFormedTest_768 96 112 128
  wellFormedTest_768_block_6
  wellFormedTest_768_block_7)))
  (interval_append wellFormedTest_768 128 192 256
  (interval_append wellFormedTest_768 128 160 192
  (interval_append wellFormedTest_768 128 144 160
  wellFormedTest_768_block_8
  wellFormedTest_768_block_9)
  (interval_append wellFormedTest_768 160 176 192
  wellFormedTest_768_block_10
  wellFormedTest_768_block_11))
  (interval_append wellFormedTest_768 192 224 256
  (interval_append wellFormedTest_768 192 208 224
  wellFormedTest_768_block_12
  wellFormedTest_768_block_13)
  (interval_append wellFormedTest_768 224 240 256
  wellFormedTest_768_block_14
  wellFormedTest_768_block_15))))
theorem wellFormedTestInterval768 : Interval wellFormedTest 768 1024 := by
  intro i hlo hhi
  have h := wellFormedTest_768_complete (i-768) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_1024 (i : Nat) := wellFormedTest (i+1024)
theorem wellFormedTest_1024_block_0 : Interval wellFormedTest_1024 0 16 :=
  interval_of_check wellFormedTest_1024 0 16 (by decide +kernel)

theorem wellFormedTest_1024_block_1 : Interval wellFormedTest_1024 16 32 :=
  interval_of_check wellFormedTest_1024 16 16 (by decide +kernel)

theorem wellFormedTest_1024_block_2 : Interval wellFormedTest_1024 32 48 :=
  interval_of_check wellFormedTest_1024 32 16 (by decide +kernel)

theorem wellFormedTest_1024_block_3 : Interval wellFormedTest_1024 48 64 :=
  interval_of_check wellFormedTest_1024 48 16 (by decide +kernel)

theorem wellFormedTest_1024_block_4 : Interval wellFormedTest_1024 64 80 :=
  interval_of_check wellFormedTest_1024 64 16 (by decide +kernel)

theorem wellFormedTest_1024_block_5 : Interval wellFormedTest_1024 80 96 :=
  interval_of_check wellFormedTest_1024 80 16 (by decide +kernel)

theorem wellFormedTest_1024_block_6 : Interval wellFormedTest_1024 96 112 :=
  interval_of_check wellFormedTest_1024 96 16 (by decide +kernel)

theorem wellFormedTest_1024_block_7 : Interval wellFormedTest_1024 112 128 :=
  interval_of_check wellFormedTest_1024 112 16 (by decide +kernel)

theorem wellFormedTest_1024_block_8 : Interval wellFormedTest_1024 128 144 :=
  interval_of_check wellFormedTest_1024 128 16 (by decide +kernel)

theorem wellFormedTest_1024_block_9 : Interval wellFormedTest_1024 144 160 :=
  interval_of_check wellFormedTest_1024 144 16 (by decide +kernel)

theorem wellFormedTest_1024_block_10 : Interval wellFormedTest_1024 160 176 :=
  interval_of_check wellFormedTest_1024 160 16 (by decide +kernel)

theorem wellFormedTest_1024_block_11 : Interval wellFormedTest_1024 176 192 :=
  interval_of_check wellFormedTest_1024 176 16 (by decide +kernel)

theorem wellFormedTest_1024_block_12 : Interval wellFormedTest_1024 192 208 :=
  interval_of_check wellFormedTest_1024 192 16 (by decide +kernel)

theorem wellFormedTest_1024_block_13 : Interval wellFormedTest_1024 208 224 :=
  interval_of_check wellFormedTest_1024 208 16 (by decide +kernel)

theorem wellFormedTest_1024_block_14 : Interval wellFormedTest_1024 224 240 :=
  interval_of_check wellFormedTest_1024 224 16 (by decide +kernel)

theorem wellFormedTest_1024_block_15 : Interval wellFormedTest_1024 240 256 :=
  interval_of_check wellFormedTest_1024 240 16 (by decide +kernel)

theorem wellFormedTest_1024_complete : Interval wellFormedTest_1024 0 256 :=
  (interval_append wellFormedTest_1024 0 128 256
  (interval_append wellFormedTest_1024 0 64 128
  (interval_append wellFormedTest_1024 0 32 64
  (interval_append wellFormedTest_1024 0 16 32
  wellFormedTest_1024_block_0
  wellFormedTest_1024_block_1)
  (interval_append wellFormedTest_1024 32 48 64
  wellFormedTest_1024_block_2
  wellFormedTest_1024_block_3))
  (interval_append wellFormedTest_1024 64 96 128
  (interval_append wellFormedTest_1024 64 80 96
  wellFormedTest_1024_block_4
  wellFormedTest_1024_block_5)
  (interval_append wellFormedTest_1024 96 112 128
  wellFormedTest_1024_block_6
  wellFormedTest_1024_block_7)))
  (interval_append wellFormedTest_1024 128 192 256
  (interval_append wellFormedTest_1024 128 160 192
  (interval_append wellFormedTest_1024 128 144 160
  wellFormedTest_1024_block_8
  wellFormedTest_1024_block_9)
  (interval_append wellFormedTest_1024 160 176 192
  wellFormedTest_1024_block_10
  wellFormedTest_1024_block_11))
  (interval_append wellFormedTest_1024 192 224 256
  (interval_append wellFormedTest_1024 192 208 224
  wellFormedTest_1024_block_12
  wellFormedTest_1024_block_13)
  (interval_append wellFormedTest_1024 224 240 256
  wellFormedTest_1024_block_14
  wellFormedTest_1024_block_15))))
theorem wellFormedTestInterval1024 : Interval wellFormedTest 1024 1280 := by
  intro i hlo hhi
  have h := wellFormedTest_1024_complete (i-1024) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_1024, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_1280 (i : Nat) := wellFormedTest (i+1280)
theorem wellFormedTest_1280_block_0 : Interval wellFormedTest_1280 0 16 :=
  interval_of_check wellFormedTest_1280 0 16 (by decide +kernel)

theorem wellFormedTest_1280_block_1 : Interval wellFormedTest_1280 16 32 :=
  interval_of_check wellFormedTest_1280 16 16 (by decide +kernel)

theorem wellFormedTest_1280_block_2 : Interval wellFormedTest_1280 32 48 :=
  interval_of_check wellFormedTest_1280 32 16 (by decide +kernel)

theorem wellFormedTest_1280_block_3 : Interval wellFormedTest_1280 48 64 :=
  interval_of_check wellFormedTest_1280 48 16 (by decide +kernel)

theorem wellFormedTest_1280_block_4 : Interval wellFormedTest_1280 64 80 :=
  interval_of_check wellFormedTest_1280 64 16 (by decide +kernel)

theorem wellFormedTest_1280_block_5 : Interval wellFormedTest_1280 80 96 :=
  interval_of_check wellFormedTest_1280 80 16 (by decide +kernel)

theorem wellFormedTest_1280_block_6 : Interval wellFormedTest_1280 96 112 :=
  interval_of_check wellFormedTest_1280 96 16 (by decide +kernel)

theorem wellFormedTest_1280_block_7 : Interval wellFormedTest_1280 112 128 :=
  interval_of_check wellFormedTest_1280 112 16 (by decide +kernel)

theorem wellFormedTest_1280_block_8 : Interval wellFormedTest_1280 128 144 :=
  interval_of_check wellFormedTest_1280 128 16 (by decide +kernel)

theorem wellFormedTest_1280_block_9 : Interval wellFormedTest_1280 144 160 :=
  interval_of_check wellFormedTest_1280 144 16 (by decide +kernel)

theorem wellFormedTest_1280_block_10 : Interval wellFormedTest_1280 160 176 :=
  interval_of_check wellFormedTest_1280 160 16 (by decide +kernel)

theorem wellFormedTest_1280_block_11 : Interval wellFormedTest_1280 176 192 :=
  interval_of_check wellFormedTest_1280 176 16 (by decide +kernel)

theorem wellFormedTest_1280_block_12 : Interval wellFormedTest_1280 192 208 :=
  interval_of_check wellFormedTest_1280 192 16 (by decide +kernel)

theorem wellFormedTest_1280_block_13 : Interval wellFormedTest_1280 208 224 :=
  interval_of_check wellFormedTest_1280 208 16 (by decide +kernel)

theorem wellFormedTest_1280_block_14 : Interval wellFormedTest_1280 224 240 :=
  interval_of_check wellFormedTest_1280 224 16 (by decide +kernel)

theorem wellFormedTest_1280_block_15 : Interval wellFormedTest_1280 240 256 :=
  interval_of_check wellFormedTest_1280 240 16 (by decide +kernel)

theorem wellFormedTest_1280_complete : Interval wellFormedTest_1280 0 256 :=
  (interval_append wellFormedTest_1280 0 128 256
  (interval_append wellFormedTest_1280 0 64 128
  (interval_append wellFormedTest_1280 0 32 64
  (interval_append wellFormedTest_1280 0 16 32
  wellFormedTest_1280_block_0
  wellFormedTest_1280_block_1)
  (interval_append wellFormedTest_1280 32 48 64
  wellFormedTest_1280_block_2
  wellFormedTest_1280_block_3))
  (interval_append wellFormedTest_1280 64 96 128
  (interval_append wellFormedTest_1280 64 80 96
  wellFormedTest_1280_block_4
  wellFormedTest_1280_block_5)
  (interval_append wellFormedTest_1280 96 112 128
  wellFormedTest_1280_block_6
  wellFormedTest_1280_block_7)))
  (interval_append wellFormedTest_1280 128 192 256
  (interval_append wellFormedTest_1280 128 160 192
  (interval_append wellFormedTest_1280 128 144 160
  wellFormedTest_1280_block_8
  wellFormedTest_1280_block_9)
  (interval_append wellFormedTest_1280 160 176 192
  wellFormedTest_1280_block_10
  wellFormedTest_1280_block_11))
  (interval_append wellFormedTest_1280 192 224 256
  (interval_append wellFormedTest_1280 192 208 224
  wellFormedTest_1280_block_12
  wellFormedTest_1280_block_13)
  (interval_append wellFormedTest_1280 224 240 256
  wellFormedTest_1280_block_14
  wellFormedTest_1280_block_15))))
theorem wellFormedTestInterval1280 : Interval wellFormedTest 1280 1536 := by
  intro i hlo hhi
  have h := wellFormedTest_1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_1536 (i : Nat) := wellFormedTest (i+1536)
theorem wellFormedTest_1536_block_0 : Interval wellFormedTest_1536 0 16 :=
  interval_of_check wellFormedTest_1536 0 16 (by decide +kernel)

theorem wellFormedTest_1536_block_1 : Interval wellFormedTest_1536 16 32 :=
  interval_of_check wellFormedTest_1536 16 16 (by decide +kernel)

theorem wellFormedTest_1536_block_2 : Interval wellFormedTest_1536 32 48 :=
  interval_of_check wellFormedTest_1536 32 16 (by decide +kernel)

theorem wellFormedTest_1536_block_3 : Interval wellFormedTest_1536 48 64 :=
  interval_of_check wellFormedTest_1536 48 16 (by decide +kernel)

theorem wellFormedTest_1536_block_4 : Interval wellFormedTest_1536 64 80 :=
  interval_of_check wellFormedTest_1536 64 16 (by decide +kernel)

theorem wellFormedTest_1536_block_5 : Interval wellFormedTest_1536 80 96 :=
  interval_of_check wellFormedTest_1536 80 16 (by decide +kernel)

theorem wellFormedTest_1536_block_6 : Interval wellFormedTest_1536 96 112 :=
  interval_of_check wellFormedTest_1536 96 16 (by decide +kernel)

theorem wellFormedTest_1536_block_7 : Interval wellFormedTest_1536 112 128 :=
  interval_of_check wellFormedTest_1536 112 16 (by decide +kernel)

theorem wellFormedTest_1536_block_8 : Interval wellFormedTest_1536 128 144 :=
  interval_of_check wellFormedTest_1536 128 16 (by decide +kernel)

theorem wellFormedTest_1536_block_9 : Interval wellFormedTest_1536 144 160 :=
  interval_of_check wellFormedTest_1536 144 16 (by decide +kernel)

theorem wellFormedTest_1536_block_10 : Interval wellFormedTest_1536 160 176 :=
  interval_of_check wellFormedTest_1536 160 16 (by decide +kernel)

theorem wellFormedTest_1536_block_11 : Interval wellFormedTest_1536 176 192 :=
  interval_of_check wellFormedTest_1536 176 16 (by decide +kernel)

theorem wellFormedTest_1536_block_12 : Interval wellFormedTest_1536 192 208 :=
  interval_of_check wellFormedTest_1536 192 16 (by decide +kernel)

theorem wellFormedTest_1536_block_13 : Interval wellFormedTest_1536 208 224 :=
  interval_of_check wellFormedTest_1536 208 16 (by decide +kernel)

theorem wellFormedTest_1536_block_14 : Interval wellFormedTest_1536 224 240 :=
  interval_of_check wellFormedTest_1536 224 16 (by decide +kernel)

theorem wellFormedTest_1536_block_15 : Interval wellFormedTest_1536 240 256 :=
  interval_of_check wellFormedTest_1536 240 16 (by decide +kernel)

theorem wellFormedTest_1536_complete : Interval wellFormedTest_1536 0 256 :=
  (interval_append wellFormedTest_1536 0 128 256
  (interval_append wellFormedTest_1536 0 64 128
  (interval_append wellFormedTest_1536 0 32 64
  (interval_append wellFormedTest_1536 0 16 32
  wellFormedTest_1536_block_0
  wellFormedTest_1536_block_1)
  (interval_append wellFormedTest_1536 32 48 64
  wellFormedTest_1536_block_2
  wellFormedTest_1536_block_3))
  (interval_append wellFormedTest_1536 64 96 128
  (interval_append wellFormedTest_1536 64 80 96
  wellFormedTest_1536_block_4
  wellFormedTest_1536_block_5)
  (interval_append wellFormedTest_1536 96 112 128
  wellFormedTest_1536_block_6
  wellFormedTest_1536_block_7)))
  (interval_append wellFormedTest_1536 128 192 256
  (interval_append wellFormedTest_1536 128 160 192
  (interval_append wellFormedTest_1536 128 144 160
  wellFormedTest_1536_block_8
  wellFormedTest_1536_block_9)
  (interval_append wellFormedTest_1536 160 176 192
  wellFormedTest_1536_block_10
  wellFormedTest_1536_block_11))
  (interval_append wellFormedTest_1536 192 224 256
  (interval_append wellFormedTest_1536 192 208 224
  wellFormedTest_1536_block_12
  wellFormedTest_1536_block_13)
  (interval_append wellFormedTest_1536 224 240 256
  wellFormedTest_1536_block_14
  wellFormedTest_1536_block_15))))
theorem wellFormedTestInterval1536 : Interval wellFormedTest 1536 1792 := by
  intro i hlo hhi
  have h := wellFormedTest_1536_complete (i-1536) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_1536, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_1792 (i : Nat) := wellFormedTest (i+1792)
theorem wellFormedTest_1792_block_0 : Interval wellFormedTest_1792 0 16 :=
  interval_of_check wellFormedTest_1792 0 16 (by decide +kernel)

theorem wellFormedTest_1792_block_1 : Interval wellFormedTest_1792 16 32 :=
  interval_of_check wellFormedTest_1792 16 16 (by decide +kernel)

theorem wellFormedTest_1792_block_2 : Interval wellFormedTest_1792 32 48 :=
  interval_of_check wellFormedTest_1792 32 16 (by decide +kernel)

theorem wellFormedTest_1792_block_3 : Interval wellFormedTest_1792 48 64 :=
  interval_of_check wellFormedTest_1792 48 16 (by decide +kernel)

theorem wellFormedTest_1792_block_4 : Interval wellFormedTest_1792 64 80 :=
  interval_of_check wellFormedTest_1792 64 16 (by decide +kernel)

theorem wellFormedTest_1792_block_5 : Interval wellFormedTest_1792 80 96 :=
  interval_of_check wellFormedTest_1792 80 16 (by decide +kernel)

theorem wellFormedTest_1792_block_6 : Interval wellFormedTest_1792 96 112 :=
  interval_of_check wellFormedTest_1792 96 16 (by decide +kernel)

theorem wellFormedTest_1792_block_7 : Interval wellFormedTest_1792 112 128 :=
  interval_of_check wellFormedTest_1792 112 16 (by decide +kernel)

theorem wellFormedTest_1792_block_8 : Interval wellFormedTest_1792 128 144 :=
  interval_of_check wellFormedTest_1792 128 16 (by decide +kernel)

theorem wellFormedTest_1792_block_9 : Interval wellFormedTest_1792 144 160 :=
  interval_of_check wellFormedTest_1792 144 16 (by decide +kernel)

theorem wellFormedTest_1792_block_10 : Interval wellFormedTest_1792 160 176 :=
  interval_of_check wellFormedTest_1792 160 16 (by decide +kernel)

theorem wellFormedTest_1792_block_11 : Interval wellFormedTest_1792 176 192 :=
  interval_of_check wellFormedTest_1792 176 16 (by decide +kernel)

theorem wellFormedTest_1792_block_12 : Interval wellFormedTest_1792 192 208 :=
  interval_of_check wellFormedTest_1792 192 16 (by decide +kernel)

theorem wellFormedTest_1792_block_13 : Interval wellFormedTest_1792 208 224 :=
  interval_of_check wellFormedTest_1792 208 16 (by decide +kernel)

theorem wellFormedTest_1792_block_14 : Interval wellFormedTest_1792 224 240 :=
  interval_of_check wellFormedTest_1792 224 16 (by decide +kernel)

theorem wellFormedTest_1792_block_15 : Interval wellFormedTest_1792 240 256 :=
  interval_of_check wellFormedTest_1792 240 16 (by decide +kernel)

theorem wellFormedTest_1792_complete : Interval wellFormedTest_1792 0 256 :=
  (interval_append wellFormedTest_1792 0 128 256
  (interval_append wellFormedTest_1792 0 64 128
  (interval_append wellFormedTest_1792 0 32 64
  (interval_append wellFormedTest_1792 0 16 32
  wellFormedTest_1792_block_0
  wellFormedTest_1792_block_1)
  (interval_append wellFormedTest_1792 32 48 64
  wellFormedTest_1792_block_2
  wellFormedTest_1792_block_3))
  (interval_append wellFormedTest_1792 64 96 128
  (interval_append wellFormedTest_1792 64 80 96
  wellFormedTest_1792_block_4
  wellFormedTest_1792_block_5)
  (interval_append wellFormedTest_1792 96 112 128
  wellFormedTest_1792_block_6
  wellFormedTest_1792_block_7)))
  (interval_append wellFormedTest_1792 128 192 256
  (interval_append wellFormedTest_1792 128 160 192
  (interval_append wellFormedTest_1792 128 144 160
  wellFormedTest_1792_block_8
  wellFormedTest_1792_block_9)
  (interval_append wellFormedTest_1792 160 176 192
  wellFormedTest_1792_block_10
  wellFormedTest_1792_block_11))
  (interval_append wellFormedTest_1792 192 224 256
  (interval_append wellFormedTest_1792 192 208 224
  wellFormedTest_1792_block_12
  wellFormedTest_1792_block_13)
  (interval_append wellFormedTest_1792 224 240 256
  wellFormedTest_1792_block_14
  wellFormedTest_1792_block_15))))
theorem wellFormedTestInterval1792 : Interval wellFormedTest 1792 2048 := by
  intro i hlo hhi
  have h := wellFormedTest_1792_complete (i-1792) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_1792, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_2048 (i : Nat) := wellFormedTest (i+2048)
theorem wellFormedTest_2048_block_0 : Interval wellFormedTest_2048 0 16 :=
  interval_of_check wellFormedTest_2048 0 16 (by decide +kernel)

theorem wellFormedTest_2048_block_1 : Interval wellFormedTest_2048 16 32 :=
  interval_of_check wellFormedTest_2048 16 16 (by decide +kernel)

theorem wellFormedTest_2048_block_2 : Interval wellFormedTest_2048 32 48 :=
  interval_of_check wellFormedTest_2048 32 16 (by decide +kernel)

theorem wellFormedTest_2048_block_3 : Interval wellFormedTest_2048 48 64 :=
  interval_of_check wellFormedTest_2048 48 16 (by decide +kernel)

theorem wellFormedTest_2048_block_4 : Interval wellFormedTest_2048 64 80 :=
  interval_of_check wellFormedTest_2048 64 16 (by decide +kernel)

theorem wellFormedTest_2048_block_5 : Interval wellFormedTest_2048 80 96 :=
  interval_of_check wellFormedTest_2048 80 16 (by decide +kernel)

theorem wellFormedTest_2048_block_6 : Interval wellFormedTest_2048 96 112 :=
  interval_of_check wellFormedTest_2048 96 16 (by decide +kernel)

theorem wellFormedTest_2048_block_7 : Interval wellFormedTest_2048 112 128 :=
  interval_of_check wellFormedTest_2048 112 16 (by decide +kernel)

theorem wellFormedTest_2048_block_8 : Interval wellFormedTest_2048 128 144 :=
  interval_of_check wellFormedTest_2048 128 16 (by decide +kernel)

theorem wellFormedTest_2048_block_9 : Interval wellFormedTest_2048 144 160 :=
  interval_of_check wellFormedTest_2048 144 16 (by decide +kernel)

theorem wellFormedTest_2048_block_10 : Interval wellFormedTest_2048 160 176 :=
  interval_of_check wellFormedTest_2048 160 16 (by decide +kernel)

theorem wellFormedTest_2048_block_11 : Interval wellFormedTest_2048 176 192 :=
  interval_of_check wellFormedTest_2048 176 16 (by decide +kernel)

theorem wellFormedTest_2048_block_12 : Interval wellFormedTest_2048 192 208 :=
  interval_of_check wellFormedTest_2048 192 16 (by decide +kernel)

theorem wellFormedTest_2048_block_13 : Interval wellFormedTest_2048 208 224 :=
  interval_of_check wellFormedTest_2048 208 16 (by decide +kernel)

theorem wellFormedTest_2048_block_14 : Interval wellFormedTest_2048 224 240 :=
  interval_of_check wellFormedTest_2048 224 16 (by decide +kernel)

theorem wellFormedTest_2048_block_15 : Interval wellFormedTest_2048 240 256 :=
  interval_of_check wellFormedTest_2048 240 16 (by decide +kernel)

theorem wellFormedTest_2048_complete : Interval wellFormedTest_2048 0 256 :=
  (interval_append wellFormedTest_2048 0 128 256
  (interval_append wellFormedTest_2048 0 64 128
  (interval_append wellFormedTest_2048 0 32 64
  (interval_append wellFormedTest_2048 0 16 32
  wellFormedTest_2048_block_0
  wellFormedTest_2048_block_1)
  (interval_append wellFormedTest_2048 32 48 64
  wellFormedTest_2048_block_2
  wellFormedTest_2048_block_3))
  (interval_append wellFormedTest_2048 64 96 128
  (interval_append wellFormedTest_2048 64 80 96
  wellFormedTest_2048_block_4
  wellFormedTest_2048_block_5)
  (interval_append wellFormedTest_2048 96 112 128
  wellFormedTest_2048_block_6
  wellFormedTest_2048_block_7)))
  (interval_append wellFormedTest_2048 128 192 256
  (interval_append wellFormedTest_2048 128 160 192
  (interval_append wellFormedTest_2048 128 144 160
  wellFormedTest_2048_block_8
  wellFormedTest_2048_block_9)
  (interval_append wellFormedTest_2048 160 176 192
  wellFormedTest_2048_block_10
  wellFormedTest_2048_block_11))
  (interval_append wellFormedTest_2048 192 224 256
  (interval_append wellFormedTest_2048 192 208 224
  wellFormedTest_2048_block_12
  wellFormedTest_2048_block_13)
  (interval_append wellFormedTest_2048 224 240 256
  wellFormedTest_2048_block_14
  wellFormedTest_2048_block_15))))
theorem wellFormedTestInterval2048 : Interval wellFormedTest 2048 2304 := by
  intro i hlo hhi
  have h := wellFormedTest_2048_complete (i-2048) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_2048, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_2304 (i : Nat) := wellFormedTest (i+2304)
theorem wellFormedTest_2304_block_0 : Interval wellFormedTest_2304 0 16 :=
  interval_of_check wellFormedTest_2304 0 16 (by decide +kernel)

theorem wellFormedTest_2304_block_1 : Interval wellFormedTest_2304 16 32 :=
  interval_of_check wellFormedTest_2304 16 16 (by decide +kernel)

theorem wellFormedTest_2304_block_2 : Interval wellFormedTest_2304 32 48 :=
  interval_of_check wellFormedTest_2304 32 16 (by decide +kernel)

theorem wellFormedTest_2304_block_3 : Interval wellFormedTest_2304 48 64 :=
  interval_of_check wellFormedTest_2304 48 16 (by decide +kernel)

theorem wellFormedTest_2304_block_4 : Interval wellFormedTest_2304 64 80 :=
  interval_of_check wellFormedTest_2304 64 16 (by decide +kernel)

theorem wellFormedTest_2304_block_5 : Interval wellFormedTest_2304 80 96 :=
  interval_of_check wellFormedTest_2304 80 16 (by decide +kernel)

theorem wellFormedTest_2304_block_6 : Interval wellFormedTest_2304 96 112 :=
  interval_of_check wellFormedTest_2304 96 16 (by decide +kernel)

theorem wellFormedTest_2304_block_7 : Interval wellFormedTest_2304 112 128 :=
  interval_of_check wellFormedTest_2304 112 16 (by decide +kernel)

theorem wellFormedTest_2304_block_8 : Interval wellFormedTest_2304 128 144 :=
  interval_of_check wellFormedTest_2304 128 16 (by decide +kernel)

theorem wellFormedTest_2304_block_9 : Interval wellFormedTest_2304 144 160 :=
  interval_of_check wellFormedTest_2304 144 16 (by decide +kernel)

theorem wellFormedTest_2304_block_10 : Interval wellFormedTest_2304 160 176 :=
  interval_of_check wellFormedTest_2304 160 16 (by decide +kernel)

theorem wellFormedTest_2304_block_11 : Interval wellFormedTest_2304 176 192 :=
  interval_of_check wellFormedTest_2304 176 16 (by decide +kernel)

theorem wellFormedTest_2304_block_12 : Interval wellFormedTest_2304 192 208 :=
  interval_of_check wellFormedTest_2304 192 16 (by decide +kernel)

theorem wellFormedTest_2304_block_13 : Interval wellFormedTest_2304 208 224 :=
  interval_of_check wellFormedTest_2304 208 16 (by decide +kernel)

theorem wellFormedTest_2304_block_14 : Interval wellFormedTest_2304 224 240 :=
  interval_of_check wellFormedTest_2304 224 16 (by decide +kernel)

theorem wellFormedTest_2304_block_15 : Interval wellFormedTest_2304 240 256 :=
  interval_of_check wellFormedTest_2304 240 16 (by decide +kernel)

theorem wellFormedTest_2304_complete : Interval wellFormedTest_2304 0 256 :=
  (interval_append wellFormedTest_2304 0 128 256
  (interval_append wellFormedTest_2304 0 64 128
  (interval_append wellFormedTest_2304 0 32 64
  (interval_append wellFormedTest_2304 0 16 32
  wellFormedTest_2304_block_0
  wellFormedTest_2304_block_1)
  (interval_append wellFormedTest_2304 32 48 64
  wellFormedTest_2304_block_2
  wellFormedTest_2304_block_3))
  (interval_append wellFormedTest_2304 64 96 128
  (interval_append wellFormedTest_2304 64 80 96
  wellFormedTest_2304_block_4
  wellFormedTest_2304_block_5)
  (interval_append wellFormedTest_2304 96 112 128
  wellFormedTest_2304_block_6
  wellFormedTest_2304_block_7)))
  (interval_append wellFormedTest_2304 128 192 256
  (interval_append wellFormedTest_2304 128 160 192
  (interval_append wellFormedTest_2304 128 144 160
  wellFormedTest_2304_block_8
  wellFormedTest_2304_block_9)
  (interval_append wellFormedTest_2304 160 176 192
  wellFormedTest_2304_block_10
  wellFormedTest_2304_block_11))
  (interval_append wellFormedTest_2304 192 224 256
  (interval_append wellFormedTest_2304 192 208 224
  wellFormedTest_2304_block_12
  wellFormedTest_2304_block_13)
  (interval_append wellFormedTest_2304 224 240 256
  wellFormedTest_2304_block_14
  wellFormedTest_2304_block_15))))
theorem wellFormedTestInterval2304 : Interval wellFormedTest 2304 2560 := by
  intro i hlo hhi
  have h := wellFormedTest_2304_complete (i-2304) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_2304, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed010 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_2560 (i : Nat) := wellFormedTest (i+2560)
theorem wellFormedTest_2560_block_0 : Interval wellFormedTest_2560 0 16 :=
  interval_of_check wellFormedTest_2560 0 16 (by decide +kernel)

theorem wellFormedTest_2560_block_1 : Interval wellFormedTest_2560 16 32 :=
  interval_of_check wellFormedTest_2560 16 16 (by decide +kernel)

theorem wellFormedTest_2560_block_2 : Interval wellFormedTest_2560 32 48 :=
  interval_of_check wellFormedTest_2560 32 16 (by decide +kernel)

theorem wellFormedTest_2560_block_3 : Interval wellFormedTest_2560 48 64 :=
  interval_of_check wellFormedTest_2560 48 16 (by decide +kernel)

theorem wellFormedTest_2560_block_4 : Interval wellFormedTest_2560 64 80 :=
  interval_of_check wellFormedTest_2560 64 16 (by decide +kernel)

theorem wellFormedTest_2560_block_5 : Interval wellFormedTest_2560 80 96 :=
  interval_of_check wellFormedTest_2560 80 16 (by decide +kernel)

theorem wellFormedTest_2560_block_6 : Interval wellFormedTest_2560 96 112 :=
  interval_of_check wellFormedTest_2560 96 16 (by decide +kernel)

theorem wellFormedTest_2560_block_7 : Interval wellFormedTest_2560 112 128 :=
  interval_of_check wellFormedTest_2560 112 16 (by decide +kernel)

theorem wellFormedTest_2560_block_8 : Interval wellFormedTest_2560 128 144 :=
  interval_of_check wellFormedTest_2560 128 16 (by decide +kernel)

theorem wellFormedTest_2560_block_9 : Interval wellFormedTest_2560 144 160 :=
  interval_of_check wellFormedTest_2560 144 16 (by decide +kernel)

theorem wellFormedTest_2560_block_10 : Interval wellFormedTest_2560 160 176 :=
  interval_of_check wellFormedTest_2560 160 16 (by decide +kernel)

theorem wellFormedTest_2560_block_11 : Interval wellFormedTest_2560 176 192 :=
  interval_of_check wellFormedTest_2560 176 16 (by decide +kernel)

theorem wellFormedTest_2560_block_12 : Interval wellFormedTest_2560 192 208 :=
  interval_of_check wellFormedTest_2560 192 16 (by decide +kernel)

theorem wellFormedTest_2560_block_13 : Interval wellFormedTest_2560 208 224 :=
  interval_of_check wellFormedTest_2560 208 16 (by decide +kernel)

theorem wellFormedTest_2560_block_14 : Interval wellFormedTest_2560 224 240 :=
  interval_of_check wellFormedTest_2560 224 16 (by decide +kernel)

theorem wellFormedTest_2560_block_15 : Interval wellFormedTest_2560 240 256 :=
  interval_of_check wellFormedTest_2560 240 16 (by decide +kernel)

theorem wellFormedTest_2560_complete : Interval wellFormedTest_2560 0 256 :=
  (interval_append wellFormedTest_2560 0 128 256
  (interval_append wellFormedTest_2560 0 64 128
  (interval_append wellFormedTest_2560 0 32 64
  (interval_append wellFormedTest_2560 0 16 32
  wellFormedTest_2560_block_0
  wellFormedTest_2560_block_1)
  (interval_append wellFormedTest_2560 32 48 64
  wellFormedTest_2560_block_2
  wellFormedTest_2560_block_3))
  (interval_append wellFormedTest_2560 64 96 128
  (interval_append wellFormedTest_2560 64 80 96
  wellFormedTest_2560_block_4
  wellFormedTest_2560_block_5)
  (interval_append wellFormedTest_2560 96 112 128
  wellFormedTest_2560_block_6
  wellFormedTest_2560_block_7)))
  (interval_append wellFormedTest_2560 128 192 256
  (interval_append wellFormedTest_2560 128 160 192
  (interval_append wellFormedTest_2560 128 144 160
  wellFormedTest_2560_block_8
  wellFormedTest_2560_block_9)
  (interval_append wellFormedTest_2560 160 176 192
  wellFormedTest_2560_block_10
  wellFormedTest_2560_block_11))
  (interval_append wellFormedTest_2560 192 224 256
  (interval_append wellFormedTest_2560 192 208 224
  wellFormedTest_2560_block_12
  wellFormedTest_2560_block_13)
  (interval_append wellFormedTest_2560 224 240 256
  wellFormedTest_2560_block_14
  wellFormedTest_2560_block_15))))
theorem wellFormedTestInterval2560 : Interval wellFormedTest 2560 2816 := by
  intro i hlo hhi
  have h := wellFormedTest_2560_complete (i-2560) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_2560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed011 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_2816 (i : Nat) := wellFormedTest (i+2816)
theorem wellFormedTest_2816_block_0 : Interval wellFormedTest_2816 0 16 :=
  interval_of_check wellFormedTest_2816 0 16 (by decide +kernel)

theorem wellFormedTest_2816_block_1 : Interval wellFormedTest_2816 16 32 :=
  interval_of_check wellFormedTest_2816 16 16 (by decide +kernel)

theorem wellFormedTest_2816_block_2 : Interval wellFormedTest_2816 32 48 :=
  interval_of_check wellFormedTest_2816 32 16 (by decide +kernel)

theorem wellFormedTest_2816_block_3 : Interval wellFormedTest_2816 48 64 :=
  interval_of_check wellFormedTest_2816 48 16 (by decide +kernel)

theorem wellFormedTest_2816_block_4 : Interval wellFormedTest_2816 64 80 :=
  interval_of_check wellFormedTest_2816 64 16 (by decide +kernel)

theorem wellFormedTest_2816_block_5 : Interval wellFormedTest_2816 80 96 :=
  interval_of_check wellFormedTest_2816 80 16 (by decide +kernel)

theorem wellFormedTest_2816_block_6 : Interval wellFormedTest_2816 96 112 :=
  interval_of_check wellFormedTest_2816 96 16 (by decide +kernel)

theorem wellFormedTest_2816_block_7 : Interval wellFormedTest_2816 112 128 :=
  interval_of_check wellFormedTest_2816 112 16 (by decide +kernel)

theorem wellFormedTest_2816_block_8 : Interval wellFormedTest_2816 128 144 :=
  interval_of_check wellFormedTest_2816 128 16 (by decide +kernel)

theorem wellFormedTest_2816_block_9 : Interval wellFormedTest_2816 144 160 :=
  interval_of_check wellFormedTest_2816 144 16 (by decide +kernel)

theorem wellFormedTest_2816_block_10 : Interval wellFormedTest_2816 160 176 :=
  interval_of_check wellFormedTest_2816 160 16 (by decide +kernel)

theorem wellFormedTest_2816_block_11 : Interval wellFormedTest_2816 176 192 :=
  interval_of_check wellFormedTest_2816 176 16 (by decide +kernel)

theorem wellFormedTest_2816_block_12 : Interval wellFormedTest_2816 192 208 :=
  interval_of_check wellFormedTest_2816 192 16 (by decide +kernel)

theorem wellFormedTest_2816_block_13 : Interval wellFormedTest_2816 208 224 :=
  interval_of_check wellFormedTest_2816 208 16 (by decide +kernel)

theorem wellFormedTest_2816_block_14 : Interval wellFormedTest_2816 224 240 :=
  interval_of_check wellFormedTest_2816 224 16 (by decide +kernel)

theorem wellFormedTest_2816_block_15 : Interval wellFormedTest_2816 240 256 :=
  interval_of_check wellFormedTest_2816 240 16 (by decide +kernel)

theorem wellFormedTest_2816_complete : Interval wellFormedTest_2816 0 256 :=
  (interval_append wellFormedTest_2816 0 128 256
  (interval_append wellFormedTest_2816 0 64 128
  (interval_append wellFormedTest_2816 0 32 64
  (interval_append wellFormedTest_2816 0 16 32
  wellFormedTest_2816_block_0
  wellFormedTest_2816_block_1)
  (interval_append wellFormedTest_2816 32 48 64
  wellFormedTest_2816_block_2
  wellFormedTest_2816_block_3))
  (interval_append wellFormedTest_2816 64 96 128
  (interval_append wellFormedTest_2816 64 80 96
  wellFormedTest_2816_block_4
  wellFormedTest_2816_block_5)
  (interval_append wellFormedTest_2816 96 112 128
  wellFormedTest_2816_block_6
  wellFormedTest_2816_block_7)))
  (interval_append wellFormedTest_2816 128 192 256
  (interval_append wellFormedTest_2816 128 160 192
  (interval_append wellFormedTest_2816 128 144 160
  wellFormedTest_2816_block_8
  wellFormedTest_2816_block_9)
  (interval_append wellFormedTest_2816 160 176 192
  wellFormedTest_2816_block_10
  wellFormedTest_2816_block_11))
  (interval_append wellFormedTest_2816 192 224 256
  (interval_append wellFormedTest_2816 192 208 224
  wellFormedTest_2816_block_12
  wellFormedTest_2816_block_13)
  (interval_append wellFormedTest_2816 224 240 256
  wellFormedTest_2816_block_14
  wellFormedTest_2816_block_15))))
theorem wellFormedTestInterval2816 : Interval wellFormedTest 2816 3072 := by
  intro i hlo hhi
  have h := wellFormedTest_2816_complete (i-2816) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_2816, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
