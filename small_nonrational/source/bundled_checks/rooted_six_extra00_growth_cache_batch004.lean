module
prelude
public import RootedSixExtra00GrowthCacheData

/- RootedSixExtra00GrowthCacheBad029 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheBad030 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheBad031 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheBad032 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheBad033 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheBad034 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

theorem badTest_8704_complete : Interval badTest_8704 0 120 :=
  (interval_append badTest_8704 0 56 120
  (interval_append badTest_8704 0 24 56
  (interval_append badTest_8704 0 8 24
  badTest_8704_block_0
  (interval_append badTest_8704 8 16 24
  badTest_8704_block_1
  badTest_8704_block_2))
  (interval_append badTest_8704 24 40 56
  (interval_append badTest_8704 24 32 40
  badTest_8704_block_3
  badTest_8704_block_4)
  (interval_append badTest_8704 40 48 56
  badTest_8704_block_5
  badTest_8704_block_6)))
  (interval_append badTest_8704 56 88 120
  (interval_append badTest_8704 56 72 88
  (interval_append badTest_8704 56 64 72
  badTest_8704_block_7
  badTest_8704_block_8)
  (interval_append badTest_8704 72 80 88
  badTest_8704_block_9
  badTest_8704_block_10))
  (interval_append badTest_8704 88 104 120
  (interval_append badTest_8704 88 96 104
  badTest_8704_block_11
  badTest_8704_block_12)
  (interval_append badTest_8704 104 112 120
  badTest_8704_block_13
  badTest_8704_block_14))))
theorem badTestInterval8704 : Interval badTest 8704 8824 := by
  intro i hlo hhi
  have h := badTest_8704_complete (i-8704) (Nat.zero_le _) (by omega)
  simpa only [badTest_8704, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
