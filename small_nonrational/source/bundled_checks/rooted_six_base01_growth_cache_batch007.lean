module
prelude
public import RootedSixBase01GrowthCacheData

/- RootedSixBase01GrowthCacheBad052 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_13312 (i : Nat) := badTest (i+13312)
theorem badTest_13312_block_0 : Interval badTest_13312 0 8 :=
  interval_of_check badTest_13312 0 8 (by decide +kernel)

theorem badTest_13312_block_1 : Interval badTest_13312 8 16 :=
  interval_of_check badTest_13312 8 8 (by decide +kernel)

theorem badTest_13312_block_2 : Interval badTest_13312 16 24 :=
  interval_of_check badTest_13312 16 8 (by decide +kernel)

theorem badTest_13312_block_3 : Interval badTest_13312 24 32 :=
  interval_of_check badTest_13312 24 8 (by decide +kernel)

theorem badTest_13312_block_4 : Interval badTest_13312 32 40 :=
  interval_of_check badTest_13312 32 8 (by decide +kernel)

theorem badTest_13312_block_5 : Interval badTest_13312 40 48 :=
  interval_of_check badTest_13312 40 8 (by decide +kernel)

theorem badTest_13312_block_6 : Interval badTest_13312 48 56 :=
  interval_of_check badTest_13312 48 8 (by decide +kernel)

theorem badTest_13312_block_7 : Interval badTest_13312 56 64 :=
  interval_of_check badTest_13312 56 8 (by decide +kernel)

theorem badTest_13312_block_8 : Interval badTest_13312 64 72 :=
  interval_of_check badTest_13312 64 8 (by decide +kernel)

theorem badTest_13312_block_9 : Interval badTest_13312 72 80 :=
  interval_of_check badTest_13312 72 8 (by decide +kernel)

theorem badTest_13312_block_10 : Interval badTest_13312 80 88 :=
  interval_of_check badTest_13312 80 8 (by decide +kernel)

theorem badTest_13312_block_11 : Interval badTest_13312 88 96 :=
  interval_of_check badTest_13312 88 8 (by decide +kernel)

theorem badTest_13312_block_12 : Interval badTest_13312 96 104 :=
  interval_of_check badTest_13312 96 8 (by decide +kernel)

theorem badTest_13312_block_13 : Interval badTest_13312 104 112 :=
  interval_of_check badTest_13312 104 8 (by decide +kernel)

theorem badTest_13312_block_14 : Interval badTest_13312 112 120 :=
  interval_of_check badTest_13312 112 8 (by decide +kernel)

theorem badTest_13312_block_15 : Interval badTest_13312 120 128 :=
  interval_of_check badTest_13312 120 8 (by decide +kernel)

theorem badTest_13312_block_16 : Interval badTest_13312 128 136 :=
  interval_of_check badTest_13312 128 8 (by decide +kernel)

theorem badTest_13312_block_17 : Interval badTest_13312 136 144 :=
  interval_of_check badTest_13312 136 8 (by decide +kernel)

theorem badTest_13312_block_18 : Interval badTest_13312 144 152 :=
  interval_of_check badTest_13312 144 8 (by decide +kernel)

theorem badTest_13312_block_19 : Interval badTest_13312 152 160 :=
  interval_of_check badTest_13312 152 8 (by decide +kernel)

theorem badTest_13312_block_20 : Interval badTest_13312 160 168 :=
  interval_of_check badTest_13312 160 8 (by decide +kernel)

theorem badTest_13312_block_21 : Interval badTest_13312 168 176 :=
  interval_of_check badTest_13312 168 8 (by decide +kernel)

theorem badTest_13312_block_22 : Interval badTest_13312 176 184 :=
  interval_of_check badTest_13312 176 8 (by decide +kernel)

theorem badTest_13312_block_23 : Interval badTest_13312 184 192 :=
  interval_of_check badTest_13312 184 8 (by decide +kernel)

theorem badTest_13312_block_24 : Interval badTest_13312 192 200 :=
  interval_of_check badTest_13312 192 8 (by decide +kernel)

theorem badTest_13312_block_25 : Interval badTest_13312 200 208 :=
  interval_of_check badTest_13312 200 8 (by decide +kernel)

theorem badTest_13312_block_26 : Interval badTest_13312 208 216 :=
  interval_of_check badTest_13312 208 8 (by decide +kernel)

theorem badTest_13312_block_27 : Interval badTest_13312 216 224 :=
  interval_of_check badTest_13312 216 8 (by decide +kernel)

theorem badTest_13312_block_28 : Interval badTest_13312 224 232 :=
  interval_of_check badTest_13312 224 8 (by decide +kernel)

theorem badTest_13312_block_29 : Interval badTest_13312 232 240 :=
  interval_of_check badTest_13312 232 8 (by decide +kernel)

theorem badTest_13312_block_30 : Interval badTest_13312 240 248 :=
  interval_of_check badTest_13312 240 8 (by decide +kernel)

theorem badTest_13312_block_31 : Interval badTest_13312 248 256 :=
  interval_of_check badTest_13312 248 8 (by decide +kernel)

theorem badTest_13312_complete : Interval badTest_13312 0 256 :=
  (interval_append badTest_13312 0 128 256
  (interval_append badTest_13312 0 64 128
  (interval_append badTest_13312 0 32 64
  (interval_append badTest_13312 0 16 32
  (interval_append badTest_13312 0 8 16
  badTest_13312_block_0
  badTest_13312_block_1)
  (interval_append badTest_13312 16 24 32
  badTest_13312_block_2
  badTest_13312_block_3))
  (interval_append badTest_13312 32 48 64
  (interval_append badTest_13312 32 40 48
  badTest_13312_block_4
  badTest_13312_block_5)
  (interval_append badTest_13312 48 56 64
  badTest_13312_block_6
  badTest_13312_block_7)))
  (interval_append badTest_13312 64 96 128
  (interval_append badTest_13312 64 80 96
  (interval_append badTest_13312 64 72 80
  badTest_13312_block_8
  badTest_13312_block_9)
  (interval_append badTest_13312 80 88 96
  badTest_13312_block_10
  badTest_13312_block_11))
  (interval_append badTest_13312 96 112 128
  (interval_append badTest_13312 96 104 112
  badTest_13312_block_12
  badTest_13312_block_13)
  (interval_append badTest_13312 112 120 128
  badTest_13312_block_14
  badTest_13312_block_15))))
  (interval_append badTest_13312 128 192 256
  (interval_append badTest_13312 128 160 192
  (interval_append badTest_13312 128 144 160
  (interval_append badTest_13312 128 136 144
  badTest_13312_block_16
  badTest_13312_block_17)
  (interval_append badTest_13312 144 152 160
  badTest_13312_block_18
  badTest_13312_block_19))
  (interval_append badTest_13312 160 176 192
  (interval_append badTest_13312 160 168 176
  badTest_13312_block_20
  badTest_13312_block_21)
  (interval_append badTest_13312 176 184 192
  badTest_13312_block_22
  badTest_13312_block_23)))
  (interval_append badTest_13312 192 224 256
  (interval_append badTest_13312 192 208 224
  (interval_append badTest_13312 192 200 208
  badTest_13312_block_24
  badTest_13312_block_25)
  (interval_append badTest_13312 208 216 224
  badTest_13312_block_26
  badTest_13312_block_27))
  (interval_append badTest_13312 224 240 256
  (interval_append badTest_13312 224 232 240
  badTest_13312_block_28
  badTest_13312_block_29)
  (interval_append badTest_13312 240 248 256
  badTest_13312_block_30
  badTest_13312_block_31)))))
theorem badTestInterval13312 : Interval badTest 13312 13568 := by
  intro i hlo hhi
  have h := badTest_13312_complete (i-13312) (Nat.zero_le _) (by omega)
  simpa only [badTest_13312, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad053 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_13568 (i : Nat) := badTest (i+13568)
theorem badTest_13568_block_0 : Interval badTest_13568 0 8 :=
  interval_of_check badTest_13568 0 8 (by decide +kernel)

theorem badTest_13568_block_1 : Interval badTest_13568 8 16 :=
  interval_of_check badTest_13568 8 8 (by decide +kernel)

theorem badTest_13568_block_2 : Interval badTest_13568 16 24 :=
  interval_of_check badTest_13568 16 8 (by decide +kernel)

theorem badTest_13568_block_3 : Interval badTest_13568 24 32 :=
  interval_of_check badTest_13568 24 8 (by decide +kernel)

theorem badTest_13568_block_4 : Interval badTest_13568 32 40 :=
  interval_of_check badTest_13568 32 8 (by decide +kernel)

theorem badTest_13568_block_5 : Interval badTest_13568 40 48 :=
  interval_of_check badTest_13568 40 8 (by decide +kernel)

theorem badTest_13568_block_6 : Interval badTest_13568 48 56 :=
  interval_of_check badTest_13568 48 8 (by decide +kernel)

theorem badTest_13568_block_7 : Interval badTest_13568 56 64 :=
  interval_of_check badTest_13568 56 8 (by decide +kernel)

theorem badTest_13568_block_8 : Interval badTest_13568 64 72 :=
  interval_of_check badTest_13568 64 8 (by decide +kernel)

theorem badTest_13568_block_9 : Interval badTest_13568 72 80 :=
  interval_of_check badTest_13568 72 8 (by decide +kernel)

theorem badTest_13568_block_10 : Interval badTest_13568 80 88 :=
  interval_of_check badTest_13568 80 8 (by decide +kernel)

theorem badTest_13568_block_11 : Interval badTest_13568 88 96 :=
  interval_of_check badTest_13568 88 8 (by decide +kernel)

theorem badTest_13568_block_12 : Interval badTest_13568 96 104 :=
  interval_of_check badTest_13568 96 8 (by decide +kernel)

theorem badTest_13568_block_13 : Interval badTest_13568 104 112 :=
  interval_of_check badTest_13568 104 8 (by decide +kernel)

theorem badTest_13568_block_14 : Interval badTest_13568 112 120 :=
  interval_of_check badTest_13568 112 8 (by decide +kernel)

theorem badTest_13568_block_15 : Interval badTest_13568 120 128 :=
  interval_of_check badTest_13568 120 8 (by decide +kernel)

theorem badTest_13568_block_16 : Interval badTest_13568 128 136 :=
  interval_of_check badTest_13568 128 8 (by decide +kernel)

theorem badTest_13568_block_17 : Interval badTest_13568 136 144 :=
  interval_of_check badTest_13568 136 8 (by decide +kernel)

theorem badTest_13568_block_18 : Interval badTest_13568 144 152 :=
  interval_of_check badTest_13568 144 8 (by decide +kernel)

theorem badTest_13568_block_19 : Interval badTest_13568 152 160 :=
  interval_of_check badTest_13568 152 8 (by decide +kernel)

theorem badTest_13568_block_20 : Interval badTest_13568 160 168 :=
  interval_of_check badTest_13568 160 8 (by decide +kernel)

theorem badTest_13568_block_21 : Interval badTest_13568 168 176 :=
  interval_of_check badTest_13568 168 8 (by decide +kernel)

theorem badTest_13568_block_22 : Interval badTest_13568 176 184 :=
  interval_of_check badTest_13568 176 8 (by decide +kernel)

theorem badTest_13568_block_23 : Interval badTest_13568 184 192 :=
  interval_of_check badTest_13568 184 8 (by decide +kernel)

theorem badTest_13568_block_24 : Interval badTest_13568 192 200 :=
  interval_of_check badTest_13568 192 8 (by decide +kernel)

theorem badTest_13568_block_25 : Interval badTest_13568 200 208 :=
  interval_of_check badTest_13568 200 8 (by decide +kernel)

theorem badTest_13568_block_26 : Interval badTest_13568 208 216 :=
  interval_of_check badTest_13568 208 8 (by decide +kernel)

theorem badTest_13568_block_27 : Interval badTest_13568 216 224 :=
  interval_of_check badTest_13568 216 8 (by decide +kernel)

theorem badTest_13568_block_28 : Interval badTest_13568 224 232 :=
  interval_of_check badTest_13568 224 8 (by decide +kernel)

theorem badTest_13568_block_29 : Interval badTest_13568 232 240 :=
  interval_of_check badTest_13568 232 8 (by decide +kernel)

theorem badTest_13568_block_30 : Interval badTest_13568 240 248 :=
  interval_of_check badTest_13568 240 8 (by decide +kernel)

theorem badTest_13568_block_31 : Interval badTest_13568 248 256 :=
  interval_of_check badTest_13568 248 8 (by decide +kernel)

theorem badTest_13568_complete : Interval badTest_13568 0 256 :=
  (interval_append badTest_13568 0 128 256
  (interval_append badTest_13568 0 64 128
  (interval_append badTest_13568 0 32 64
  (interval_append badTest_13568 0 16 32
  (interval_append badTest_13568 0 8 16
  badTest_13568_block_0
  badTest_13568_block_1)
  (interval_append badTest_13568 16 24 32
  badTest_13568_block_2
  badTest_13568_block_3))
  (interval_append badTest_13568 32 48 64
  (interval_append badTest_13568 32 40 48
  badTest_13568_block_4
  badTest_13568_block_5)
  (interval_append badTest_13568 48 56 64
  badTest_13568_block_6
  badTest_13568_block_7)))
  (interval_append badTest_13568 64 96 128
  (interval_append badTest_13568 64 80 96
  (interval_append badTest_13568 64 72 80
  badTest_13568_block_8
  badTest_13568_block_9)
  (interval_append badTest_13568 80 88 96
  badTest_13568_block_10
  badTest_13568_block_11))
  (interval_append badTest_13568 96 112 128
  (interval_append badTest_13568 96 104 112
  badTest_13568_block_12
  badTest_13568_block_13)
  (interval_append badTest_13568 112 120 128
  badTest_13568_block_14
  badTest_13568_block_15))))
  (interval_append badTest_13568 128 192 256
  (interval_append badTest_13568 128 160 192
  (interval_append badTest_13568 128 144 160
  (interval_append badTest_13568 128 136 144
  badTest_13568_block_16
  badTest_13568_block_17)
  (interval_append badTest_13568 144 152 160
  badTest_13568_block_18
  badTest_13568_block_19))
  (interval_append badTest_13568 160 176 192
  (interval_append badTest_13568 160 168 176
  badTest_13568_block_20
  badTest_13568_block_21)
  (interval_append badTest_13568 176 184 192
  badTest_13568_block_22
  badTest_13568_block_23)))
  (interval_append badTest_13568 192 224 256
  (interval_append badTest_13568 192 208 224
  (interval_append badTest_13568 192 200 208
  badTest_13568_block_24
  badTest_13568_block_25)
  (interval_append badTest_13568 208 216 224
  badTest_13568_block_26
  badTest_13568_block_27))
  (interval_append badTest_13568 224 240 256
  (interval_append badTest_13568 224 232 240
  badTest_13568_block_28
  badTest_13568_block_29)
  (interval_append badTest_13568 240 248 256
  badTest_13568_block_30
  badTest_13568_block_31)))))
theorem badTestInterval13568 : Interval badTest 13568 13824 := by
  intro i hlo hhi
  have h := badTest_13568_complete (i-13568) (Nat.zero_le _) (by omega)
  simpa only [badTest_13568, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad054 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_13824 (i : Nat) := badTest (i+13824)
theorem badTest_13824_block_0 : Interval badTest_13824 0 8 :=
  interval_of_check badTest_13824 0 8 (by decide +kernel)

theorem badTest_13824_block_1 : Interval badTest_13824 8 16 :=
  interval_of_check badTest_13824 8 8 (by decide +kernel)

theorem badTest_13824_block_2 : Interval badTest_13824 16 24 :=
  interval_of_check badTest_13824 16 8 (by decide +kernel)

theorem badTest_13824_block_3 : Interval badTest_13824 24 32 :=
  interval_of_check badTest_13824 24 8 (by decide +kernel)

theorem badTest_13824_block_4 : Interval badTest_13824 32 40 :=
  interval_of_check badTest_13824 32 8 (by decide +kernel)

theorem badTest_13824_block_5 : Interval badTest_13824 40 48 :=
  interval_of_check badTest_13824 40 8 (by decide +kernel)

theorem badTest_13824_block_6 : Interval badTest_13824 48 56 :=
  interval_of_check badTest_13824 48 8 (by decide +kernel)

theorem badTest_13824_block_7 : Interval badTest_13824 56 64 :=
  interval_of_check badTest_13824 56 8 (by decide +kernel)

theorem badTest_13824_block_8 : Interval badTest_13824 64 72 :=
  interval_of_check badTest_13824 64 8 (by decide +kernel)

theorem badTest_13824_block_9 : Interval badTest_13824 72 80 :=
  interval_of_check badTest_13824 72 8 (by decide +kernel)

theorem badTest_13824_block_10 : Interval badTest_13824 80 88 :=
  interval_of_check badTest_13824 80 8 (by decide +kernel)

theorem badTest_13824_block_11 : Interval badTest_13824 88 96 :=
  interval_of_check badTest_13824 88 8 (by decide +kernel)

theorem badTest_13824_block_12 : Interval badTest_13824 96 104 :=
  interval_of_check badTest_13824 96 8 (by decide +kernel)

theorem badTest_13824_block_13 : Interval badTest_13824 104 112 :=
  interval_of_check badTest_13824 104 8 (by decide +kernel)

theorem badTest_13824_block_14 : Interval badTest_13824 112 120 :=
  interval_of_check badTest_13824 112 8 (by decide +kernel)

theorem badTest_13824_block_15 : Interval badTest_13824 120 128 :=
  interval_of_check badTest_13824 120 8 (by decide +kernel)

theorem badTest_13824_block_16 : Interval badTest_13824 128 136 :=
  interval_of_check badTest_13824 128 8 (by decide +kernel)

theorem badTest_13824_block_17 : Interval badTest_13824 136 144 :=
  interval_of_check badTest_13824 136 8 (by decide +kernel)

theorem badTest_13824_block_18 : Interval badTest_13824 144 152 :=
  interval_of_check badTest_13824 144 8 (by decide +kernel)

theorem badTest_13824_block_19 : Interval badTest_13824 152 160 :=
  interval_of_check badTest_13824 152 8 (by decide +kernel)

theorem badTest_13824_block_20 : Interval badTest_13824 160 168 :=
  interval_of_check badTest_13824 160 8 (by decide +kernel)

theorem badTest_13824_block_21 : Interval badTest_13824 168 176 :=
  interval_of_check badTest_13824 168 8 (by decide +kernel)

theorem badTest_13824_block_22 : Interval badTest_13824 176 184 :=
  interval_of_check badTest_13824 176 8 (by decide +kernel)

theorem badTest_13824_block_23 : Interval badTest_13824 184 192 :=
  interval_of_check badTest_13824 184 8 (by decide +kernel)

theorem badTest_13824_block_24 : Interval badTest_13824 192 200 :=
  interval_of_check badTest_13824 192 8 (by decide +kernel)

theorem badTest_13824_block_25 : Interval badTest_13824 200 208 :=
  interval_of_check badTest_13824 200 8 (by decide +kernel)

theorem badTest_13824_block_26 : Interval badTest_13824 208 216 :=
  interval_of_check badTest_13824 208 8 (by decide +kernel)

theorem badTest_13824_block_27 : Interval badTest_13824 216 224 :=
  interval_of_check badTest_13824 216 8 (by decide +kernel)

theorem badTest_13824_block_28 : Interval badTest_13824 224 232 :=
  interval_of_check badTest_13824 224 8 (by decide +kernel)

theorem badTest_13824_block_29 : Interval badTest_13824 232 240 :=
  interval_of_check badTest_13824 232 8 (by decide +kernel)

theorem badTest_13824_block_30 : Interval badTest_13824 240 248 :=
  interval_of_check badTest_13824 240 8 (by decide +kernel)

theorem badTest_13824_block_31 : Interval badTest_13824 248 256 :=
  interval_of_check badTest_13824 248 8 (by decide +kernel)

theorem badTest_13824_complete : Interval badTest_13824 0 256 :=
  (interval_append badTest_13824 0 128 256
  (interval_append badTest_13824 0 64 128
  (interval_append badTest_13824 0 32 64
  (interval_append badTest_13824 0 16 32
  (interval_append badTest_13824 0 8 16
  badTest_13824_block_0
  badTest_13824_block_1)
  (interval_append badTest_13824 16 24 32
  badTest_13824_block_2
  badTest_13824_block_3))
  (interval_append badTest_13824 32 48 64
  (interval_append badTest_13824 32 40 48
  badTest_13824_block_4
  badTest_13824_block_5)
  (interval_append badTest_13824 48 56 64
  badTest_13824_block_6
  badTest_13824_block_7)))
  (interval_append badTest_13824 64 96 128
  (interval_append badTest_13824 64 80 96
  (interval_append badTest_13824 64 72 80
  badTest_13824_block_8
  badTest_13824_block_9)
  (interval_append badTest_13824 80 88 96
  badTest_13824_block_10
  badTest_13824_block_11))
  (interval_append badTest_13824 96 112 128
  (interval_append badTest_13824 96 104 112
  badTest_13824_block_12
  badTest_13824_block_13)
  (interval_append badTest_13824 112 120 128
  badTest_13824_block_14
  badTest_13824_block_15))))
  (interval_append badTest_13824 128 192 256
  (interval_append badTest_13824 128 160 192
  (interval_append badTest_13824 128 144 160
  (interval_append badTest_13824 128 136 144
  badTest_13824_block_16
  badTest_13824_block_17)
  (interval_append badTest_13824 144 152 160
  badTest_13824_block_18
  badTest_13824_block_19))
  (interval_append badTest_13824 160 176 192
  (interval_append badTest_13824 160 168 176
  badTest_13824_block_20
  badTest_13824_block_21)
  (interval_append badTest_13824 176 184 192
  badTest_13824_block_22
  badTest_13824_block_23)))
  (interval_append badTest_13824 192 224 256
  (interval_append badTest_13824 192 208 224
  (interval_append badTest_13824 192 200 208
  badTest_13824_block_24
  badTest_13824_block_25)
  (interval_append badTest_13824 208 216 224
  badTest_13824_block_26
  badTest_13824_block_27))
  (interval_append badTest_13824 224 240 256
  (interval_append badTest_13824 224 232 240
  badTest_13824_block_28
  badTest_13824_block_29)
  (interval_append badTest_13824 240 248 256
  badTest_13824_block_30
  badTest_13824_block_31)))))
theorem badTestInterval13824 : Interval badTest 13824 14080 := by
  intro i hlo hhi
  have h := badTest_13824_complete (i-13824) (Nat.zero_le _) (by omega)
  simpa only [badTest_13824, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad055 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_14080 (i : Nat) := badTest (i+14080)
theorem badTest_14080_block_0 : Interval badTest_14080 0 8 :=
  interval_of_check badTest_14080 0 8 (by decide +kernel)

theorem badTest_14080_block_1 : Interval badTest_14080 8 16 :=
  interval_of_check badTest_14080 8 8 (by decide +kernel)

theorem badTest_14080_block_2 : Interval badTest_14080 16 24 :=
  interval_of_check badTest_14080 16 8 (by decide +kernel)

theorem badTest_14080_block_3 : Interval badTest_14080 24 32 :=
  interval_of_check badTest_14080 24 8 (by decide +kernel)

theorem badTest_14080_block_4 : Interval badTest_14080 32 40 :=
  interval_of_check badTest_14080 32 8 (by decide +kernel)

theorem badTest_14080_block_5 : Interval badTest_14080 40 48 :=
  interval_of_check badTest_14080 40 8 (by decide +kernel)

theorem badTest_14080_block_6 : Interval badTest_14080 48 56 :=
  interval_of_check badTest_14080 48 8 (by decide +kernel)

theorem badTest_14080_block_7 : Interval badTest_14080 56 64 :=
  interval_of_check badTest_14080 56 8 (by decide +kernel)

theorem badTest_14080_block_8 : Interval badTest_14080 64 72 :=
  interval_of_check badTest_14080 64 8 (by decide +kernel)

theorem badTest_14080_block_9 : Interval badTest_14080 72 80 :=
  interval_of_check badTest_14080 72 8 (by decide +kernel)

theorem badTest_14080_block_10 : Interval badTest_14080 80 88 :=
  interval_of_check badTest_14080 80 8 (by decide +kernel)

theorem badTest_14080_block_11 : Interval badTest_14080 88 96 :=
  interval_of_check badTest_14080 88 8 (by decide +kernel)

theorem badTest_14080_block_12 : Interval badTest_14080 96 104 :=
  interval_of_check badTest_14080 96 8 (by decide +kernel)

theorem badTest_14080_block_13 : Interval badTest_14080 104 112 :=
  interval_of_check badTest_14080 104 8 (by decide +kernel)

theorem badTest_14080_block_14 : Interval badTest_14080 112 120 :=
  interval_of_check badTest_14080 112 8 (by decide +kernel)

theorem badTest_14080_block_15 : Interval badTest_14080 120 128 :=
  interval_of_check badTest_14080 120 8 (by decide +kernel)

theorem badTest_14080_block_16 : Interval badTest_14080 128 136 :=
  interval_of_check badTest_14080 128 8 (by decide +kernel)

theorem badTest_14080_block_17 : Interval badTest_14080 136 144 :=
  interval_of_check badTest_14080 136 8 (by decide +kernel)

theorem badTest_14080_block_18 : Interval badTest_14080 144 152 :=
  interval_of_check badTest_14080 144 8 (by decide +kernel)

theorem badTest_14080_block_19 : Interval badTest_14080 152 160 :=
  interval_of_check badTest_14080 152 8 (by decide +kernel)

theorem badTest_14080_block_20 : Interval badTest_14080 160 168 :=
  interval_of_check badTest_14080 160 8 (by decide +kernel)

theorem badTest_14080_block_21 : Interval badTest_14080 168 176 :=
  interval_of_check badTest_14080 168 8 (by decide +kernel)

theorem badTest_14080_block_22 : Interval badTest_14080 176 184 :=
  interval_of_check badTest_14080 176 8 (by decide +kernel)

theorem badTest_14080_block_23 : Interval badTest_14080 184 192 :=
  interval_of_check badTest_14080 184 8 (by decide +kernel)

theorem badTest_14080_block_24 : Interval badTest_14080 192 200 :=
  interval_of_check badTest_14080 192 8 (by decide +kernel)

theorem badTest_14080_block_25 : Interval badTest_14080 200 208 :=
  interval_of_check badTest_14080 200 8 (by decide +kernel)

theorem badTest_14080_block_26 : Interval badTest_14080 208 216 :=
  interval_of_check badTest_14080 208 8 (by decide +kernel)

theorem badTest_14080_block_27 : Interval badTest_14080 216 224 :=
  interval_of_check badTest_14080 216 8 (by decide +kernel)

theorem badTest_14080_block_28 : Interval badTest_14080 224 232 :=
  interval_of_check badTest_14080 224 8 (by decide +kernel)

theorem badTest_14080_block_29 : Interval badTest_14080 232 240 :=
  interval_of_check badTest_14080 232 8 (by decide +kernel)

theorem badTest_14080_block_30 : Interval badTest_14080 240 248 :=
  interval_of_check badTest_14080 240 8 (by decide +kernel)

theorem badTest_14080_block_31 : Interval badTest_14080 248 256 :=
  interval_of_check badTest_14080 248 8 (by decide +kernel)

theorem badTest_14080_complete : Interval badTest_14080 0 256 :=
  (interval_append badTest_14080 0 128 256
  (interval_append badTest_14080 0 64 128
  (interval_append badTest_14080 0 32 64
  (interval_append badTest_14080 0 16 32
  (interval_append badTest_14080 0 8 16
  badTest_14080_block_0
  badTest_14080_block_1)
  (interval_append badTest_14080 16 24 32
  badTest_14080_block_2
  badTest_14080_block_3))
  (interval_append badTest_14080 32 48 64
  (interval_append badTest_14080 32 40 48
  badTest_14080_block_4
  badTest_14080_block_5)
  (interval_append badTest_14080 48 56 64
  badTest_14080_block_6
  badTest_14080_block_7)))
  (interval_append badTest_14080 64 96 128
  (interval_append badTest_14080 64 80 96
  (interval_append badTest_14080 64 72 80
  badTest_14080_block_8
  badTest_14080_block_9)
  (interval_append badTest_14080 80 88 96
  badTest_14080_block_10
  badTest_14080_block_11))
  (interval_append badTest_14080 96 112 128
  (interval_append badTest_14080 96 104 112
  badTest_14080_block_12
  badTest_14080_block_13)
  (interval_append badTest_14080 112 120 128
  badTest_14080_block_14
  badTest_14080_block_15))))
  (interval_append badTest_14080 128 192 256
  (interval_append badTest_14080 128 160 192
  (interval_append badTest_14080 128 144 160
  (interval_append badTest_14080 128 136 144
  badTest_14080_block_16
  badTest_14080_block_17)
  (interval_append badTest_14080 144 152 160
  badTest_14080_block_18
  badTest_14080_block_19))
  (interval_append badTest_14080 160 176 192
  (interval_append badTest_14080 160 168 176
  badTest_14080_block_20
  badTest_14080_block_21)
  (interval_append badTest_14080 176 184 192
  badTest_14080_block_22
  badTest_14080_block_23)))
  (interval_append badTest_14080 192 224 256
  (interval_append badTest_14080 192 208 224
  (interval_append badTest_14080 192 200 208
  badTest_14080_block_24
  badTest_14080_block_25)
  (interval_append badTest_14080 208 216 224
  badTest_14080_block_26
  badTest_14080_block_27))
  (interval_append badTest_14080 224 240 256
  (interval_append badTest_14080 224 232 240
  badTest_14080_block_28
  badTest_14080_block_29)
  (interval_append badTest_14080 240 248 256
  badTest_14080_block_30
  badTest_14080_block_31)))))
theorem badTestInterval14080 : Interval badTest 14080 14336 := by
  intro i hlo hhi
  have h := badTest_14080_complete (i-14080) (Nat.zero_le _) (by omega)
  simpa only [badTest_14080, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad056 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_14336 (i : Nat) := badTest (i+14336)
theorem badTest_14336_block_0 : Interval badTest_14336 0 8 :=
  interval_of_check badTest_14336 0 8 (by decide +kernel)

theorem badTest_14336_block_1 : Interval badTest_14336 8 16 :=
  interval_of_check badTest_14336 8 8 (by decide +kernel)

theorem badTest_14336_block_2 : Interval badTest_14336 16 24 :=
  interval_of_check badTest_14336 16 8 (by decide +kernel)

theorem badTest_14336_block_3 : Interval badTest_14336 24 32 :=
  interval_of_check badTest_14336 24 8 (by decide +kernel)

theorem badTest_14336_block_4 : Interval badTest_14336 32 40 :=
  interval_of_check badTest_14336 32 8 (by decide +kernel)

theorem badTest_14336_block_5 : Interval badTest_14336 40 48 :=
  interval_of_check badTest_14336 40 8 (by decide +kernel)

theorem badTest_14336_block_6 : Interval badTest_14336 48 56 :=
  interval_of_check badTest_14336 48 8 (by decide +kernel)

theorem badTest_14336_block_7 : Interval badTest_14336 56 64 :=
  interval_of_check badTest_14336 56 8 (by decide +kernel)

theorem badTest_14336_block_8 : Interval badTest_14336 64 72 :=
  interval_of_check badTest_14336 64 8 (by decide +kernel)

theorem badTest_14336_block_9 : Interval badTest_14336 72 80 :=
  interval_of_check badTest_14336 72 8 (by decide +kernel)

theorem badTest_14336_block_10 : Interval badTest_14336 80 88 :=
  interval_of_check badTest_14336 80 8 (by decide +kernel)

theorem badTest_14336_block_11 : Interval badTest_14336 88 96 :=
  interval_of_check badTest_14336 88 8 (by decide +kernel)

theorem badTest_14336_block_12 : Interval badTest_14336 96 104 :=
  interval_of_check badTest_14336 96 8 (by decide +kernel)

theorem badTest_14336_block_13 : Interval badTest_14336 104 112 :=
  interval_of_check badTest_14336 104 8 (by decide +kernel)

theorem badTest_14336_block_14 : Interval badTest_14336 112 120 :=
  interval_of_check badTest_14336 112 8 (by decide +kernel)

theorem badTest_14336_block_15 : Interval badTest_14336 120 128 :=
  interval_of_check badTest_14336 120 8 (by decide +kernel)

theorem badTest_14336_block_16 : Interval badTest_14336 128 136 :=
  interval_of_check badTest_14336 128 8 (by decide +kernel)

theorem badTest_14336_block_17 : Interval badTest_14336 136 144 :=
  interval_of_check badTest_14336 136 8 (by decide +kernel)

theorem badTest_14336_block_18 : Interval badTest_14336 144 152 :=
  interval_of_check badTest_14336 144 8 (by decide +kernel)

theorem badTest_14336_block_19 : Interval badTest_14336 152 160 :=
  interval_of_check badTest_14336 152 8 (by decide +kernel)

theorem badTest_14336_block_20 : Interval badTest_14336 160 168 :=
  interval_of_check badTest_14336 160 8 (by decide +kernel)

theorem badTest_14336_block_21 : Interval badTest_14336 168 176 :=
  interval_of_check badTest_14336 168 8 (by decide +kernel)

theorem badTest_14336_block_22 : Interval badTest_14336 176 184 :=
  interval_of_check badTest_14336 176 8 (by decide +kernel)

theorem badTest_14336_block_23 : Interval badTest_14336 184 192 :=
  interval_of_check badTest_14336 184 8 (by decide +kernel)

theorem badTest_14336_block_24 : Interval badTest_14336 192 200 :=
  interval_of_check badTest_14336 192 8 (by decide +kernel)

theorem badTest_14336_block_25 : Interval badTest_14336 200 208 :=
  interval_of_check badTest_14336 200 8 (by decide +kernel)

theorem badTest_14336_block_26 : Interval badTest_14336 208 216 :=
  interval_of_check badTest_14336 208 8 (by decide +kernel)

theorem badTest_14336_block_27 : Interval badTest_14336 216 224 :=
  interval_of_check badTest_14336 216 8 (by decide +kernel)

theorem badTest_14336_block_28 : Interval badTest_14336 224 232 :=
  interval_of_check badTest_14336 224 8 (by decide +kernel)

theorem badTest_14336_block_29 : Interval badTest_14336 232 240 :=
  interval_of_check badTest_14336 232 8 (by decide +kernel)

theorem badTest_14336_block_30 : Interval badTest_14336 240 248 :=
  interval_of_check badTest_14336 240 8 (by decide +kernel)

theorem badTest_14336_block_31 : Interval badTest_14336 248 256 :=
  interval_of_check badTest_14336 248 8 (by decide +kernel)

theorem badTest_14336_complete : Interval badTest_14336 0 256 :=
  (interval_append badTest_14336 0 128 256
  (interval_append badTest_14336 0 64 128
  (interval_append badTest_14336 0 32 64
  (interval_append badTest_14336 0 16 32
  (interval_append badTest_14336 0 8 16
  badTest_14336_block_0
  badTest_14336_block_1)
  (interval_append badTest_14336 16 24 32
  badTest_14336_block_2
  badTest_14336_block_3))
  (interval_append badTest_14336 32 48 64
  (interval_append badTest_14336 32 40 48
  badTest_14336_block_4
  badTest_14336_block_5)
  (interval_append badTest_14336 48 56 64
  badTest_14336_block_6
  badTest_14336_block_7)))
  (interval_append badTest_14336 64 96 128
  (interval_append badTest_14336 64 80 96
  (interval_append badTest_14336 64 72 80
  badTest_14336_block_8
  badTest_14336_block_9)
  (interval_append badTest_14336 80 88 96
  badTest_14336_block_10
  badTest_14336_block_11))
  (interval_append badTest_14336 96 112 128
  (interval_append badTest_14336 96 104 112
  badTest_14336_block_12
  badTest_14336_block_13)
  (interval_append badTest_14336 112 120 128
  badTest_14336_block_14
  badTest_14336_block_15))))
  (interval_append badTest_14336 128 192 256
  (interval_append badTest_14336 128 160 192
  (interval_append badTest_14336 128 144 160
  (interval_append badTest_14336 128 136 144
  badTest_14336_block_16
  badTest_14336_block_17)
  (interval_append badTest_14336 144 152 160
  badTest_14336_block_18
  badTest_14336_block_19))
  (interval_append badTest_14336 160 176 192
  (interval_append badTest_14336 160 168 176
  badTest_14336_block_20
  badTest_14336_block_21)
  (interval_append badTest_14336 176 184 192
  badTest_14336_block_22
  badTest_14336_block_23)))
  (interval_append badTest_14336 192 224 256
  (interval_append badTest_14336 192 208 224
  (interval_append badTest_14336 192 200 208
  badTest_14336_block_24
  badTest_14336_block_25)
  (interval_append badTest_14336 208 216 224
  badTest_14336_block_26
  badTest_14336_block_27))
  (interval_append badTest_14336 224 240 256
  (interval_append badTest_14336 224 232 240
  badTest_14336_block_28
  badTest_14336_block_29)
  (interval_append badTest_14336 240 248 256
  badTest_14336_block_30
  badTest_14336_block_31)))))
theorem badTestInterval14336 : Interval badTest 14336 14592 := by
  intro i hlo hhi
  have h := badTest_14336_complete (i-14336) (Nat.zero_le _) (by omega)
  simpa only [badTest_14336, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad057 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_14592 (i : Nat) := badTest (i+14592)
theorem badTest_14592_block_0 : Interval badTest_14592 0 8 :=
  interval_of_check badTest_14592 0 8 (by decide +kernel)

theorem badTest_14592_block_1 : Interval badTest_14592 8 16 :=
  interval_of_check badTest_14592 8 8 (by decide +kernel)

theorem badTest_14592_block_2 : Interval badTest_14592 16 24 :=
  interval_of_check badTest_14592 16 8 (by decide +kernel)

theorem badTest_14592_block_3 : Interval badTest_14592 24 32 :=
  interval_of_check badTest_14592 24 8 (by decide +kernel)

theorem badTest_14592_block_4 : Interval badTest_14592 32 40 :=
  interval_of_check badTest_14592 32 8 (by decide +kernel)

theorem badTest_14592_block_5 : Interval badTest_14592 40 48 :=
  interval_of_check badTest_14592 40 8 (by decide +kernel)

theorem badTest_14592_block_6 : Interval badTest_14592 48 56 :=
  interval_of_check badTest_14592 48 8 (by decide +kernel)

theorem badTest_14592_block_7 : Interval badTest_14592 56 64 :=
  interval_of_check badTest_14592 56 8 (by decide +kernel)

theorem badTest_14592_block_8 : Interval badTest_14592 64 72 :=
  interval_of_check badTest_14592 64 8 (by decide +kernel)

theorem badTest_14592_block_9 : Interval badTest_14592 72 80 :=
  interval_of_check badTest_14592 72 8 (by decide +kernel)

theorem badTest_14592_block_10 : Interval badTest_14592 80 88 :=
  interval_of_check badTest_14592 80 8 (by decide +kernel)

theorem badTest_14592_block_11 : Interval badTest_14592 88 96 :=
  interval_of_check badTest_14592 88 8 (by decide +kernel)

theorem badTest_14592_block_12 : Interval badTest_14592 96 104 :=
  interval_of_check badTest_14592 96 8 (by decide +kernel)

theorem badTest_14592_block_13 : Interval badTest_14592 104 112 :=
  interval_of_check badTest_14592 104 8 (by decide +kernel)

theorem badTest_14592_block_14 : Interval badTest_14592 112 120 :=
  interval_of_check badTest_14592 112 8 (by decide +kernel)

theorem badTest_14592_block_15 : Interval badTest_14592 120 128 :=
  interval_of_check badTest_14592 120 8 (by decide +kernel)

theorem badTest_14592_block_16 : Interval badTest_14592 128 136 :=
  interval_of_check badTest_14592 128 8 (by decide +kernel)

theorem badTest_14592_block_17 : Interval badTest_14592 136 144 :=
  interval_of_check badTest_14592 136 8 (by decide +kernel)

theorem badTest_14592_block_18 : Interval badTest_14592 144 152 :=
  interval_of_check badTest_14592 144 8 (by decide +kernel)

theorem badTest_14592_block_19 : Interval badTest_14592 152 160 :=
  interval_of_check badTest_14592 152 8 (by decide +kernel)

theorem badTest_14592_block_20 : Interval badTest_14592 160 168 :=
  interval_of_check badTest_14592 160 8 (by decide +kernel)

theorem badTest_14592_block_21 : Interval badTest_14592 168 176 :=
  interval_of_check badTest_14592 168 8 (by decide +kernel)

theorem badTest_14592_block_22 : Interval badTest_14592 176 184 :=
  interval_of_check badTest_14592 176 8 (by decide +kernel)

theorem badTest_14592_block_23 : Interval badTest_14592 184 192 :=
  interval_of_check badTest_14592 184 8 (by decide +kernel)

theorem badTest_14592_block_24 : Interval badTest_14592 192 200 :=
  interval_of_check badTest_14592 192 8 (by decide +kernel)

theorem badTest_14592_block_25 : Interval badTest_14592 200 208 :=
  interval_of_check badTest_14592 200 8 (by decide +kernel)

theorem badTest_14592_block_26 : Interval badTest_14592 208 216 :=
  interval_of_check badTest_14592 208 8 (by decide +kernel)

theorem badTest_14592_block_27 : Interval badTest_14592 216 224 :=
  interval_of_check badTest_14592 216 8 (by decide +kernel)

theorem badTest_14592_block_28 : Interval badTest_14592 224 232 :=
  interval_of_check badTest_14592 224 8 (by decide +kernel)

theorem badTest_14592_block_29 : Interval badTest_14592 232 240 :=
  interval_of_check badTest_14592 232 8 (by decide +kernel)

theorem badTest_14592_block_30 : Interval badTest_14592 240 248 :=
  interval_of_check badTest_14592 240 8 (by decide +kernel)

theorem badTest_14592_block_31 : Interval badTest_14592 248 256 :=
  interval_of_check badTest_14592 248 8 (by decide +kernel)

theorem badTest_14592_complete : Interval badTest_14592 0 256 :=
  (interval_append badTest_14592 0 128 256
  (interval_append badTest_14592 0 64 128
  (interval_append badTest_14592 0 32 64
  (interval_append badTest_14592 0 16 32
  (interval_append badTest_14592 0 8 16
  badTest_14592_block_0
  badTest_14592_block_1)
  (interval_append badTest_14592 16 24 32
  badTest_14592_block_2
  badTest_14592_block_3))
  (interval_append badTest_14592 32 48 64
  (interval_append badTest_14592 32 40 48
  badTest_14592_block_4
  badTest_14592_block_5)
  (interval_append badTest_14592 48 56 64
  badTest_14592_block_6
  badTest_14592_block_7)))
  (interval_append badTest_14592 64 96 128
  (interval_append badTest_14592 64 80 96
  (interval_append badTest_14592 64 72 80
  badTest_14592_block_8
  badTest_14592_block_9)
  (interval_append badTest_14592 80 88 96
  badTest_14592_block_10
  badTest_14592_block_11))
  (interval_append badTest_14592 96 112 128
  (interval_append badTest_14592 96 104 112
  badTest_14592_block_12
  badTest_14592_block_13)
  (interval_append badTest_14592 112 120 128
  badTest_14592_block_14
  badTest_14592_block_15))))
  (interval_append badTest_14592 128 192 256
  (interval_append badTest_14592 128 160 192
  (interval_append badTest_14592 128 144 160
  (interval_append badTest_14592 128 136 144
  badTest_14592_block_16
  badTest_14592_block_17)
  (interval_append badTest_14592 144 152 160
  badTest_14592_block_18
  badTest_14592_block_19))
  (interval_append badTest_14592 160 176 192
  (interval_append badTest_14592 160 168 176
  badTest_14592_block_20
  badTest_14592_block_21)
  (interval_append badTest_14592 176 184 192
  badTest_14592_block_22
  badTest_14592_block_23)))
  (interval_append badTest_14592 192 224 256
  (interval_append badTest_14592 192 208 224
  (interval_append badTest_14592 192 200 208
  badTest_14592_block_24
  badTest_14592_block_25)
  (interval_append badTest_14592 208 216 224
  badTest_14592_block_26
  badTest_14592_block_27))
  (interval_append badTest_14592 224 240 256
  (interval_append badTest_14592 224 232 240
  badTest_14592_block_28
  badTest_14592_block_29)
  (interval_append badTest_14592 240 248 256
  badTest_14592_block_30
  badTest_14592_block_31)))))
theorem badTestInterval14592 : Interval badTest 14592 14848 := by
  intro i hlo hhi
  have h := badTest_14592_complete (i-14592) (Nat.zero_le _) (by omega)
  simpa only [badTest_14592, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad058 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_14848 (i : Nat) := badTest (i+14848)
theorem badTest_14848_block_0 : Interval badTest_14848 0 8 :=
  interval_of_check badTest_14848 0 8 (by decide +kernel)

theorem badTest_14848_block_1 : Interval badTest_14848 8 16 :=
  interval_of_check badTest_14848 8 8 (by decide +kernel)

theorem badTest_14848_block_2 : Interval badTest_14848 16 24 :=
  interval_of_check badTest_14848 16 8 (by decide +kernel)

theorem badTest_14848_block_3 : Interval badTest_14848 24 32 :=
  interval_of_check badTest_14848 24 8 (by decide +kernel)

theorem badTest_14848_block_4 : Interval badTest_14848 32 40 :=
  interval_of_check badTest_14848 32 8 (by decide +kernel)

theorem badTest_14848_block_5 : Interval badTest_14848 40 48 :=
  interval_of_check badTest_14848 40 8 (by decide +kernel)

theorem badTest_14848_block_6 : Interval badTest_14848 48 56 :=
  interval_of_check badTest_14848 48 8 (by decide +kernel)

theorem badTest_14848_block_7 : Interval badTest_14848 56 64 :=
  interval_of_check badTest_14848 56 8 (by decide +kernel)

theorem badTest_14848_block_8 : Interval badTest_14848 64 72 :=
  interval_of_check badTest_14848 64 8 (by decide +kernel)

theorem badTest_14848_block_9 : Interval badTest_14848 72 80 :=
  interval_of_check badTest_14848 72 8 (by decide +kernel)

theorem badTest_14848_block_10 : Interval badTest_14848 80 88 :=
  interval_of_check badTest_14848 80 8 (by decide +kernel)

theorem badTest_14848_block_11 : Interval badTest_14848 88 96 :=
  interval_of_check badTest_14848 88 8 (by decide +kernel)

theorem badTest_14848_block_12 : Interval badTest_14848 96 104 :=
  interval_of_check badTest_14848 96 8 (by decide +kernel)

theorem badTest_14848_block_13 : Interval badTest_14848 104 112 :=
  interval_of_check badTest_14848 104 8 (by decide +kernel)

theorem badTest_14848_block_14 : Interval badTest_14848 112 120 :=
  interval_of_check badTest_14848 112 8 (by decide +kernel)

theorem badTest_14848_block_15 : Interval badTest_14848 120 128 :=
  interval_of_check badTest_14848 120 8 (by decide +kernel)

theorem badTest_14848_block_16 : Interval badTest_14848 128 136 :=
  interval_of_check badTest_14848 128 8 (by decide +kernel)

theorem badTest_14848_block_17 : Interval badTest_14848 136 144 :=
  interval_of_check badTest_14848 136 8 (by decide +kernel)

theorem badTest_14848_block_18 : Interval badTest_14848 144 152 :=
  interval_of_check badTest_14848 144 8 (by decide +kernel)

theorem badTest_14848_block_19 : Interval badTest_14848 152 160 :=
  interval_of_check badTest_14848 152 8 (by decide +kernel)

theorem badTest_14848_block_20 : Interval badTest_14848 160 168 :=
  interval_of_check badTest_14848 160 8 (by decide +kernel)

theorem badTest_14848_block_21 : Interval badTest_14848 168 176 :=
  interval_of_check badTest_14848 168 8 (by decide +kernel)

theorem badTest_14848_block_22 : Interval badTest_14848 176 184 :=
  interval_of_check badTest_14848 176 8 (by decide +kernel)

theorem badTest_14848_block_23 : Interval badTest_14848 184 192 :=
  interval_of_check badTest_14848 184 8 (by decide +kernel)

theorem badTest_14848_block_24 : Interval badTest_14848 192 200 :=
  interval_of_check badTest_14848 192 8 (by decide +kernel)

theorem badTest_14848_block_25 : Interval badTest_14848 200 208 :=
  interval_of_check badTest_14848 200 8 (by decide +kernel)

theorem badTest_14848_block_26 : Interval badTest_14848 208 216 :=
  interval_of_check badTest_14848 208 8 (by decide +kernel)

theorem badTest_14848_block_27 : Interval badTest_14848 216 224 :=
  interval_of_check badTest_14848 216 8 (by decide +kernel)

theorem badTest_14848_block_28 : Interval badTest_14848 224 232 :=
  interval_of_check badTest_14848 224 8 (by decide +kernel)

theorem badTest_14848_block_29 : Interval badTest_14848 232 240 :=
  interval_of_check badTest_14848 232 8 (by decide +kernel)

theorem badTest_14848_block_30 : Interval badTest_14848 240 248 :=
  interval_of_check badTest_14848 240 8 (by decide +kernel)

theorem badTest_14848_block_31 : Interval badTest_14848 248 256 :=
  interval_of_check badTest_14848 248 8 (by decide +kernel)

theorem badTest_14848_complete : Interval badTest_14848 0 256 :=
  (interval_append badTest_14848 0 128 256
  (interval_append badTest_14848 0 64 128
  (interval_append badTest_14848 0 32 64
  (interval_append badTest_14848 0 16 32
  (interval_append badTest_14848 0 8 16
  badTest_14848_block_0
  badTest_14848_block_1)
  (interval_append badTest_14848 16 24 32
  badTest_14848_block_2
  badTest_14848_block_3))
  (interval_append badTest_14848 32 48 64
  (interval_append badTest_14848 32 40 48
  badTest_14848_block_4
  badTest_14848_block_5)
  (interval_append badTest_14848 48 56 64
  badTest_14848_block_6
  badTest_14848_block_7)))
  (interval_append badTest_14848 64 96 128
  (interval_append badTest_14848 64 80 96
  (interval_append badTest_14848 64 72 80
  badTest_14848_block_8
  badTest_14848_block_9)
  (interval_append badTest_14848 80 88 96
  badTest_14848_block_10
  badTest_14848_block_11))
  (interval_append badTest_14848 96 112 128
  (interval_append badTest_14848 96 104 112
  badTest_14848_block_12
  badTest_14848_block_13)
  (interval_append badTest_14848 112 120 128
  badTest_14848_block_14
  badTest_14848_block_15))))
  (interval_append badTest_14848 128 192 256
  (interval_append badTest_14848 128 160 192
  (interval_append badTest_14848 128 144 160
  (interval_append badTest_14848 128 136 144
  badTest_14848_block_16
  badTest_14848_block_17)
  (interval_append badTest_14848 144 152 160
  badTest_14848_block_18
  badTest_14848_block_19))
  (interval_append badTest_14848 160 176 192
  (interval_append badTest_14848 160 168 176
  badTest_14848_block_20
  badTest_14848_block_21)
  (interval_append badTest_14848 176 184 192
  badTest_14848_block_22
  badTest_14848_block_23)))
  (interval_append badTest_14848 192 224 256
  (interval_append badTest_14848 192 208 224
  (interval_append badTest_14848 192 200 208
  badTest_14848_block_24
  badTest_14848_block_25)
  (interval_append badTest_14848 208 216 224
  badTest_14848_block_26
  badTest_14848_block_27))
  (interval_append badTest_14848 224 240 256
  (interval_append badTest_14848 224 232 240
  badTest_14848_block_28
  badTest_14848_block_29)
  (interval_append badTest_14848 240 248 256
  badTest_14848_block_30
  badTest_14848_block_31)))))
theorem badTestInterval14848 : Interval badTest 14848 15104 := by
  intro i hlo hhi
  have h := badTest_14848_complete (i-14848) (Nat.zero_le _) (by omega)
  simpa only [badTest_14848, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad059 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_15104 (i : Nat) := badTest (i+15104)
theorem badTest_15104_block_0 : Interval badTest_15104 0 8 :=
  interval_of_check badTest_15104 0 8 (by decide +kernel)

theorem badTest_15104_block_1 : Interval badTest_15104 8 16 :=
  interval_of_check badTest_15104 8 8 (by decide +kernel)

theorem badTest_15104_block_2 : Interval badTest_15104 16 24 :=
  interval_of_check badTest_15104 16 8 (by decide +kernel)

theorem badTest_15104_block_3 : Interval badTest_15104 24 32 :=
  interval_of_check badTest_15104 24 8 (by decide +kernel)

theorem badTest_15104_block_4 : Interval badTest_15104 32 40 :=
  interval_of_check badTest_15104 32 8 (by decide +kernel)

theorem badTest_15104_block_5 : Interval badTest_15104 40 48 :=
  interval_of_check badTest_15104 40 8 (by decide +kernel)

theorem badTest_15104_block_6 : Interval badTest_15104 48 56 :=
  interval_of_check badTest_15104 48 8 (by decide +kernel)

theorem badTest_15104_block_7 : Interval badTest_15104 56 64 :=
  interval_of_check badTest_15104 56 8 (by decide +kernel)

theorem badTest_15104_block_8 : Interval badTest_15104 64 72 :=
  interval_of_check badTest_15104 64 8 (by decide +kernel)

theorem badTest_15104_block_9 : Interval badTest_15104 72 80 :=
  interval_of_check badTest_15104 72 8 (by decide +kernel)

theorem badTest_15104_block_10 : Interval badTest_15104 80 88 :=
  interval_of_check badTest_15104 80 8 (by decide +kernel)

theorem badTest_15104_block_11 : Interval badTest_15104 88 96 :=
  interval_of_check badTest_15104 88 8 (by decide +kernel)

theorem badTest_15104_block_12 : Interval badTest_15104 96 104 :=
  interval_of_check badTest_15104 96 8 (by decide +kernel)

theorem badTest_15104_block_13 : Interval badTest_15104 104 112 :=
  interval_of_check badTest_15104 104 8 (by decide +kernel)

theorem badTest_15104_block_14 : Interval badTest_15104 112 120 :=
  interval_of_check badTest_15104 112 8 (by decide +kernel)

theorem badTest_15104_block_15 : Interval badTest_15104 120 128 :=
  interval_of_check badTest_15104 120 8 (by decide +kernel)

theorem badTest_15104_block_16 : Interval badTest_15104 128 136 :=
  interval_of_check badTest_15104 128 8 (by decide +kernel)

theorem badTest_15104_block_17 : Interval badTest_15104 136 142 :=
  interval_of_check badTest_15104 136 6 (by decide +kernel)

theorem badTest_15104_complete : Interval badTest_15104 0 142 :=
  (interval_append badTest_15104 0 72 142
  (interval_append badTest_15104 0 32 72
  (interval_append badTest_15104 0 16 32
  (interval_append badTest_15104 0 8 16
  badTest_15104_block_0
  badTest_15104_block_1)
  (interval_append badTest_15104 16 24 32
  badTest_15104_block_2
  badTest_15104_block_3))
  (interval_append badTest_15104 32 48 72
  (interval_append badTest_15104 32 40 48
  badTest_15104_block_4
  badTest_15104_block_5)
  (interval_append badTest_15104 48 56 72
  badTest_15104_block_6
  (interval_append badTest_15104 56 64 72
  badTest_15104_block_7
  badTest_15104_block_8))))
  (interval_append badTest_15104 72 104 142
  (interval_append badTest_15104 72 88 104
  (interval_append badTest_15104 72 80 88
  badTest_15104_block_9
  badTest_15104_block_10)
  (interval_append badTest_15104 88 96 104
  badTest_15104_block_11
  badTest_15104_block_12))
  (interval_append badTest_15104 104 120 142
  (interval_append badTest_15104 104 112 120
  badTest_15104_block_13
  badTest_15104_block_14)
  (interval_append badTest_15104 120 128 142
  badTest_15104_block_15
  (interval_append badTest_15104 128 136 142
  badTest_15104_block_16
  badTest_15104_block_17)))))
theorem badTestInterval15104 : Interval badTest 15104 15246 := by
  intro i hlo hhi
  have h := badTest_15104_complete (i-15104) (Nat.zero_le _) (by omega)
  simpa only [badTest_15104, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
