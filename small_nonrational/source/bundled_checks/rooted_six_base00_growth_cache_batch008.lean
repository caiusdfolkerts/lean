module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheBad042 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_10752 (i : Nat) := badTest (i+10752)
theorem badTest_10752_block_0 : Interval badTest_10752 0 8 :=
  interval_of_check badTest_10752 0 8 (by decide +kernel)

theorem badTest_10752_block_1 : Interval badTest_10752 8 16 :=
  interval_of_check badTest_10752 8 8 (by decide +kernel)

theorem badTest_10752_block_2 : Interval badTest_10752 16 24 :=
  interval_of_check badTest_10752 16 8 (by decide +kernel)

theorem badTest_10752_block_3 : Interval badTest_10752 24 32 :=
  interval_of_check badTest_10752 24 8 (by decide +kernel)

theorem badTest_10752_block_4 : Interval badTest_10752 32 40 :=
  interval_of_check badTest_10752 32 8 (by decide +kernel)

theorem badTest_10752_block_5 : Interval badTest_10752 40 48 :=
  interval_of_check badTest_10752 40 8 (by decide +kernel)

theorem badTest_10752_block_6 : Interval badTest_10752 48 56 :=
  interval_of_check badTest_10752 48 8 (by decide +kernel)

theorem badTest_10752_block_7 : Interval badTest_10752 56 64 :=
  interval_of_check badTest_10752 56 8 (by decide +kernel)

theorem badTest_10752_block_8 : Interval badTest_10752 64 72 :=
  interval_of_check badTest_10752 64 8 (by decide +kernel)

theorem badTest_10752_block_9 : Interval badTest_10752 72 80 :=
  interval_of_check badTest_10752 72 8 (by decide +kernel)

theorem badTest_10752_block_10 : Interval badTest_10752 80 88 :=
  interval_of_check badTest_10752 80 8 (by decide +kernel)

theorem badTest_10752_block_11 : Interval badTest_10752 88 96 :=
  interval_of_check badTest_10752 88 8 (by decide +kernel)

theorem badTest_10752_block_12 : Interval badTest_10752 96 104 :=
  interval_of_check badTest_10752 96 8 (by decide +kernel)

theorem badTest_10752_block_13 : Interval badTest_10752 104 112 :=
  interval_of_check badTest_10752 104 8 (by decide +kernel)

theorem badTest_10752_block_14 : Interval badTest_10752 112 120 :=
  interval_of_check badTest_10752 112 8 (by decide +kernel)

theorem badTest_10752_block_15 : Interval badTest_10752 120 128 :=
  interval_of_check badTest_10752 120 8 (by decide +kernel)

theorem badTest_10752_block_16 : Interval badTest_10752 128 136 :=
  interval_of_check badTest_10752 128 8 (by decide +kernel)

theorem badTest_10752_block_17 : Interval badTest_10752 136 144 :=
  interval_of_check badTest_10752 136 8 (by decide +kernel)

theorem badTest_10752_block_18 : Interval badTest_10752 144 152 :=
  interval_of_check badTest_10752 144 8 (by decide +kernel)

theorem badTest_10752_block_19 : Interval badTest_10752 152 160 :=
  interval_of_check badTest_10752 152 8 (by decide +kernel)

theorem badTest_10752_block_20 : Interval badTest_10752 160 168 :=
  interval_of_check badTest_10752 160 8 (by decide +kernel)

theorem badTest_10752_block_21 : Interval badTest_10752 168 176 :=
  interval_of_check badTest_10752 168 8 (by decide +kernel)

theorem badTest_10752_block_22 : Interval badTest_10752 176 184 :=
  interval_of_check badTest_10752 176 8 (by decide +kernel)

theorem badTest_10752_block_23 : Interval badTest_10752 184 192 :=
  interval_of_check badTest_10752 184 8 (by decide +kernel)

theorem badTest_10752_block_24 : Interval badTest_10752 192 200 :=
  interval_of_check badTest_10752 192 8 (by decide +kernel)

theorem badTest_10752_block_25 : Interval badTest_10752 200 208 :=
  interval_of_check badTest_10752 200 8 (by decide +kernel)

theorem badTest_10752_block_26 : Interval badTest_10752 208 216 :=
  interval_of_check badTest_10752 208 8 (by decide +kernel)

theorem badTest_10752_block_27 : Interval badTest_10752 216 224 :=
  interval_of_check badTest_10752 216 8 (by decide +kernel)

theorem badTest_10752_block_28 : Interval badTest_10752 224 232 :=
  interval_of_check badTest_10752 224 8 (by decide +kernel)

theorem badTest_10752_block_29 : Interval badTest_10752 232 240 :=
  interval_of_check badTest_10752 232 8 (by decide +kernel)

theorem badTest_10752_block_30 : Interval badTest_10752 240 248 :=
  interval_of_check badTest_10752 240 8 (by decide +kernel)

theorem badTest_10752_block_31 : Interval badTest_10752 248 256 :=
  interval_of_check badTest_10752 248 8 (by decide +kernel)

theorem badTest_10752_complete : Interval badTest_10752 0 256 :=
  (interval_append badTest_10752 0 128 256
  (interval_append badTest_10752 0 64 128
  (interval_append badTest_10752 0 32 64
  (interval_append badTest_10752 0 16 32
  (interval_append badTest_10752 0 8 16
  badTest_10752_block_0
  badTest_10752_block_1)
  (interval_append badTest_10752 16 24 32
  badTest_10752_block_2
  badTest_10752_block_3))
  (interval_append badTest_10752 32 48 64
  (interval_append badTest_10752 32 40 48
  badTest_10752_block_4
  badTest_10752_block_5)
  (interval_append badTest_10752 48 56 64
  badTest_10752_block_6
  badTest_10752_block_7)))
  (interval_append badTest_10752 64 96 128
  (interval_append badTest_10752 64 80 96
  (interval_append badTest_10752 64 72 80
  badTest_10752_block_8
  badTest_10752_block_9)
  (interval_append badTest_10752 80 88 96
  badTest_10752_block_10
  badTest_10752_block_11))
  (interval_append badTest_10752 96 112 128
  (interval_append badTest_10752 96 104 112
  badTest_10752_block_12
  badTest_10752_block_13)
  (interval_append badTest_10752 112 120 128
  badTest_10752_block_14
  badTest_10752_block_15))))
  (interval_append badTest_10752 128 192 256
  (interval_append badTest_10752 128 160 192
  (interval_append badTest_10752 128 144 160
  (interval_append badTest_10752 128 136 144
  badTest_10752_block_16
  badTest_10752_block_17)
  (interval_append badTest_10752 144 152 160
  badTest_10752_block_18
  badTest_10752_block_19))
  (interval_append badTest_10752 160 176 192
  (interval_append badTest_10752 160 168 176
  badTest_10752_block_20
  badTest_10752_block_21)
  (interval_append badTest_10752 176 184 192
  badTest_10752_block_22
  badTest_10752_block_23)))
  (interval_append badTest_10752 192 224 256
  (interval_append badTest_10752 192 208 224
  (interval_append badTest_10752 192 200 208
  badTest_10752_block_24
  badTest_10752_block_25)
  (interval_append badTest_10752 208 216 224
  badTest_10752_block_26
  badTest_10752_block_27))
  (interval_append badTest_10752 224 240 256
  (interval_append badTest_10752 224 232 240
  badTest_10752_block_28
  badTest_10752_block_29)
  (interval_append badTest_10752 240 248 256
  badTest_10752_block_30
  badTest_10752_block_31)))))
theorem badTestInterval10752 : Interval badTest 10752 11008 := by
  intro i hlo hhi
  have h := badTest_10752_complete (i-10752) (Nat.zero_le _) (by omega)
  simpa only [badTest_10752, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad043 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_11008 (i : Nat) := badTest (i+11008)
theorem badTest_11008_block_0 : Interval badTest_11008 0 8 :=
  interval_of_check badTest_11008 0 8 (by decide +kernel)

theorem badTest_11008_block_1 : Interval badTest_11008 8 16 :=
  interval_of_check badTest_11008 8 8 (by decide +kernel)

theorem badTest_11008_block_2 : Interval badTest_11008 16 24 :=
  interval_of_check badTest_11008 16 8 (by decide +kernel)

theorem badTest_11008_block_3 : Interval badTest_11008 24 32 :=
  interval_of_check badTest_11008 24 8 (by decide +kernel)

theorem badTest_11008_block_4 : Interval badTest_11008 32 40 :=
  interval_of_check badTest_11008 32 8 (by decide +kernel)

theorem badTest_11008_block_5 : Interval badTest_11008 40 48 :=
  interval_of_check badTest_11008 40 8 (by decide +kernel)

theorem badTest_11008_block_6 : Interval badTest_11008 48 56 :=
  interval_of_check badTest_11008 48 8 (by decide +kernel)

theorem badTest_11008_block_7 : Interval badTest_11008 56 64 :=
  interval_of_check badTest_11008 56 8 (by decide +kernel)

theorem badTest_11008_block_8 : Interval badTest_11008 64 72 :=
  interval_of_check badTest_11008 64 8 (by decide +kernel)

theorem badTest_11008_block_9 : Interval badTest_11008 72 80 :=
  interval_of_check badTest_11008 72 8 (by decide +kernel)

theorem badTest_11008_block_10 : Interval badTest_11008 80 88 :=
  interval_of_check badTest_11008 80 8 (by decide +kernel)

theorem badTest_11008_block_11 : Interval badTest_11008 88 96 :=
  interval_of_check badTest_11008 88 8 (by decide +kernel)

theorem badTest_11008_block_12 : Interval badTest_11008 96 104 :=
  interval_of_check badTest_11008 96 8 (by decide +kernel)

theorem badTest_11008_block_13 : Interval badTest_11008 104 112 :=
  interval_of_check badTest_11008 104 8 (by decide +kernel)

theorem badTest_11008_block_14 : Interval badTest_11008 112 120 :=
  interval_of_check badTest_11008 112 8 (by decide +kernel)

theorem badTest_11008_block_15 : Interval badTest_11008 120 128 :=
  interval_of_check badTest_11008 120 8 (by decide +kernel)

theorem badTest_11008_block_16 : Interval badTest_11008 128 136 :=
  interval_of_check badTest_11008 128 8 (by decide +kernel)

theorem badTest_11008_block_17 : Interval badTest_11008 136 144 :=
  interval_of_check badTest_11008 136 8 (by decide +kernel)

theorem badTest_11008_block_18 : Interval badTest_11008 144 152 :=
  interval_of_check badTest_11008 144 8 (by decide +kernel)

theorem badTest_11008_block_19 : Interval badTest_11008 152 160 :=
  interval_of_check badTest_11008 152 8 (by decide +kernel)

theorem badTest_11008_block_20 : Interval badTest_11008 160 168 :=
  interval_of_check badTest_11008 160 8 (by decide +kernel)

theorem badTest_11008_block_21 : Interval badTest_11008 168 176 :=
  interval_of_check badTest_11008 168 8 (by decide +kernel)

theorem badTest_11008_block_22 : Interval badTest_11008 176 184 :=
  interval_of_check badTest_11008 176 8 (by decide +kernel)

theorem badTest_11008_block_23 : Interval badTest_11008 184 192 :=
  interval_of_check badTest_11008 184 8 (by decide +kernel)

theorem badTest_11008_block_24 : Interval badTest_11008 192 200 :=
  interval_of_check badTest_11008 192 8 (by decide +kernel)

theorem badTest_11008_block_25 : Interval badTest_11008 200 208 :=
  interval_of_check badTest_11008 200 8 (by decide +kernel)

theorem badTest_11008_block_26 : Interval badTest_11008 208 216 :=
  interval_of_check badTest_11008 208 8 (by decide +kernel)

theorem badTest_11008_block_27 : Interval badTest_11008 216 224 :=
  interval_of_check badTest_11008 216 8 (by decide +kernel)

theorem badTest_11008_block_28 : Interval badTest_11008 224 232 :=
  interval_of_check badTest_11008 224 8 (by decide +kernel)

theorem badTest_11008_block_29 : Interval badTest_11008 232 240 :=
  interval_of_check badTest_11008 232 8 (by decide +kernel)

theorem badTest_11008_block_30 : Interval badTest_11008 240 248 :=
  interval_of_check badTest_11008 240 8 (by decide +kernel)

theorem badTest_11008_block_31 : Interval badTest_11008 248 256 :=
  interval_of_check badTest_11008 248 8 (by decide +kernel)

theorem badTest_11008_complete : Interval badTest_11008 0 256 :=
  (interval_append badTest_11008 0 128 256
  (interval_append badTest_11008 0 64 128
  (interval_append badTest_11008 0 32 64
  (interval_append badTest_11008 0 16 32
  (interval_append badTest_11008 0 8 16
  badTest_11008_block_0
  badTest_11008_block_1)
  (interval_append badTest_11008 16 24 32
  badTest_11008_block_2
  badTest_11008_block_3))
  (interval_append badTest_11008 32 48 64
  (interval_append badTest_11008 32 40 48
  badTest_11008_block_4
  badTest_11008_block_5)
  (interval_append badTest_11008 48 56 64
  badTest_11008_block_6
  badTest_11008_block_7)))
  (interval_append badTest_11008 64 96 128
  (interval_append badTest_11008 64 80 96
  (interval_append badTest_11008 64 72 80
  badTest_11008_block_8
  badTest_11008_block_9)
  (interval_append badTest_11008 80 88 96
  badTest_11008_block_10
  badTest_11008_block_11))
  (interval_append badTest_11008 96 112 128
  (interval_append badTest_11008 96 104 112
  badTest_11008_block_12
  badTest_11008_block_13)
  (interval_append badTest_11008 112 120 128
  badTest_11008_block_14
  badTest_11008_block_15))))
  (interval_append badTest_11008 128 192 256
  (interval_append badTest_11008 128 160 192
  (interval_append badTest_11008 128 144 160
  (interval_append badTest_11008 128 136 144
  badTest_11008_block_16
  badTest_11008_block_17)
  (interval_append badTest_11008 144 152 160
  badTest_11008_block_18
  badTest_11008_block_19))
  (interval_append badTest_11008 160 176 192
  (interval_append badTest_11008 160 168 176
  badTest_11008_block_20
  badTest_11008_block_21)
  (interval_append badTest_11008 176 184 192
  badTest_11008_block_22
  badTest_11008_block_23)))
  (interval_append badTest_11008 192 224 256
  (interval_append badTest_11008 192 208 224
  (interval_append badTest_11008 192 200 208
  badTest_11008_block_24
  badTest_11008_block_25)
  (interval_append badTest_11008 208 216 224
  badTest_11008_block_26
  badTest_11008_block_27))
  (interval_append badTest_11008 224 240 256
  (interval_append badTest_11008 224 232 240
  badTest_11008_block_28
  badTest_11008_block_29)
  (interval_append badTest_11008 240 248 256
  badTest_11008_block_30
  badTest_11008_block_31)))))
theorem badTestInterval11008 : Interval badTest 11008 11264 := by
  intro i hlo hhi
  have h := badTest_11008_complete (i-11008) (Nat.zero_le _) (by omega)
  simpa only [badTest_11008, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad044 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_11264 (i : Nat) := badTest (i+11264)
theorem badTest_11264_block_0 : Interval badTest_11264 0 8 :=
  interval_of_check badTest_11264 0 8 (by decide +kernel)

theorem badTest_11264_block_1 : Interval badTest_11264 8 16 :=
  interval_of_check badTest_11264 8 8 (by decide +kernel)

theorem badTest_11264_block_2 : Interval badTest_11264 16 24 :=
  interval_of_check badTest_11264 16 8 (by decide +kernel)

theorem badTest_11264_block_3 : Interval badTest_11264 24 32 :=
  interval_of_check badTest_11264 24 8 (by decide +kernel)

theorem badTest_11264_block_4 : Interval badTest_11264 32 40 :=
  interval_of_check badTest_11264 32 8 (by decide +kernel)

theorem badTest_11264_block_5 : Interval badTest_11264 40 48 :=
  interval_of_check badTest_11264 40 8 (by decide +kernel)

theorem badTest_11264_block_6 : Interval badTest_11264 48 56 :=
  interval_of_check badTest_11264 48 8 (by decide +kernel)

theorem badTest_11264_block_7 : Interval badTest_11264 56 64 :=
  interval_of_check badTest_11264 56 8 (by decide +kernel)

theorem badTest_11264_block_8 : Interval badTest_11264 64 72 :=
  interval_of_check badTest_11264 64 8 (by decide +kernel)

theorem badTest_11264_block_9 : Interval badTest_11264 72 80 :=
  interval_of_check badTest_11264 72 8 (by decide +kernel)

theorem badTest_11264_block_10 : Interval badTest_11264 80 88 :=
  interval_of_check badTest_11264 80 8 (by decide +kernel)

theorem badTest_11264_block_11 : Interval badTest_11264 88 96 :=
  interval_of_check badTest_11264 88 8 (by decide +kernel)

theorem badTest_11264_block_12 : Interval badTest_11264 96 104 :=
  interval_of_check badTest_11264 96 8 (by decide +kernel)

theorem badTest_11264_block_13 : Interval badTest_11264 104 112 :=
  interval_of_check badTest_11264 104 8 (by decide +kernel)

theorem badTest_11264_block_14 : Interval badTest_11264 112 120 :=
  interval_of_check badTest_11264 112 8 (by decide +kernel)

theorem badTest_11264_block_15 : Interval badTest_11264 120 128 :=
  interval_of_check badTest_11264 120 8 (by decide +kernel)

theorem badTest_11264_block_16 : Interval badTest_11264 128 136 :=
  interval_of_check badTest_11264 128 8 (by decide +kernel)

theorem badTest_11264_block_17 : Interval badTest_11264 136 144 :=
  interval_of_check badTest_11264 136 8 (by decide +kernel)

theorem badTest_11264_block_18 : Interval badTest_11264 144 152 :=
  interval_of_check badTest_11264 144 8 (by decide +kernel)

theorem badTest_11264_block_19 : Interval badTest_11264 152 160 :=
  interval_of_check badTest_11264 152 8 (by decide +kernel)

theorem badTest_11264_block_20 : Interval badTest_11264 160 168 :=
  interval_of_check badTest_11264 160 8 (by decide +kernel)

theorem badTest_11264_block_21 : Interval badTest_11264 168 176 :=
  interval_of_check badTest_11264 168 8 (by decide +kernel)

theorem badTest_11264_block_22 : Interval badTest_11264 176 184 :=
  interval_of_check badTest_11264 176 8 (by decide +kernel)

theorem badTest_11264_block_23 : Interval badTest_11264 184 192 :=
  interval_of_check badTest_11264 184 8 (by decide +kernel)

theorem badTest_11264_block_24 : Interval badTest_11264 192 200 :=
  interval_of_check badTest_11264 192 8 (by decide +kernel)

theorem badTest_11264_block_25 : Interval badTest_11264 200 208 :=
  interval_of_check badTest_11264 200 8 (by decide +kernel)

theorem badTest_11264_block_26 : Interval badTest_11264 208 216 :=
  interval_of_check badTest_11264 208 8 (by decide +kernel)

theorem badTest_11264_block_27 : Interval badTest_11264 216 224 :=
  interval_of_check badTest_11264 216 8 (by decide +kernel)

theorem badTest_11264_block_28 : Interval badTest_11264 224 232 :=
  interval_of_check badTest_11264 224 8 (by decide +kernel)

theorem badTest_11264_block_29 : Interval badTest_11264 232 240 :=
  interval_of_check badTest_11264 232 8 (by decide +kernel)

theorem badTest_11264_block_30 : Interval badTest_11264 240 248 :=
  interval_of_check badTest_11264 240 8 (by decide +kernel)

theorem badTest_11264_block_31 : Interval badTest_11264 248 256 :=
  interval_of_check badTest_11264 248 8 (by decide +kernel)

theorem badTest_11264_complete : Interval badTest_11264 0 256 :=
  (interval_append badTest_11264 0 128 256
  (interval_append badTest_11264 0 64 128
  (interval_append badTest_11264 0 32 64
  (interval_append badTest_11264 0 16 32
  (interval_append badTest_11264 0 8 16
  badTest_11264_block_0
  badTest_11264_block_1)
  (interval_append badTest_11264 16 24 32
  badTest_11264_block_2
  badTest_11264_block_3))
  (interval_append badTest_11264 32 48 64
  (interval_append badTest_11264 32 40 48
  badTest_11264_block_4
  badTest_11264_block_5)
  (interval_append badTest_11264 48 56 64
  badTest_11264_block_6
  badTest_11264_block_7)))
  (interval_append badTest_11264 64 96 128
  (interval_append badTest_11264 64 80 96
  (interval_append badTest_11264 64 72 80
  badTest_11264_block_8
  badTest_11264_block_9)
  (interval_append badTest_11264 80 88 96
  badTest_11264_block_10
  badTest_11264_block_11))
  (interval_append badTest_11264 96 112 128
  (interval_append badTest_11264 96 104 112
  badTest_11264_block_12
  badTest_11264_block_13)
  (interval_append badTest_11264 112 120 128
  badTest_11264_block_14
  badTest_11264_block_15))))
  (interval_append badTest_11264 128 192 256
  (interval_append badTest_11264 128 160 192
  (interval_append badTest_11264 128 144 160
  (interval_append badTest_11264 128 136 144
  badTest_11264_block_16
  badTest_11264_block_17)
  (interval_append badTest_11264 144 152 160
  badTest_11264_block_18
  badTest_11264_block_19))
  (interval_append badTest_11264 160 176 192
  (interval_append badTest_11264 160 168 176
  badTest_11264_block_20
  badTest_11264_block_21)
  (interval_append badTest_11264 176 184 192
  badTest_11264_block_22
  badTest_11264_block_23)))
  (interval_append badTest_11264 192 224 256
  (interval_append badTest_11264 192 208 224
  (interval_append badTest_11264 192 200 208
  badTest_11264_block_24
  badTest_11264_block_25)
  (interval_append badTest_11264 208 216 224
  badTest_11264_block_26
  badTest_11264_block_27))
  (interval_append badTest_11264 224 240 256
  (interval_append badTest_11264 224 232 240
  badTest_11264_block_28
  badTest_11264_block_29)
  (interval_append badTest_11264 240 248 256
  badTest_11264_block_30
  badTest_11264_block_31)))))
theorem badTestInterval11264 : Interval badTest 11264 11520 := by
  intro i hlo hhi
  have h := badTest_11264_complete (i-11264) (Nat.zero_le _) (by omega)
  simpa only [badTest_11264, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad045 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_11520 (i : Nat) := badTest (i+11520)
theorem badTest_11520_block_0 : Interval badTest_11520 0 8 :=
  interval_of_check badTest_11520 0 8 (by decide +kernel)

theorem badTest_11520_block_1 : Interval badTest_11520 8 16 :=
  interval_of_check badTest_11520 8 8 (by decide +kernel)

theorem badTest_11520_block_2 : Interval badTest_11520 16 24 :=
  interval_of_check badTest_11520 16 8 (by decide +kernel)

theorem badTest_11520_block_3 : Interval badTest_11520 24 32 :=
  interval_of_check badTest_11520 24 8 (by decide +kernel)

theorem badTest_11520_block_4 : Interval badTest_11520 32 40 :=
  interval_of_check badTest_11520 32 8 (by decide +kernel)

theorem badTest_11520_block_5 : Interval badTest_11520 40 48 :=
  interval_of_check badTest_11520 40 8 (by decide +kernel)

theorem badTest_11520_block_6 : Interval badTest_11520 48 56 :=
  interval_of_check badTest_11520 48 8 (by decide +kernel)

theorem badTest_11520_block_7 : Interval badTest_11520 56 64 :=
  interval_of_check badTest_11520 56 8 (by decide +kernel)

theorem badTest_11520_block_8 : Interval badTest_11520 64 72 :=
  interval_of_check badTest_11520 64 8 (by decide +kernel)

theorem badTest_11520_block_9 : Interval badTest_11520 72 80 :=
  interval_of_check badTest_11520 72 8 (by decide +kernel)

theorem badTest_11520_block_10 : Interval badTest_11520 80 88 :=
  interval_of_check badTest_11520 80 8 (by decide +kernel)

theorem badTest_11520_block_11 : Interval badTest_11520 88 96 :=
  interval_of_check badTest_11520 88 8 (by decide +kernel)

theorem badTest_11520_block_12 : Interval badTest_11520 96 104 :=
  interval_of_check badTest_11520 96 8 (by decide +kernel)

theorem badTest_11520_block_13 : Interval badTest_11520 104 112 :=
  interval_of_check badTest_11520 104 8 (by decide +kernel)

theorem badTest_11520_block_14 : Interval badTest_11520 112 120 :=
  interval_of_check badTest_11520 112 8 (by decide +kernel)

theorem badTest_11520_block_15 : Interval badTest_11520 120 128 :=
  interval_of_check badTest_11520 120 8 (by decide +kernel)

theorem badTest_11520_block_16 : Interval badTest_11520 128 136 :=
  interval_of_check badTest_11520 128 8 (by decide +kernel)

theorem badTest_11520_block_17 : Interval badTest_11520 136 144 :=
  interval_of_check badTest_11520 136 8 (by decide +kernel)

theorem badTest_11520_block_18 : Interval badTest_11520 144 152 :=
  interval_of_check badTest_11520 144 8 (by decide +kernel)

theorem badTest_11520_block_19 : Interval badTest_11520 152 160 :=
  interval_of_check badTest_11520 152 8 (by decide +kernel)

theorem badTest_11520_block_20 : Interval badTest_11520 160 168 :=
  interval_of_check badTest_11520 160 8 (by decide +kernel)

theorem badTest_11520_block_21 : Interval badTest_11520 168 176 :=
  interval_of_check badTest_11520 168 8 (by decide +kernel)

theorem badTest_11520_block_22 : Interval badTest_11520 176 184 :=
  interval_of_check badTest_11520 176 8 (by decide +kernel)

theorem badTest_11520_block_23 : Interval badTest_11520 184 192 :=
  interval_of_check badTest_11520 184 8 (by decide +kernel)

theorem badTest_11520_block_24 : Interval badTest_11520 192 200 :=
  interval_of_check badTest_11520 192 8 (by decide +kernel)

theorem badTest_11520_block_25 : Interval badTest_11520 200 208 :=
  interval_of_check badTest_11520 200 8 (by decide +kernel)

theorem badTest_11520_block_26 : Interval badTest_11520 208 216 :=
  interval_of_check badTest_11520 208 8 (by decide +kernel)

theorem badTest_11520_block_27 : Interval badTest_11520 216 224 :=
  interval_of_check badTest_11520 216 8 (by decide +kernel)

theorem badTest_11520_block_28 : Interval badTest_11520 224 232 :=
  interval_of_check badTest_11520 224 8 (by decide +kernel)

theorem badTest_11520_block_29 : Interval badTest_11520 232 240 :=
  interval_of_check badTest_11520 232 8 (by decide +kernel)

theorem badTest_11520_block_30 : Interval badTest_11520 240 248 :=
  interval_of_check badTest_11520 240 8 (by decide +kernel)

theorem badTest_11520_block_31 : Interval badTest_11520 248 256 :=
  interval_of_check badTest_11520 248 8 (by decide +kernel)

theorem badTest_11520_complete : Interval badTest_11520 0 256 :=
  (interval_append badTest_11520 0 128 256
  (interval_append badTest_11520 0 64 128
  (interval_append badTest_11520 0 32 64
  (interval_append badTest_11520 0 16 32
  (interval_append badTest_11520 0 8 16
  badTest_11520_block_0
  badTest_11520_block_1)
  (interval_append badTest_11520 16 24 32
  badTest_11520_block_2
  badTest_11520_block_3))
  (interval_append badTest_11520 32 48 64
  (interval_append badTest_11520 32 40 48
  badTest_11520_block_4
  badTest_11520_block_5)
  (interval_append badTest_11520 48 56 64
  badTest_11520_block_6
  badTest_11520_block_7)))
  (interval_append badTest_11520 64 96 128
  (interval_append badTest_11520 64 80 96
  (interval_append badTest_11520 64 72 80
  badTest_11520_block_8
  badTest_11520_block_9)
  (interval_append badTest_11520 80 88 96
  badTest_11520_block_10
  badTest_11520_block_11))
  (interval_append badTest_11520 96 112 128
  (interval_append badTest_11520 96 104 112
  badTest_11520_block_12
  badTest_11520_block_13)
  (interval_append badTest_11520 112 120 128
  badTest_11520_block_14
  badTest_11520_block_15))))
  (interval_append badTest_11520 128 192 256
  (interval_append badTest_11520 128 160 192
  (interval_append badTest_11520 128 144 160
  (interval_append badTest_11520 128 136 144
  badTest_11520_block_16
  badTest_11520_block_17)
  (interval_append badTest_11520 144 152 160
  badTest_11520_block_18
  badTest_11520_block_19))
  (interval_append badTest_11520 160 176 192
  (interval_append badTest_11520 160 168 176
  badTest_11520_block_20
  badTest_11520_block_21)
  (interval_append badTest_11520 176 184 192
  badTest_11520_block_22
  badTest_11520_block_23)))
  (interval_append badTest_11520 192 224 256
  (interval_append badTest_11520 192 208 224
  (interval_append badTest_11520 192 200 208
  badTest_11520_block_24
  badTest_11520_block_25)
  (interval_append badTest_11520 208 216 224
  badTest_11520_block_26
  badTest_11520_block_27))
  (interval_append badTest_11520 224 240 256
  (interval_append badTest_11520 224 232 240
  badTest_11520_block_28
  badTest_11520_block_29)
  (interval_append badTest_11520 240 248 256
  badTest_11520_block_30
  badTest_11520_block_31)))))
theorem badTestInterval11520 : Interval badTest 11520 11776 := by
  intro i hlo hhi
  have h := badTest_11520_complete (i-11520) (Nat.zero_le _) (by omega)
  simpa only [badTest_11520, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad046 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_11776 (i : Nat) := badTest (i+11776)
theorem badTest_11776_block_0 : Interval badTest_11776 0 8 :=
  interval_of_check badTest_11776 0 8 (by decide +kernel)

theorem badTest_11776_block_1 : Interval badTest_11776 8 16 :=
  interval_of_check badTest_11776 8 8 (by decide +kernel)

theorem badTest_11776_block_2 : Interval badTest_11776 16 24 :=
  interval_of_check badTest_11776 16 8 (by decide +kernel)

theorem badTest_11776_block_3 : Interval badTest_11776 24 32 :=
  interval_of_check badTest_11776 24 8 (by decide +kernel)

theorem badTest_11776_block_4 : Interval badTest_11776 32 40 :=
  interval_of_check badTest_11776 32 8 (by decide +kernel)

theorem badTest_11776_block_5 : Interval badTest_11776 40 48 :=
  interval_of_check badTest_11776 40 8 (by decide +kernel)

theorem badTest_11776_block_6 : Interval badTest_11776 48 56 :=
  interval_of_check badTest_11776 48 8 (by decide +kernel)

theorem badTest_11776_block_7 : Interval badTest_11776 56 64 :=
  interval_of_check badTest_11776 56 8 (by decide +kernel)

theorem badTest_11776_block_8 : Interval badTest_11776 64 72 :=
  interval_of_check badTest_11776 64 8 (by decide +kernel)

theorem badTest_11776_block_9 : Interval badTest_11776 72 80 :=
  interval_of_check badTest_11776 72 8 (by decide +kernel)

theorem badTest_11776_block_10 : Interval badTest_11776 80 88 :=
  interval_of_check badTest_11776 80 8 (by decide +kernel)

theorem badTest_11776_block_11 : Interval badTest_11776 88 96 :=
  interval_of_check badTest_11776 88 8 (by decide +kernel)

theorem badTest_11776_block_12 : Interval badTest_11776 96 104 :=
  interval_of_check badTest_11776 96 8 (by decide +kernel)

theorem badTest_11776_block_13 : Interval badTest_11776 104 112 :=
  interval_of_check badTest_11776 104 8 (by decide +kernel)

theorem badTest_11776_block_14 : Interval badTest_11776 112 120 :=
  interval_of_check badTest_11776 112 8 (by decide +kernel)

theorem badTest_11776_block_15 : Interval badTest_11776 120 128 :=
  interval_of_check badTest_11776 120 8 (by decide +kernel)

theorem badTest_11776_block_16 : Interval badTest_11776 128 136 :=
  interval_of_check badTest_11776 128 8 (by decide +kernel)

theorem badTest_11776_block_17 : Interval badTest_11776 136 144 :=
  interval_of_check badTest_11776 136 8 (by decide +kernel)

theorem badTest_11776_block_18 : Interval badTest_11776 144 152 :=
  interval_of_check badTest_11776 144 8 (by decide +kernel)

theorem badTest_11776_block_19 : Interval badTest_11776 152 160 :=
  interval_of_check badTest_11776 152 8 (by decide +kernel)

theorem badTest_11776_block_20 : Interval badTest_11776 160 168 :=
  interval_of_check badTest_11776 160 8 (by decide +kernel)

theorem badTest_11776_block_21 : Interval badTest_11776 168 176 :=
  interval_of_check badTest_11776 168 8 (by decide +kernel)

theorem badTest_11776_block_22 : Interval badTest_11776 176 184 :=
  interval_of_check badTest_11776 176 8 (by decide +kernel)

theorem badTest_11776_block_23 : Interval badTest_11776 184 192 :=
  interval_of_check badTest_11776 184 8 (by decide +kernel)

theorem badTest_11776_block_24 : Interval badTest_11776 192 200 :=
  interval_of_check badTest_11776 192 8 (by decide +kernel)

theorem badTest_11776_block_25 : Interval badTest_11776 200 208 :=
  interval_of_check badTest_11776 200 8 (by decide +kernel)

theorem badTest_11776_block_26 : Interval badTest_11776 208 216 :=
  interval_of_check badTest_11776 208 8 (by decide +kernel)

theorem badTest_11776_block_27 : Interval badTest_11776 216 224 :=
  interval_of_check badTest_11776 216 8 (by decide +kernel)

theorem badTest_11776_block_28 : Interval badTest_11776 224 232 :=
  interval_of_check badTest_11776 224 8 (by decide +kernel)

theorem badTest_11776_block_29 : Interval badTest_11776 232 240 :=
  interval_of_check badTest_11776 232 8 (by decide +kernel)

theorem badTest_11776_block_30 : Interval badTest_11776 240 248 :=
  interval_of_check badTest_11776 240 8 (by decide +kernel)

theorem badTest_11776_block_31 : Interval badTest_11776 248 256 :=
  interval_of_check badTest_11776 248 8 (by decide +kernel)

theorem badTest_11776_complete : Interval badTest_11776 0 256 :=
  (interval_append badTest_11776 0 128 256
  (interval_append badTest_11776 0 64 128
  (interval_append badTest_11776 0 32 64
  (interval_append badTest_11776 0 16 32
  (interval_append badTest_11776 0 8 16
  badTest_11776_block_0
  badTest_11776_block_1)
  (interval_append badTest_11776 16 24 32
  badTest_11776_block_2
  badTest_11776_block_3))
  (interval_append badTest_11776 32 48 64
  (interval_append badTest_11776 32 40 48
  badTest_11776_block_4
  badTest_11776_block_5)
  (interval_append badTest_11776 48 56 64
  badTest_11776_block_6
  badTest_11776_block_7)))
  (interval_append badTest_11776 64 96 128
  (interval_append badTest_11776 64 80 96
  (interval_append badTest_11776 64 72 80
  badTest_11776_block_8
  badTest_11776_block_9)
  (interval_append badTest_11776 80 88 96
  badTest_11776_block_10
  badTest_11776_block_11))
  (interval_append badTest_11776 96 112 128
  (interval_append badTest_11776 96 104 112
  badTest_11776_block_12
  badTest_11776_block_13)
  (interval_append badTest_11776 112 120 128
  badTest_11776_block_14
  badTest_11776_block_15))))
  (interval_append badTest_11776 128 192 256
  (interval_append badTest_11776 128 160 192
  (interval_append badTest_11776 128 144 160
  (interval_append badTest_11776 128 136 144
  badTest_11776_block_16
  badTest_11776_block_17)
  (interval_append badTest_11776 144 152 160
  badTest_11776_block_18
  badTest_11776_block_19))
  (interval_append badTest_11776 160 176 192
  (interval_append badTest_11776 160 168 176
  badTest_11776_block_20
  badTest_11776_block_21)
  (interval_append badTest_11776 176 184 192
  badTest_11776_block_22
  badTest_11776_block_23)))
  (interval_append badTest_11776 192 224 256
  (interval_append badTest_11776 192 208 224
  (interval_append badTest_11776 192 200 208
  badTest_11776_block_24
  badTest_11776_block_25)
  (interval_append badTest_11776 208 216 224
  badTest_11776_block_26
  badTest_11776_block_27))
  (interval_append badTest_11776 224 240 256
  (interval_append badTest_11776 224 232 240
  badTest_11776_block_28
  badTest_11776_block_29)
  (interval_append badTest_11776 240 248 256
  badTest_11776_block_30
  badTest_11776_block_31)))))
theorem badTestInterval11776 : Interval badTest 11776 12032 := by
  intro i hlo hhi
  have h := badTest_11776_complete (i-11776) (Nat.zero_le _) (by omega)
  simpa only [badTest_11776, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad047 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_12032 (i : Nat) := badTest (i+12032)
theorem badTest_12032_block_0 : Interval badTest_12032 0 8 :=
  interval_of_check badTest_12032 0 8 (by decide +kernel)

theorem badTest_12032_block_1 : Interval badTest_12032 8 16 :=
  interval_of_check badTest_12032 8 8 (by decide +kernel)

theorem badTest_12032_block_2 : Interval badTest_12032 16 24 :=
  interval_of_check badTest_12032 16 8 (by decide +kernel)

theorem badTest_12032_block_3 : Interval badTest_12032 24 32 :=
  interval_of_check badTest_12032 24 8 (by decide +kernel)

theorem badTest_12032_block_4 : Interval badTest_12032 32 40 :=
  interval_of_check badTest_12032 32 8 (by decide +kernel)

theorem badTest_12032_block_5 : Interval badTest_12032 40 48 :=
  interval_of_check badTest_12032 40 8 (by decide +kernel)

theorem badTest_12032_block_6 : Interval badTest_12032 48 56 :=
  interval_of_check badTest_12032 48 8 (by decide +kernel)

theorem badTest_12032_block_7 : Interval badTest_12032 56 64 :=
  interval_of_check badTest_12032 56 8 (by decide +kernel)

theorem badTest_12032_block_8 : Interval badTest_12032 64 72 :=
  interval_of_check badTest_12032 64 8 (by decide +kernel)

theorem badTest_12032_block_9 : Interval badTest_12032 72 80 :=
  interval_of_check badTest_12032 72 8 (by decide +kernel)

theorem badTest_12032_block_10 : Interval badTest_12032 80 88 :=
  interval_of_check badTest_12032 80 8 (by decide +kernel)

theorem badTest_12032_block_11 : Interval badTest_12032 88 96 :=
  interval_of_check badTest_12032 88 8 (by decide +kernel)

theorem badTest_12032_block_12 : Interval badTest_12032 96 104 :=
  interval_of_check badTest_12032 96 8 (by decide +kernel)

theorem badTest_12032_block_13 : Interval badTest_12032 104 112 :=
  interval_of_check badTest_12032 104 8 (by decide +kernel)

theorem badTest_12032_block_14 : Interval badTest_12032 112 120 :=
  interval_of_check badTest_12032 112 8 (by decide +kernel)

theorem badTest_12032_block_15 : Interval badTest_12032 120 128 :=
  interval_of_check badTest_12032 120 8 (by decide +kernel)

theorem badTest_12032_block_16 : Interval badTest_12032 128 136 :=
  interval_of_check badTest_12032 128 8 (by decide +kernel)

theorem badTest_12032_block_17 : Interval badTest_12032 136 144 :=
  interval_of_check badTest_12032 136 8 (by decide +kernel)

theorem badTest_12032_block_18 : Interval badTest_12032 144 152 :=
  interval_of_check badTest_12032 144 8 (by decide +kernel)

theorem badTest_12032_block_19 : Interval badTest_12032 152 160 :=
  interval_of_check badTest_12032 152 8 (by decide +kernel)

theorem badTest_12032_block_20 : Interval badTest_12032 160 168 :=
  interval_of_check badTest_12032 160 8 (by decide +kernel)

theorem badTest_12032_block_21 : Interval badTest_12032 168 176 :=
  interval_of_check badTest_12032 168 8 (by decide +kernel)

theorem badTest_12032_block_22 : Interval badTest_12032 176 184 :=
  interval_of_check badTest_12032 176 8 (by decide +kernel)

theorem badTest_12032_block_23 : Interval badTest_12032 184 192 :=
  interval_of_check badTest_12032 184 8 (by decide +kernel)

theorem badTest_12032_block_24 : Interval badTest_12032 192 200 :=
  interval_of_check badTest_12032 192 8 (by decide +kernel)

theorem badTest_12032_block_25 : Interval badTest_12032 200 208 :=
  interval_of_check badTest_12032 200 8 (by decide +kernel)

theorem badTest_12032_block_26 : Interval badTest_12032 208 216 :=
  interval_of_check badTest_12032 208 8 (by decide +kernel)

theorem badTest_12032_block_27 : Interval badTest_12032 216 224 :=
  interval_of_check badTest_12032 216 8 (by decide +kernel)

theorem badTest_12032_block_28 : Interval badTest_12032 224 232 :=
  interval_of_check badTest_12032 224 8 (by decide +kernel)

theorem badTest_12032_block_29 : Interval badTest_12032 232 240 :=
  interval_of_check badTest_12032 232 8 (by decide +kernel)

theorem badTest_12032_block_30 : Interval badTest_12032 240 248 :=
  interval_of_check badTest_12032 240 8 (by decide +kernel)

theorem badTest_12032_block_31 : Interval badTest_12032 248 256 :=
  interval_of_check badTest_12032 248 8 (by decide +kernel)

theorem badTest_12032_complete : Interval badTest_12032 0 256 :=
  (interval_append badTest_12032 0 128 256
  (interval_append badTest_12032 0 64 128
  (interval_append badTest_12032 0 32 64
  (interval_append badTest_12032 0 16 32
  (interval_append badTest_12032 0 8 16
  badTest_12032_block_0
  badTest_12032_block_1)
  (interval_append badTest_12032 16 24 32
  badTest_12032_block_2
  badTest_12032_block_3))
  (interval_append badTest_12032 32 48 64
  (interval_append badTest_12032 32 40 48
  badTest_12032_block_4
  badTest_12032_block_5)
  (interval_append badTest_12032 48 56 64
  badTest_12032_block_6
  badTest_12032_block_7)))
  (interval_append badTest_12032 64 96 128
  (interval_append badTest_12032 64 80 96
  (interval_append badTest_12032 64 72 80
  badTest_12032_block_8
  badTest_12032_block_9)
  (interval_append badTest_12032 80 88 96
  badTest_12032_block_10
  badTest_12032_block_11))
  (interval_append badTest_12032 96 112 128
  (interval_append badTest_12032 96 104 112
  badTest_12032_block_12
  badTest_12032_block_13)
  (interval_append badTest_12032 112 120 128
  badTest_12032_block_14
  badTest_12032_block_15))))
  (interval_append badTest_12032 128 192 256
  (interval_append badTest_12032 128 160 192
  (interval_append badTest_12032 128 144 160
  (interval_append badTest_12032 128 136 144
  badTest_12032_block_16
  badTest_12032_block_17)
  (interval_append badTest_12032 144 152 160
  badTest_12032_block_18
  badTest_12032_block_19))
  (interval_append badTest_12032 160 176 192
  (interval_append badTest_12032 160 168 176
  badTest_12032_block_20
  badTest_12032_block_21)
  (interval_append badTest_12032 176 184 192
  badTest_12032_block_22
  badTest_12032_block_23)))
  (interval_append badTest_12032 192 224 256
  (interval_append badTest_12032 192 208 224
  (interval_append badTest_12032 192 200 208
  badTest_12032_block_24
  badTest_12032_block_25)
  (interval_append badTest_12032 208 216 224
  badTest_12032_block_26
  badTest_12032_block_27))
  (interval_append badTest_12032 224 240 256
  (interval_append badTest_12032 224 232 240
  badTest_12032_block_28
  badTest_12032_block_29)
  (interval_append badTest_12032 240 248 256
  badTest_12032_block_30
  badTest_12032_block_31)))))
theorem badTestInterval12032 : Interval badTest 12032 12288 := by
  intro i hlo hhi
  have h := badTest_12032_complete (i-12032) (Nat.zero_le _) (by omega)
  simpa only [badTest_12032, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad048 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_12288 (i : Nat) := badTest (i+12288)
theorem badTest_12288_block_0 : Interval badTest_12288 0 8 :=
  interval_of_check badTest_12288 0 8 (by decide +kernel)

theorem badTest_12288_block_1 : Interval badTest_12288 8 16 :=
  interval_of_check badTest_12288 8 8 (by decide +kernel)

theorem badTest_12288_block_2 : Interval badTest_12288 16 24 :=
  interval_of_check badTest_12288 16 8 (by decide +kernel)

theorem badTest_12288_block_3 : Interval badTest_12288 24 32 :=
  interval_of_check badTest_12288 24 8 (by decide +kernel)

theorem badTest_12288_block_4 : Interval badTest_12288 32 40 :=
  interval_of_check badTest_12288 32 8 (by decide +kernel)

theorem badTest_12288_block_5 : Interval badTest_12288 40 48 :=
  interval_of_check badTest_12288 40 8 (by decide +kernel)

theorem badTest_12288_block_6 : Interval badTest_12288 48 56 :=
  interval_of_check badTest_12288 48 8 (by decide +kernel)

theorem badTest_12288_block_7 : Interval badTest_12288 56 64 :=
  interval_of_check badTest_12288 56 8 (by decide +kernel)

theorem badTest_12288_block_8 : Interval badTest_12288 64 72 :=
  interval_of_check badTest_12288 64 8 (by decide +kernel)

theorem badTest_12288_block_9 : Interval badTest_12288 72 80 :=
  interval_of_check badTest_12288 72 8 (by decide +kernel)

theorem badTest_12288_block_10 : Interval badTest_12288 80 88 :=
  interval_of_check badTest_12288 80 8 (by decide +kernel)

theorem badTest_12288_block_11 : Interval badTest_12288 88 96 :=
  interval_of_check badTest_12288 88 8 (by decide +kernel)

theorem badTest_12288_block_12 : Interval badTest_12288 96 104 :=
  interval_of_check badTest_12288 96 8 (by decide +kernel)

theorem badTest_12288_block_13 : Interval badTest_12288 104 112 :=
  interval_of_check badTest_12288 104 8 (by decide +kernel)

theorem badTest_12288_block_14 : Interval badTest_12288 112 120 :=
  interval_of_check badTest_12288 112 8 (by decide +kernel)

theorem badTest_12288_block_15 : Interval badTest_12288 120 128 :=
  interval_of_check badTest_12288 120 8 (by decide +kernel)

theorem badTest_12288_block_16 : Interval badTest_12288 128 136 :=
  interval_of_check badTest_12288 128 8 (by decide +kernel)

theorem badTest_12288_block_17 : Interval badTest_12288 136 144 :=
  interval_of_check badTest_12288 136 8 (by decide +kernel)

theorem badTest_12288_block_18 : Interval badTest_12288 144 152 :=
  interval_of_check badTest_12288 144 8 (by decide +kernel)

theorem badTest_12288_block_19 : Interval badTest_12288 152 160 :=
  interval_of_check badTest_12288 152 8 (by decide +kernel)

theorem badTest_12288_block_20 : Interval badTest_12288 160 168 :=
  interval_of_check badTest_12288 160 8 (by decide +kernel)

theorem badTest_12288_block_21 : Interval badTest_12288 168 176 :=
  interval_of_check badTest_12288 168 8 (by decide +kernel)

theorem badTest_12288_block_22 : Interval badTest_12288 176 184 :=
  interval_of_check badTest_12288 176 8 (by decide +kernel)

theorem badTest_12288_block_23 : Interval badTest_12288 184 192 :=
  interval_of_check badTest_12288 184 8 (by decide +kernel)

theorem badTest_12288_block_24 : Interval badTest_12288 192 200 :=
  interval_of_check badTest_12288 192 8 (by decide +kernel)

theorem badTest_12288_block_25 : Interval badTest_12288 200 208 :=
  interval_of_check badTest_12288 200 8 (by decide +kernel)

theorem badTest_12288_block_26 : Interval badTest_12288 208 216 :=
  interval_of_check badTest_12288 208 8 (by decide +kernel)

theorem badTest_12288_block_27 : Interval badTest_12288 216 224 :=
  interval_of_check badTest_12288 216 8 (by decide +kernel)

theorem badTest_12288_block_28 : Interval badTest_12288 224 232 :=
  interval_of_check badTest_12288 224 8 (by decide +kernel)

theorem badTest_12288_block_29 : Interval badTest_12288 232 240 :=
  interval_of_check badTest_12288 232 8 (by decide +kernel)

theorem badTest_12288_block_30 : Interval badTest_12288 240 248 :=
  interval_of_check badTest_12288 240 8 (by decide +kernel)

theorem badTest_12288_block_31 : Interval badTest_12288 248 256 :=
  interval_of_check badTest_12288 248 8 (by decide +kernel)

theorem badTest_12288_complete : Interval badTest_12288 0 256 :=
  (interval_append badTest_12288 0 128 256
  (interval_append badTest_12288 0 64 128
  (interval_append badTest_12288 0 32 64
  (interval_append badTest_12288 0 16 32
  (interval_append badTest_12288 0 8 16
  badTest_12288_block_0
  badTest_12288_block_1)
  (interval_append badTest_12288 16 24 32
  badTest_12288_block_2
  badTest_12288_block_3))
  (interval_append badTest_12288 32 48 64
  (interval_append badTest_12288 32 40 48
  badTest_12288_block_4
  badTest_12288_block_5)
  (interval_append badTest_12288 48 56 64
  badTest_12288_block_6
  badTest_12288_block_7)))
  (interval_append badTest_12288 64 96 128
  (interval_append badTest_12288 64 80 96
  (interval_append badTest_12288 64 72 80
  badTest_12288_block_8
  badTest_12288_block_9)
  (interval_append badTest_12288 80 88 96
  badTest_12288_block_10
  badTest_12288_block_11))
  (interval_append badTest_12288 96 112 128
  (interval_append badTest_12288 96 104 112
  badTest_12288_block_12
  badTest_12288_block_13)
  (interval_append badTest_12288 112 120 128
  badTest_12288_block_14
  badTest_12288_block_15))))
  (interval_append badTest_12288 128 192 256
  (interval_append badTest_12288 128 160 192
  (interval_append badTest_12288 128 144 160
  (interval_append badTest_12288 128 136 144
  badTest_12288_block_16
  badTest_12288_block_17)
  (interval_append badTest_12288 144 152 160
  badTest_12288_block_18
  badTest_12288_block_19))
  (interval_append badTest_12288 160 176 192
  (interval_append badTest_12288 160 168 176
  badTest_12288_block_20
  badTest_12288_block_21)
  (interval_append badTest_12288 176 184 192
  badTest_12288_block_22
  badTest_12288_block_23)))
  (interval_append badTest_12288 192 224 256
  (interval_append badTest_12288 192 208 224
  (interval_append badTest_12288 192 200 208
  badTest_12288_block_24
  badTest_12288_block_25)
  (interval_append badTest_12288 208 216 224
  badTest_12288_block_26
  badTest_12288_block_27))
  (interval_append badTest_12288 224 240 256
  (interval_append badTest_12288 224 232 240
  badTest_12288_block_28
  badTest_12288_block_29)
  (interval_append badTest_12288 240 248 256
  badTest_12288_block_30
  badTest_12288_block_31)))))
theorem badTestInterval12288 : Interval badTest 12288 12544 := by
  intro i hlo hhi
  have h := badTest_12288_complete (i-12288) (Nat.zero_le _) (by omega)
  simpa only [badTest_12288, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad049 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_12544 (i : Nat) := badTest (i+12544)
theorem badTest_12544_block_0 : Interval badTest_12544 0 8 :=
  interval_of_check badTest_12544 0 8 (by decide +kernel)

theorem badTest_12544_block_1 : Interval badTest_12544 8 16 :=
  interval_of_check badTest_12544 8 8 (by decide +kernel)

theorem badTest_12544_block_2 : Interval badTest_12544 16 24 :=
  interval_of_check badTest_12544 16 8 (by decide +kernel)

theorem badTest_12544_block_3 : Interval badTest_12544 24 32 :=
  interval_of_check badTest_12544 24 8 (by decide +kernel)

theorem badTest_12544_block_4 : Interval badTest_12544 32 40 :=
  interval_of_check badTest_12544 32 8 (by decide +kernel)

theorem badTest_12544_block_5 : Interval badTest_12544 40 48 :=
  interval_of_check badTest_12544 40 8 (by decide +kernel)

theorem badTest_12544_block_6 : Interval badTest_12544 48 56 :=
  interval_of_check badTest_12544 48 8 (by decide +kernel)

theorem badTest_12544_block_7 : Interval badTest_12544 56 64 :=
  interval_of_check badTest_12544 56 8 (by decide +kernel)

theorem badTest_12544_block_8 : Interval badTest_12544 64 72 :=
  interval_of_check badTest_12544 64 8 (by decide +kernel)

theorem badTest_12544_block_9 : Interval badTest_12544 72 80 :=
  interval_of_check badTest_12544 72 8 (by decide +kernel)

theorem badTest_12544_block_10 : Interval badTest_12544 80 88 :=
  interval_of_check badTest_12544 80 8 (by decide +kernel)

theorem badTest_12544_block_11 : Interval badTest_12544 88 96 :=
  interval_of_check badTest_12544 88 8 (by decide +kernel)

theorem badTest_12544_block_12 : Interval badTest_12544 96 104 :=
  interval_of_check badTest_12544 96 8 (by decide +kernel)

theorem badTest_12544_block_13 : Interval badTest_12544 104 112 :=
  interval_of_check badTest_12544 104 8 (by decide +kernel)

theorem badTest_12544_block_14 : Interval badTest_12544 112 120 :=
  interval_of_check badTest_12544 112 8 (by decide +kernel)

theorem badTest_12544_block_15 : Interval badTest_12544 120 128 :=
  interval_of_check badTest_12544 120 8 (by decide +kernel)

theorem badTest_12544_block_16 : Interval badTest_12544 128 136 :=
  interval_of_check badTest_12544 128 8 (by decide +kernel)

theorem badTest_12544_block_17 : Interval badTest_12544 136 144 :=
  interval_of_check badTest_12544 136 8 (by decide +kernel)

theorem badTest_12544_block_18 : Interval badTest_12544 144 152 :=
  interval_of_check badTest_12544 144 8 (by decide +kernel)

theorem badTest_12544_block_19 : Interval badTest_12544 152 160 :=
  interval_of_check badTest_12544 152 8 (by decide +kernel)

theorem badTest_12544_block_20 : Interval badTest_12544 160 168 :=
  interval_of_check badTest_12544 160 8 (by decide +kernel)

theorem badTest_12544_block_21 : Interval badTest_12544 168 176 :=
  interval_of_check badTest_12544 168 8 (by decide +kernel)

theorem badTest_12544_block_22 : Interval badTest_12544 176 184 :=
  interval_of_check badTest_12544 176 8 (by decide +kernel)

theorem badTest_12544_block_23 : Interval badTest_12544 184 192 :=
  interval_of_check badTest_12544 184 8 (by decide +kernel)

theorem badTest_12544_block_24 : Interval badTest_12544 192 200 :=
  interval_of_check badTest_12544 192 8 (by decide +kernel)

theorem badTest_12544_block_25 : Interval badTest_12544 200 208 :=
  interval_of_check badTest_12544 200 8 (by decide +kernel)

theorem badTest_12544_block_26 : Interval badTest_12544 208 216 :=
  interval_of_check badTest_12544 208 8 (by decide +kernel)

theorem badTest_12544_block_27 : Interval badTest_12544 216 224 :=
  interval_of_check badTest_12544 216 8 (by decide +kernel)

theorem badTest_12544_block_28 : Interval badTest_12544 224 232 :=
  interval_of_check badTest_12544 224 8 (by decide +kernel)

theorem badTest_12544_block_29 : Interval badTest_12544 232 240 :=
  interval_of_check badTest_12544 232 8 (by decide +kernel)

theorem badTest_12544_block_30 : Interval badTest_12544 240 248 :=
  interval_of_check badTest_12544 240 8 (by decide +kernel)

theorem badTest_12544_block_31 : Interval badTest_12544 248 256 :=
  interval_of_check badTest_12544 248 8 (by decide +kernel)

theorem badTest_12544_complete : Interval badTest_12544 0 256 :=
  (interval_append badTest_12544 0 128 256
  (interval_append badTest_12544 0 64 128
  (interval_append badTest_12544 0 32 64
  (interval_append badTest_12544 0 16 32
  (interval_append badTest_12544 0 8 16
  badTest_12544_block_0
  badTest_12544_block_1)
  (interval_append badTest_12544 16 24 32
  badTest_12544_block_2
  badTest_12544_block_3))
  (interval_append badTest_12544 32 48 64
  (interval_append badTest_12544 32 40 48
  badTest_12544_block_4
  badTest_12544_block_5)
  (interval_append badTest_12544 48 56 64
  badTest_12544_block_6
  badTest_12544_block_7)))
  (interval_append badTest_12544 64 96 128
  (interval_append badTest_12544 64 80 96
  (interval_append badTest_12544 64 72 80
  badTest_12544_block_8
  badTest_12544_block_9)
  (interval_append badTest_12544 80 88 96
  badTest_12544_block_10
  badTest_12544_block_11))
  (interval_append badTest_12544 96 112 128
  (interval_append badTest_12544 96 104 112
  badTest_12544_block_12
  badTest_12544_block_13)
  (interval_append badTest_12544 112 120 128
  badTest_12544_block_14
  badTest_12544_block_15))))
  (interval_append badTest_12544 128 192 256
  (interval_append badTest_12544 128 160 192
  (interval_append badTest_12544 128 144 160
  (interval_append badTest_12544 128 136 144
  badTest_12544_block_16
  badTest_12544_block_17)
  (interval_append badTest_12544 144 152 160
  badTest_12544_block_18
  badTest_12544_block_19))
  (interval_append badTest_12544 160 176 192
  (interval_append badTest_12544 160 168 176
  badTest_12544_block_20
  badTest_12544_block_21)
  (interval_append badTest_12544 176 184 192
  badTest_12544_block_22
  badTest_12544_block_23)))
  (interval_append badTest_12544 192 224 256
  (interval_append badTest_12544 192 208 224
  (interval_append badTest_12544 192 200 208
  badTest_12544_block_24
  badTest_12544_block_25)
  (interval_append badTest_12544 208 216 224
  badTest_12544_block_26
  badTest_12544_block_27))
  (interval_append badTest_12544 224 240 256
  (interval_append badTest_12544 224 232 240
  badTest_12544_block_28
  badTest_12544_block_29)
  (interval_append badTest_12544 240 248 256
  badTest_12544_block_30
  badTest_12544_block_31)))))
theorem badTestInterval12544 : Interval badTest 12544 12800 := by
  intro i hlo hhi
  have h := badTest_12544_complete (i-12544) (Nat.zero_le _) (by omega)
  simpa only [badTest_12544, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad050 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_12800 (i : Nat) := badTest (i+12800)
theorem badTest_12800_block_0 : Interval badTest_12800 0 8 :=
  interval_of_check badTest_12800 0 8 (by decide +kernel)

theorem badTest_12800_block_1 : Interval badTest_12800 8 16 :=
  interval_of_check badTest_12800 8 8 (by decide +kernel)

theorem badTest_12800_block_2 : Interval badTest_12800 16 24 :=
  interval_of_check badTest_12800 16 8 (by decide +kernel)

theorem badTest_12800_block_3 : Interval badTest_12800 24 32 :=
  interval_of_check badTest_12800 24 8 (by decide +kernel)

theorem badTest_12800_block_4 : Interval badTest_12800 32 40 :=
  interval_of_check badTest_12800 32 8 (by decide +kernel)

theorem badTest_12800_block_5 : Interval badTest_12800 40 48 :=
  interval_of_check badTest_12800 40 8 (by decide +kernel)

theorem badTest_12800_block_6 : Interval badTest_12800 48 56 :=
  interval_of_check badTest_12800 48 8 (by decide +kernel)

theorem badTest_12800_block_7 : Interval badTest_12800 56 64 :=
  interval_of_check badTest_12800 56 8 (by decide +kernel)

theorem badTest_12800_block_8 : Interval badTest_12800 64 72 :=
  interval_of_check badTest_12800 64 8 (by decide +kernel)

theorem badTest_12800_block_9 : Interval badTest_12800 72 80 :=
  interval_of_check badTest_12800 72 8 (by decide +kernel)

theorem badTest_12800_block_10 : Interval badTest_12800 80 88 :=
  interval_of_check badTest_12800 80 8 (by decide +kernel)

theorem badTest_12800_block_11 : Interval badTest_12800 88 96 :=
  interval_of_check badTest_12800 88 8 (by decide +kernel)

theorem badTest_12800_block_12 : Interval badTest_12800 96 104 :=
  interval_of_check badTest_12800 96 8 (by decide +kernel)

theorem badTest_12800_block_13 : Interval badTest_12800 104 112 :=
  interval_of_check badTest_12800 104 8 (by decide +kernel)

theorem badTest_12800_block_14 : Interval badTest_12800 112 120 :=
  interval_of_check badTest_12800 112 8 (by decide +kernel)

theorem badTest_12800_block_15 : Interval badTest_12800 120 128 :=
  interval_of_check badTest_12800 120 8 (by decide +kernel)

theorem badTest_12800_block_16 : Interval badTest_12800 128 136 :=
  interval_of_check badTest_12800 128 8 (by decide +kernel)

theorem badTest_12800_block_17 : Interval badTest_12800 136 144 :=
  interval_of_check badTest_12800 136 8 (by decide +kernel)

theorem badTest_12800_block_18 : Interval badTest_12800 144 152 :=
  interval_of_check badTest_12800 144 8 (by decide +kernel)

theorem badTest_12800_block_19 : Interval badTest_12800 152 160 :=
  interval_of_check badTest_12800 152 8 (by decide +kernel)

theorem badTest_12800_block_20 : Interval badTest_12800 160 168 :=
  interval_of_check badTest_12800 160 8 (by decide +kernel)

theorem badTest_12800_block_21 : Interval badTest_12800 168 176 :=
  interval_of_check badTest_12800 168 8 (by decide +kernel)

theorem badTest_12800_block_22 : Interval badTest_12800 176 184 :=
  interval_of_check badTest_12800 176 8 (by decide +kernel)

theorem badTest_12800_block_23 : Interval badTest_12800 184 192 :=
  interval_of_check badTest_12800 184 8 (by decide +kernel)

theorem badTest_12800_block_24 : Interval badTest_12800 192 200 :=
  interval_of_check badTest_12800 192 8 (by decide +kernel)

theorem badTest_12800_block_25 : Interval badTest_12800 200 208 :=
  interval_of_check badTest_12800 200 8 (by decide +kernel)

theorem badTest_12800_block_26 : Interval badTest_12800 208 216 :=
  interval_of_check badTest_12800 208 8 (by decide +kernel)

theorem badTest_12800_block_27 : Interval badTest_12800 216 224 :=
  interval_of_check badTest_12800 216 8 (by decide +kernel)

theorem badTest_12800_block_28 : Interval badTest_12800 224 232 :=
  interval_of_check badTest_12800 224 8 (by decide +kernel)

theorem badTest_12800_block_29 : Interval badTest_12800 232 240 :=
  interval_of_check badTest_12800 232 8 (by decide +kernel)

theorem badTest_12800_block_30 : Interval badTest_12800 240 248 :=
  interval_of_check badTest_12800 240 8 (by decide +kernel)

theorem badTest_12800_block_31 : Interval badTest_12800 248 256 :=
  interval_of_check badTest_12800 248 8 (by decide +kernel)

theorem badTest_12800_complete : Interval badTest_12800 0 256 :=
  (interval_append badTest_12800 0 128 256
  (interval_append badTest_12800 0 64 128
  (interval_append badTest_12800 0 32 64
  (interval_append badTest_12800 0 16 32
  (interval_append badTest_12800 0 8 16
  badTest_12800_block_0
  badTest_12800_block_1)
  (interval_append badTest_12800 16 24 32
  badTest_12800_block_2
  badTest_12800_block_3))
  (interval_append badTest_12800 32 48 64
  (interval_append badTest_12800 32 40 48
  badTest_12800_block_4
  badTest_12800_block_5)
  (interval_append badTest_12800 48 56 64
  badTest_12800_block_6
  badTest_12800_block_7)))
  (interval_append badTest_12800 64 96 128
  (interval_append badTest_12800 64 80 96
  (interval_append badTest_12800 64 72 80
  badTest_12800_block_8
  badTest_12800_block_9)
  (interval_append badTest_12800 80 88 96
  badTest_12800_block_10
  badTest_12800_block_11))
  (interval_append badTest_12800 96 112 128
  (interval_append badTest_12800 96 104 112
  badTest_12800_block_12
  badTest_12800_block_13)
  (interval_append badTest_12800 112 120 128
  badTest_12800_block_14
  badTest_12800_block_15))))
  (interval_append badTest_12800 128 192 256
  (interval_append badTest_12800 128 160 192
  (interval_append badTest_12800 128 144 160
  (interval_append badTest_12800 128 136 144
  badTest_12800_block_16
  badTest_12800_block_17)
  (interval_append badTest_12800 144 152 160
  badTest_12800_block_18
  badTest_12800_block_19))
  (interval_append badTest_12800 160 176 192
  (interval_append badTest_12800 160 168 176
  badTest_12800_block_20
  badTest_12800_block_21)
  (interval_append badTest_12800 176 184 192
  badTest_12800_block_22
  badTest_12800_block_23)))
  (interval_append badTest_12800 192 224 256
  (interval_append badTest_12800 192 208 224
  (interval_append badTest_12800 192 200 208
  badTest_12800_block_24
  badTest_12800_block_25)
  (interval_append badTest_12800 208 216 224
  badTest_12800_block_26
  badTest_12800_block_27))
  (interval_append badTest_12800 224 240 256
  (interval_append badTest_12800 224 232 240
  badTest_12800_block_28
  badTest_12800_block_29)
  (interval_append badTest_12800 240 248 256
  badTest_12800_block_30
  badTest_12800_block_31)))))
theorem badTestInterval12800 : Interval badTest 12800 13056 := by
  intro i hlo hhi
  have h := badTest_12800_complete (i-12800) (Nat.zero_le _) (by omega)
  simpa only [badTest_12800, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad051 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_13056 (i : Nat) := badTest (i+13056)
theorem badTest_13056_block_0 : Interval badTest_13056 0 8 :=
  interval_of_check badTest_13056 0 8 (by decide +kernel)

theorem badTest_13056_block_1 : Interval badTest_13056 8 16 :=
  interval_of_check badTest_13056 8 8 (by decide +kernel)

theorem badTest_13056_block_2 : Interval badTest_13056 16 24 :=
  interval_of_check badTest_13056 16 8 (by decide +kernel)

theorem badTest_13056_block_3 : Interval badTest_13056 24 32 :=
  interval_of_check badTest_13056 24 8 (by decide +kernel)

theorem badTest_13056_block_4 : Interval badTest_13056 32 40 :=
  interval_of_check badTest_13056 32 8 (by decide +kernel)

theorem badTest_13056_block_5 : Interval badTest_13056 40 48 :=
  interval_of_check badTest_13056 40 8 (by decide +kernel)

theorem badTest_13056_block_6 : Interval badTest_13056 48 56 :=
  interval_of_check badTest_13056 48 8 (by decide +kernel)

theorem badTest_13056_block_7 : Interval badTest_13056 56 64 :=
  interval_of_check badTest_13056 56 8 (by decide +kernel)

theorem badTest_13056_block_8 : Interval badTest_13056 64 72 :=
  interval_of_check badTest_13056 64 8 (by decide +kernel)

theorem badTest_13056_block_9 : Interval badTest_13056 72 80 :=
  interval_of_check badTest_13056 72 8 (by decide +kernel)

theorem badTest_13056_block_10 : Interval badTest_13056 80 88 :=
  interval_of_check badTest_13056 80 8 (by decide +kernel)

theorem badTest_13056_block_11 : Interval badTest_13056 88 96 :=
  interval_of_check badTest_13056 88 8 (by decide +kernel)

theorem badTest_13056_block_12 : Interval badTest_13056 96 104 :=
  interval_of_check badTest_13056 96 8 (by decide +kernel)

theorem badTest_13056_block_13 : Interval badTest_13056 104 112 :=
  interval_of_check badTest_13056 104 8 (by decide +kernel)

theorem badTest_13056_block_14 : Interval badTest_13056 112 120 :=
  interval_of_check badTest_13056 112 8 (by decide +kernel)

theorem badTest_13056_block_15 : Interval badTest_13056 120 128 :=
  interval_of_check badTest_13056 120 8 (by decide +kernel)

theorem badTest_13056_block_16 : Interval badTest_13056 128 136 :=
  interval_of_check badTest_13056 128 8 (by decide +kernel)

theorem badTest_13056_block_17 : Interval badTest_13056 136 144 :=
  interval_of_check badTest_13056 136 8 (by decide +kernel)

theorem badTest_13056_block_18 : Interval badTest_13056 144 152 :=
  interval_of_check badTest_13056 144 8 (by decide +kernel)

theorem badTest_13056_block_19 : Interval badTest_13056 152 160 :=
  interval_of_check badTest_13056 152 8 (by decide +kernel)

theorem badTest_13056_block_20 : Interval badTest_13056 160 168 :=
  interval_of_check badTest_13056 160 8 (by decide +kernel)

theorem badTest_13056_block_21 : Interval badTest_13056 168 176 :=
  interval_of_check badTest_13056 168 8 (by decide +kernel)

theorem badTest_13056_block_22 : Interval badTest_13056 176 184 :=
  interval_of_check badTest_13056 176 8 (by decide +kernel)

theorem badTest_13056_block_23 : Interval badTest_13056 184 192 :=
  interval_of_check badTest_13056 184 8 (by decide +kernel)

theorem badTest_13056_block_24 : Interval badTest_13056 192 200 :=
  interval_of_check badTest_13056 192 8 (by decide +kernel)

theorem badTest_13056_block_25 : Interval badTest_13056 200 208 :=
  interval_of_check badTest_13056 200 8 (by decide +kernel)

theorem badTest_13056_block_26 : Interval badTest_13056 208 216 :=
  interval_of_check badTest_13056 208 8 (by decide +kernel)

theorem badTest_13056_block_27 : Interval badTest_13056 216 224 :=
  interval_of_check badTest_13056 216 8 (by decide +kernel)

theorem badTest_13056_block_28 : Interval badTest_13056 224 232 :=
  interval_of_check badTest_13056 224 8 (by decide +kernel)

theorem badTest_13056_block_29 : Interval badTest_13056 232 240 :=
  interval_of_check badTest_13056 232 8 (by decide +kernel)

theorem badTest_13056_block_30 : Interval badTest_13056 240 248 :=
  interval_of_check badTest_13056 240 8 (by decide +kernel)

theorem badTest_13056_block_31 : Interval badTest_13056 248 256 :=
  interval_of_check badTest_13056 248 8 (by decide +kernel)

theorem badTest_13056_complete : Interval badTest_13056 0 256 :=
  (interval_append badTest_13056 0 128 256
  (interval_append badTest_13056 0 64 128
  (interval_append badTest_13056 0 32 64
  (interval_append badTest_13056 0 16 32
  (interval_append badTest_13056 0 8 16
  badTest_13056_block_0
  badTest_13056_block_1)
  (interval_append badTest_13056 16 24 32
  badTest_13056_block_2
  badTest_13056_block_3))
  (interval_append badTest_13056 32 48 64
  (interval_append badTest_13056 32 40 48
  badTest_13056_block_4
  badTest_13056_block_5)
  (interval_append badTest_13056 48 56 64
  badTest_13056_block_6
  badTest_13056_block_7)))
  (interval_append badTest_13056 64 96 128
  (interval_append badTest_13056 64 80 96
  (interval_append badTest_13056 64 72 80
  badTest_13056_block_8
  badTest_13056_block_9)
  (interval_append badTest_13056 80 88 96
  badTest_13056_block_10
  badTest_13056_block_11))
  (interval_append badTest_13056 96 112 128
  (interval_append badTest_13056 96 104 112
  badTest_13056_block_12
  badTest_13056_block_13)
  (interval_append badTest_13056 112 120 128
  badTest_13056_block_14
  badTest_13056_block_15))))
  (interval_append badTest_13056 128 192 256
  (interval_append badTest_13056 128 160 192
  (interval_append badTest_13056 128 144 160
  (interval_append badTest_13056 128 136 144
  badTest_13056_block_16
  badTest_13056_block_17)
  (interval_append badTest_13056 144 152 160
  badTest_13056_block_18
  badTest_13056_block_19))
  (interval_append badTest_13056 160 176 192
  (interval_append badTest_13056 160 168 176
  badTest_13056_block_20
  badTest_13056_block_21)
  (interval_append badTest_13056 176 184 192
  badTest_13056_block_22
  badTest_13056_block_23)))
  (interval_append badTest_13056 192 224 256
  (interval_append badTest_13056 192 208 224
  (interval_append badTest_13056 192 200 208
  badTest_13056_block_24
  badTest_13056_block_25)
  (interval_append badTest_13056 208 216 224
  badTest_13056_block_26
  badTest_13056_block_27))
  (interval_append badTest_13056 224 240 256
  (interval_append badTest_13056 224 232 240
  badTest_13056_block_28
  badTest_13056_block_29)
  (interval_append badTest_13056 240 248 256
  badTest_13056_block_30
  badTest_13056_block_31)))))
theorem badTestInterval13056 : Interval badTest 13056 13312 := by
  intro i hlo hhi
  have h := badTest_13056_complete (i-13056) (Nat.zero_le _) (by omega)
  simpa only [badTest_13056, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad052 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad053 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad054 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad055 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad056 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad057 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
