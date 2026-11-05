module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheBad074 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_18944 (i : Nat) := badTest (i+18944)
theorem badTest_18944_block_0 : Interval badTest_18944 0 8 :=
  interval_of_check badTest_18944 0 8 (by decide +kernel)

theorem badTest_18944_block_1 : Interval badTest_18944 8 16 :=
  interval_of_check badTest_18944 8 8 (by decide +kernel)

theorem badTest_18944_block_2 : Interval badTest_18944 16 24 :=
  interval_of_check badTest_18944 16 8 (by decide +kernel)

theorem badTest_18944_block_3 : Interval badTest_18944 24 32 :=
  interval_of_check badTest_18944 24 8 (by decide +kernel)

theorem badTest_18944_block_4 : Interval badTest_18944 32 40 :=
  interval_of_check badTest_18944 32 8 (by decide +kernel)

theorem badTest_18944_block_5 : Interval badTest_18944 40 48 :=
  interval_of_check badTest_18944 40 8 (by decide +kernel)

theorem badTest_18944_block_6 : Interval badTest_18944 48 56 :=
  interval_of_check badTest_18944 48 8 (by decide +kernel)

theorem badTest_18944_block_7 : Interval badTest_18944 56 64 :=
  interval_of_check badTest_18944 56 8 (by decide +kernel)

theorem badTest_18944_block_8 : Interval badTest_18944 64 72 :=
  interval_of_check badTest_18944 64 8 (by decide +kernel)

theorem badTest_18944_block_9 : Interval badTest_18944 72 80 :=
  interval_of_check badTest_18944 72 8 (by decide +kernel)

theorem badTest_18944_block_10 : Interval badTest_18944 80 88 :=
  interval_of_check badTest_18944 80 8 (by decide +kernel)

theorem badTest_18944_block_11 : Interval badTest_18944 88 96 :=
  interval_of_check badTest_18944 88 8 (by decide +kernel)

theorem badTest_18944_block_12 : Interval badTest_18944 96 104 :=
  interval_of_check badTest_18944 96 8 (by decide +kernel)

theorem badTest_18944_block_13 : Interval badTest_18944 104 112 :=
  interval_of_check badTest_18944 104 8 (by decide +kernel)

theorem badTest_18944_block_14 : Interval badTest_18944 112 120 :=
  interval_of_check badTest_18944 112 8 (by decide +kernel)

theorem badTest_18944_block_15 : Interval badTest_18944 120 128 :=
  interval_of_check badTest_18944 120 8 (by decide +kernel)

theorem badTest_18944_block_16 : Interval badTest_18944 128 136 :=
  interval_of_check badTest_18944 128 8 (by decide +kernel)

theorem badTest_18944_block_17 : Interval badTest_18944 136 144 :=
  interval_of_check badTest_18944 136 8 (by decide +kernel)

theorem badTest_18944_block_18 : Interval badTest_18944 144 152 :=
  interval_of_check badTest_18944 144 8 (by decide +kernel)

theorem badTest_18944_block_19 : Interval badTest_18944 152 160 :=
  interval_of_check badTest_18944 152 8 (by decide +kernel)

theorem badTest_18944_block_20 : Interval badTest_18944 160 168 :=
  interval_of_check badTest_18944 160 8 (by decide +kernel)

theorem badTest_18944_block_21 : Interval badTest_18944 168 176 :=
  interval_of_check badTest_18944 168 8 (by decide +kernel)

theorem badTest_18944_block_22 : Interval badTest_18944 176 184 :=
  interval_of_check badTest_18944 176 8 (by decide +kernel)

theorem badTest_18944_block_23 : Interval badTest_18944 184 192 :=
  interval_of_check badTest_18944 184 8 (by decide +kernel)

theorem badTest_18944_block_24 : Interval badTest_18944 192 200 :=
  interval_of_check badTest_18944 192 8 (by decide +kernel)

theorem badTest_18944_block_25 : Interval badTest_18944 200 208 :=
  interval_of_check badTest_18944 200 8 (by decide +kernel)

theorem badTest_18944_block_26 : Interval badTest_18944 208 216 :=
  interval_of_check badTest_18944 208 8 (by decide +kernel)

theorem badTest_18944_block_27 : Interval badTest_18944 216 224 :=
  interval_of_check badTest_18944 216 8 (by decide +kernel)

theorem badTest_18944_block_28 : Interval badTest_18944 224 232 :=
  interval_of_check badTest_18944 224 8 (by decide +kernel)

theorem badTest_18944_block_29 : Interval badTest_18944 232 240 :=
  interval_of_check badTest_18944 232 8 (by decide +kernel)

theorem badTest_18944_block_30 : Interval badTest_18944 240 248 :=
  interval_of_check badTest_18944 240 8 (by decide +kernel)

theorem badTest_18944_block_31 : Interval badTest_18944 248 256 :=
  interval_of_check badTest_18944 248 8 (by decide +kernel)

theorem badTest_18944_complete : Interval badTest_18944 0 256 :=
  (interval_append badTest_18944 0 128 256
  (interval_append badTest_18944 0 64 128
  (interval_append badTest_18944 0 32 64
  (interval_append badTest_18944 0 16 32
  (interval_append badTest_18944 0 8 16
  badTest_18944_block_0
  badTest_18944_block_1)
  (interval_append badTest_18944 16 24 32
  badTest_18944_block_2
  badTest_18944_block_3))
  (interval_append badTest_18944 32 48 64
  (interval_append badTest_18944 32 40 48
  badTest_18944_block_4
  badTest_18944_block_5)
  (interval_append badTest_18944 48 56 64
  badTest_18944_block_6
  badTest_18944_block_7)))
  (interval_append badTest_18944 64 96 128
  (interval_append badTest_18944 64 80 96
  (interval_append badTest_18944 64 72 80
  badTest_18944_block_8
  badTest_18944_block_9)
  (interval_append badTest_18944 80 88 96
  badTest_18944_block_10
  badTest_18944_block_11))
  (interval_append badTest_18944 96 112 128
  (interval_append badTest_18944 96 104 112
  badTest_18944_block_12
  badTest_18944_block_13)
  (interval_append badTest_18944 112 120 128
  badTest_18944_block_14
  badTest_18944_block_15))))
  (interval_append badTest_18944 128 192 256
  (interval_append badTest_18944 128 160 192
  (interval_append badTest_18944 128 144 160
  (interval_append badTest_18944 128 136 144
  badTest_18944_block_16
  badTest_18944_block_17)
  (interval_append badTest_18944 144 152 160
  badTest_18944_block_18
  badTest_18944_block_19))
  (interval_append badTest_18944 160 176 192
  (interval_append badTest_18944 160 168 176
  badTest_18944_block_20
  badTest_18944_block_21)
  (interval_append badTest_18944 176 184 192
  badTest_18944_block_22
  badTest_18944_block_23)))
  (interval_append badTest_18944 192 224 256
  (interval_append badTest_18944 192 208 224
  (interval_append badTest_18944 192 200 208
  badTest_18944_block_24
  badTest_18944_block_25)
  (interval_append badTest_18944 208 216 224
  badTest_18944_block_26
  badTest_18944_block_27))
  (interval_append badTest_18944 224 240 256
  (interval_append badTest_18944 224 232 240
  badTest_18944_block_28
  badTest_18944_block_29)
  (interval_append badTest_18944 240 248 256
  badTest_18944_block_30
  badTest_18944_block_31)))))
theorem badTestInterval18944 : Interval badTest 18944 19200 := by
  intro i hlo hhi
  have h := badTest_18944_complete (i-18944) (Nat.zero_le _) (by omega)
  simpa only [badTest_18944, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad075 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_19200 (i : Nat) := badTest (i+19200)
theorem badTest_19200_block_0 : Interval badTest_19200 0 8 :=
  interval_of_check badTest_19200 0 8 (by decide +kernel)

theorem badTest_19200_block_1 : Interval badTest_19200 8 16 :=
  interval_of_check badTest_19200 8 8 (by decide +kernel)

theorem badTest_19200_block_2 : Interval badTest_19200 16 24 :=
  interval_of_check badTest_19200 16 8 (by decide +kernel)

theorem badTest_19200_block_3 : Interval badTest_19200 24 32 :=
  interval_of_check badTest_19200 24 8 (by decide +kernel)

theorem badTest_19200_block_4 : Interval badTest_19200 32 40 :=
  interval_of_check badTest_19200 32 8 (by decide +kernel)

theorem badTest_19200_block_5 : Interval badTest_19200 40 48 :=
  interval_of_check badTest_19200 40 8 (by decide +kernel)

theorem badTest_19200_block_6 : Interval badTest_19200 48 56 :=
  interval_of_check badTest_19200 48 8 (by decide +kernel)

theorem badTest_19200_block_7 : Interval badTest_19200 56 64 :=
  interval_of_check badTest_19200 56 8 (by decide +kernel)

theorem badTest_19200_block_8 : Interval badTest_19200 64 72 :=
  interval_of_check badTest_19200 64 8 (by decide +kernel)

theorem badTest_19200_block_9 : Interval badTest_19200 72 80 :=
  interval_of_check badTest_19200 72 8 (by decide +kernel)

theorem badTest_19200_block_10 : Interval badTest_19200 80 88 :=
  interval_of_check badTest_19200 80 8 (by decide +kernel)

theorem badTest_19200_block_11 : Interval badTest_19200 88 96 :=
  interval_of_check badTest_19200 88 8 (by decide +kernel)

theorem badTest_19200_block_12 : Interval badTest_19200 96 104 :=
  interval_of_check badTest_19200 96 8 (by decide +kernel)

theorem badTest_19200_block_13 : Interval badTest_19200 104 112 :=
  interval_of_check badTest_19200 104 8 (by decide +kernel)

theorem badTest_19200_block_14 : Interval badTest_19200 112 120 :=
  interval_of_check badTest_19200 112 8 (by decide +kernel)

theorem badTest_19200_block_15 : Interval badTest_19200 120 128 :=
  interval_of_check badTest_19200 120 8 (by decide +kernel)

theorem badTest_19200_block_16 : Interval badTest_19200 128 136 :=
  interval_of_check badTest_19200 128 8 (by decide +kernel)

theorem badTest_19200_block_17 : Interval badTest_19200 136 144 :=
  interval_of_check badTest_19200 136 8 (by decide +kernel)

theorem badTest_19200_block_18 : Interval badTest_19200 144 152 :=
  interval_of_check badTest_19200 144 8 (by decide +kernel)

theorem badTest_19200_block_19 : Interval badTest_19200 152 160 :=
  interval_of_check badTest_19200 152 8 (by decide +kernel)

theorem badTest_19200_block_20 : Interval badTest_19200 160 168 :=
  interval_of_check badTest_19200 160 8 (by decide +kernel)

theorem badTest_19200_block_21 : Interval badTest_19200 168 176 :=
  interval_of_check badTest_19200 168 8 (by decide +kernel)

theorem badTest_19200_block_22 : Interval badTest_19200 176 184 :=
  interval_of_check badTest_19200 176 8 (by decide +kernel)

theorem badTest_19200_block_23 : Interval badTest_19200 184 192 :=
  interval_of_check badTest_19200 184 8 (by decide +kernel)

theorem badTest_19200_block_24 : Interval badTest_19200 192 200 :=
  interval_of_check badTest_19200 192 8 (by decide +kernel)

theorem badTest_19200_block_25 : Interval badTest_19200 200 208 :=
  interval_of_check badTest_19200 200 8 (by decide +kernel)

theorem badTest_19200_block_26 : Interval badTest_19200 208 216 :=
  interval_of_check badTest_19200 208 8 (by decide +kernel)

theorem badTest_19200_block_27 : Interval badTest_19200 216 224 :=
  interval_of_check badTest_19200 216 8 (by decide +kernel)

theorem badTest_19200_block_28 : Interval badTest_19200 224 232 :=
  interval_of_check badTest_19200 224 8 (by decide +kernel)

theorem badTest_19200_block_29 : Interval badTest_19200 232 240 :=
  interval_of_check badTest_19200 232 8 (by decide +kernel)

theorem badTest_19200_block_30 : Interval badTest_19200 240 248 :=
  interval_of_check badTest_19200 240 8 (by decide +kernel)

theorem badTest_19200_block_31 : Interval badTest_19200 248 256 :=
  interval_of_check badTest_19200 248 8 (by decide +kernel)

theorem badTest_19200_complete : Interval badTest_19200 0 256 :=
  (interval_append badTest_19200 0 128 256
  (interval_append badTest_19200 0 64 128
  (interval_append badTest_19200 0 32 64
  (interval_append badTest_19200 0 16 32
  (interval_append badTest_19200 0 8 16
  badTest_19200_block_0
  badTest_19200_block_1)
  (interval_append badTest_19200 16 24 32
  badTest_19200_block_2
  badTest_19200_block_3))
  (interval_append badTest_19200 32 48 64
  (interval_append badTest_19200 32 40 48
  badTest_19200_block_4
  badTest_19200_block_5)
  (interval_append badTest_19200 48 56 64
  badTest_19200_block_6
  badTest_19200_block_7)))
  (interval_append badTest_19200 64 96 128
  (interval_append badTest_19200 64 80 96
  (interval_append badTest_19200 64 72 80
  badTest_19200_block_8
  badTest_19200_block_9)
  (interval_append badTest_19200 80 88 96
  badTest_19200_block_10
  badTest_19200_block_11))
  (interval_append badTest_19200 96 112 128
  (interval_append badTest_19200 96 104 112
  badTest_19200_block_12
  badTest_19200_block_13)
  (interval_append badTest_19200 112 120 128
  badTest_19200_block_14
  badTest_19200_block_15))))
  (interval_append badTest_19200 128 192 256
  (interval_append badTest_19200 128 160 192
  (interval_append badTest_19200 128 144 160
  (interval_append badTest_19200 128 136 144
  badTest_19200_block_16
  badTest_19200_block_17)
  (interval_append badTest_19200 144 152 160
  badTest_19200_block_18
  badTest_19200_block_19))
  (interval_append badTest_19200 160 176 192
  (interval_append badTest_19200 160 168 176
  badTest_19200_block_20
  badTest_19200_block_21)
  (interval_append badTest_19200 176 184 192
  badTest_19200_block_22
  badTest_19200_block_23)))
  (interval_append badTest_19200 192 224 256
  (interval_append badTest_19200 192 208 224
  (interval_append badTest_19200 192 200 208
  badTest_19200_block_24
  badTest_19200_block_25)
  (interval_append badTest_19200 208 216 224
  badTest_19200_block_26
  badTest_19200_block_27))
  (interval_append badTest_19200 224 240 256
  (interval_append badTest_19200 224 232 240
  badTest_19200_block_28
  badTest_19200_block_29)
  (interval_append badTest_19200 240 248 256
  badTest_19200_block_30
  badTest_19200_block_31)))))
theorem badTestInterval19200 : Interval badTest 19200 19456 := by
  intro i hlo hhi
  have h := badTest_19200_complete (i-19200) (Nat.zero_le _) (by omega)
  simpa only [badTest_19200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad076 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_19456 (i : Nat) := badTest (i+19456)
theorem badTest_19456_block_0 : Interval badTest_19456 0 8 :=
  interval_of_check badTest_19456 0 8 (by decide +kernel)

theorem badTest_19456_block_1 : Interval badTest_19456 8 16 :=
  interval_of_check badTest_19456 8 8 (by decide +kernel)

theorem badTest_19456_block_2 : Interval badTest_19456 16 24 :=
  interval_of_check badTest_19456 16 8 (by decide +kernel)

theorem badTest_19456_block_3 : Interval badTest_19456 24 32 :=
  interval_of_check badTest_19456 24 8 (by decide +kernel)

theorem badTest_19456_block_4 : Interval badTest_19456 32 40 :=
  interval_of_check badTest_19456 32 8 (by decide +kernel)

theorem badTest_19456_block_5 : Interval badTest_19456 40 48 :=
  interval_of_check badTest_19456 40 8 (by decide +kernel)

theorem badTest_19456_block_6 : Interval badTest_19456 48 56 :=
  interval_of_check badTest_19456 48 8 (by decide +kernel)

theorem badTest_19456_block_7 : Interval badTest_19456 56 64 :=
  interval_of_check badTest_19456 56 8 (by decide +kernel)

theorem badTest_19456_block_8 : Interval badTest_19456 64 72 :=
  interval_of_check badTest_19456 64 8 (by decide +kernel)

theorem badTest_19456_block_9 : Interval badTest_19456 72 80 :=
  interval_of_check badTest_19456 72 8 (by decide +kernel)

theorem badTest_19456_block_10 : Interval badTest_19456 80 88 :=
  interval_of_check badTest_19456 80 8 (by decide +kernel)

theorem badTest_19456_block_11 : Interval badTest_19456 88 96 :=
  interval_of_check badTest_19456 88 8 (by decide +kernel)

theorem badTest_19456_block_12 : Interval badTest_19456 96 104 :=
  interval_of_check badTest_19456 96 8 (by decide +kernel)

theorem badTest_19456_block_13 : Interval badTest_19456 104 112 :=
  interval_of_check badTest_19456 104 8 (by decide +kernel)

theorem badTest_19456_block_14 : Interval badTest_19456 112 120 :=
  interval_of_check badTest_19456 112 8 (by decide +kernel)

theorem badTest_19456_block_15 : Interval badTest_19456 120 128 :=
  interval_of_check badTest_19456 120 8 (by decide +kernel)

theorem badTest_19456_block_16 : Interval badTest_19456 128 136 :=
  interval_of_check badTest_19456 128 8 (by decide +kernel)

theorem badTest_19456_block_17 : Interval badTest_19456 136 144 :=
  interval_of_check badTest_19456 136 8 (by decide +kernel)

theorem badTest_19456_block_18 : Interval badTest_19456 144 152 :=
  interval_of_check badTest_19456 144 8 (by decide +kernel)

theorem badTest_19456_block_19 : Interval badTest_19456 152 160 :=
  interval_of_check badTest_19456 152 8 (by decide +kernel)

theorem badTest_19456_block_20 : Interval badTest_19456 160 168 :=
  interval_of_check badTest_19456 160 8 (by decide +kernel)

theorem badTest_19456_block_21 : Interval badTest_19456 168 176 :=
  interval_of_check badTest_19456 168 8 (by decide +kernel)

theorem badTest_19456_block_22 : Interval badTest_19456 176 184 :=
  interval_of_check badTest_19456 176 8 (by decide +kernel)

theorem badTest_19456_block_23 : Interval badTest_19456 184 192 :=
  interval_of_check badTest_19456 184 8 (by decide +kernel)

theorem badTest_19456_block_24 : Interval badTest_19456 192 200 :=
  interval_of_check badTest_19456 192 8 (by decide +kernel)

theorem badTest_19456_block_25 : Interval badTest_19456 200 208 :=
  interval_of_check badTest_19456 200 8 (by decide +kernel)

theorem badTest_19456_block_26 : Interval badTest_19456 208 216 :=
  interval_of_check badTest_19456 208 8 (by decide +kernel)

theorem badTest_19456_block_27 : Interval badTest_19456 216 224 :=
  interval_of_check badTest_19456 216 8 (by decide +kernel)

theorem badTest_19456_block_28 : Interval badTest_19456 224 232 :=
  interval_of_check badTest_19456 224 8 (by decide +kernel)

theorem badTest_19456_block_29 : Interval badTest_19456 232 240 :=
  interval_of_check badTest_19456 232 8 (by decide +kernel)

theorem badTest_19456_block_30 : Interval badTest_19456 240 248 :=
  interval_of_check badTest_19456 240 8 (by decide +kernel)

theorem badTest_19456_block_31 : Interval badTest_19456 248 256 :=
  interval_of_check badTest_19456 248 8 (by decide +kernel)

theorem badTest_19456_complete : Interval badTest_19456 0 256 :=
  (interval_append badTest_19456 0 128 256
  (interval_append badTest_19456 0 64 128
  (interval_append badTest_19456 0 32 64
  (interval_append badTest_19456 0 16 32
  (interval_append badTest_19456 0 8 16
  badTest_19456_block_0
  badTest_19456_block_1)
  (interval_append badTest_19456 16 24 32
  badTest_19456_block_2
  badTest_19456_block_3))
  (interval_append badTest_19456 32 48 64
  (interval_append badTest_19456 32 40 48
  badTest_19456_block_4
  badTest_19456_block_5)
  (interval_append badTest_19456 48 56 64
  badTest_19456_block_6
  badTest_19456_block_7)))
  (interval_append badTest_19456 64 96 128
  (interval_append badTest_19456 64 80 96
  (interval_append badTest_19456 64 72 80
  badTest_19456_block_8
  badTest_19456_block_9)
  (interval_append badTest_19456 80 88 96
  badTest_19456_block_10
  badTest_19456_block_11))
  (interval_append badTest_19456 96 112 128
  (interval_append badTest_19456 96 104 112
  badTest_19456_block_12
  badTest_19456_block_13)
  (interval_append badTest_19456 112 120 128
  badTest_19456_block_14
  badTest_19456_block_15))))
  (interval_append badTest_19456 128 192 256
  (interval_append badTest_19456 128 160 192
  (interval_append badTest_19456 128 144 160
  (interval_append badTest_19456 128 136 144
  badTest_19456_block_16
  badTest_19456_block_17)
  (interval_append badTest_19456 144 152 160
  badTest_19456_block_18
  badTest_19456_block_19))
  (interval_append badTest_19456 160 176 192
  (interval_append badTest_19456 160 168 176
  badTest_19456_block_20
  badTest_19456_block_21)
  (interval_append badTest_19456 176 184 192
  badTest_19456_block_22
  badTest_19456_block_23)))
  (interval_append badTest_19456 192 224 256
  (interval_append badTest_19456 192 208 224
  (interval_append badTest_19456 192 200 208
  badTest_19456_block_24
  badTest_19456_block_25)
  (interval_append badTest_19456 208 216 224
  badTest_19456_block_26
  badTest_19456_block_27))
  (interval_append badTest_19456 224 240 256
  (interval_append badTest_19456 224 232 240
  badTest_19456_block_28
  badTest_19456_block_29)
  (interval_append badTest_19456 240 248 256
  badTest_19456_block_30
  badTest_19456_block_31)))))
theorem badTestInterval19456 : Interval badTest 19456 19712 := by
  intro i hlo hhi
  have h := badTest_19456_complete (i-19456) (Nat.zero_le _) (by omega)
  simpa only [badTest_19456, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad077 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_19712 (i : Nat) := badTest (i+19712)
theorem badTest_19712_block_0 : Interval badTest_19712 0 8 :=
  interval_of_check badTest_19712 0 8 (by decide +kernel)

theorem badTest_19712_block_1 : Interval badTest_19712 8 16 :=
  interval_of_check badTest_19712 8 8 (by decide +kernel)

theorem badTest_19712_block_2 : Interval badTest_19712 16 24 :=
  interval_of_check badTest_19712 16 8 (by decide +kernel)

theorem badTest_19712_block_3 : Interval badTest_19712 24 32 :=
  interval_of_check badTest_19712 24 8 (by decide +kernel)

theorem badTest_19712_block_4 : Interval badTest_19712 32 40 :=
  interval_of_check badTest_19712 32 8 (by decide +kernel)

theorem badTest_19712_block_5 : Interval badTest_19712 40 48 :=
  interval_of_check badTest_19712 40 8 (by decide +kernel)

theorem badTest_19712_block_6 : Interval badTest_19712 48 56 :=
  interval_of_check badTest_19712 48 8 (by decide +kernel)

theorem badTest_19712_block_7 : Interval badTest_19712 56 64 :=
  interval_of_check badTest_19712 56 8 (by decide +kernel)

theorem badTest_19712_block_8 : Interval badTest_19712 64 72 :=
  interval_of_check badTest_19712 64 8 (by decide +kernel)

theorem badTest_19712_block_9 : Interval badTest_19712 72 80 :=
  interval_of_check badTest_19712 72 8 (by decide +kernel)

theorem badTest_19712_block_10 : Interval badTest_19712 80 88 :=
  interval_of_check badTest_19712 80 8 (by decide +kernel)

theorem badTest_19712_block_11 : Interval badTest_19712 88 96 :=
  interval_of_check badTest_19712 88 8 (by decide +kernel)

theorem badTest_19712_block_12 : Interval badTest_19712 96 104 :=
  interval_of_check badTest_19712 96 8 (by decide +kernel)

theorem badTest_19712_block_13 : Interval badTest_19712 104 112 :=
  interval_of_check badTest_19712 104 8 (by decide +kernel)

theorem badTest_19712_block_14 : Interval badTest_19712 112 120 :=
  interval_of_check badTest_19712 112 8 (by decide +kernel)

theorem badTest_19712_block_15 : Interval badTest_19712 120 128 :=
  interval_of_check badTest_19712 120 8 (by decide +kernel)

theorem badTest_19712_block_16 : Interval badTest_19712 128 136 :=
  interval_of_check badTest_19712 128 8 (by decide +kernel)

theorem badTest_19712_block_17 : Interval badTest_19712 136 144 :=
  interval_of_check badTest_19712 136 8 (by decide +kernel)

theorem badTest_19712_block_18 : Interval badTest_19712 144 152 :=
  interval_of_check badTest_19712 144 8 (by decide +kernel)

theorem badTest_19712_block_19 : Interval badTest_19712 152 160 :=
  interval_of_check badTest_19712 152 8 (by decide +kernel)

theorem badTest_19712_block_20 : Interval badTest_19712 160 168 :=
  interval_of_check badTest_19712 160 8 (by decide +kernel)

theorem badTest_19712_block_21 : Interval badTest_19712 168 176 :=
  interval_of_check badTest_19712 168 8 (by decide +kernel)

theorem badTest_19712_block_22 : Interval badTest_19712 176 184 :=
  interval_of_check badTest_19712 176 8 (by decide +kernel)

theorem badTest_19712_block_23 : Interval badTest_19712 184 192 :=
  interval_of_check badTest_19712 184 8 (by decide +kernel)

theorem badTest_19712_block_24 : Interval badTest_19712 192 200 :=
  interval_of_check badTest_19712 192 8 (by decide +kernel)

theorem badTest_19712_block_25 : Interval badTest_19712 200 208 :=
  interval_of_check badTest_19712 200 8 (by decide +kernel)

theorem badTest_19712_block_26 : Interval badTest_19712 208 216 :=
  interval_of_check badTest_19712 208 8 (by decide +kernel)

theorem badTest_19712_block_27 : Interval badTest_19712 216 224 :=
  interval_of_check badTest_19712 216 8 (by decide +kernel)

theorem badTest_19712_block_28 : Interval badTest_19712 224 232 :=
  interval_of_check badTest_19712 224 8 (by decide +kernel)

theorem badTest_19712_block_29 : Interval badTest_19712 232 240 :=
  interval_of_check badTest_19712 232 8 (by decide +kernel)

theorem badTest_19712_block_30 : Interval badTest_19712 240 248 :=
  interval_of_check badTest_19712 240 8 (by decide +kernel)

theorem badTest_19712_block_31 : Interval badTest_19712 248 256 :=
  interval_of_check badTest_19712 248 8 (by decide +kernel)

theorem badTest_19712_complete : Interval badTest_19712 0 256 :=
  (interval_append badTest_19712 0 128 256
  (interval_append badTest_19712 0 64 128
  (interval_append badTest_19712 0 32 64
  (interval_append badTest_19712 0 16 32
  (interval_append badTest_19712 0 8 16
  badTest_19712_block_0
  badTest_19712_block_1)
  (interval_append badTest_19712 16 24 32
  badTest_19712_block_2
  badTest_19712_block_3))
  (interval_append badTest_19712 32 48 64
  (interval_append badTest_19712 32 40 48
  badTest_19712_block_4
  badTest_19712_block_5)
  (interval_append badTest_19712 48 56 64
  badTest_19712_block_6
  badTest_19712_block_7)))
  (interval_append badTest_19712 64 96 128
  (interval_append badTest_19712 64 80 96
  (interval_append badTest_19712 64 72 80
  badTest_19712_block_8
  badTest_19712_block_9)
  (interval_append badTest_19712 80 88 96
  badTest_19712_block_10
  badTest_19712_block_11))
  (interval_append badTest_19712 96 112 128
  (interval_append badTest_19712 96 104 112
  badTest_19712_block_12
  badTest_19712_block_13)
  (interval_append badTest_19712 112 120 128
  badTest_19712_block_14
  badTest_19712_block_15))))
  (interval_append badTest_19712 128 192 256
  (interval_append badTest_19712 128 160 192
  (interval_append badTest_19712 128 144 160
  (interval_append badTest_19712 128 136 144
  badTest_19712_block_16
  badTest_19712_block_17)
  (interval_append badTest_19712 144 152 160
  badTest_19712_block_18
  badTest_19712_block_19))
  (interval_append badTest_19712 160 176 192
  (interval_append badTest_19712 160 168 176
  badTest_19712_block_20
  badTest_19712_block_21)
  (interval_append badTest_19712 176 184 192
  badTest_19712_block_22
  badTest_19712_block_23)))
  (interval_append badTest_19712 192 224 256
  (interval_append badTest_19712 192 208 224
  (interval_append badTest_19712 192 200 208
  badTest_19712_block_24
  badTest_19712_block_25)
  (interval_append badTest_19712 208 216 224
  badTest_19712_block_26
  badTest_19712_block_27))
  (interval_append badTest_19712 224 240 256
  (interval_append badTest_19712 224 232 240
  badTest_19712_block_28
  badTest_19712_block_29)
  (interval_append badTest_19712 240 248 256
  badTest_19712_block_30
  badTest_19712_block_31)))))
theorem badTestInterval19712 : Interval badTest 19712 19968 := by
  intro i hlo hhi
  have h := badTest_19712_complete (i-19712) (Nat.zero_le _) (by omega)
  simpa only [badTest_19712, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad078 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_19968 (i : Nat) := badTest (i+19968)
theorem badTest_19968_block_0 : Interval badTest_19968 0 8 :=
  interval_of_check badTest_19968 0 8 (by decide +kernel)

theorem badTest_19968_block_1 : Interval badTest_19968 8 16 :=
  interval_of_check badTest_19968 8 8 (by decide +kernel)

theorem badTest_19968_block_2 : Interval badTest_19968 16 24 :=
  interval_of_check badTest_19968 16 8 (by decide +kernel)

theorem badTest_19968_block_3 : Interval badTest_19968 24 32 :=
  interval_of_check badTest_19968 24 8 (by decide +kernel)

theorem badTest_19968_block_4 : Interval badTest_19968 32 40 :=
  interval_of_check badTest_19968 32 8 (by decide +kernel)

theorem badTest_19968_block_5 : Interval badTest_19968 40 48 :=
  interval_of_check badTest_19968 40 8 (by decide +kernel)

theorem badTest_19968_block_6 : Interval badTest_19968 48 56 :=
  interval_of_check badTest_19968 48 8 (by decide +kernel)

theorem badTest_19968_block_7 : Interval badTest_19968 56 64 :=
  interval_of_check badTest_19968 56 8 (by decide +kernel)

theorem badTest_19968_block_8 : Interval badTest_19968 64 72 :=
  interval_of_check badTest_19968 64 8 (by decide +kernel)

theorem badTest_19968_block_9 : Interval badTest_19968 72 80 :=
  interval_of_check badTest_19968 72 8 (by decide +kernel)

theorem badTest_19968_block_10 : Interval badTest_19968 80 88 :=
  interval_of_check badTest_19968 80 8 (by decide +kernel)

theorem badTest_19968_block_11 : Interval badTest_19968 88 96 :=
  interval_of_check badTest_19968 88 8 (by decide +kernel)

theorem badTest_19968_block_12 : Interval badTest_19968 96 104 :=
  interval_of_check badTest_19968 96 8 (by decide +kernel)

theorem badTest_19968_block_13 : Interval badTest_19968 104 112 :=
  interval_of_check badTest_19968 104 8 (by decide +kernel)

theorem badTest_19968_block_14 : Interval badTest_19968 112 120 :=
  interval_of_check badTest_19968 112 8 (by decide +kernel)

theorem badTest_19968_block_15 : Interval badTest_19968 120 128 :=
  interval_of_check badTest_19968 120 8 (by decide +kernel)

theorem badTest_19968_block_16 : Interval badTest_19968 128 136 :=
  interval_of_check badTest_19968 128 8 (by decide +kernel)

theorem badTest_19968_block_17 : Interval badTest_19968 136 144 :=
  interval_of_check badTest_19968 136 8 (by decide +kernel)

theorem badTest_19968_block_18 : Interval badTest_19968 144 152 :=
  interval_of_check badTest_19968 144 8 (by decide +kernel)

theorem badTest_19968_block_19 : Interval badTest_19968 152 160 :=
  interval_of_check badTest_19968 152 8 (by decide +kernel)

theorem badTest_19968_block_20 : Interval badTest_19968 160 168 :=
  interval_of_check badTest_19968 160 8 (by decide +kernel)

theorem badTest_19968_block_21 : Interval badTest_19968 168 176 :=
  interval_of_check badTest_19968 168 8 (by decide +kernel)

theorem badTest_19968_block_22 : Interval badTest_19968 176 184 :=
  interval_of_check badTest_19968 176 8 (by decide +kernel)

theorem badTest_19968_block_23 : Interval badTest_19968 184 192 :=
  interval_of_check badTest_19968 184 8 (by decide +kernel)

theorem badTest_19968_block_24 : Interval badTest_19968 192 200 :=
  interval_of_check badTest_19968 192 8 (by decide +kernel)

theorem badTest_19968_block_25 : Interval badTest_19968 200 208 :=
  interval_of_check badTest_19968 200 8 (by decide +kernel)

theorem badTest_19968_block_26 : Interval badTest_19968 208 216 :=
  interval_of_check badTest_19968 208 8 (by decide +kernel)

theorem badTest_19968_block_27 : Interval badTest_19968 216 224 :=
  interval_of_check badTest_19968 216 8 (by decide +kernel)

theorem badTest_19968_block_28 : Interval badTest_19968 224 232 :=
  interval_of_check badTest_19968 224 8 (by decide +kernel)

theorem badTest_19968_block_29 : Interval badTest_19968 232 240 :=
  interval_of_check badTest_19968 232 8 (by decide +kernel)

theorem badTest_19968_block_30 : Interval badTest_19968 240 248 :=
  interval_of_check badTest_19968 240 8 (by decide +kernel)

theorem badTest_19968_block_31 : Interval badTest_19968 248 256 :=
  interval_of_check badTest_19968 248 8 (by decide +kernel)

theorem badTest_19968_complete : Interval badTest_19968 0 256 :=
  (interval_append badTest_19968 0 128 256
  (interval_append badTest_19968 0 64 128
  (interval_append badTest_19968 0 32 64
  (interval_append badTest_19968 0 16 32
  (interval_append badTest_19968 0 8 16
  badTest_19968_block_0
  badTest_19968_block_1)
  (interval_append badTest_19968 16 24 32
  badTest_19968_block_2
  badTest_19968_block_3))
  (interval_append badTest_19968 32 48 64
  (interval_append badTest_19968 32 40 48
  badTest_19968_block_4
  badTest_19968_block_5)
  (interval_append badTest_19968 48 56 64
  badTest_19968_block_6
  badTest_19968_block_7)))
  (interval_append badTest_19968 64 96 128
  (interval_append badTest_19968 64 80 96
  (interval_append badTest_19968 64 72 80
  badTest_19968_block_8
  badTest_19968_block_9)
  (interval_append badTest_19968 80 88 96
  badTest_19968_block_10
  badTest_19968_block_11))
  (interval_append badTest_19968 96 112 128
  (interval_append badTest_19968 96 104 112
  badTest_19968_block_12
  badTest_19968_block_13)
  (interval_append badTest_19968 112 120 128
  badTest_19968_block_14
  badTest_19968_block_15))))
  (interval_append badTest_19968 128 192 256
  (interval_append badTest_19968 128 160 192
  (interval_append badTest_19968 128 144 160
  (interval_append badTest_19968 128 136 144
  badTest_19968_block_16
  badTest_19968_block_17)
  (interval_append badTest_19968 144 152 160
  badTest_19968_block_18
  badTest_19968_block_19))
  (interval_append badTest_19968 160 176 192
  (interval_append badTest_19968 160 168 176
  badTest_19968_block_20
  badTest_19968_block_21)
  (interval_append badTest_19968 176 184 192
  badTest_19968_block_22
  badTest_19968_block_23)))
  (interval_append badTest_19968 192 224 256
  (interval_append badTest_19968 192 208 224
  (interval_append badTest_19968 192 200 208
  badTest_19968_block_24
  badTest_19968_block_25)
  (interval_append badTest_19968 208 216 224
  badTest_19968_block_26
  badTest_19968_block_27))
  (interval_append badTest_19968 224 240 256
  (interval_append badTest_19968 224 232 240
  badTest_19968_block_28
  badTest_19968_block_29)
  (interval_append badTest_19968 240 248 256
  badTest_19968_block_30
  badTest_19968_block_31)))))
theorem badTestInterval19968 : Interval badTest 19968 20224 := by
  intro i hlo hhi
  have h := badTest_19968_complete (i-19968) (Nat.zero_le _) (by omega)
  simpa only [badTest_19968, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad079 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_20224 (i : Nat) := badTest (i+20224)
theorem badTest_20224_block_0 : Interval badTest_20224 0 8 :=
  interval_of_check badTest_20224 0 8 (by decide +kernel)

theorem badTest_20224_block_1 : Interval badTest_20224 8 16 :=
  interval_of_check badTest_20224 8 8 (by decide +kernel)

theorem badTest_20224_block_2 : Interval badTest_20224 16 24 :=
  interval_of_check badTest_20224 16 8 (by decide +kernel)

theorem badTest_20224_block_3 : Interval badTest_20224 24 32 :=
  interval_of_check badTest_20224 24 8 (by decide +kernel)

theorem badTest_20224_block_4 : Interval badTest_20224 32 40 :=
  interval_of_check badTest_20224 32 8 (by decide +kernel)

theorem badTest_20224_block_5 : Interval badTest_20224 40 48 :=
  interval_of_check badTest_20224 40 8 (by decide +kernel)

theorem badTest_20224_block_6 : Interval badTest_20224 48 56 :=
  interval_of_check badTest_20224 48 8 (by decide +kernel)

theorem badTest_20224_block_7 : Interval badTest_20224 56 64 :=
  interval_of_check badTest_20224 56 8 (by decide +kernel)

theorem badTest_20224_block_8 : Interval badTest_20224 64 72 :=
  interval_of_check badTest_20224 64 8 (by decide +kernel)

theorem badTest_20224_block_9 : Interval badTest_20224 72 80 :=
  interval_of_check badTest_20224 72 8 (by decide +kernel)

theorem badTest_20224_block_10 : Interval badTest_20224 80 88 :=
  interval_of_check badTest_20224 80 8 (by decide +kernel)

theorem badTest_20224_block_11 : Interval badTest_20224 88 96 :=
  interval_of_check badTest_20224 88 8 (by decide +kernel)

theorem badTest_20224_block_12 : Interval badTest_20224 96 104 :=
  interval_of_check badTest_20224 96 8 (by decide +kernel)

theorem badTest_20224_block_13 : Interval badTest_20224 104 112 :=
  interval_of_check badTest_20224 104 8 (by decide +kernel)

theorem badTest_20224_block_14 : Interval badTest_20224 112 120 :=
  interval_of_check badTest_20224 112 8 (by decide +kernel)

theorem badTest_20224_block_15 : Interval badTest_20224 120 128 :=
  interval_of_check badTest_20224 120 8 (by decide +kernel)

theorem badTest_20224_block_16 : Interval badTest_20224 128 136 :=
  interval_of_check badTest_20224 128 8 (by decide +kernel)

theorem badTest_20224_block_17 : Interval badTest_20224 136 144 :=
  interval_of_check badTest_20224 136 8 (by decide +kernel)

theorem badTest_20224_block_18 : Interval badTest_20224 144 152 :=
  interval_of_check badTest_20224 144 8 (by decide +kernel)

theorem badTest_20224_block_19 : Interval badTest_20224 152 160 :=
  interval_of_check badTest_20224 152 8 (by decide +kernel)

theorem badTest_20224_block_20 : Interval badTest_20224 160 168 :=
  interval_of_check badTest_20224 160 8 (by decide +kernel)

theorem badTest_20224_block_21 : Interval badTest_20224 168 176 :=
  interval_of_check badTest_20224 168 8 (by decide +kernel)

theorem badTest_20224_block_22 : Interval badTest_20224 176 184 :=
  interval_of_check badTest_20224 176 8 (by decide +kernel)

theorem badTest_20224_block_23 : Interval badTest_20224 184 192 :=
  interval_of_check badTest_20224 184 8 (by decide +kernel)

theorem badTest_20224_block_24 : Interval badTest_20224 192 200 :=
  interval_of_check badTest_20224 192 8 (by decide +kernel)

theorem badTest_20224_block_25 : Interval badTest_20224 200 208 :=
  interval_of_check badTest_20224 200 8 (by decide +kernel)

theorem badTest_20224_block_26 : Interval badTest_20224 208 216 :=
  interval_of_check badTest_20224 208 8 (by decide +kernel)

theorem badTest_20224_block_27 : Interval badTest_20224 216 224 :=
  interval_of_check badTest_20224 216 8 (by decide +kernel)

theorem badTest_20224_block_28 : Interval badTest_20224 224 232 :=
  interval_of_check badTest_20224 224 8 (by decide +kernel)

theorem badTest_20224_block_29 : Interval badTest_20224 232 240 :=
  interval_of_check badTest_20224 232 8 (by decide +kernel)

theorem badTest_20224_block_30 : Interval badTest_20224 240 248 :=
  interval_of_check badTest_20224 240 8 (by decide +kernel)

theorem badTest_20224_block_31 : Interval badTest_20224 248 256 :=
  interval_of_check badTest_20224 248 8 (by decide +kernel)

theorem badTest_20224_complete : Interval badTest_20224 0 256 :=
  (interval_append badTest_20224 0 128 256
  (interval_append badTest_20224 0 64 128
  (interval_append badTest_20224 0 32 64
  (interval_append badTest_20224 0 16 32
  (interval_append badTest_20224 0 8 16
  badTest_20224_block_0
  badTest_20224_block_1)
  (interval_append badTest_20224 16 24 32
  badTest_20224_block_2
  badTest_20224_block_3))
  (interval_append badTest_20224 32 48 64
  (interval_append badTest_20224 32 40 48
  badTest_20224_block_4
  badTest_20224_block_5)
  (interval_append badTest_20224 48 56 64
  badTest_20224_block_6
  badTest_20224_block_7)))
  (interval_append badTest_20224 64 96 128
  (interval_append badTest_20224 64 80 96
  (interval_append badTest_20224 64 72 80
  badTest_20224_block_8
  badTest_20224_block_9)
  (interval_append badTest_20224 80 88 96
  badTest_20224_block_10
  badTest_20224_block_11))
  (interval_append badTest_20224 96 112 128
  (interval_append badTest_20224 96 104 112
  badTest_20224_block_12
  badTest_20224_block_13)
  (interval_append badTest_20224 112 120 128
  badTest_20224_block_14
  badTest_20224_block_15))))
  (interval_append badTest_20224 128 192 256
  (interval_append badTest_20224 128 160 192
  (interval_append badTest_20224 128 144 160
  (interval_append badTest_20224 128 136 144
  badTest_20224_block_16
  badTest_20224_block_17)
  (interval_append badTest_20224 144 152 160
  badTest_20224_block_18
  badTest_20224_block_19))
  (interval_append badTest_20224 160 176 192
  (interval_append badTest_20224 160 168 176
  badTest_20224_block_20
  badTest_20224_block_21)
  (interval_append badTest_20224 176 184 192
  badTest_20224_block_22
  badTest_20224_block_23)))
  (interval_append badTest_20224 192 224 256
  (interval_append badTest_20224 192 208 224
  (interval_append badTest_20224 192 200 208
  badTest_20224_block_24
  badTest_20224_block_25)
  (interval_append badTest_20224 208 216 224
  badTest_20224_block_26
  badTest_20224_block_27))
  (interval_append badTest_20224 224 240 256
  (interval_append badTest_20224 224 232 240
  badTest_20224_block_28
  badTest_20224_block_29)
  (interval_append badTest_20224 240 248 256
  badTest_20224_block_30
  badTest_20224_block_31)))))
theorem badTestInterval20224 : Interval badTest 20224 20480 := by
  intro i hlo hhi
  have h := badTest_20224_complete (i-20224) (Nat.zero_le _) (by omega)
  simpa only [badTest_20224, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad080 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_20480 (i : Nat) := badTest (i+20480)
theorem badTest_20480_block_0 : Interval badTest_20480 0 8 :=
  interval_of_check badTest_20480 0 8 (by decide +kernel)

theorem badTest_20480_block_1 : Interval badTest_20480 8 16 :=
  interval_of_check badTest_20480 8 8 (by decide +kernel)

theorem badTest_20480_block_2 : Interval badTest_20480 16 24 :=
  interval_of_check badTest_20480 16 8 (by decide +kernel)

theorem badTest_20480_block_3 : Interval badTest_20480 24 32 :=
  interval_of_check badTest_20480 24 8 (by decide +kernel)

theorem badTest_20480_block_4 : Interval badTest_20480 32 40 :=
  interval_of_check badTest_20480 32 8 (by decide +kernel)

theorem badTest_20480_block_5 : Interval badTest_20480 40 48 :=
  interval_of_check badTest_20480 40 8 (by decide +kernel)

theorem badTest_20480_block_6 : Interval badTest_20480 48 56 :=
  interval_of_check badTest_20480 48 8 (by decide +kernel)

theorem badTest_20480_block_7 : Interval badTest_20480 56 64 :=
  interval_of_check badTest_20480 56 8 (by decide +kernel)

theorem badTest_20480_block_8 : Interval badTest_20480 64 72 :=
  interval_of_check badTest_20480 64 8 (by decide +kernel)

theorem badTest_20480_block_9 : Interval badTest_20480 72 80 :=
  interval_of_check badTest_20480 72 8 (by decide +kernel)

theorem badTest_20480_block_10 : Interval badTest_20480 80 88 :=
  interval_of_check badTest_20480 80 8 (by decide +kernel)

theorem badTest_20480_block_11 : Interval badTest_20480 88 96 :=
  interval_of_check badTest_20480 88 8 (by decide +kernel)

theorem badTest_20480_block_12 : Interval badTest_20480 96 104 :=
  interval_of_check badTest_20480 96 8 (by decide +kernel)

theorem badTest_20480_block_13 : Interval badTest_20480 104 112 :=
  interval_of_check badTest_20480 104 8 (by decide +kernel)

theorem badTest_20480_block_14 : Interval badTest_20480 112 120 :=
  interval_of_check badTest_20480 112 8 (by decide +kernel)

theorem badTest_20480_block_15 : Interval badTest_20480 120 128 :=
  interval_of_check badTest_20480 120 8 (by decide +kernel)

theorem badTest_20480_block_16 : Interval badTest_20480 128 136 :=
  interval_of_check badTest_20480 128 8 (by decide +kernel)

theorem badTest_20480_block_17 : Interval badTest_20480 136 144 :=
  interval_of_check badTest_20480 136 8 (by decide +kernel)

theorem badTest_20480_block_18 : Interval badTest_20480 144 152 :=
  interval_of_check badTest_20480 144 8 (by decide +kernel)

theorem badTest_20480_block_19 : Interval badTest_20480 152 160 :=
  interval_of_check badTest_20480 152 8 (by decide +kernel)

theorem badTest_20480_block_20 : Interval badTest_20480 160 168 :=
  interval_of_check badTest_20480 160 8 (by decide +kernel)

theorem badTest_20480_block_21 : Interval badTest_20480 168 176 :=
  interval_of_check badTest_20480 168 8 (by decide +kernel)

theorem badTest_20480_block_22 : Interval badTest_20480 176 184 :=
  interval_of_check badTest_20480 176 8 (by decide +kernel)

theorem badTest_20480_block_23 : Interval badTest_20480 184 192 :=
  interval_of_check badTest_20480 184 8 (by decide +kernel)

theorem badTest_20480_block_24 : Interval badTest_20480 192 200 :=
  interval_of_check badTest_20480 192 8 (by decide +kernel)

theorem badTest_20480_block_25 : Interval badTest_20480 200 208 :=
  interval_of_check badTest_20480 200 8 (by decide +kernel)

theorem badTest_20480_block_26 : Interval badTest_20480 208 216 :=
  interval_of_check badTest_20480 208 8 (by decide +kernel)

theorem badTest_20480_block_27 : Interval badTest_20480 216 224 :=
  interval_of_check badTest_20480 216 8 (by decide +kernel)

theorem badTest_20480_block_28 : Interval badTest_20480 224 232 :=
  interval_of_check badTest_20480 224 8 (by decide +kernel)

theorem badTest_20480_block_29 : Interval badTest_20480 232 240 :=
  interval_of_check badTest_20480 232 8 (by decide +kernel)

theorem badTest_20480_block_30 : Interval badTest_20480 240 248 :=
  interval_of_check badTest_20480 240 8 (by decide +kernel)

theorem badTest_20480_block_31 : Interval badTest_20480 248 256 :=
  interval_of_check badTest_20480 248 8 (by decide +kernel)

theorem badTest_20480_complete : Interval badTest_20480 0 256 :=
  (interval_append badTest_20480 0 128 256
  (interval_append badTest_20480 0 64 128
  (interval_append badTest_20480 0 32 64
  (interval_append badTest_20480 0 16 32
  (interval_append badTest_20480 0 8 16
  badTest_20480_block_0
  badTest_20480_block_1)
  (interval_append badTest_20480 16 24 32
  badTest_20480_block_2
  badTest_20480_block_3))
  (interval_append badTest_20480 32 48 64
  (interval_append badTest_20480 32 40 48
  badTest_20480_block_4
  badTest_20480_block_5)
  (interval_append badTest_20480 48 56 64
  badTest_20480_block_6
  badTest_20480_block_7)))
  (interval_append badTest_20480 64 96 128
  (interval_append badTest_20480 64 80 96
  (interval_append badTest_20480 64 72 80
  badTest_20480_block_8
  badTest_20480_block_9)
  (interval_append badTest_20480 80 88 96
  badTest_20480_block_10
  badTest_20480_block_11))
  (interval_append badTest_20480 96 112 128
  (interval_append badTest_20480 96 104 112
  badTest_20480_block_12
  badTest_20480_block_13)
  (interval_append badTest_20480 112 120 128
  badTest_20480_block_14
  badTest_20480_block_15))))
  (interval_append badTest_20480 128 192 256
  (interval_append badTest_20480 128 160 192
  (interval_append badTest_20480 128 144 160
  (interval_append badTest_20480 128 136 144
  badTest_20480_block_16
  badTest_20480_block_17)
  (interval_append badTest_20480 144 152 160
  badTest_20480_block_18
  badTest_20480_block_19))
  (interval_append badTest_20480 160 176 192
  (interval_append badTest_20480 160 168 176
  badTest_20480_block_20
  badTest_20480_block_21)
  (interval_append badTest_20480 176 184 192
  badTest_20480_block_22
  badTest_20480_block_23)))
  (interval_append badTest_20480 192 224 256
  (interval_append badTest_20480 192 208 224
  (interval_append badTest_20480 192 200 208
  badTest_20480_block_24
  badTest_20480_block_25)
  (interval_append badTest_20480 208 216 224
  badTest_20480_block_26
  badTest_20480_block_27))
  (interval_append badTest_20480 224 240 256
  (interval_append badTest_20480 224 232 240
  badTest_20480_block_28
  badTest_20480_block_29)
  (interval_append badTest_20480 240 248 256
  badTest_20480_block_30
  badTest_20480_block_31)))))
theorem badTestInterval20480 : Interval badTest 20480 20736 := by
  intro i hlo hhi
  have h := badTest_20480_complete (i-20480) (Nat.zero_le _) (by omega)
  simpa only [badTest_20480, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad081 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_20736 (i : Nat) := badTest (i+20736)
theorem badTest_20736_block_0 : Interval badTest_20736 0 8 :=
  interval_of_check badTest_20736 0 8 (by decide +kernel)

theorem badTest_20736_block_1 : Interval badTest_20736 8 16 :=
  interval_of_check badTest_20736 8 8 (by decide +kernel)

theorem badTest_20736_block_2 : Interval badTest_20736 16 24 :=
  interval_of_check badTest_20736 16 8 (by decide +kernel)

theorem badTest_20736_block_3 : Interval badTest_20736 24 32 :=
  interval_of_check badTest_20736 24 8 (by decide +kernel)

theorem badTest_20736_block_4 : Interval badTest_20736 32 40 :=
  interval_of_check badTest_20736 32 8 (by decide +kernel)

theorem badTest_20736_block_5 : Interval badTest_20736 40 48 :=
  interval_of_check badTest_20736 40 8 (by decide +kernel)

theorem badTest_20736_block_6 : Interval badTest_20736 48 56 :=
  interval_of_check badTest_20736 48 8 (by decide +kernel)

theorem badTest_20736_block_7 : Interval badTest_20736 56 64 :=
  interval_of_check badTest_20736 56 8 (by decide +kernel)

theorem badTest_20736_block_8 : Interval badTest_20736 64 72 :=
  interval_of_check badTest_20736 64 8 (by decide +kernel)

theorem badTest_20736_block_9 : Interval badTest_20736 72 80 :=
  interval_of_check badTest_20736 72 8 (by decide +kernel)

theorem badTest_20736_block_10 : Interval badTest_20736 80 88 :=
  interval_of_check badTest_20736 80 8 (by decide +kernel)

theorem badTest_20736_block_11 : Interval badTest_20736 88 96 :=
  interval_of_check badTest_20736 88 8 (by decide +kernel)

theorem badTest_20736_block_12 : Interval badTest_20736 96 104 :=
  interval_of_check badTest_20736 96 8 (by decide +kernel)

theorem badTest_20736_block_13 : Interval badTest_20736 104 112 :=
  interval_of_check badTest_20736 104 8 (by decide +kernel)

theorem badTest_20736_block_14 : Interval badTest_20736 112 120 :=
  interval_of_check badTest_20736 112 8 (by decide +kernel)

theorem badTest_20736_block_15 : Interval badTest_20736 120 128 :=
  interval_of_check badTest_20736 120 8 (by decide +kernel)

theorem badTest_20736_block_16 : Interval badTest_20736 128 136 :=
  interval_of_check badTest_20736 128 8 (by decide +kernel)

theorem badTest_20736_block_17 : Interval badTest_20736 136 144 :=
  interval_of_check badTest_20736 136 8 (by decide +kernel)

theorem badTest_20736_block_18 : Interval badTest_20736 144 152 :=
  interval_of_check badTest_20736 144 8 (by decide +kernel)

theorem badTest_20736_block_19 : Interval badTest_20736 152 160 :=
  interval_of_check badTest_20736 152 8 (by decide +kernel)

theorem badTest_20736_block_20 : Interval badTest_20736 160 168 :=
  interval_of_check badTest_20736 160 8 (by decide +kernel)

theorem badTest_20736_block_21 : Interval badTest_20736 168 176 :=
  interval_of_check badTest_20736 168 8 (by decide +kernel)

theorem badTest_20736_block_22 : Interval badTest_20736 176 184 :=
  interval_of_check badTest_20736 176 8 (by decide +kernel)

theorem badTest_20736_block_23 : Interval badTest_20736 184 192 :=
  interval_of_check badTest_20736 184 8 (by decide +kernel)

theorem badTest_20736_block_24 : Interval badTest_20736 192 200 :=
  interval_of_check badTest_20736 192 8 (by decide +kernel)

theorem badTest_20736_block_25 : Interval badTest_20736 200 208 :=
  interval_of_check badTest_20736 200 8 (by decide +kernel)

theorem badTest_20736_block_26 : Interval badTest_20736 208 216 :=
  interval_of_check badTest_20736 208 8 (by decide +kernel)

theorem badTest_20736_block_27 : Interval badTest_20736 216 224 :=
  interval_of_check badTest_20736 216 8 (by decide +kernel)

theorem badTest_20736_block_28 : Interval badTest_20736 224 232 :=
  interval_of_check badTest_20736 224 8 (by decide +kernel)

theorem badTest_20736_block_29 : Interval badTest_20736 232 240 :=
  interval_of_check badTest_20736 232 8 (by decide +kernel)

theorem badTest_20736_block_30 : Interval badTest_20736 240 248 :=
  interval_of_check badTest_20736 240 8 (by decide +kernel)

theorem badTest_20736_block_31 : Interval badTest_20736 248 256 :=
  interval_of_check badTest_20736 248 8 (by decide +kernel)

theorem badTest_20736_complete : Interval badTest_20736 0 256 :=
  (interval_append badTest_20736 0 128 256
  (interval_append badTest_20736 0 64 128
  (interval_append badTest_20736 0 32 64
  (interval_append badTest_20736 0 16 32
  (interval_append badTest_20736 0 8 16
  badTest_20736_block_0
  badTest_20736_block_1)
  (interval_append badTest_20736 16 24 32
  badTest_20736_block_2
  badTest_20736_block_3))
  (interval_append badTest_20736 32 48 64
  (interval_append badTest_20736 32 40 48
  badTest_20736_block_4
  badTest_20736_block_5)
  (interval_append badTest_20736 48 56 64
  badTest_20736_block_6
  badTest_20736_block_7)))
  (interval_append badTest_20736 64 96 128
  (interval_append badTest_20736 64 80 96
  (interval_append badTest_20736 64 72 80
  badTest_20736_block_8
  badTest_20736_block_9)
  (interval_append badTest_20736 80 88 96
  badTest_20736_block_10
  badTest_20736_block_11))
  (interval_append badTest_20736 96 112 128
  (interval_append badTest_20736 96 104 112
  badTest_20736_block_12
  badTest_20736_block_13)
  (interval_append badTest_20736 112 120 128
  badTest_20736_block_14
  badTest_20736_block_15))))
  (interval_append badTest_20736 128 192 256
  (interval_append badTest_20736 128 160 192
  (interval_append badTest_20736 128 144 160
  (interval_append badTest_20736 128 136 144
  badTest_20736_block_16
  badTest_20736_block_17)
  (interval_append badTest_20736 144 152 160
  badTest_20736_block_18
  badTest_20736_block_19))
  (interval_append badTest_20736 160 176 192
  (interval_append badTest_20736 160 168 176
  badTest_20736_block_20
  badTest_20736_block_21)
  (interval_append badTest_20736 176 184 192
  badTest_20736_block_22
  badTest_20736_block_23)))
  (interval_append badTest_20736 192 224 256
  (interval_append badTest_20736 192 208 224
  (interval_append badTest_20736 192 200 208
  badTest_20736_block_24
  badTest_20736_block_25)
  (interval_append badTest_20736 208 216 224
  badTest_20736_block_26
  badTest_20736_block_27))
  (interval_append badTest_20736 224 240 256
  (interval_append badTest_20736 224 232 240
  badTest_20736_block_28
  badTest_20736_block_29)
  (interval_append badTest_20736 240 248 256
  badTest_20736_block_30
  badTest_20736_block_31)))))
theorem badTestInterval20736 : Interval badTest 20736 20992 := by
  intro i hlo hhi
  have h := badTest_20736_complete (i-20736) (Nat.zero_le _) (by omega)
  simpa only [badTest_20736, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad082 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_20992 (i : Nat) := badTest (i+20992)
theorem badTest_20992_block_0 : Interval badTest_20992 0 8 :=
  interval_of_check badTest_20992 0 8 (by decide +kernel)

theorem badTest_20992_block_1 : Interval badTest_20992 8 16 :=
  interval_of_check badTest_20992 8 8 (by decide +kernel)

theorem badTest_20992_block_2 : Interval badTest_20992 16 24 :=
  interval_of_check badTest_20992 16 8 (by decide +kernel)

theorem badTest_20992_block_3 : Interval badTest_20992 24 32 :=
  interval_of_check badTest_20992 24 8 (by decide +kernel)

theorem badTest_20992_block_4 : Interval badTest_20992 32 40 :=
  interval_of_check badTest_20992 32 8 (by decide +kernel)

theorem badTest_20992_block_5 : Interval badTest_20992 40 48 :=
  interval_of_check badTest_20992 40 8 (by decide +kernel)

theorem badTest_20992_block_6 : Interval badTest_20992 48 56 :=
  interval_of_check badTest_20992 48 8 (by decide +kernel)

theorem badTest_20992_block_7 : Interval badTest_20992 56 64 :=
  interval_of_check badTest_20992 56 8 (by decide +kernel)

theorem badTest_20992_block_8 : Interval badTest_20992 64 72 :=
  interval_of_check badTest_20992 64 8 (by decide +kernel)

theorem badTest_20992_block_9 : Interval badTest_20992 72 80 :=
  interval_of_check badTest_20992 72 8 (by decide +kernel)

theorem badTest_20992_block_10 : Interval badTest_20992 80 88 :=
  interval_of_check badTest_20992 80 8 (by decide +kernel)

theorem badTest_20992_block_11 : Interval badTest_20992 88 96 :=
  interval_of_check badTest_20992 88 8 (by decide +kernel)

theorem badTest_20992_block_12 : Interval badTest_20992 96 104 :=
  interval_of_check badTest_20992 96 8 (by decide +kernel)

theorem badTest_20992_block_13 : Interval badTest_20992 104 112 :=
  interval_of_check badTest_20992 104 8 (by decide +kernel)

theorem badTest_20992_block_14 : Interval badTest_20992 112 120 :=
  interval_of_check badTest_20992 112 8 (by decide +kernel)

theorem badTest_20992_block_15 : Interval badTest_20992 120 128 :=
  interval_of_check badTest_20992 120 8 (by decide +kernel)

theorem badTest_20992_block_16 : Interval badTest_20992 128 136 :=
  interval_of_check badTest_20992 128 8 (by decide +kernel)

theorem badTest_20992_block_17 : Interval badTest_20992 136 144 :=
  interval_of_check badTest_20992 136 8 (by decide +kernel)

theorem badTest_20992_block_18 : Interval badTest_20992 144 152 :=
  interval_of_check badTest_20992 144 8 (by decide +kernel)

theorem badTest_20992_block_19 : Interval badTest_20992 152 160 :=
  interval_of_check badTest_20992 152 8 (by decide +kernel)

theorem badTest_20992_block_20 : Interval badTest_20992 160 168 :=
  interval_of_check badTest_20992 160 8 (by decide +kernel)

theorem badTest_20992_block_21 : Interval badTest_20992 168 176 :=
  interval_of_check badTest_20992 168 8 (by decide +kernel)

theorem badTest_20992_block_22 : Interval badTest_20992 176 184 :=
  interval_of_check badTest_20992 176 8 (by decide +kernel)

theorem badTest_20992_block_23 : Interval badTest_20992 184 192 :=
  interval_of_check badTest_20992 184 8 (by decide +kernel)

theorem badTest_20992_block_24 : Interval badTest_20992 192 200 :=
  interval_of_check badTest_20992 192 8 (by decide +kernel)

theorem badTest_20992_block_25 : Interval badTest_20992 200 208 :=
  interval_of_check badTest_20992 200 8 (by decide +kernel)

theorem badTest_20992_block_26 : Interval badTest_20992 208 216 :=
  interval_of_check badTest_20992 208 8 (by decide +kernel)

theorem badTest_20992_block_27 : Interval badTest_20992 216 224 :=
  interval_of_check badTest_20992 216 8 (by decide +kernel)

theorem badTest_20992_block_28 : Interval badTest_20992 224 232 :=
  interval_of_check badTest_20992 224 8 (by decide +kernel)

theorem badTest_20992_block_29 : Interval badTest_20992 232 240 :=
  interval_of_check badTest_20992 232 8 (by decide +kernel)

theorem badTest_20992_block_30 : Interval badTest_20992 240 248 :=
  interval_of_check badTest_20992 240 8 (by decide +kernel)

theorem badTest_20992_block_31 : Interval badTest_20992 248 256 :=
  interval_of_check badTest_20992 248 8 (by decide +kernel)

theorem badTest_20992_complete : Interval badTest_20992 0 256 :=
  (interval_append badTest_20992 0 128 256
  (interval_append badTest_20992 0 64 128
  (interval_append badTest_20992 0 32 64
  (interval_append badTest_20992 0 16 32
  (interval_append badTest_20992 0 8 16
  badTest_20992_block_0
  badTest_20992_block_1)
  (interval_append badTest_20992 16 24 32
  badTest_20992_block_2
  badTest_20992_block_3))
  (interval_append badTest_20992 32 48 64
  (interval_append badTest_20992 32 40 48
  badTest_20992_block_4
  badTest_20992_block_5)
  (interval_append badTest_20992 48 56 64
  badTest_20992_block_6
  badTest_20992_block_7)))
  (interval_append badTest_20992 64 96 128
  (interval_append badTest_20992 64 80 96
  (interval_append badTest_20992 64 72 80
  badTest_20992_block_8
  badTest_20992_block_9)
  (interval_append badTest_20992 80 88 96
  badTest_20992_block_10
  badTest_20992_block_11))
  (interval_append badTest_20992 96 112 128
  (interval_append badTest_20992 96 104 112
  badTest_20992_block_12
  badTest_20992_block_13)
  (interval_append badTest_20992 112 120 128
  badTest_20992_block_14
  badTest_20992_block_15))))
  (interval_append badTest_20992 128 192 256
  (interval_append badTest_20992 128 160 192
  (interval_append badTest_20992 128 144 160
  (interval_append badTest_20992 128 136 144
  badTest_20992_block_16
  badTest_20992_block_17)
  (interval_append badTest_20992 144 152 160
  badTest_20992_block_18
  badTest_20992_block_19))
  (interval_append badTest_20992 160 176 192
  (interval_append badTest_20992 160 168 176
  badTest_20992_block_20
  badTest_20992_block_21)
  (interval_append badTest_20992 176 184 192
  badTest_20992_block_22
  badTest_20992_block_23)))
  (interval_append badTest_20992 192 224 256
  (interval_append badTest_20992 192 208 224
  (interval_append badTest_20992 192 200 208
  badTest_20992_block_24
  badTest_20992_block_25)
  (interval_append badTest_20992 208 216 224
  badTest_20992_block_26
  badTest_20992_block_27))
  (interval_append badTest_20992 224 240 256
  (interval_append badTest_20992 224 232 240
  badTest_20992_block_28
  badTest_20992_block_29)
  (interval_append badTest_20992 240 248 256
  badTest_20992_block_30
  badTest_20992_block_31)))))
theorem badTestInterval20992 : Interval badTest 20992 21248 := by
  intro i hlo hhi
  have h := badTest_20992_complete (i-20992) (Nat.zero_le _) (by omega)
  simpa only [badTest_20992, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad083 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_21248 (i : Nat) := badTest (i+21248)
theorem badTest_21248_block_0 : Interval badTest_21248 0 8 :=
  interval_of_check badTest_21248 0 8 (by decide +kernel)

theorem badTest_21248_block_1 : Interval badTest_21248 8 16 :=
  interval_of_check badTest_21248 8 8 (by decide +kernel)

theorem badTest_21248_block_2 : Interval badTest_21248 16 24 :=
  interval_of_check badTest_21248 16 8 (by decide +kernel)

theorem badTest_21248_block_3 : Interval badTest_21248 24 32 :=
  interval_of_check badTest_21248 24 8 (by decide +kernel)

theorem badTest_21248_block_4 : Interval badTest_21248 32 40 :=
  interval_of_check badTest_21248 32 8 (by decide +kernel)

theorem badTest_21248_block_5 : Interval badTest_21248 40 48 :=
  interval_of_check badTest_21248 40 8 (by decide +kernel)

theorem badTest_21248_block_6 : Interval badTest_21248 48 56 :=
  interval_of_check badTest_21248 48 8 (by decide +kernel)

theorem badTest_21248_block_7 : Interval badTest_21248 56 64 :=
  interval_of_check badTest_21248 56 8 (by decide +kernel)

theorem badTest_21248_block_8 : Interval badTest_21248 64 72 :=
  interval_of_check badTest_21248 64 8 (by decide +kernel)

theorem badTest_21248_block_9 : Interval badTest_21248 72 80 :=
  interval_of_check badTest_21248 72 8 (by decide +kernel)

theorem badTest_21248_block_10 : Interval badTest_21248 80 88 :=
  interval_of_check badTest_21248 80 8 (by decide +kernel)

theorem badTest_21248_block_11 : Interval badTest_21248 88 96 :=
  interval_of_check badTest_21248 88 8 (by decide +kernel)

theorem badTest_21248_block_12 : Interval badTest_21248 96 104 :=
  interval_of_check badTest_21248 96 8 (by decide +kernel)

theorem badTest_21248_block_13 : Interval badTest_21248 104 112 :=
  interval_of_check badTest_21248 104 8 (by decide +kernel)

theorem badTest_21248_block_14 : Interval badTest_21248 112 120 :=
  interval_of_check badTest_21248 112 8 (by decide +kernel)

theorem badTest_21248_block_15 : Interval badTest_21248 120 128 :=
  interval_of_check badTest_21248 120 8 (by decide +kernel)

theorem badTest_21248_block_16 : Interval badTest_21248 128 136 :=
  interval_of_check badTest_21248 128 8 (by decide +kernel)

theorem badTest_21248_block_17 : Interval badTest_21248 136 144 :=
  interval_of_check badTest_21248 136 8 (by decide +kernel)

theorem badTest_21248_block_18 : Interval badTest_21248 144 152 :=
  interval_of_check badTest_21248 144 8 (by decide +kernel)

theorem badTest_21248_block_19 : Interval badTest_21248 152 160 :=
  interval_of_check badTest_21248 152 8 (by decide +kernel)

theorem badTest_21248_block_20 : Interval badTest_21248 160 168 :=
  interval_of_check badTest_21248 160 8 (by decide +kernel)

theorem badTest_21248_block_21 : Interval badTest_21248 168 176 :=
  interval_of_check badTest_21248 168 8 (by decide +kernel)

theorem badTest_21248_block_22 : Interval badTest_21248 176 184 :=
  interval_of_check badTest_21248 176 8 (by decide +kernel)

theorem badTest_21248_block_23 : Interval badTest_21248 184 192 :=
  interval_of_check badTest_21248 184 8 (by decide +kernel)

theorem badTest_21248_block_24 : Interval badTest_21248 192 200 :=
  interval_of_check badTest_21248 192 8 (by decide +kernel)

theorem badTest_21248_block_25 : Interval badTest_21248 200 208 :=
  interval_of_check badTest_21248 200 8 (by decide +kernel)

theorem badTest_21248_block_26 : Interval badTest_21248 208 216 :=
  interval_of_check badTest_21248 208 8 (by decide +kernel)

theorem badTest_21248_block_27 : Interval badTest_21248 216 224 :=
  interval_of_check badTest_21248 216 8 (by decide +kernel)

theorem badTest_21248_block_28 : Interval badTest_21248 224 232 :=
  interval_of_check badTest_21248 224 8 (by decide +kernel)

theorem badTest_21248_block_29 : Interval badTest_21248 232 240 :=
  interval_of_check badTest_21248 232 8 (by decide +kernel)

theorem badTest_21248_block_30 : Interval badTest_21248 240 248 :=
  interval_of_check badTest_21248 240 8 (by decide +kernel)

theorem badTest_21248_block_31 : Interval badTest_21248 248 256 :=
  interval_of_check badTest_21248 248 8 (by decide +kernel)

theorem badTest_21248_complete : Interval badTest_21248 0 256 :=
  (interval_append badTest_21248 0 128 256
  (interval_append badTest_21248 0 64 128
  (interval_append badTest_21248 0 32 64
  (interval_append badTest_21248 0 16 32
  (interval_append badTest_21248 0 8 16
  badTest_21248_block_0
  badTest_21248_block_1)
  (interval_append badTest_21248 16 24 32
  badTest_21248_block_2
  badTest_21248_block_3))
  (interval_append badTest_21248 32 48 64
  (interval_append badTest_21248 32 40 48
  badTest_21248_block_4
  badTest_21248_block_5)
  (interval_append badTest_21248 48 56 64
  badTest_21248_block_6
  badTest_21248_block_7)))
  (interval_append badTest_21248 64 96 128
  (interval_append badTest_21248 64 80 96
  (interval_append badTest_21248 64 72 80
  badTest_21248_block_8
  badTest_21248_block_9)
  (interval_append badTest_21248 80 88 96
  badTest_21248_block_10
  badTest_21248_block_11))
  (interval_append badTest_21248 96 112 128
  (interval_append badTest_21248 96 104 112
  badTest_21248_block_12
  badTest_21248_block_13)
  (interval_append badTest_21248 112 120 128
  badTest_21248_block_14
  badTest_21248_block_15))))
  (interval_append badTest_21248 128 192 256
  (interval_append badTest_21248 128 160 192
  (interval_append badTest_21248 128 144 160
  (interval_append badTest_21248 128 136 144
  badTest_21248_block_16
  badTest_21248_block_17)
  (interval_append badTest_21248 144 152 160
  badTest_21248_block_18
  badTest_21248_block_19))
  (interval_append badTest_21248 160 176 192
  (interval_append badTest_21248 160 168 176
  badTest_21248_block_20
  badTest_21248_block_21)
  (interval_append badTest_21248 176 184 192
  badTest_21248_block_22
  badTest_21248_block_23)))
  (interval_append badTest_21248 192 224 256
  (interval_append badTest_21248 192 208 224
  (interval_append badTest_21248 192 200 208
  badTest_21248_block_24
  badTest_21248_block_25)
  (interval_append badTest_21248 208 216 224
  badTest_21248_block_26
  badTest_21248_block_27))
  (interval_append badTest_21248 224 240 256
  (interval_append badTest_21248 224 232 240
  badTest_21248_block_28
  badTest_21248_block_29)
  (interval_append badTest_21248 240 248 256
  badTest_21248_block_30
  badTest_21248_block_31)))))
theorem badTestInterval21248 : Interval badTest 21248 21504 := by
  intro i hlo hhi
  have h := badTest_21248_complete (i-21248) (Nat.zero_le _) (by omega)
  simpa only [badTest_21248, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad084 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_21504 (i : Nat) := badTest (i+21504)
theorem badTest_21504_block_0 : Interval badTest_21504 0 8 :=
  interval_of_check badTest_21504 0 8 (by decide +kernel)

theorem badTest_21504_block_1 : Interval badTest_21504 8 16 :=
  interval_of_check badTest_21504 8 8 (by decide +kernel)

theorem badTest_21504_block_2 : Interval badTest_21504 16 24 :=
  interval_of_check badTest_21504 16 8 (by decide +kernel)

theorem badTest_21504_block_3 : Interval badTest_21504 24 32 :=
  interval_of_check badTest_21504 24 8 (by decide +kernel)

theorem badTest_21504_block_4 : Interval badTest_21504 32 40 :=
  interval_of_check badTest_21504 32 8 (by decide +kernel)

theorem badTest_21504_block_5 : Interval badTest_21504 40 48 :=
  interval_of_check badTest_21504 40 8 (by decide +kernel)

theorem badTest_21504_block_6 : Interval badTest_21504 48 56 :=
  interval_of_check badTest_21504 48 8 (by decide +kernel)

theorem badTest_21504_block_7 : Interval badTest_21504 56 64 :=
  interval_of_check badTest_21504 56 8 (by decide +kernel)

theorem badTest_21504_block_8 : Interval badTest_21504 64 72 :=
  interval_of_check badTest_21504 64 8 (by decide +kernel)

theorem badTest_21504_block_9 : Interval badTest_21504 72 80 :=
  interval_of_check badTest_21504 72 8 (by decide +kernel)

theorem badTest_21504_block_10 : Interval badTest_21504 80 88 :=
  interval_of_check badTest_21504 80 8 (by decide +kernel)

theorem badTest_21504_block_11 : Interval badTest_21504 88 96 :=
  interval_of_check badTest_21504 88 8 (by decide +kernel)

theorem badTest_21504_block_12 : Interval badTest_21504 96 104 :=
  interval_of_check badTest_21504 96 8 (by decide +kernel)

theorem badTest_21504_block_13 : Interval badTest_21504 104 112 :=
  interval_of_check badTest_21504 104 8 (by decide +kernel)

theorem badTest_21504_block_14 : Interval badTest_21504 112 120 :=
  interval_of_check badTest_21504 112 8 (by decide +kernel)

theorem badTest_21504_block_15 : Interval badTest_21504 120 128 :=
  interval_of_check badTest_21504 120 8 (by decide +kernel)

theorem badTest_21504_block_16 : Interval badTest_21504 128 136 :=
  interval_of_check badTest_21504 128 8 (by decide +kernel)

theorem badTest_21504_block_17 : Interval badTest_21504 136 144 :=
  interval_of_check badTest_21504 136 8 (by decide +kernel)

theorem badTest_21504_block_18 : Interval badTest_21504 144 152 :=
  interval_of_check badTest_21504 144 8 (by decide +kernel)

theorem badTest_21504_block_19 : Interval badTest_21504 152 160 :=
  interval_of_check badTest_21504 152 8 (by decide +kernel)

theorem badTest_21504_block_20 : Interval badTest_21504 160 168 :=
  interval_of_check badTest_21504 160 8 (by decide +kernel)

theorem badTest_21504_block_21 : Interval badTest_21504 168 176 :=
  interval_of_check badTest_21504 168 8 (by decide +kernel)

theorem badTest_21504_block_22 : Interval badTest_21504 176 184 :=
  interval_of_check badTest_21504 176 8 (by decide +kernel)

theorem badTest_21504_block_23 : Interval badTest_21504 184 192 :=
  interval_of_check badTest_21504 184 8 (by decide +kernel)

theorem badTest_21504_block_24 : Interval badTest_21504 192 200 :=
  interval_of_check badTest_21504 192 8 (by decide +kernel)

theorem badTest_21504_block_25 : Interval badTest_21504 200 208 :=
  interval_of_check badTest_21504 200 8 (by decide +kernel)

theorem badTest_21504_block_26 : Interval badTest_21504 208 216 :=
  interval_of_check badTest_21504 208 8 (by decide +kernel)

theorem badTest_21504_block_27 : Interval badTest_21504 216 224 :=
  interval_of_check badTest_21504 216 8 (by decide +kernel)

theorem badTest_21504_block_28 : Interval badTest_21504 224 232 :=
  interval_of_check badTest_21504 224 8 (by decide +kernel)

theorem badTest_21504_block_29 : Interval badTest_21504 232 240 :=
  interval_of_check badTest_21504 232 8 (by decide +kernel)

theorem badTest_21504_block_30 : Interval badTest_21504 240 248 :=
  interval_of_check badTest_21504 240 8 (by decide +kernel)

theorem badTest_21504_block_31 : Interval badTest_21504 248 256 :=
  interval_of_check badTest_21504 248 8 (by decide +kernel)

theorem badTest_21504_complete : Interval badTest_21504 0 256 :=
  (interval_append badTest_21504 0 128 256
  (interval_append badTest_21504 0 64 128
  (interval_append badTest_21504 0 32 64
  (interval_append badTest_21504 0 16 32
  (interval_append badTest_21504 0 8 16
  badTest_21504_block_0
  badTest_21504_block_1)
  (interval_append badTest_21504 16 24 32
  badTest_21504_block_2
  badTest_21504_block_3))
  (interval_append badTest_21504 32 48 64
  (interval_append badTest_21504 32 40 48
  badTest_21504_block_4
  badTest_21504_block_5)
  (interval_append badTest_21504 48 56 64
  badTest_21504_block_6
  badTest_21504_block_7)))
  (interval_append badTest_21504 64 96 128
  (interval_append badTest_21504 64 80 96
  (interval_append badTest_21504 64 72 80
  badTest_21504_block_8
  badTest_21504_block_9)
  (interval_append badTest_21504 80 88 96
  badTest_21504_block_10
  badTest_21504_block_11))
  (interval_append badTest_21504 96 112 128
  (interval_append badTest_21504 96 104 112
  badTest_21504_block_12
  badTest_21504_block_13)
  (interval_append badTest_21504 112 120 128
  badTest_21504_block_14
  badTest_21504_block_15))))
  (interval_append badTest_21504 128 192 256
  (interval_append badTest_21504 128 160 192
  (interval_append badTest_21504 128 144 160
  (interval_append badTest_21504 128 136 144
  badTest_21504_block_16
  badTest_21504_block_17)
  (interval_append badTest_21504 144 152 160
  badTest_21504_block_18
  badTest_21504_block_19))
  (interval_append badTest_21504 160 176 192
  (interval_append badTest_21504 160 168 176
  badTest_21504_block_20
  badTest_21504_block_21)
  (interval_append badTest_21504 176 184 192
  badTest_21504_block_22
  badTest_21504_block_23)))
  (interval_append badTest_21504 192 224 256
  (interval_append badTest_21504 192 208 224
  (interval_append badTest_21504 192 200 208
  badTest_21504_block_24
  badTest_21504_block_25)
  (interval_append badTest_21504 208 216 224
  badTest_21504_block_26
  badTest_21504_block_27))
  (interval_append badTest_21504 224 240 256
  (interval_append badTest_21504 224 232 240
  badTest_21504_block_28
  badTest_21504_block_29)
  (interval_append badTest_21504 240 248 256
  badTest_21504_block_30
  badTest_21504_block_31)))))
theorem badTestInterval21504 : Interval badTest 21504 21760 := by
  intro i hlo hhi
  have h := badTest_21504_complete (i-21504) (Nat.zero_le _) (by omega)
  simpa only [badTest_21504, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad085 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_21760 (i : Nat) := badTest (i+21760)
theorem badTest_21760_block_0 : Interval badTest_21760 0 8 :=
  interval_of_check badTest_21760 0 8 (by decide +kernel)

theorem badTest_21760_block_1 : Interval badTest_21760 8 16 :=
  interval_of_check badTest_21760 8 8 (by decide +kernel)

theorem badTest_21760_block_2 : Interval badTest_21760 16 24 :=
  interval_of_check badTest_21760 16 8 (by decide +kernel)

theorem badTest_21760_block_3 : Interval badTest_21760 24 32 :=
  interval_of_check badTest_21760 24 8 (by decide +kernel)

theorem badTest_21760_block_4 : Interval badTest_21760 32 40 :=
  interval_of_check badTest_21760 32 8 (by decide +kernel)

theorem badTest_21760_block_5 : Interval badTest_21760 40 48 :=
  interval_of_check badTest_21760 40 8 (by decide +kernel)

theorem badTest_21760_block_6 : Interval badTest_21760 48 56 :=
  interval_of_check badTest_21760 48 8 (by decide +kernel)

theorem badTest_21760_block_7 : Interval badTest_21760 56 64 :=
  interval_of_check badTest_21760 56 8 (by decide +kernel)

theorem badTest_21760_block_8 : Interval badTest_21760 64 72 :=
  interval_of_check badTest_21760 64 8 (by decide +kernel)

theorem badTest_21760_block_9 : Interval badTest_21760 72 80 :=
  interval_of_check badTest_21760 72 8 (by decide +kernel)

theorem badTest_21760_block_10 : Interval badTest_21760 80 88 :=
  interval_of_check badTest_21760 80 8 (by decide +kernel)

theorem badTest_21760_block_11 : Interval badTest_21760 88 96 :=
  interval_of_check badTest_21760 88 8 (by decide +kernel)

theorem badTest_21760_block_12 : Interval badTest_21760 96 104 :=
  interval_of_check badTest_21760 96 8 (by decide +kernel)

theorem badTest_21760_block_13 : Interval badTest_21760 104 112 :=
  interval_of_check badTest_21760 104 8 (by decide +kernel)

theorem badTest_21760_block_14 : Interval badTest_21760 112 120 :=
  interval_of_check badTest_21760 112 8 (by decide +kernel)

theorem badTest_21760_block_15 : Interval badTest_21760 120 128 :=
  interval_of_check badTest_21760 120 8 (by decide +kernel)

theorem badTest_21760_block_16 : Interval badTest_21760 128 136 :=
  interval_of_check badTest_21760 128 8 (by decide +kernel)

theorem badTest_21760_block_17 : Interval badTest_21760 136 144 :=
  interval_of_check badTest_21760 136 8 (by decide +kernel)

theorem badTest_21760_block_18 : Interval badTest_21760 144 152 :=
  interval_of_check badTest_21760 144 8 (by decide +kernel)

theorem badTest_21760_block_19 : Interval badTest_21760 152 160 :=
  interval_of_check badTest_21760 152 8 (by decide +kernel)

theorem badTest_21760_block_20 : Interval badTest_21760 160 168 :=
  interval_of_check badTest_21760 160 8 (by decide +kernel)

theorem badTest_21760_block_21 : Interval badTest_21760 168 176 :=
  interval_of_check badTest_21760 168 8 (by decide +kernel)

theorem badTest_21760_block_22 : Interval badTest_21760 176 184 :=
  interval_of_check badTest_21760 176 8 (by decide +kernel)

theorem badTest_21760_block_23 : Interval badTest_21760 184 192 :=
  interval_of_check badTest_21760 184 8 (by decide +kernel)

theorem badTest_21760_block_24 : Interval badTest_21760 192 200 :=
  interval_of_check badTest_21760 192 8 (by decide +kernel)

theorem badTest_21760_block_25 : Interval badTest_21760 200 208 :=
  interval_of_check badTest_21760 200 8 (by decide +kernel)

theorem badTest_21760_block_26 : Interval badTest_21760 208 216 :=
  interval_of_check badTest_21760 208 8 (by decide +kernel)

theorem badTest_21760_complete : Interval badTest_21760 0 216 :=
  (interval_append badTest_21760 0 104 216
  (interval_append badTest_21760 0 48 104
  (interval_append badTest_21760 0 24 48
  (interval_append badTest_21760 0 8 24
  badTest_21760_block_0
  (interval_append badTest_21760 8 16 24
  badTest_21760_block_1
  badTest_21760_block_2))
  (interval_append badTest_21760 24 32 48
  badTest_21760_block_3
  (interval_append badTest_21760 32 40 48
  badTest_21760_block_4
  badTest_21760_block_5)))
  (interval_append badTest_21760 48 72 104
  (interval_append badTest_21760 48 56 72
  badTest_21760_block_6
  (interval_append badTest_21760 56 64 72
  badTest_21760_block_7
  badTest_21760_block_8))
  (interval_append badTest_21760 72 88 104
  (interval_append badTest_21760 72 80 88
  badTest_21760_block_9
  badTest_21760_block_10)
  (interval_append badTest_21760 88 96 104
  badTest_21760_block_11
  badTest_21760_block_12))))
  (interval_append badTest_21760 104 160 216
  (interval_append badTest_21760 104 128 160
  (interval_append badTest_21760 104 112 128
  badTest_21760_block_13
  (interval_append badTest_21760 112 120 128
  badTest_21760_block_14
  badTest_21760_block_15))
  (interval_append badTest_21760 128 144 160
  (interval_append badTest_21760 128 136 144
  badTest_21760_block_16
  badTest_21760_block_17)
  (interval_append badTest_21760 144 152 160
  badTest_21760_block_18
  badTest_21760_block_19)))
  (interval_append badTest_21760 160 184 216
  (interval_append badTest_21760 160 168 184
  badTest_21760_block_20
  (interval_append badTest_21760 168 176 184
  badTest_21760_block_21
  badTest_21760_block_22))
  (interval_append badTest_21760 184 200 216
  (interval_append badTest_21760 184 192 200
  badTest_21760_block_23
  badTest_21760_block_24)
  (interval_append badTest_21760 200 208 216
  badTest_21760_block_25
  badTest_21760_block_26)))))
theorem badTestInterval21760 : Interval badTest 21760 21976 := by
  intro i hlo hhi
  have h := badTest_21760_complete (i-21760) (Nat.zero_le _) (by omega)
  simpa only [badTest_21760, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
