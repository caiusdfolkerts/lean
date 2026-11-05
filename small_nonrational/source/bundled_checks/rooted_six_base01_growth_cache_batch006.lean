module
prelude
public import RootedSixBase01GrowthCacheData

/- RootedSixBase01GrowthCacheBad036 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_9216 (i : Nat) := badTest (i+9216)
theorem badTest_9216_block_0 : Interval badTest_9216 0 8 :=
  interval_of_check badTest_9216 0 8 (by decide +kernel)

theorem badTest_9216_block_1 : Interval badTest_9216 8 16 :=
  interval_of_check badTest_9216 8 8 (by decide +kernel)

theorem badTest_9216_block_2 : Interval badTest_9216 16 24 :=
  interval_of_check badTest_9216 16 8 (by decide +kernel)

theorem badTest_9216_block_3 : Interval badTest_9216 24 32 :=
  interval_of_check badTest_9216 24 8 (by decide +kernel)

theorem badTest_9216_block_4 : Interval badTest_9216 32 40 :=
  interval_of_check badTest_9216 32 8 (by decide +kernel)

theorem badTest_9216_block_5 : Interval badTest_9216 40 48 :=
  interval_of_check badTest_9216 40 8 (by decide +kernel)

theorem badTest_9216_block_6 : Interval badTest_9216 48 56 :=
  interval_of_check badTest_9216 48 8 (by decide +kernel)

theorem badTest_9216_block_7 : Interval badTest_9216 56 64 :=
  interval_of_check badTest_9216 56 8 (by decide +kernel)

theorem badTest_9216_block_8 : Interval badTest_9216 64 72 :=
  interval_of_check badTest_9216 64 8 (by decide +kernel)

theorem badTest_9216_block_9 : Interval badTest_9216 72 80 :=
  interval_of_check badTest_9216 72 8 (by decide +kernel)

theorem badTest_9216_block_10 : Interval badTest_9216 80 88 :=
  interval_of_check badTest_9216 80 8 (by decide +kernel)

theorem badTest_9216_block_11 : Interval badTest_9216 88 96 :=
  interval_of_check badTest_9216 88 8 (by decide +kernel)

theorem badTest_9216_block_12 : Interval badTest_9216 96 104 :=
  interval_of_check badTest_9216 96 8 (by decide +kernel)

theorem badTest_9216_block_13 : Interval badTest_9216 104 112 :=
  interval_of_check badTest_9216 104 8 (by decide +kernel)

theorem badTest_9216_block_14 : Interval badTest_9216 112 120 :=
  interval_of_check badTest_9216 112 8 (by decide +kernel)

theorem badTest_9216_block_15 : Interval badTest_9216 120 128 :=
  interval_of_check badTest_9216 120 8 (by decide +kernel)

theorem badTest_9216_block_16 : Interval badTest_9216 128 136 :=
  interval_of_check badTest_9216 128 8 (by decide +kernel)

theorem badTest_9216_block_17 : Interval badTest_9216 136 144 :=
  interval_of_check badTest_9216 136 8 (by decide +kernel)

theorem badTest_9216_block_18 : Interval badTest_9216 144 152 :=
  interval_of_check badTest_9216 144 8 (by decide +kernel)

theorem badTest_9216_block_19 : Interval badTest_9216 152 160 :=
  interval_of_check badTest_9216 152 8 (by decide +kernel)

theorem badTest_9216_block_20 : Interval badTest_9216 160 168 :=
  interval_of_check badTest_9216 160 8 (by decide +kernel)

theorem badTest_9216_block_21 : Interval badTest_9216 168 176 :=
  interval_of_check badTest_9216 168 8 (by decide +kernel)

theorem badTest_9216_block_22 : Interval badTest_9216 176 184 :=
  interval_of_check badTest_9216 176 8 (by decide +kernel)

theorem badTest_9216_block_23 : Interval badTest_9216 184 192 :=
  interval_of_check badTest_9216 184 8 (by decide +kernel)

theorem badTest_9216_block_24 : Interval badTest_9216 192 200 :=
  interval_of_check badTest_9216 192 8 (by decide +kernel)

theorem badTest_9216_block_25 : Interval badTest_9216 200 208 :=
  interval_of_check badTest_9216 200 8 (by decide +kernel)

theorem badTest_9216_block_26 : Interval badTest_9216 208 216 :=
  interval_of_check badTest_9216 208 8 (by decide +kernel)

theorem badTest_9216_block_27 : Interval badTest_9216 216 224 :=
  interval_of_check badTest_9216 216 8 (by decide +kernel)

theorem badTest_9216_block_28 : Interval badTest_9216 224 232 :=
  interval_of_check badTest_9216 224 8 (by decide +kernel)

theorem badTest_9216_block_29 : Interval badTest_9216 232 240 :=
  interval_of_check badTest_9216 232 8 (by decide +kernel)

theorem badTest_9216_block_30 : Interval badTest_9216 240 248 :=
  interval_of_check badTest_9216 240 8 (by decide +kernel)

theorem badTest_9216_block_31 : Interval badTest_9216 248 256 :=
  interval_of_check badTest_9216 248 8 (by decide +kernel)

theorem badTest_9216_complete : Interval badTest_9216 0 256 :=
  (interval_append badTest_9216 0 128 256
  (interval_append badTest_9216 0 64 128
  (interval_append badTest_9216 0 32 64
  (interval_append badTest_9216 0 16 32
  (interval_append badTest_9216 0 8 16
  badTest_9216_block_0
  badTest_9216_block_1)
  (interval_append badTest_9216 16 24 32
  badTest_9216_block_2
  badTest_9216_block_3))
  (interval_append badTest_9216 32 48 64
  (interval_append badTest_9216 32 40 48
  badTest_9216_block_4
  badTest_9216_block_5)
  (interval_append badTest_9216 48 56 64
  badTest_9216_block_6
  badTest_9216_block_7)))
  (interval_append badTest_9216 64 96 128
  (interval_append badTest_9216 64 80 96
  (interval_append badTest_9216 64 72 80
  badTest_9216_block_8
  badTest_9216_block_9)
  (interval_append badTest_9216 80 88 96
  badTest_9216_block_10
  badTest_9216_block_11))
  (interval_append badTest_9216 96 112 128
  (interval_append badTest_9216 96 104 112
  badTest_9216_block_12
  badTest_9216_block_13)
  (interval_append badTest_9216 112 120 128
  badTest_9216_block_14
  badTest_9216_block_15))))
  (interval_append badTest_9216 128 192 256
  (interval_append badTest_9216 128 160 192
  (interval_append badTest_9216 128 144 160
  (interval_append badTest_9216 128 136 144
  badTest_9216_block_16
  badTest_9216_block_17)
  (interval_append badTest_9216 144 152 160
  badTest_9216_block_18
  badTest_9216_block_19))
  (interval_append badTest_9216 160 176 192
  (interval_append badTest_9216 160 168 176
  badTest_9216_block_20
  badTest_9216_block_21)
  (interval_append badTest_9216 176 184 192
  badTest_9216_block_22
  badTest_9216_block_23)))
  (interval_append badTest_9216 192 224 256
  (interval_append badTest_9216 192 208 224
  (interval_append badTest_9216 192 200 208
  badTest_9216_block_24
  badTest_9216_block_25)
  (interval_append badTest_9216 208 216 224
  badTest_9216_block_26
  badTest_9216_block_27))
  (interval_append badTest_9216 224 240 256
  (interval_append badTest_9216 224 232 240
  badTest_9216_block_28
  badTest_9216_block_29)
  (interval_append badTest_9216 240 248 256
  badTest_9216_block_30
  badTest_9216_block_31)))))
theorem badTestInterval9216 : Interval badTest 9216 9472 := by
  intro i hlo hhi
  have h := badTest_9216_complete (i-9216) (Nat.zero_le _) (by omega)
  simpa only [badTest_9216, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad037 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_9472 (i : Nat) := badTest (i+9472)
theorem badTest_9472_block_0 : Interval badTest_9472 0 8 :=
  interval_of_check badTest_9472 0 8 (by decide +kernel)

theorem badTest_9472_block_1 : Interval badTest_9472 8 16 :=
  interval_of_check badTest_9472 8 8 (by decide +kernel)

theorem badTest_9472_block_2 : Interval badTest_9472 16 24 :=
  interval_of_check badTest_9472 16 8 (by decide +kernel)

theorem badTest_9472_block_3 : Interval badTest_9472 24 32 :=
  interval_of_check badTest_9472 24 8 (by decide +kernel)

theorem badTest_9472_block_4 : Interval badTest_9472 32 40 :=
  interval_of_check badTest_9472 32 8 (by decide +kernel)

theorem badTest_9472_block_5 : Interval badTest_9472 40 48 :=
  interval_of_check badTest_9472 40 8 (by decide +kernel)

theorem badTest_9472_block_6 : Interval badTest_9472 48 56 :=
  interval_of_check badTest_9472 48 8 (by decide +kernel)

theorem badTest_9472_block_7 : Interval badTest_9472 56 64 :=
  interval_of_check badTest_9472 56 8 (by decide +kernel)

theorem badTest_9472_block_8 : Interval badTest_9472 64 72 :=
  interval_of_check badTest_9472 64 8 (by decide +kernel)

theorem badTest_9472_block_9 : Interval badTest_9472 72 80 :=
  interval_of_check badTest_9472 72 8 (by decide +kernel)

theorem badTest_9472_block_10 : Interval badTest_9472 80 88 :=
  interval_of_check badTest_9472 80 8 (by decide +kernel)

theorem badTest_9472_block_11 : Interval badTest_9472 88 96 :=
  interval_of_check badTest_9472 88 8 (by decide +kernel)

theorem badTest_9472_block_12 : Interval badTest_9472 96 104 :=
  interval_of_check badTest_9472 96 8 (by decide +kernel)

theorem badTest_9472_block_13 : Interval badTest_9472 104 112 :=
  interval_of_check badTest_9472 104 8 (by decide +kernel)

theorem badTest_9472_block_14 : Interval badTest_9472 112 120 :=
  interval_of_check badTest_9472 112 8 (by decide +kernel)

theorem badTest_9472_block_15 : Interval badTest_9472 120 128 :=
  interval_of_check badTest_9472 120 8 (by decide +kernel)

theorem badTest_9472_block_16 : Interval badTest_9472 128 136 :=
  interval_of_check badTest_9472 128 8 (by decide +kernel)

theorem badTest_9472_block_17 : Interval badTest_9472 136 144 :=
  interval_of_check badTest_9472 136 8 (by decide +kernel)

theorem badTest_9472_block_18 : Interval badTest_9472 144 152 :=
  interval_of_check badTest_9472 144 8 (by decide +kernel)

theorem badTest_9472_block_19 : Interval badTest_9472 152 160 :=
  interval_of_check badTest_9472 152 8 (by decide +kernel)

theorem badTest_9472_block_20 : Interval badTest_9472 160 168 :=
  interval_of_check badTest_9472 160 8 (by decide +kernel)

theorem badTest_9472_block_21 : Interval badTest_9472 168 176 :=
  interval_of_check badTest_9472 168 8 (by decide +kernel)

theorem badTest_9472_block_22 : Interval badTest_9472 176 184 :=
  interval_of_check badTest_9472 176 8 (by decide +kernel)

theorem badTest_9472_block_23 : Interval badTest_9472 184 192 :=
  interval_of_check badTest_9472 184 8 (by decide +kernel)

theorem badTest_9472_block_24 : Interval badTest_9472 192 200 :=
  interval_of_check badTest_9472 192 8 (by decide +kernel)

theorem badTest_9472_block_25 : Interval badTest_9472 200 208 :=
  interval_of_check badTest_9472 200 8 (by decide +kernel)

theorem badTest_9472_block_26 : Interval badTest_9472 208 216 :=
  interval_of_check badTest_9472 208 8 (by decide +kernel)

theorem badTest_9472_block_27 : Interval badTest_9472 216 224 :=
  interval_of_check badTest_9472 216 8 (by decide +kernel)

theorem badTest_9472_block_28 : Interval badTest_9472 224 232 :=
  interval_of_check badTest_9472 224 8 (by decide +kernel)

theorem badTest_9472_block_29 : Interval badTest_9472 232 240 :=
  interval_of_check badTest_9472 232 8 (by decide +kernel)

theorem badTest_9472_block_30 : Interval badTest_9472 240 248 :=
  interval_of_check badTest_9472 240 8 (by decide +kernel)

theorem badTest_9472_block_31 : Interval badTest_9472 248 256 :=
  interval_of_check badTest_9472 248 8 (by decide +kernel)

theorem badTest_9472_complete : Interval badTest_9472 0 256 :=
  (interval_append badTest_9472 0 128 256
  (interval_append badTest_9472 0 64 128
  (interval_append badTest_9472 0 32 64
  (interval_append badTest_9472 0 16 32
  (interval_append badTest_9472 0 8 16
  badTest_9472_block_0
  badTest_9472_block_1)
  (interval_append badTest_9472 16 24 32
  badTest_9472_block_2
  badTest_9472_block_3))
  (interval_append badTest_9472 32 48 64
  (interval_append badTest_9472 32 40 48
  badTest_9472_block_4
  badTest_9472_block_5)
  (interval_append badTest_9472 48 56 64
  badTest_9472_block_6
  badTest_9472_block_7)))
  (interval_append badTest_9472 64 96 128
  (interval_append badTest_9472 64 80 96
  (interval_append badTest_9472 64 72 80
  badTest_9472_block_8
  badTest_9472_block_9)
  (interval_append badTest_9472 80 88 96
  badTest_9472_block_10
  badTest_9472_block_11))
  (interval_append badTest_9472 96 112 128
  (interval_append badTest_9472 96 104 112
  badTest_9472_block_12
  badTest_9472_block_13)
  (interval_append badTest_9472 112 120 128
  badTest_9472_block_14
  badTest_9472_block_15))))
  (interval_append badTest_9472 128 192 256
  (interval_append badTest_9472 128 160 192
  (interval_append badTest_9472 128 144 160
  (interval_append badTest_9472 128 136 144
  badTest_9472_block_16
  badTest_9472_block_17)
  (interval_append badTest_9472 144 152 160
  badTest_9472_block_18
  badTest_9472_block_19))
  (interval_append badTest_9472 160 176 192
  (interval_append badTest_9472 160 168 176
  badTest_9472_block_20
  badTest_9472_block_21)
  (interval_append badTest_9472 176 184 192
  badTest_9472_block_22
  badTest_9472_block_23)))
  (interval_append badTest_9472 192 224 256
  (interval_append badTest_9472 192 208 224
  (interval_append badTest_9472 192 200 208
  badTest_9472_block_24
  badTest_9472_block_25)
  (interval_append badTest_9472 208 216 224
  badTest_9472_block_26
  badTest_9472_block_27))
  (interval_append badTest_9472 224 240 256
  (interval_append badTest_9472 224 232 240
  badTest_9472_block_28
  badTest_9472_block_29)
  (interval_append badTest_9472 240 248 256
  badTest_9472_block_30
  badTest_9472_block_31)))))
theorem badTestInterval9472 : Interval badTest 9472 9728 := by
  intro i hlo hhi
  have h := badTest_9472_complete (i-9472) (Nat.zero_le _) (by omega)
  simpa only [badTest_9472, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad038 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_9728 (i : Nat) := badTest (i+9728)
theorem badTest_9728_block_0 : Interval badTest_9728 0 8 :=
  interval_of_check badTest_9728 0 8 (by decide +kernel)

theorem badTest_9728_block_1 : Interval badTest_9728 8 16 :=
  interval_of_check badTest_9728 8 8 (by decide +kernel)

theorem badTest_9728_block_2 : Interval badTest_9728 16 24 :=
  interval_of_check badTest_9728 16 8 (by decide +kernel)

theorem badTest_9728_block_3 : Interval badTest_9728 24 32 :=
  interval_of_check badTest_9728 24 8 (by decide +kernel)

theorem badTest_9728_block_4 : Interval badTest_9728 32 40 :=
  interval_of_check badTest_9728 32 8 (by decide +kernel)

theorem badTest_9728_block_5 : Interval badTest_9728 40 48 :=
  interval_of_check badTest_9728 40 8 (by decide +kernel)

theorem badTest_9728_block_6 : Interval badTest_9728 48 56 :=
  interval_of_check badTest_9728 48 8 (by decide +kernel)

theorem badTest_9728_block_7 : Interval badTest_9728 56 64 :=
  interval_of_check badTest_9728 56 8 (by decide +kernel)

theorem badTest_9728_block_8 : Interval badTest_9728 64 72 :=
  interval_of_check badTest_9728 64 8 (by decide +kernel)

theorem badTest_9728_block_9 : Interval badTest_9728 72 80 :=
  interval_of_check badTest_9728 72 8 (by decide +kernel)

theorem badTest_9728_block_10 : Interval badTest_9728 80 88 :=
  interval_of_check badTest_9728 80 8 (by decide +kernel)

theorem badTest_9728_block_11 : Interval badTest_9728 88 96 :=
  interval_of_check badTest_9728 88 8 (by decide +kernel)

theorem badTest_9728_block_12 : Interval badTest_9728 96 104 :=
  interval_of_check badTest_9728 96 8 (by decide +kernel)

theorem badTest_9728_block_13 : Interval badTest_9728 104 112 :=
  interval_of_check badTest_9728 104 8 (by decide +kernel)

theorem badTest_9728_block_14 : Interval badTest_9728 112 120 :=
  interval_of_check badTest_9728 112 8 (by decide +kernel)

theorem badTest_9728_block_15 : Interval badTest_9728 120 128 :=
  interval_of_check badTest_9728 120 8 (by decide +kernel)

theorem badTest_9728_block_16 : Interval badTest_9728 128 136 :=
  interval_of_check badTest_9728 128 8 (by decide +kernel)

theorem badTest_9728_block_17 : Interval badTest_9728 136 144 :=
  interval_of_check badTest_9728 136 8 (by decide +kernel)

theorem badTest_9728_block_18 : Interval badTest_9728 144 152 :=
  interval_of_check badTest_9728 144 8 (by decide +kernel)

theorem badTest_9728_block_19 : Interval badTest_9728 152 160 :=
  interval_of_check badTest_9728 152 8 (by decide +kernel)

theorem badTest_9728_block_20 : Interval badTest_9728 160 168 :=
  interval_of_check badTest_9728 160 8 (by decide +kernel)

theorem badTest_9728_block_21 : Interval badTest_9728 168 176 :=
  interval_of_check badTest_9728 168 8 (by decide +kernel)

theorem badTest_9728_block_22 : Interval badTest_9728 176 184 :=
  interval_of_check badTest_9728 176 8 (by decide +kernel)

theorem badTest_9728_block_23 : Interval badTest_9728 184 192 :=
  interval_of_check badTest_9728 184 8 (by decide +kernel)

theorem badTest_9728_block_24 : Interval badTest_9728 192 200 :=
  interval_of_check badTest_9728 192 8 (by decide +kernel)

theorem badTest_9728_block_25 : Interval badTest_9728 200 208 :=
  interval_of_check badTest_9728 200 8 (by decide +kernel)

theorem badTest_9728_block_26 : Interval badTest_9728 208 216 :=
  interval_of_check badTest_9728 208 8 (by decide +kernel)

theorem badTest_9728_block_27 : Interval badTest_9728 216 224 :=
  interval_of_check badTest_9728 216 8 (by decide +kernel)

theorem badTest_9728_block_28 : Interval badTest_9728 224 232 :=
  interval_of_check badTest_9728 224 8 (by decide +kernel)

theorem badTest_9728_block_29 : Interval badTest_9728 232 240 :=
  interval_of_check badTest_9728 232 8 (by decide +kernel)

theorem badTest_9728_block_30 : Interval badTest_9728 240 248 :=
  interval_of_check badTest_9728 240 8 (by decide +kernel)

theorem badTest_9728_block_31 : Interval badTest_9728 248 256 :=
  interval_of_check badTest_9728 248 8 (by decide +kernel)

theorem badTest_9728_complete : Interval badTest_9728 0 256 :=
  (interval_append badTest_9728 0 128 256
  (interval_append badTest_9728 0 64 128
  (interval_append badTest_9728 0 32 64
  (interval_append badTest_9728 0 16 32
  (interval_append badTest_9728 0 8 16
  badTest_9728_block_0
  badTest_9728_block_1)
  (interval_append badTest_9728 16 24 32
  badTest_9728_block_2
  badTest_9728_block_3))
  (interval_append badTest_9728 32 48 64
  (interval_append badTest_9728 32 40 48
  badTest_9728_block_4
  badTest_9728_block_5)
  (interval_append badTest_9728 48 56 64
  badTest_9728_block_6
  badTest_9728_block_7)))
  (interval_append badTest_9728 64 96 128
  (interval_append badTest_9728 64 80 96
  (interval_append badTest_9728 64 72 80
  badTest_9728_block_8
  badTest_9728_block_9)
  (interval_append badTest_9728 80 88 96
  badTest_9728_block_10
  badTest_9728_block_11))
  (interval_append badTest_9728 96 112 128
  (interval_append badTest_9728 96 104 112
  badTest_9728_block_12
  badTest_9728_block_13)
  (interval_append badTest_9728 112 120 128
  badTest_9728_block_14
  badTest_9728_block_15))))
  (interval_append badTest_9728 128 192 256
  (interval_append badTest_9728 128 160 192
  (interval_append badTest_9728 128 144 160
  (interval_append badTest_9728 128 136 144
  badTest_9728_block_16
  badTest_9728_block_17)
  (interval_append badTest_9728 144 152 160
  badTest_9728_block_18
  badTest_9728_block_19))
  (interval_append badTest_9728 160 176 192
  (interval_append badTest_9728 160 168 176
  badTest_9728_block_20
  badTest_9728_block_21)
  (interval_append badTest_9728 176 184 192
  badTest_9728_block_22
  badTest_9728_block_23)))
  (interval_append badTest_9728 192 224 256
  (interval_append badTest_9728 192 208 224
  (interval_append badTest_9728 192 200 208
  badTest_9728_block_24
  badTest_9728_block_25)
  (interval_append badTest_9728 208 216 224
  badTest_9728_block_26
  badTest_9728_block_27))
  (interval_append badTest_9728 224 240 256
  (interval_append badTest_9728 224 232 240
  badTest_9728_block_28
  badTest_9728_block_29)
  (interval_append badTest_9728 240 248 256
  badTest_9728_block_30
  badTest_9728_block_31)))))
theorem badTestInterval9728 : Interval badTest 9728 9984 := by
  intro i hlo hhi
  have h := badTest_9728_complete (i-9728) (Nat.zero_le _) (by omega)
  simpa only [badTest_9728, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad039 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_9984 (i : Nat) := badTest (i+9984)
theorem badTest_9984_block_0 : Interval badTest_9984 0 8 :=
  interval_of_check badTest_9984 0 8 (by decide +kernel)

theorem badTest_9984_block_1 : Interval badTest_9984 8 16 :=
  interval_of_check badTest_9984 8 8 (by decide +kernel)

theorem badTest_9984_block_2 : Interval badTest_9984 16 24 :=
  interval_of_check badTest_9984 16 8 (by decide +kernel)

theorem badTest_9984_block_3 : Interval badTest_9984 24 32 :=
  interval_of_check badTest_9984 24 8 (by decide +kernel)

theorem badTest_9984_block_4 : Interval badTest_9984 32 40 :=
  interval_of_check badTest_9984 32 8 (by decide +kernel)

theorem badTest_9984_block_5 : Interval badTest_9984 40 48 :=
  interval_of_check badTest_9984 40 8 (by decide +kernel)

theorem badTest_9984_block_6 : Interval badTest_9984 48 56 :=
  interval_of_check badTest_9984 48 8 (by decide +kernel)

theorem badTest_9984_block_7 : Interval badTest_9984 56 64 :=
  interval_of_check badTest_9984 56 8 (by decide +kernel)

theorem badTest_9984_block_8 : Interval badTest_9984 64 72 :=
  interval_of_check badTest_9984 64 8 (by decide +kernel)

theorem badTest_9984_block_9 : Interval badTest_9984 72 80 :=
  interval_of_check badTest_9984 72 8 (by decide +kernel)

theorem badTest_9984_block_10 : Interval badTest_9984 80 88 :=
  interval_of_check badTest_9984 80 8 (by decide +kernel)

theorem badTest_9984_block_11 : Interval badTest_9984 88 96 :=
  interval_of_check badTest_9984 88 8 (by decide +kernel)

theorem badTest_9984_block_12 : Interval badTest_9984 96 104 :=
  interval_of_check badTest_9984 96 8 (by decide +kernel)

theorem badTest_9984_block_13 : Interval badTest_9984 104 112 :=
  interval_of_check badTest_9984 104 8 (by decide +kernel)

theorem badTest_9984_block_14 : Interval badTest_9984 112 120 :=
  interval_of_check badTest_9984 112 8 (by decide +kernel)

theorem badTest_9984_block_15 : Interval badTest_9984 120 128 :=
  interval_of_check badTest_9984 120 8 (by decide +kernel)

theorem badTest_9984_block_16 : Interval badTest_9984 128 136 :=
  interval_of_check badTest_9984 128 8 (by decide +kernel)

theorem badTest_9984_block_17 : Interval badTest_9984 136 144 :=
  interval_of_check badTest_9984 136 8 (by decide +kernel)

theorem badTest_9984_block_18 : Interval badTest_9984 144 152 :=
  interval_of_check badTest_9984 144 8 (by decide +kernel)

theorem badTest_9984_block_19 : Interval badTest_9984 152 160 :=
  interval_of_check badTest_9984 152 8 (by decide +kernel)

theorem badTest_9984_block_20 : Interval badTest_9984 160 168 :=
  interval_of_check badTest_9984 160 8 (by decide +kernel)

theorem badTest_9984_block_21 : Interval badTest_9984 168 176 :=
  interval_of_check badTest_9984 168 8 (by decide +kernel)

theorem badTest_9984_block_22 : Interval badTest_9984 176 184 :=
  interval_of_check badTest_9984 176 8 (by decide +kernel)

theorem badTest_9984_block_23 : Interval badTest_9984 184 192 :=
  interval_of_check badTest_9984 184 8 (by decide +kernel)

theorem badTest_9984_block_24 : Interval badTest_9984 192 200 :=
  interval_of_check badTest_9984 192 8 (by decide +kernel)

theorem badTest_9984_block_25 : Interval badTest_9984 200 208 :=
  interval_of_check badTest_9984 200 8 (by decide +kernel)

theorem badTest_9984_block_26 : Interval badTest_9984 208 216 :=
  interval_of_check badTest_9984 208 8 (by decide +kernel)

theorem badTest_9984_block_27 : Interval badTest_9984 216 224 :=
  interval_of_check badTest_9984 216 8 (by decide +kernel)

theorem badTest_9984_block_28 : Interval badTest_9984 224 232 :=
  interval_of_check badTest_9984 224 8 (by decide +kernel)

theorem badTest_9984_block_29 : Interval badTest_9984 232 240 :=
  interval_of_check badTest_9984 232 8 (by decide +kernel)

theorem badTest_9984_block_30 : Interval badTest_9984 240 248 :=
  interval_of_check badTest_9984 240 8 (by decide +kernel)

theorem badTest_9984_block_31 : Interval badTest_9984 248 256 :=
  interval_of_check badTest_9984 248 8 (by decide +kernel)

theorem badTest_9984_complete : Interval badTest_9984 0 256 :=
  (interval_append badTest_9984 0 128 256
  (interval_append badTest_9984 0 64 128
  (interval_append badTest_9984 0 32 64
  (interval_append badTest_9984 0 16 32
  (interval_append badTest_9984 0 8 16
  badTest_9984_block_0
  badTest_9984_block_1)
  (interval_append badTest_9984 16 24 32
  badTest_9984_block_2
  badTest_9984_block_3))
  (interval_append badTest_9984 32 48 64
  (interval_append badTest_9984 32 40 48
  badTest_9984_block_4
  badTest_9984_block_5)
  (interval_append badTest_9984 48 56 64
  badTest_9984_block_6
  badTest_9984_block_7)))
  (interval_append badTest_9984 64 96 128
  (interval_append badTest_9984 64 80 96
  (interval_append badTest_9984 64 72 80
  badTest_9984_block_8
  badTest_9984_block_9)
  (interval_append badTest_9984 80 88 96
  badTest_9984_block_10
  badTest_9984_block_11))
  (interval_append badTest_9984 96 112 128
  (interval_append badTest_9984 96 104 112
  badTest_9984_block_12
  badTest_9984_block_13)
  (interval_append badTest_9984 112 120 128
  badTest_9984_block_14
  badTest_9984_block_15))))
  (interval_append badTest_9984 128 192 256
  (interval_append badTest_9984 128 160 192
  (interval_append badTest_9984 128 144 160
  (interval_append badTest_9984 128 136 144
  badTest_9984_block_16
  badTest_9984_block_17)
  (interval_append badTest_9984 144 152 160
  badTest_9984_block_18
  badTest_9984_block_19))
  (interval_append badTest_9984 160 176 192
  (interval_append badTest_9984 160 168 176
  badTest_9984_block_20
  badTest_9984_block_21)
  (interval_append badTest_9984 176 184 192
  badTest_9984_block_22
  badTest_9984_block_23)))
  (interval_append badTest_9984 192 224 256
  (interval_append badTest_9984 192 208 224
  (interval_append badTest_9984 192 200 208
  badTest_9984_block_24
  badTest_9984_block_25)
  (interval_append badTest_9984 208 216 224
  badTest_9984_block_26
  badTest_9984_block_27))
  (interval_append badTest_9984 224 240 256
  (interval_append badTest_9984 224 232 240
  badTest_9984_block_28
  badTest_9984_block_29)
  (interval_append badTest_9984 240 248 256
  badTest_9984_block_30
  badTest_9984_block_31)))))
theorem badTestInterval9984 : Interval badTest 9984 10240 := by
  intro i hlo hhi
  have h := badTest_9984_complete (i-9984) (Nat.zero_le _) (by omega)
  simpa only [badTest_9984, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad040 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_10240 (i : Nat) := badTest (i+10240)
theorem badTest_10240_block_0 : Interval badTest_10240 0 8 :=
  interval_of_check badTest_10240 0 8 (by decide +kernel)

theorem badTest_10240_block_1 : Interval badTest_10240 8 16 :=
  interval_of_check badTest_10240 8 8 (by decide +kernel)

theorem badTest_10240_block_2 : Interval badTest_10240 16 24 :=
  interval_of_check badTest_10240 16 8 (by decide +kernel)

theorem badTest_10240_block_3 : Interval badTest_10240 24 32 :=
  interval_of_check badTest_10240 24 8 (by decide +kernel)

theorem badTest_10240_block_4 : Interval badTest_10240 32 40 :=
  interval_of_check badTest_10240 32 8 (by decide +kernel)

theorem badTest_10240_block_5 : Interval badTest_10240 40 48 :=
  interval_of_check badTest_10240 40 8 (by decide +kernel)

theorem badTest_10240_block_6 : Interval badTest_10240 48 56 :=
  interval_of_check badTest_10240 48 8 (by decide +kernel)

theorem badTest_10240_block_7 : Interval badTest_10240 56 64 :=
  interval_of_check badTest_10240 56 8 (by decide +kernel)

theorem badTest_10240_block_8 : Interval badTest_10240 64 72 :=
  interval_of_check badTest_10240 64 8 (by decide +kernel)

theorem badTest_10240_block_9 : Interval badTest_10240 72 80 :=
  interval_of_check badTest_10240 72 8 (by decide +kernel)

theorem badTest_10240_block_10 : Interval badTest_10240 80 88 :=
  interval_of_check badTest_10240 80 8 (by decide +kernel)

theorem badTest_10240_block_11 : Interval badTest_10240 88 96 :=
  interval_of_check badTest_10240 88 8 (by decide +kernel)

theorem badTest_10240_block_12 : Interval badTest_10240 96 104 :=
  interval_of_check badTest_10240 96 8 (by decide +kernel)

theorem badTest_10240_block_13 : Interval badTest_10240 104 112 :=
  interval_of_check badTest_10240 104 8 (by decide +kernel)

theorem badTest_10240_block_14 : Interval badTest_10240 112 120 :=
  interval_of_check badTest_10240 112 8 (by decide +kernel)

theorem badTest_10240_block_15 : Interval badTest_10240 120 128 :=
  interval_of_check badTest_10240 120 8 (by decide +kernel)

theorem badTest_10240_block_16 : Interval badTest_10240 128 136 :=
  interval_of_check badTest_10240 128 8 (by decide +kernel)

theorem badTest_10240_block_17 : Interval badTest_10240 136 144 :=
  interval_of_check badTest_10240 136 8 (by decide +kernel)

theorem badTest_10240_block_18 : Interval badTest_10240 144 152 :=
  interval_of_check badTest_10240 144 8 (by decide +kernel)

theorem badTest_10240_block_19 : Interval badTest_10240 152 160 :=
  interval_of_check badTest_10240 152 8 (by decide +kernel)

theorem badTest_10240_block_20 : Interval badTest_10240 160 168 :=
  interval_of_check badTest_10240 160 8 (by decide +kernel)

theorem badTest_10240_block_21 : Interval badTest_10240 168 176 :=
  interval_of_check badTest_10240 168 8 (by decide +kernel)

theorem badTest_10240_block_22 : Interval badTest_10240 176 184 :=
  interval_of_check badTest_10240 176 8 (by decide +kernel)

theorem badTest_10240_block_23 : Interval badTest_10240 184 192 :=
  interval_of_check badTest_10240 184 8 (by decide +kernel)

theorem badTest_10240_block_24 : Interval badTest_10240 192 200 :=
  interval_of_check badTest_10240 192 8 (by decide +kernel)

theorem badTest_10240_block_25 : Interval badTest_10240 200 208 :=
  interval_of_check badTest_10240 200 8 (by decide +kernel)

theorem badTest_10240_block_26 : Interval badTest_10240 208 216 :=
  interval_of_check badTest_10240 208 8 (by decide +kernel)

theorem badTest_10240_block_27 : Interval badTest_10240 216 224 :=
  interval_of_check badTest_10240 216 8 (by decide +kernel)

theorem badTest_10240_block_28 : Interval badTest_10240 224 232 :=
  interval_of_check badTest_10240 224 8 (by decide +kernel)

theorem badTest_10240_block_29 : Interval badTest_10240 232 240 :=
  interval_of_check badTest_10240 232 8 (by decide +kernel)

theorem badTest_10240_block_30 : Interval badTest_10240 240 248 :=
  interval_of_check badTest_10240 240 8 (by decide +kernel)

theorem badTest_10240_block_31 : Interval badTest_10240 248 256 :=
  interval_of_check badTest_10240 248 8 (by decide +kernel)

theorem badTest_10240_complete : Interval badTest_10240 0 256 :=
  (interval_append badTest_10240 0 128 256
  (interval_append badTest_10240 0 64 128
  (interval_append badTest_10240 0 32 64
  (interval_append badTest_10240 0 16 32
  (interval_append badTest_10240 0 8 16
  badTest_10240_block_0
  badTest_10240_block_1)
  (interval_append badTest_10240 16 24 32
  badTest_10240_block_2
  badTest_10240_block_3))
  (interval_append badTest_10240 32 48 64
  (interval_append badTest_10240 32 40 48
  badTest_10240_block_4
  badTest_10240_block_5)
  (interval_append badTest_10240 48 56 64
  badTest_10240_block_6
  badTest_10240_block_7)))
  (interval_append badTest_10240 64 96 128
  (interval_append badTest_10240 64 80 96
  (interval_append badTest_10240 64 72 80
  badTest_10240_block_8
  badTest_10240_block_9)
  (interval_append badTest_10240 80 88 96
  badTest_10240_block_10
  badTest_10240_block_11))
  (interval_append badTest_10240 96 112 128
  (interval_append badTest_10240 96 104 112
  badTest_10240_block_12
  badTest_10240_block_13)
  (interval_append badTest_10240 112 120 128
  badTest_10240_block_14
  badTest_10240_block_15))))
  (interval_append badTest_10240 128 192 256
  (interval_append badTest_10240 128 160 192
  (interval_append badTest_10240 128 144 160
  (interval_append badTest_10240 128 136 144
  badTest_10240_block_16
  badTest_10240_block_17)
  (interval_append badTest_10240 144 152 160
  badTest_10240_block_18
  badTest_10240_block_19))
  (interval_append badTest_10240 160 176 192
  (interval_append badTest_10240 160 168 176
  badTest_10240_block_20
  badTest_10240_block_21)
  (interval_append badTest_10240 176 184 192
  badTest_10240_block_22
  badTest_10240_block_23)))
  (interval_append badTest_10240 192 224 256
  (interval_append badTest_10240 192 208 224
  (interval_append badTest_10240 192 200 208
  badTest_10240_block_24
  badTest_10240_block_25)
  (interval_append badTest_10240 208 216 224
  badTest_10240_block_26
  badTest_10240_block_27))
  (interval_append badTest_10240 224 240 256
  (interval_append badTest_10240 224 232 240
  badTest_10240_block_28
  badTest_10240_block_29)
  (interval_append badTest_10240 240 248 256
  badTest_10240_block_30
  badTest_10240_block_31)))))
theorem badTestInterval10240 : Interval badTest 10240 10496 := by
  intro i hlo hhi
  have h := badTest_10240_complete (i-10240) (Nat.zero_le _) (by omega)
  simpa only [badTest_10240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad041 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_10496 (i : Nat) := badTest (i+10496)
theorem badTest_10496_block_0 : Interval badTest_10496 0 8 :=
  interval_of_check badTest_10496 0 8 (by decide +kernel)

theorem badTest_10496_block_1 : Interval badTest_10496 8 16 :=
  interval_of_check badTest_10496 8 8 (by decide +kernel)

theorem badTest_10496_block_2 : Interval badTest_10496 16 24 :=
  interval_of_check badTest_10496 16 8 (by decide +kernel)

theorem badTest_10496_block_3 : Interval badTest_10496 24 32 :=
  interval_of_check badTest_10496 24 8 (by decide +kernel)

theorem badTest_10496_block_4 : Interval badTest_10496 32 40 :=
  interval_of_check badTest_10496 32 8 (by decide +kernel)

theorem badTest_10496_block_5 : Interval badTest_10496 40 48 :=
  interval_of_check badTest_10496 40 8 (by decide +kernel)

theorem badTest_10496_block_6 : Interval badTest_10496 48 56 :=
  interval_of_check badTest_10496 48 8 (by decide +kernel)

theorem badTest_10496_block_7 : Interval badTest_10496 56 64 :=
  interval_of_check badTest_10496 56 8 (by decide +kernel)

theorem badTest_10496_block_8 : Interval badTest_10496 64 72 :=
  interval_of_check badTest_10496 64 8 (by decide +kernel)

theorem badTest_10496_block_9 : Interval badTest_10496 72 80 :=
  interval_of_check badTest_10496 72 8 (by decide +kernel)

theorem badTest_10496_block_10 : Interval badTest_10496 80 88 :=
  interval_of_check badTest_10496 80 8 (by decide +kernel)

theorem badTest_10496_block_11 : Interval badTest_10496 88 96 :=
  interval_of_check badTest_10496 88 8 (by decide +kernel)

theorem badTest_10496_block_12 : Interval badTest_10496 96 104 :=
  interval_of_check badTest_10496 96 8 (by decide +kernel)

theorem badTest_10496_block_13 : Interval badTest_10496 104 112 :=
  interval_of_check badTest_10496 104 8 (by decide +kernel)

theorem badTest_10496_block_14 : Interval badTest_10496 112 120 :=
  interval_of_check badTest_10496 112 8 (by decide +kernel)

theorem badTest_10496_block_15 : Interval badTest_10496 120 128 :=
  interval_of_check badTest_10496 120 8 (by decide +kernel)

theorem badTest_10496_block_16 : Interval badTest_10496 128 136 :=
  interval_of_check badTest_10496 128 8 (by decide +kernel)

theorem badTest_10496_block_17 : Interval badTest_10496 136 144 :=
  interval_of_check badTest_10496 136 8 (by decide +kernel)

theorem badTest_10496_block_18 : Interval badTest_10496 144 152 :=
  interval_of_check badTest_10496 144 8 (by decide +kernel)

theorem badTest_10496_block_19 : Interval badTest_10496 152 160 :=
  interval_of_check badTest_10496 152 8 (by decide +kernel)

theorem badTest_10496_block_20 : Interval badTest_10496 160 168 :=
  interval_of_check badTest_10496 160 8 (by decide +kernel)

theorem badTest_10496_block_21 : Interval badTest_10496 168 176 :=
  interval_of_check badTest_10496 168 8 (by decide +kernel)

theorem badTest_10496_block_22 : Interval badTest_10496 176 184 :=
  interval_of_check badTest_10496 176 8 (by decide +kernel)

theorem badTest_10496_block_23 : Interval badTest_10496 184 192 :=
  interval_of_check badTest_10496 184 8 (by decide +kernel)

theorem badTest_10496_block_24 : Interval badTest_10496 192 200 :=
  interval_of_check badTest_10496 192 8 (by decide +kernel)

theorem badTest_10496_block_25 : Interval badTest_10496 200 208 :=
  interval_of_check badTest_10496 200 8 (by decide +kernel)

theorem badTest_10496_block_26 : Interval badTest_10496 208 216 :=
  interval_of_check badTest_10496 208 8 (by decide +kernel)

theorem badTest_10496_block_27 : Interval badTest_10496 216 224 :=
  interval_of_check badTest_10496 216 8 (by decide +kernel)

theorem badTest_10496_block_28 : Interval badTest_10496 224 232 :=
  interval_of_check badTest_10496 224 8 (by decide +kernel)

theorem badTest_10496_block_29 : Interval badTest_10496 232 240 :=
  interval_of_check badTest_10496 232 8 (by decide +kernel)

theorem badTest_10496_block_30 : Interval badTest_10496 240 248 :=
  interval_of_check badTest_10496 240 8 (by decide +kernel)

theorem badTest_10496_block_31 : Interval badTest_10496 248 256 :=
  interval_of_check badTest_10496 248 8 (by decide +kernel)

theorem badTest_10496_complete : Interval badTest_10496 0 256 :=
  (interval_append badTest_10496 0 128 256
  (interval_append badTest_10496 0 64 128
  (interval_append badTest_10496 0 32 64
  (interval_append badTest_10496 0 16 32
  (interval_append badTest_10496 0 8 16
  badTest_10496_block_0
  badTest_10496_block_1)
  (interval_append badTest_10496 16 24 32
  badTest_10496_block_2
  badTest_10496_block_3))
  (interval_append badTest_10496 32 48 64
  (interval_append badTest_10496 32 40 48
  badTest_10496_block_4
  badTest_10496_block_5)
  (interval_append badTest_10496 48 56 64
  badTest_10496_block_6
  badTest_10496_block_7)))
  (interval_append badTest_10496 64 96 128
  (interval_append badTest_10496 64 80 96
  (interval_append badTest_10496 64 72 80
  badTest_10496_block_8
  badTest_10496_block_9)
  (interval_append badTest_10496 80 88 96
  badTest_10496_block_10
  badTest_10496_block_11))
  (interval_append badTest_10496 96 112 128
  (interval_append badTest_10496 96 104 112
  badTest_10496_block_12
  badTest_10496_block_13)
  (interval_append badTest_10496 112 120 128
  badTest_10496_block_14
  badTest_10496_block_15))))
  (interval_append badTest_10496 128 192 256
  (interval_append badTest_10496 128 160 192
  (interval_append badTest_10496 128 144 160
  (interval_append badTest_10496 128 136 144
  badTest_10496_block_16
  badTest_10496_block_17)
  (interval_append badTest_10496 144 152 160
  badTest_10496_block_18
  badTest_10496_block_19))
  (interval_append badTest_10496 160 176 192
  (interval_append badTest_10496 160 168 176
  badTest_10496_block_20
  badTest_10496_block_21)
  (interval_append badTest_10496 176 184 192
  badTest_10496_block_22
  badTest_10496_block_23)))
  (interval_append badTest_10496 192 224 256
  (interval_append badTest_10496 192 208 224
  (interval_append badTest_10496 192 200 208
  badTest_10496_block_24
  badTest_10496_block_25)
  (interval_append badTest_10496 208 216 224
  badTest_10496_block_26
  badTest_10496_block_27))
  (interval_append badTest_10496 224 240 256
  (interval_append badTest_10496 224 232 240
  badTest_10496_block_28
  badTest_10496_block_29)
  (interval_append badTest_10496 240 248 256
  badTest_10496_block_30
  badTest_10496_block_31)))))
theorem badTestInterval10496 : Interval badTest 10496 10752 := by
  intro i hlo hhi
  have h := badTest_10496_complete (i-10496) (Nat.zero_le _) (by omega)
  simpa only [badTest_10496, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad042 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad043 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad044 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad045 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad046 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad047 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad048 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad049 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad050 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad051 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
