module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheBad010 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_2560 (i : Nat) := badTest (i+2560)
theorem badTest_2560_block_0 : Interval badTest_2560 0 8 :=
  interval_of_check badTest_2560 0 8 (by decide +kernel)

theorem badTest_2560_block_1 : Interval badTest_2560 8 16 :=
  interval_of_check badTest_2560 8 8 (by decide +kernel)

theorem badTest_2560_block_2 : Interval badTest_2560 16 24 :=
  interval_of_check badTest_2560 16 8 (by decide +kernel)

theorem badTest_2560_block_3 : Interval badTest_2560 24 32 :=
  interval_of_check badTest_2560 24 8 (by decide +kernel)

theorem badTest_2560_block_4 : Interval badTest_2560 32 40 :=
  interval_of_check badTest_2560 32 8 (by decide +kernel)

theorem badTest_2560_block_5 : Interval badTest_2560 40 48 :=
  interval_of_check badTest_2560 40 8 (by decide +kernel)

theorem badTest_2560_block_6 : Interval badTest_2560 48 56 :=
  interval_of_check badTest_2560 48 8 (by decide +kernel)

theorem badTest_2560_block_7 : Interval badTest_2560 56 64 :=
  interval_of_check badTest_2560 56 8 (by decide +kernel)

theorem badTest_2560_block_8 : Interval badTest_2560 64 72 :=
  interval_of_check badTest_2560 64 8 (by decide +kernel)

theorem badTest_2560_block_9 : Interval badTest_2560 72 80 :=
  interval_of_check badTest_2560 72 8 (by decide +kernel)

theorem badTest_2560_block_10 : Interval badTest_2560 80 88 :=
  interval_of_check badTest_2560 80 8 (by decide +kernel)

theorem badTest_2560_block_11 : Interval badTest_2560 88 96 :=
  interval_of_check badTest_2560 88 8 (by decide +kernel)

theorem badTest_2560_block_12 : Interval badTest_2560 96 104 :=
  interval_of_check badTest_2560 96 8 (by decide +kernel)

theorem badTest_2560_block_13 : Interval badTest_2560 104 112 :=
  interval_of_check badTest_2560 104 8 (by decide +kernel)

theorem badTest_2560_block_14 : Interval badTest_2560 112 120 :=
  interval_of_check badTest_2560 112 8 (by decide +kernel)

theorem badTest_2560_block_15 : Interval badTest_2560 120 128 :=
  interval_of_check badTest_2560 120 8 (by decide +kernel)

theorem badTest_2560_block_16 : Interval badTest_2560 128 136 :=
  interval_of_check badTest_2560 128 8 (by decide +kernel)

theorem badTest_2560_block_17 : Interval badTest_2560 136 144 :=
  interval_of_check badTest_2560 136 8 (by decide +kernel)

theorem badTest_2560_block_18 : Interval badTest_2560 144 152 :=
  interval_of_check badTest_2560 144 8 (by decide +kernel)

theorem badTest_2560_block_19 : Interval badTest_2560 152 160 :=
  interval_of_check badTest_2560 152 8 (by decide +kernel)

theorem badTest_2560_block_20 : Interval badTest_2560 160 168 :=
  interval_of_check badTest_2560 160 8 (by decide +kernel)

theorem badTest_2560_block_21 : Interval badTest_2560 168 176 :=
  interval_of_check badTest_2560 168 8 (by decide +kernel)

theorem badTest_2560_block_22 : Interval badTest_2560 176 184 :=
  interval_of_check badTest_2560 176 8 (by decide +kernel)

theorem badTest_2560_block_23 : Interval badTest_2560 184 192 :=
  interval_of_check badTest_2560 184 8 (by decide +kernel)

theorem badTest_2560_block_24 : Interval badTest_2560 192 200 :=
  interval_of_check badTest_2560 192 8 (by decide +kernel)

theorem badTest_2560_block_25 : Interval badTest_2560 200 208 :=
  interval_of_check badTest_2560 200 8 (by decide +kernel)

theorem badTest_2560_block_26 : Interval badTest_2560 208 216 :=
  interval_of_check badTest_2560 208 8 (by decide +kernel)

theorem badTest_2560_block_27 : Interval badTest_2560 216 224 :=
  interval_of_check badTest_2560 216 8 (by decide +kernel)

theorem badTest_2560_block_28 : Interval badTest_2560 224 232 :=
  interval_of_check badTest_2560 224 8 (by decide +kernel)

theorem badTest_2560_block_29 : Interval badTest_2560 232 240 :=
  interval_of_check badTest_2560 232 8 (by decide +kernel)

theorem badTest_2560_block_30 : Interval badTest_2560 240 248 :=
  interval_of_check badTest_2560 240 8 (by decide +kernel)

theorem badTest_2560_block_31 : Interval badTest_2560 248 256 :=
  interval_of_check badTest_2560 248 8 (by decide +kernel)

theorem badTest_2560_complete : Interval badTest_2560 0 256 :=
  (interval_append badTest_2560 0 128 256
  (interval_append badTest_2560 0 64 128
  (interval_append badTest_2560 0 32 64
  (interval_append badTest_2560 0 16 32
  (interval_append badTest_2560 0 8 16
  badTest_2560_block_0
  badTest_2560_block_1)
  (interval_append badTest_2560 16 24 32
  badTest_2560_block_2
  badTest_2560_block_3))
  (interval_append badTest_2560 32 48 64
  (interval_append badTest_2560 32 40 48
  badTest_2560_block_4
  badTest_2560_block_5)
  (interval_append badTest_2560 48 56 64
  badTest_2560_block_6
  badTest_2560_block_7)))
  (interval_append badTest_2560 64 96 128
  (interval_append badTest_2560 64 80 96
  (interval_append badTest_2560 64 72 80
  badTest_2560_block_8
  badTest_2560_block_9)
  (interval_append badTest_2560 80 88 96
  badTest_2560_block_10
  badTest_2560_block_11))
  (interval_append badTest_2560 96 112 128
  (interval_append badTest_2560 96 104 112
  badTest_2560_block_12
  badTest_2560_block_13)
  (interval_append badTest_2560 112 120 128
  badTest_2560_block_14
  badTest_2560_block_15))))
  (interval_append badTest_2560 128 192 256
  (interval_append badTest_2560 128 160 192
  (interval_append badTest_2560 128 144 160
  (interval_append badTest_2560 128 136 144
  badTest_2560_block_16
  badTest_2560_block_17)
  (interval_append badTest_2560 144 152 160
  badTest_2560_block_18
  badTest_2560_block_19))
  (interval_append badTest_2560 160 176 192
  (interval_append badTest_2560 160 168 176
  badTest_2560_block_20
  badTest_2560_block_21)
  (interval_append badTest_2560 176 184 192
  badTest_2560_block_22
  badTest_2560_block_23)))
  (interval_append badTest_2560 192 224 256
  (interval_append badTest_2560 192 208 224
  (interval_append badTest_2560 192 200 208
  badTest_2560_block_24
  badTest_2560_block_25)
  (interval_append badTest_2560 208 216 224
  badTest_2560_block_26
  badTest_2560_block_27))
  (interval_append badTest_2560 224 240 256
  (interval_append badTest_2560 224 232 240
  badTest_2560_block_28
  badTest_2560_block_29)
  (interval_append badTest_2560 240 248 256
  badTest_2560_block_30
  badTest_2560_block_31)))))
theorem badTestInterval2560 : Interval badTest 2560 2816 := by
  intro i hlo hhi
  have h := badTest_2560_complete (i-2560) (Nat.zero_le _) (by omega)
  simpa only [badTest_2560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad011 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_2816 (i : Nat) := badTest (i+2816)
theorem badTest_2816_block_0 : Interval badTest_2816 0 8 :=
  interval_of_check badTest_2816 0 8 (by decide +kernel)

theorem badTest_2816_block_1 : Interval badTest_2816 8 16 :=
  interval_of_check badTest_2816 8 8 (by decide +kernel)

theorem badTest_2816_block_2 : Interval badTest_2816 16 24 :=
  interval_of_check badTest_2816 16 8 (by decide +kernel)

theorem badTest_2816_block_3 : Interval badTest_2816 24 32 :=
  interval_of_check badTest_2816 24 8 (by decide +kernel)

theorem badTest_2816_block_4 : Interval badTest_2816 32 40 :=
  interval_of_check badTest_2816 32 8 (by decide +kernel)

theorem badTest_2816_block_5 : Interval badTest_2816 40 48 :=
  interval_of_check badTest_2816 40 8 (by decide +kernel)

theorem badTest_2816_block_6 : Interval badTest_2816 48 56 :=
  interval_of_check badTest_2816 48 8 (by decide +kernel)

theorem badTest_2816_block_7 : Interval badTest_2816 56 64 :=
  interval_of_check badTest_2816 56 8 (by decide +kernel)

theorem badTest_2816_block_8 : Interval badTest_2816 64 72 :=
  interval_of_check badTest_2816 64 8 (by decide +kernel)

theorem badTest_2816_block_9 : Interval badTest_2816 72 80 :=
  interval_of_check badTest_2816 72 8 (by decide +kernel)

theorem badTest_2816_block_10 : Interval badTest_2816 80 88 :=
  interval_of_check badTest_2816 80 8 (by decide +kernel)

theorem badTest_2816_block_11 : Interval badTest_2816 88 96 :=
  interval_of_check badTest_2816 88 8 (by decide +kernel)

theorem badTest_2816_block_12 : Interval badTest_2816 96 104 :=
  interval_of_check badTest_2816 96 8 (by decide +kernel)

theorem badTest_2816_block_13 : Interval badTest_2816 104 112 :=
  interval_of_check badTest_2816 104 8 (by decide +kernel)

theorem badTest_2816_block_14 : Interval badTest_2816 112 120 :=
  interval_of_check badTest_2816 112 8 (by decide +kernel)

theorem badTest_2816_block_15 : Interval badTest_2816 120 128 :=
  interval_of_check badTest_2816 120 8 (by decide +kernel)

theorem badTest_2816_block_16 : Interval badTest_2816 128 136 :=
  interval_of_check badTest_2816 128 8 (by decide +kernel)

theorem badTest_2816_block_17 : Interval badTest_2816 136 144 :=
  interval_of_check badTest_2816 136 8 (by decide +kernel)

theorem badTest_2816_block_18 : Interval badTest_2816 144 152 :=
  interval_of_check badTest_2816 144 8 (by decide +kernel)

theorem badTest_2816_block_19 : Interval badTest_2816 152 160 :=
  interval_of_check badTest_2816 152 8 (by decide +kernel)

theorem badTest_2816_block_20 : Interval badTest_2816 160 168 :=
  interval_of_check badTest_2816 160 8 (by decide +kernel)

theorem badTest_2816_block_21 : Interval badTest_2816 168 176 :=
  interval_of_check badTest_2816 168 8 (by decide +kernel)

theorem badTest_2816_block_22 : Interval badTest_2816 176 184 :=
  interval_of_check badTest_2816 176 8 (by decide +kernel)

theorem badTest_2816_block_23 : Interval badTest_2816 184 192 :=
  interval_of_check badTest_2816 184 8 (by decide +kernel)

theorem badTest_2816_block_24 : Interval badTest_2816 192 200 :=
  interval_of_check badTest_2816 192 8 (by decide +kernel)

theorem badTest_2816_block_25 : Interval badTest_2816 200 208 :=
  interval_of_check badTest_2816 200 8 (by decide +kernel)

theorem badTest_2816_block_26 : Interval badTest_2816 208 216 :=
  interval_of_check badTest_2816 208 8 (by decide +kernel)

theorem badTest_2816_block_27 : Interval badTest_2816 216 224 :=
  interval_of_check badTest_2816 216 8 (by decide +kernel)

theorem badTest_2816_block_28 : Interval badTest_2816 224 232 :=
  interval_of_check badTest_2816 224 8 (by decide +kernel)

theorem badTest_2816_block_29 : Interval badTest_2816 232 240 :=
  interval_of_check badTest_2816 232 8 (by decide +kernel)

theorem badTest_2816_block_30 : Interval badTest_2816 240 248 :=
  interval_of_check badTest_2816 240 8 (by decide +kernel)

theorem badTest_2816_block_31 : Interval badTest_2816 248 256 :=
  interval_of_check badTest_2816 248 8 (by decide +kernel)

theorem badTest_2816_complete : Interval badTest_2816 0 256 :=
  (interval_append badTest_2816 0 128 256
  (interval_append badTest_2816 0 64 128
  (interval_append badTest_2816 0 32 64
  (interval_append badTest_2816 0 16 32
  (interval_append badTest_2816 0 8 16
  badTest_2816_block_0
  badTest_2816_block_1)
  (interval_append badTest_2816 16 24 32
  badTest_2816_block_2
  badTest_2816_block_3))
  (interval_append badTest_2816 32 48 64
  (interval_append badTest_2816 32 40 48
  badTest_2816_block_4
  badTest_2816_block_5)
  (interval_append badTest_2816 48 56 64
  badTest_2816_block_6
  badTest_2816_block_7)))
  (interval_append badTest_2816 64 96 128
  (interval_append badTest_2816 64 80 96
  (interval_append badTest_2816 64 72 80
  badTest_2816_block_8
  badTest_2816_block_9)
  (interval_append badTest_2816 80 88 96
  badTest_2816_block_10
  badTest_2816_block_11))
  (interval_append badTest_2816 96 112 128
  (interval_append badTest_2816 96 104 112
  badTest_2816_block_12
  badTest_2816_block_13)
  (interval_append badTest_2816 112 120 128
  badTest_2816_block_14
  badTest_2816_block_15))))
  (interval_append badTest_2816 128 192 256
  (interval_append badTest_2816 128 160 192
  (interval_append badTest_2816 128 144 160
  (interval_append badTest_2816 128 136 144
  badTest_2816_block_16
  badTest_2816_block_17)
  (interval_append badTest_2816 144 152 160
  badTest_2816_block_18
  badTest_2816_block_19))
  (interval_append badTest_2816 160 176 192
  (interval_append badTest_2816 160 168 176
  badTest_2816_block_20
  badTest_2816_block_21)
  (interval_append badTest_2816 176 184 192
  badTest_2816_block_22
  badTest_2816_block_23)))
  (interval_append badTest_2816 192 224 256
  (interval_append badTest_2816 192 208 224
  (interval_append badTest_2816 192 200 208
  badTest_2816_block_24
  badTest_2816_block_25)
  (interval_append badTest_2816 208 216 224
  badTest_2816_block_26
  badTest_2816_block_27))
  (interval_append badTest_2816 224 240 256
  (interval_append badTest_2816 224 232 240
  badTest_2816_block_28
  badTest_2816_block_29)
  (interval_append badTest_2816 240 248 256
  badTest_2816_block_30
  badTest_2816_block_31)))))
theorem badTestInterval2816 : Interval badTest 2816 3072 := by
  intro i hlo hhi
  have h := badTest_2816_complete (i-2816) (Nat.zero_le _) (by omega)
  simpa only [badTest_2816, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad012 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_3072 (i : Nat) := badTest (i+3072)
theorem badTest_3072_block_0 : Interval badTest_3072 0 8 :=
  interval_of_check badTest_3072 0 8 (by decide +kernel)

theorem badTest_3072_block_1 : Interval badTest_3072 8 16 :=
  interval_of_check badTest_3072 8 8 (by decide +kernel)

theorem badTest_3072_block_2 : Interval badTest_3072 16 24 :=
  interval_of_check badTest_3072 16 8 (by decide +kernel)

theorem badTest_3072_block_3 : Interval badTest_3072 24 32 :=
  interval_of_check badTest_3072 24 8 (by decide +kernel)

theorem badTest_3072_block_4 : Interval badTest_3072 32 40 :=
  interval_of_check badTest_3072 32 8 (by decide +kernel)

theorem badTest_3072_block_5 : Interval badTest_3072 40 48 :=
  interval_of_check badTest_3072 40 8 (by decide +kernel)

theorem badTest_3072_block_6 : Interval badTest_3072 48 56 :=
  interval_of_check badTest_3072 48 8 (by decide +kernel)

theorem badTest_3072_block_7 : Interval badTest_3072 56 64 :=
  interval_of_check badTest_3072 56 8 (by decide +kernel)

theorem badTest_3072_block_8 : Interval badTest_3072 64 72 :=
  interval_of_check badTest_3072 64 8 (by decide +kernel)

theorem badTest_3072_block_9 : Interval badTest_3072 72 80 :=
  interval_of_check badTest_3072 72 8 (by decide +kernel)

theorem badTest_3072_block_10 : Interval badTest_3072 80 88 :=
  interval_of_check badTest_3072 80 8 (by decide +kernel)

theorem badTest_3072_block_11 : Interval badTest_3072 88 96 :=
  interval_of_check badTest_3072 88 8 (by decide +kernel)

theorem badTest_3072_block_12 : Interval badTest_3072 96 104 :=
  interval_of_check badTest_3072 96 8 (by decide +kernel)

theorem badTest_3072_block_13 : Interval badTest_3072 104 112 :=
  interval_of_check badTest_3072 104 8 (by decide +kernel)

theorem badTest_3072_block_14 : Interval badTest_3072 112 120 :=
  interval_of_check badTest_3072 112 8 (by decide +kernel)

theorem badTest_3072_block_15 : Interval badTest_3072 120 128 :=
  interval_of_check badTest_3072 120 8 (by decide +kernel)

theorem badTest_3072_block_16 : Interval badTest_3072 128 136 :=
  interval_of_check badTest_3072 128 8 (by decide +kernel)

theorem badTest_3072_block_17 : Interval badTest_3072 136 144 :=
  interval_of_check badTest_3072 136 8 (by decide +kernel)

theorem badTest_3072_block_18 : Interval badTest_3072 144 152 :=
  interval_of_check badTest_3072 144 8 (by decide +kernel)

theorem badTest_3072_block_19 : Interval badTest_3072 152 160 :=
  interval_of_check badTest_3072 152 8 (by decide +kernel)

theorem badTest_3072_block_20 : Interval badTest_3072 160 168 :=
  interval_of_check badTest_3072 160 8 (by decide +kernel)

theorem badTest_3072_block_21 : Interval badTest_3072 168 176 :=
  interval_of_check badTest_3072 168 8 (by decide +kernel)

theorem badTest_3072_block_22 : Interval badTest_3072 176 184 :=
  interval_of_check badTest_3072 176 8 (by decide +kernel)

theorem badTest_3072_block_23 : Interval badTest_3072 184 192 :=
  interval_of_check badTest_3072 184 8 (by decide +kernel)

theorem badTest_3072_block_24 : Interval badTest_3072 192 200 :=
  interval_of_check badTest_3072 192 8 (by decide +kernel)

theorem badTest_3072_block_25 : Interval badTest_3072 200 208 :=
  interval_of_check badTest_3072 200 8 (by decide +kernel)

theorem badTest_3072_block_26 : Interval badTest_3072 208 216 :=
  interval_of_check badTest_3072 208 8 (by decide +kernel)

theorem badTest_3072_block_27 : Interval badTest_3072 216 224 :=
  interval_of_check badTest_3072 216 8 (by decide +kernel)

theorem badTest_3072_block_28 : Interval badTest_3072 224 232 :=
  interval_of_check badTest_3072 224 8 (by decide +kernel)

theorem badTest_3072_block_29 : Interval badTest_3072 232 240 :=
  interval_of_check badTest_3072 232 8 (by decide +kernel)

theorem badTest_3072_block_30 : Interval badTest_3072 240 248 :=
  interval_of_check badTest_3072 240 8 (by decide +kernel)

theorem badTest_3072_block_31 : Interval badTest_3072 248 256 :=
  interval_of_check badTest_3072 248 8 (by decide +kernel)

theorem badTest_3072_complete : Interval badTest_3072 0 256 :=
  (interval_append badTest_3072 0 128 256
  (interval_append badTest_3072 0 64 128
  (interval_append badTest_3072 0 32 64
  (interval_append badTest_3072 0 16 32
  (interval_append badTest_3072 0 8 16
  badTest_3072_block_0
  badTest_3072_block_1)
  (interval_append badTest_3072 16 24 32
  badTest_3072_block_2
  badTest_3072_block_3))
  (interval_append badTest_3072 32 48 64
  (interval_append badTest_3072 32 40 48
  badTest_3072_block_4
  badTest_3072_block_5)
  (interval_append badTest_3072 48 56 64
  badTest_3072_block_6
  badTest_3072_block_7)))
  (interval_append badTest_3072 64 96 128
  (interval_append badTest_3072 64 80 96
  (interval_append badTest_3072 64 72 80
  badTest_3072_block_8
  badTest_3072_block_9)
  (interval_append badTest_3072 80 88 96
  badTest_3072_block_10
  badTest_3072_block_11))
  (interval_append badTest_3072 96 112 128
  (interval_append badTest_3072 96 104 112
  badTest_3072_block_12
  badTest_3072_block_13)
  (interval_append badTest_3072 112 120 128
  badTest_3072_block_14
  badTest_3072_block_15))))
  (interval_append badTest_3072 128 192 256
  (interval_append badTest_3072 128 160 192
  (interval_append badTest_3072 128 144 160
  (interval_append badTest_3072 128 136 144
  badTest_3072_block_16
  badTest_3072_block_17)
  (interval_append badTest_3072 144 152 160
  badTest_3072_block_18
  badTest_3072_block_19))
  (interval_append badTest_3072 160 176 192
  (interval_append badTest_3072 160 168 176
  badTest_3072_block_20
  badTest_3072_block_21)
  (interval_append badTest_3072 176 184 192
  badTest_3072_block_22
  badTest_3072_block_23)))
  (interval_append badTest_3072 192 224 256
  (interval_append badTest_3072 192 208 224
  (interval_append badTest_3072 192 200 208
  badTest_3072_block_24
  badTest_3072_block_25)
  (interval_append badTest_3072 208 216 224
  badTest_3072_block_26
  badTest_3072_block_27))
  (interval_append badTest_3072 224 240 256
  (interval_append badTest_3072 224 232 240
  badTest_3072_block_28
  badTest_3072_block_29)
  (interval_append badTest_3072 240 248 256
  badTest_3072_block_30
  badTest_3072_block_31)))))
theorem badTestInterval3072 : Interval badTest 3072 3328 := by
  intro i hlo hhi
  have h := badTest_3072_complete (i-3072) (Nat.zero_le _) (by omega)
  simpa only [badTest_3072, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad013 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_3328 (i : Nat) := badTest (i+3328)
theorem badTest_3328_block_0 : Interval badTest_3328 0 8 :=
  interval_of_check badTest_3328 0 8 (by decide +kernel)

theorem badTest_3328_block_1 : Interval badTest_3328 8 16 :=
  interval_of_check badTest_3328 8 8 (by decide +kernel)

theorem badTest_3328_block_2 : Interval badTest_3328 16 24 :=
  interval_of_check badTest_3328 16 8 (by decide +kernel)

theorem badTest_3328_block_3 : Interval badTest_3328 24 32 :=
  interval_of_check badTest_3328 24 8 (by decide +kernel)

theorem badTest_3328_block_4 : Interval badTest_3328 32 40 :=
  interval_of_check badTest_3328 32 8 (by decide +kernel)

theorem badTest_3328_block_5 : Interval badTest_3328 40 48 :=
  interval_of_check badTest_3328 40 8 (by decide +kernel)

theorem badTest_3328_block_6 : Interval badTest_3328 48 56 :=
  interval_of_check badTest_3328 48 8 (by decide +kernel)

theorem badTest_3328_block_7 : Interval badTest_3328 56 64 :=
  interval_of_check badTest_3328 56 8 (by decide +kernel)

theorem badTest_3328_block_8 : Interval badTest_3328 64 72 :=
  interval_of_check badTest_3328 64 8 (by decide +kernel)

theorem badTest_3328_block_9 : Interval badTest_3328 72 80 :=
  interval_of_check badTest_3328 72 8 (by decide +kernel)

theorem badTest_3328_block_10 : Interval badTest_3328 80 88 :=
  interval_of_check badTest_3328 80 8 (by decide +kernel)

theorem badTest_3328_block_11 : Interval badTest_3328 88 96 :=
  interval_of_check badTest_3328 88 8 (by decide +kernel)

theorem badTest_3328_block_12 : Interval badTest_3328 96 104 :=
  interval_of_check badTest_3328 96 8 (by decide +kernel)

theorem badTest_3328_block_13 : Interval badTest_3328 104 112 :=
  interval_of_check badTest_3328 104 8 (by decide +kernel)

theorem badTest_3328_block_14 : Interval badTest_3328 112 120 :=
  interval_of_check badTest_3328 112 8 (by decide +kernel)

theorem badTest_3328_block_15 : Interval badTest_3328 120 128 :=
  interval_of_check badTest_3328 120 8 (by decide +kernel)

theorem badTest_3328_block_16 : Interval badTest_3328 128 136 :=
  interval_of_check badTest_3328 128 8 (by decide +kernel)

theorem badTest_3328_block_17 : Interval badTest_3328 136 144 :=
  interval_of_check badTest_3328 136 8 (by decide +kernel)

theorem badTest_3328_block_18 : Interval badTest_3328 144 152 :=
  interval_of_check badTest_3328 144 8 (by decide +kernel)

theorem badTest_3328_block_19 : Interval badTest_3328 152 160 :=
  interval_of_check badTest_3328 152 8 (by decide +kernel)

theorem badTest_3328_block_20 : Interval badTest_3328 160 168 :=
  interval_of_check badTest_3328 160 8 (by decide +kernel)

theorem badTest_3328_block_21 : Interval badTest_3328 168 176 :=
  interval_of_check badTest_3328 168 8 (by decide +kernel)

theorem badTest_3328_block_22 : Interval badTest_3328 176 184 :=
  interval_of_check badTest_3328 176 8 (by decide +kernel)

theorem badTest_3328_block_23 : Interval badTest_3328 184 192 :=
  interval_of_check badTest_3328 184 8 (by decide +kernel)

theorem badTest_3328_block_24 : Interval badTest_3328 192 200 :=
  interval_of_check badTest_3328 192 8 (by decide +kernel)

theorem badTest_3328_block_25 : Interval badTest_3328 200 208 :=
  interval_of_check badTest_3328 200 8 (by decide +kernel)

theorem badTest_3328_block_26 : Interval badTest_3328 208 216 :=
  interval_of_check badTest_3328 208 8 (by decide +kernel)

theorem badTest_3328_block_27 : Interval badTest_3328 216 224 :=
  interval_of_check badTest_3328 216 8 (by decide +kernel)

theorem badTest_3328_block_28 : Interval badTest_3328 224 232 :=
  interval_of_check badTest_3328 224 8 (by decide +kernel)

theorem badTest_3328_block_29 : Interval badTest_3328 232 240 :=
  interval_of_check badTest_3328 232 8 (by decide +kernel)

theorem badTest_3328_block_30 : Interval badTest_3328 240 248 :=
  interval_of_check badTest_3328 240 8 (by decide +kernel)

theorem badTest_3328_block_31 : Interval badTest_3328 248 256 :=
  interval_of_check badTest_3328 248 8 (by decide +kernel)

theorem badTest_3328_complete : Interval badTest_3328 0 256 :=
  (interval_append badTest_3328 0 128 256
  (interval_append badTest_3328 0 64 128
  (interval_append badTest_3328 0 32 64
  (interval_append badTest_3328 0 16 32
  (interval_append badTest_3328 0 8 16
  badTest_3328_block_0
  badTest_3328_block_1)
  (interval_append badTest_3328 16 24 32
  badTest_3328_block_2
  badTest_3328_block_3))
  (interval_append badTest_3328 32 48 64
  (interval_append badTest_3328 32 40 48
  badTest_3328_block_4
  badTest_3328_block_5)
  (interval_append badTest_3328 48 56 64
  badTest_3328_block_6
  badTest_3328_block_7)))
  (interval_append badTest_3328 64 96 128
  (interval_append badTest_3328 64 80 96
  (interval_append badTest_3328 64 72 80
  badTest_3328_block_8
  badTest_3328_block_9)
  (interval_append badTest_3328 80 88 96
  badTest_3328_block_10
  badTest_3328_block_11))
  (interval_append badTest_3328 96 112 128
  (interval_append badTest_3328 96 104 112
  badTest_3328_block_12
  badTest_3328_block_13)
  (interval_append badTest_3328 112 120 128
  badTest_3328_block_14
  badTest_3328_block_15))))
  (interval_append badTest_3328 128 192 256
  (interval_append badTest_3328 128 160 192
  (interval_append badTest_3328 128 144 160
  (interval_append badTest_3328 128 136 144
  badTest_3328_block_16
  badTest_3328_block_17)
  (interval_append badTest_3328 144 152 160
  badTest_3328_block_18
  badTest_3328_block_19))
  (interval_append badTest_3328 160 176 192
  (interval_append badTest_3328 160 168 176
  badTest_3328_block_20
  badTest_3328_block_21)
  (interval_append badTest_3328 176 184 192
  badTest_3328_block_22
  badTest_3328_block_23)))
  (interval_append badTest_3328 192 224 256
  (interval_append badTest_3328 192 208 224
  (interval_append badTest_3328 192 200 208
  badTest_3328_block_24
  badTest_3328_block_25)
  (interval_append badTest_3328 208 216 224
  badTest_3328_block_26
  badTest_3328_block_27))
  (interval_append badTest_3328 224 240 256
  (interval_append badTest_3328 224 232 240
  badTest_3328_block_28
  badTest_3328_block_29)
  (interval_append badTest_3328 240 248 256
  badTest_3328_block_30
  badTest_3328_block_31)))))
theorem badTestInterval3328 : Interval badTest 3328 3584 := by
  intro i hlo hhi
  have h := badTest_3328_complete (i-3328) (Nat.zero_le _) (by omega)
  simpa only [badTest_3328, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad014 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_3584 (i : Nat) := badTest (i+3584)
theorem badTest_3584_block_0 : Interval badTest_3584 0 8 :=
  interval_of_check badTest_3584 0 8 (by decide +kernel)

theorem badTest_3584_block_1 : Interval badTest_3584 8 16 :=
  interval_of_check badTest_3584 8 8 (by decide +kernel)

theorem badTest_3584_block_2 : Interval badTest_3584 16 24 :=
  interval_of_check badTest_3584 16 8 (by decide +kernel)

theorem badTest_3584_block_3 : Interval badTest_3584 24 32 :=
  interval_of_check badTest_3584 24 8 (by decide +kernel)

theorem badTest_3584_block_4 : Interval badTest_3584 32 40 :=
  interval_of_check badTest_3584 32 8 (by decide +kernel)

theorem badTest_3584_block_5 : Interval badTest_3584 40 48 :=
  interval_of_check badTest_3584 40 8 (by decide +kernel)

theorem badTest_3584_block_6 : Interval badTest_3584 48 56 :=
  interval_of_check badTest_3584 48 8 (by decide +kernel)

theorem badTest_3584_block_7 : Interval badTest_3584 56 64 :=
  interval_of_check badTest_3584 56 8 (by decide +kernel)

theorem badTest_3584_block_8 : Interval badTest_3584 64 72 :=
  interval_of_check badTest_3584 64 8 (by decide +kernel)

theorem badTest_3584_block_9 : Interval badTest_3584 72 80 :=
  interval_of_check badTest_3584 72 8 (by decide +kernel)

theorem badTest_3584_block_10 : Interval badTest_3584 80 88 :=
  interval_of_check badTest_3584 80 8 (by decide +kernel)

theorem badTest_3584_block_11 : Interval badTest_3584 88 96 :=
  interval_of_check badTest_3584 88 8 (by decide +kernel)

theorem badTest_3584_block_12 : Interval badTest_3584 96 104 :=
  interval_of_check badTest_3584 96 8 (by decide +kernel)

theorem badTest_3584_block_13 : Interval badTest_3584 104 112 :=
  interval_of_check badTest_3584 104 8 (by decide +kernel)

theorem badTest_3584_block_14 : Interval badTest_3584 112 120 :=
  interval_of_check badTest_3584 112 8 (by decide +kernel)

theorem badTest_3584_block_15 : Interval badTest_3584 120 128 :=
  interval_of_check badTest_3584 120 8 (by decide +kernel)

theorem badTest_3584_block_16 : Interval badTest_3584 128 136 :=
  interval_of_check badTest_3584 128 8 (by decide +kernel)

theorem badTest_3584_block_17 : Interval badTest_3584 136 144 :=
  interval_of_check badTest_3584 136 8 (by decide +kernel)

theorem badTest_3584_block_18 : Interval badTest_3584 144 152 :=
  interval_of_check badTest_3584 144 8 (by decide +kernel)

theorem badTest_3584_block_19 : Interval badTest_3584 152 160 :=
  interval_of_check badTest_3584 152 8 (by decide +kernel)

theorem badTest_3584_block_20 : Interval badTest_3584 160 168 :=
  interval_of_check badTest_3584 160 8 (by decide +kernel)

theorem badTest_3584_block_21 : Interval badTest_3584 168 176 :=
  interval_of_check badTest_3584 168 8 (by decide +kernel)

theorem badTest_3584_block_22 : Interval badTest_3584 176 184 :=
  interval_of_check badTest_3584 176 8 (by decide +kernel)

theorem badTest_3584_block_23 : Interval badTest_3584 184 192 :=
  interval_of_check badTest_3584 184 8 (by decide +kernel)

theorem badTest_3584_block_24 : Interval badTest_3584 192 200 :=
  interval_of_check badTest_3584 192 8 (by decide +kernel)

theorem badTest_3584_block_25 : Interval badTest_3584 200 208 :=
  interval_of_check badTest_3584 200 8 (by decide +kernel)

theorem badTest_3584_block_26 : Interval badTest_3584 208 216 :=
  interval_of_check badTest_3584 208 8 (by decide +kernel)

theorem badTest_3584_block_27 : Interval badTest_3584 216 224 :=
  interval_of_check badTest_3584 216 8 (by decide +kernel)

theorem badTest_3584_block_28 : Interval badTest_3584 224 232 :=
  interval_of_check badTest_3584 224 8 (by decide +kernel)

theorem badTest_3584_block_29 : Interval badTest_3584 232 240 :=
  interval_of_check badTest_3584 232 8 (by decide +kernel)

theorem badTest_3584_block_30 : Interval badTest_3584 240 248 :=
  interval_of_check badTest_3584 240 8 (by decide +kernel)

theorem badTest_3584_block_31 : Interval badTest_3584 248 256 :=
  interval_of_check badTest_3584 248 8 (by decide +kernel)

theorem badTest_3584_complete : Interval badTest_3584 0 256 :=
  (interval_append badTest_3584 0 128 256
  (interval_append badTest_3584 0 64 128
  (interval_append badTest_3584 0 32 64
  (interval_append badTest_3584 0 16 32
  (interval_append badTest_3584 0 8 16
  badTest_3584_block_0
  badTest_3584_block_1)
  (interval_append badTest_3584 16 24 32
  badTest_3584_block_2
  badTest_3584_block_3))
  (interval_append badTest_3584 32 48 64
  (interval_append badTest_3584 32 40 48
  badTest_3584_block_4
  badTest_3584_block_5)
  (interval_append badTest_3584 48 56 64
  badTest_3584_block_6
  badTest_3584_block_7)))
  (interval_append badTest_3584 64 96 128
  (interval_append badTest_3584 64 80 96
  (interval_append badTest_3584 64 72 80
  badTest_3584_block_8
  badTest_3584_block_9)
  (interval_append badTest_3584 80 88 96
  badTest_3584_block_10
  badTest_3584_block_11))
  (interval_append badTest_3584 96 112 128
  (interval_append badTest_3584 96 104 112
  badTest_3584_block_12
  badTest_3584_block_13)
  (interval_append badTest_3584 112 120 128
  badTest_3584_block_14
  badTest_3584_block_15))))
  (interval_append badTest_3584 128 192 256
  (interval_append badTest_3584 128 160 192
  (interval_append badTest_3584 128 144 160
  (interval_append badTest_3584 128 136 144
  badTest_3584_block_16
  badTest_3584_block_17)
  (interval_append badTest_3584 144 152 160
  badTest_3584_block_18
  badTest_3584_block_19))
  (interval_append badTest_3584 160 176 192
  (interval_append badTest_3584 160 168 176
  badTest_3584_block_20
  badTest_3584_block_21)
  (interval_append badTest_3584 176 184 192
  badTest_3584_block_22
  badTest_3584_block_23)))
  (interval_append badTest_3584 192 224 256
  (interval_append badTest_3584 192 208 224
  (interval_append badTest_3584 192 200 208
  badTest_3584_block_24
  badTest_3584_block_25)
  (interval_append badTest_3584 208 216 224
  badTest_3584_block_26
  badTest_3584_block_27))
  (interval_append badTest_3584 224 240 256
  (interval_append badTest_3584 224 232 240
  badTest_3584_block_28
  badTest_3584_block_29)
  (interval_append badTest_3584 240 248 256
  badTest_3584_block_30
  badTest_3584_block_31)))))
theorem badTestInterval3584 : Interval badTest 3584 3840 := by
  intro i hlo hhi
  have h := badTest_3584_complete (i-3584) (Nat.zero_le _) (by omega)
  simpa only [badTest_3584, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad015 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_3840 (i : Nat) := badTest (i+3840)
theorem badTest_3840_block_0 : Interval badTest_3840 0 8 :=
  interval_of_check badTest_3840 0 8 (by decide +kernel)

theorem badTest_3840_block_1 : Interval badTest_3840 8 16 :=
  interval_of_check badTest_3840 8 8 (by decide +kernel)

theorem badTest_3840_block_2 : Interval badTest_3840 16 24 :=
  interval_of_check badTest_3840 16 8 (by decide +kernel)

theorem badTest_3840_block_3 : Interval badTest_3840 24 32 :=
  interval_of_check badTest_3840 24 8 (by decide +kernel)

theorem badTest_3840_block_4 : Interval badTest_3840 32 40 :=
  interval_of_check badTest_3840 32 8 (by decide +kernel)

theorem badTest_3840_block_5 : Interval badTest_3840 40 48 :=
  interval_of_check badTest_3840 40 8 (by decide +kernel)

theorem badTest_3840_block_6 : Interval badTest_3840 48 56 :=
  interval_of_check badTest_3840 48 8 (by decide +kernel)

theorem badTest_3840_block_7 : Interval badTest_3840 56 64 :=
  interval_of_check badTest_3840 56 8 (by decide +kernel)

theorem badTest_3840_block_8 : Interval badTest_3840 64 72 :=
  interval_of_check badTest_3840 64 8 (by decide +kernel)

theorem badTest_3840_block_9 : Interval badTest_3840 72 80 :=
  interval_of_check badTest_3840 72 8 (by decide +kernel)

theorem badTest_3840_block_10 : Interval badTest_3840 80 88 :=
  interval_of_check badTest_3840 80 8 (by decide +kernel)

theorem badTest_3840_block_11 : Interval badTest_3840 88 96 :=
  interval_of_check badTest_3840 88 8 (by decide +kernel)

theorem badTest_3840_block_12 : Interval badTest_3840 96 104 :=
  interval_of_check badTest_3840 96 8 (by decide +kernel)

theorem badTest_3840_block_13 : Interval badTest_3840 104 112 :=
  interval_of_check badTest_3840 104 8 (by decide +kernel)

theorem badTest_3840_block_14 : Interval badTest_3840 112 120 :=
  interval_of_check badTest_3840 112 8 (by decide +kernel)

theorem badTest_3840_block_15 : Interval badTest_3840 120 128 :=
  interval_of_check badTest_3840 120 8 (by decide +kernel)

theorem badTest_3840_block_16 : Interval badTest_3840 128 136 :=
  interval_of_check badTest_3840 128 8 (by decide +kernel)

theorem badTest_3840_block_17 : Interval badTest_3840 136 144 :=
  interval_of_check badTest_3840 136 8 (by decide +kernel)

theorem badTest_3840_block_18 : Interval badTest_3840 144 152 :=
  interval_of_check badTest_3840 144 8 (by decide +kernel)

theorem badTest_3840_block_19 : Interval badTest_3840 152 160 :=
  interval_of_check badTest_3840 152 8 (by decide +kernel)

theorem badTest_3840_block_20 : Interval badTest_3840 160 168 :=
  interval_of_check badTest_3840 160 8 (by decide +kernel)

theorem badTest_3840_block_21 : Interval badTest_3840 168 176 :=
  interval_of_check badTest_3840 168 8 (by decide +kernel)

theorem badTest_3840_block_22 : Interval badTest_3840 176 184 :=
  interval_of_check badTest_3840 176 8 (by decide +kernel)

theorem badTest_3840_block_23 : Interval badTest_3840 184 192 :=
  interval_of_check badTest_3840 184 8 (by decide +kernel)

theorem badTest_3840_block_24 : Interval badTest_3840 192 200 :=
  interval_of_check badTest_3840 192 8 (by decide +kernel)

theorem badTest_3840_block_25 : Interval badTest_3840 200 208 :=
  interval_of_check badTest_3840 200 8 (by decide +kernel)

theorem badTest_3840_block_26 : Interval badTest_3840 208 216 :=
  interval_of_check badTest_3840 208 8 (by decide +kernel)

theorem badTest_3840_block_27 : Interval badTest_3840 216 224 :=
  interval_of_check badTest_3840 216 8 (by decide +kernel)

theorem badTest_3840_block_28 : Interval badTest_3840 224 232 :=
  interval_of_check badTest_3840 224 8 (by decide +kernel)

theorem badTest_3840_block_29 : Interval badTest_3840 232 240 :=
  interval_of_check badTest_3840 232 8 (by decide +kernel)

theorem badTest_3840_block_30 : Interval badTest_3840 240 248 :=
  interval_of_check badTest_3840 240 8 (by decide +kernel)

theorem badTest_3840_block_31 : Interval badTest_3840 248 256 :=
  interval_of_check badTest_3840 248 8 (by decide +kernel)

theorem badTest_3840_complete : Interval badTest_3840 0 256 :=
  (interval_append badTest_3840 0 128 256
  (interval_append badTest_3840 0 64 128
  (interval_append badTest_3840 0 32 64
  (interval_append badTest_3840 0 16 32
  (interval_append badTest_3840 0 8 16
  badTest_3840_block_0
  badTest_3840_block_1)
  (interval_append badTest_3840 16 24 32
  badTest_3840_block_2
  badTest_3840_block_3))
  (interval_append badTest_3840 32 48 64
  (interval_append badTest_3840 32 40 48
  badTest_3840_block_4
  badTest_3840_block_5)
  (interval_append badTest_3840 48 56 64
  badTest_3840_block_6
  badTest_3840_block_7)))
  (interval_append badTest_3840 64 96 128
  (interval_append badTest_3840 64 80 96
  (interval_append badTest_3840 64 72 80
  badTest_3840_block_8
  badTest_3840_block_9)
  (interval_append badTest_3840 80 88 96
  badTest_3840_block_10
  badTest_3840_block_11))
  (interval_append badTest_3840 96 112 128
  (interval_append badTest_3840 96 104 112
  badTest_3840_block_12
  badTest_3840_block_13)
  (interval_append badTest_3840 112 120 128
  badTest_3840_block_14
  badTest_3840_block_15))))
  (interval_append badTest_3840 128 192 256
  (interval_append badTest_3840 128 160 192
  (interval_append badTest_3840 128 144 160
  (interval_append badTest_3840 128 136 144
  badTest_3840_block_16
  badTest_3840_block_17)
  (interval_append badTest_3840 144 152 160
  badTest_3840_block_18
  badTest_3840_block_19))
  (interval_append badTest_3840 160 176 192
  (interval_append badTest_3840 160 168 176
  badTest_3840_block_20
  badTest_3840_block_21)
  (interval_append badTest_3840 176 184 192
  badTest_3840_block_22
  badTest_3840_block_23)))
  (interval_append badTest_3840 192 224 256
  (interval_append badTest_3840 192 208 224
  (interval_append badTest_3840 192 200 208
  badTest_3840_block_24
  badTest_3840_block_25)
  (interval_append badTest_3840 208 216 224
  badTest_3840_block_26
  badTest_3840_block_27))
  (interval_append badTest_3840 224 240 256
  (interval_append badTest_3840 224 232 240
  badTest_3840_block_28
  badTest_3840_block_29)
  (interval_append badTest_3840 240 248 256
  badTest_3840_block_30
  badTest_3840_block_31)))))
theorem badTestInterval3840 : Interval badTest 3840 4096 := by
  intro i hlo hhi
  have h := badTest_3840_complete (i-3840) (Nat.zero_le _) (by omega)
  simpa only [badTest_3840, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad016 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_4096 (i : Nat) := badTest (i+4096)
theorem badTest_4096_block_0 : Interval badTest_4096 0 8 :=
  interval_of_check badTest_4096 0 8 (by decide +kernel)

theorem badTest_4096_block_1 : Interval badTest_4096 8 16 :=
  interval_of_check badTest_4096 8 8 (by decide +kernel)

theorem badTest_4096_block_2 : Interval badTest_4096 16 24 :=
  interval_of_check badTest_4096 16 8 (by decide +kernel)

theorem badTest_4096_block_3 : Interval badTest_4096 24 32 :=
  interval_of_check badTest_4096 24 8 (by decide +kernel)

theorem badTest_4096_block_4 : Interval badTest_4096 32 40 :=
  interval_of_check badTest_4096 32 8 (by decide +kernel)

theorem badTest_4096_block_5 : Interval badTest_4096 40 48 :=
  interval_of_check badTest_4096 40 8 (by decide +kernel)

theorem badTest_4096_block_6 : Interval badTest_4096 48 56 :=
  interval_of_check badTest_4096 48 8 (by decide +kernel)

theorem badTest_4096_block_7 : Interval badTest_4096 56 64 :=
  interval_of_check badTest_4096 56 8 (by decide +kernel)

theorem badTest_4096_block_8 : Interval badTest_4096 64 72 :=
  interval_of_check badTest_4096 64 8 (by decide +kernel)

theorem badTest_4096_block_9 : Interval badTest_4096 72 80 :=
  interval_of_check badTest_4096 72 8 (by decide +kernel)

theorem badTest_4096_block_10 : Interval badTest_4096 80 88 :=
  interval_of_check badTest_4096 80 8 (by decide +kernel)

theorem badTest_4096_block_11 : Interval badTest_4096 88 96 :=
  interval_of_check badTest_4096 88 8 (by decide +kernel)

theorem badTest_4096_block_12 : Interval badTest_4096 96 104 :=
  interval_of_check badTest_4096 96 8 (by decide +kernel)

theorem badTest_4096_block_13 : Interval badTest_4096 104 112 :=
  interval_of_check badTest_4096 104 8 (by decide +kernel)

theorem badTest_4096_block_14 : Interval badTest_4096 112 120 :=
  interval_of_check badTest_4096 112 8 (by decide +kernel)

theorem badTest_4096_block_15 : Interval badTest_4096 120 128 :=
  interval_of_check badTest_4096 120 8 (by decide +kernel)

theorem badTest_4096_block_16 : Interval badTest_4096 128 136 :=
  interval_of_check badTest_4096 128 8 (by decide +kernel)

theorem badTest_4096_block_17 : Interval badTest_4096 136 144 :=
  interval_of_check badTest_4096 136 8 (by decide +kernel)

theorem badTest_4096_block_18 : Interval badTest_4096 144 152 :=
  interval_of_check badTest_4096 144 8 (by decide +kernel)

theorem badTest_4096_block_19 : Interval badTest_4096 152 160 :=
  interval_of_check badTest_4096 152 8 (by decide +kernel)

theorem badTest_4096_block_20 : Interval badTest_4096 160 168 :=
  interval_of_check badTest_4096 160 8 (by decide +kernel)

theorem badTest_4096_block_21 : Interval badTest_4096 168 176 :=
  interval_of_check badTest_4096 168 8 (by decide +kernel)

theorem badTest_4096_block_22 : Interval badTest_4096 176 184 :=
  interval_of_check badTest_4096 176 8 (by decide +kernel)

theorem badTest_4096_block_23 : Interval badTest_4096 184 192 :=
  interval_of_check badTest_4096 184 8 (by decide +kernel)

theorem badTest_4096_block_24 : Interval badTest_4096 192 200 :=
  interval_of_check badTest_4096 192 8 (by decide +kernel)

theorem badTest_4096_block_25 : Interval badTest_4096 200 208 :=
  interval_of_check badTest_4096 200 8 (by decide +kernel)

theorem badTest_4096_block_26 : Interval badTest_4096 208 216 :=
  interval_of_check badTest_4096 208 8 (by decide +kernel)

theorem badTest_4096_block_27 : Interval badTest_4096 216 224 :=
  interval_of_check badTest_4096 216 8 (by decide +kernel)

theorem badTest_4096_block_28 : Interval badTest_4096 224 232 :=
  interval_of_check badTest_4096 224 8 (by decide +kernel)

theorem badTest_4096_block_29 : Interval badTest_4096 232 240 :=
  interval_of_check badTest_4096 232 8 (by decide +kernel)

theorem badTest_4096_block_30 : Interval badTest_4096 240 248 :=
  interval_of_check badTest_4096 240 8 (by decide +kernel)

theorem badTest_4096_block_31 : Interval badTest_4096 248 256 :=
  interval_of_check badTest_4096 248 8 (by decide +kernel)

theorem badTest_4096_complete : Interval badTest_4096 0 256 :=
  (interval_append badTest_4096 0 128 256
  (interval_append badTest_4096 0 64 128
  (interval_append badTest_4096 0 32 64
  (interval_append badTest_4096 0 16 32
  (interval_append badTest_4096 0 8 16
  badTest_4096_block_0
  badTest_4096_block_1)
  (interval_append badTest_4096 16 24 32
  badTest_4096_block_2
  badTest_4096_block_3))
  (interval_append badTest_4096 32 48 64
  (interval_append badTest_4096 32 40 48
  badTest_4096_block_4
  badTest_4096_block_5)
  (interval_append badTest_4096 48 56 64
  badTest_4096_block_6
  badTest_4096_block_7)))
  (interval_append badTest_4096 64 96 128
  (interval_append badTest_4096 64 80 96
  (interval_append badTest_4096 64 72 80
  badTest_4096_block_8
  badTest_4096_block_9)
  (interval_append badTest_4096 80 88 96
  badTest_4096_block_10
  badTest_4096_block_11))
  (interval_append badTest_4096 96 112 128
  (interval_append badTest_4096 96 104 112
  badTest_4096_block_12
  badTest_4096_block_13)
  (interval_append badTest_4096 112 120 128
  badTest_4096_block_14
  badTest_4096_block_15))))
  (interval_append badTest_4096 128 192 256
  (interval_append badTest_4096 128 160 192
  (interval_append badTest_4096 128 144 160
  (interval_append badTest_4096 128 136 144
  badTest_4096_block_16
  badTest_4096_block_17)
  (interval_append badTest_4096 144 152 160
  badTest_4096_block_18
  badTest_4096_block_19))
  (interval_append badTest_4096 160 176 192
  (interval_append badTest_4096 160 168 176
  badTest_4096_block_20
  badTest_4096_block_21)
  (interval_append badTest_4096 176 184 192
  badTest_4096_block_22
  badTest_4096_block_23)))
  (interval_append badTest_4096 192 224 256
  (interval_append badTest_4096 192 208 224
  (interval_append badTest_4096 192 200 208
  badTest_4096_block_24
  badTest_4096_block_25)
  (interval_append badTest_4096 208 216 224
  badTest_4096_block_26
  badTest_4096_block_27))
  (interval_append badTest_4096 224 240 256
  (interval_append badTest_4096 224 232 240
  badTest_4096_block_28
  badTest_4096_block_29)
  (interval_append badTest_4096 240 248 256
  badTest_4096_block_30
  badTest_4096_block_31)))))
theorem badTestInterval4096 : Interval badTest 4096 4352 := by
  intro i hlo hhi
  have h := badTest_4096_complete (i-4096) (Nat.zero_le _) (by omega)
  simpa only [badTest_4096, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad017 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_4352 (i : Nat) := badTest (i+4352)
theorem badTest_4352_block_0 : Interval badTest_4352 0 8 :=
  interval_of_check badTest_4352 0 8 (by decide +kernel)

theorem badTest_4352_block_1 : Interval badTest_4352 8 16 :=
  interval_of_check badTest_4352 8 8 (by decide +kernel)

theorem badTest_4352_block_2 : Interval badTest_4352 16 24 :=
  interval_of_check badTest_4352 16 8 (by decide +kernel)

theorem badTest_4352_block_3 : Interval badTest_4352 24 32 :=
  interval_of_check badTest_4352 24 8 (by decide +kernel)

theorem badTest_4352_block_4 : Interval badTest_4352 32 40 :=
  interval_of_check badTest_4352 32 8 (by decide +kernel)

theorem badTest_4352_block_5 : Interval badTest_4352 40 48 :=
  interval_of_check badTest_4352 40 8 (by decide +kernel)

theorem badTest_4352_block_6 : Interval badTest_4352 48 56 :=
  interval_of_check badTest_4352 48 8 (by decide +kernel)

theorem badTest_4352_block_7 : Interval badTest_4352 56 64 :=
  interval_of_check badTest_4352 56 8 (by decide +kernel)

theorem badTest_4352_block_8 : Interval badTest_4352 64 72 :=
  interval_of_check badTest_4352 64 8 (by decide +kernel)

theorem badTest_4352_block_9 : Interval badTest_4352 72 80 :=
  interval_of_check badTest_4352 72 8 (by decide +kernel)

theorem badTest_4352_block_10 : Interval badTest_4352 80 88 :=
  interval_of_check badTest_4352 80 8 (by decide +kernel)

theorem badTest_4352_block_11 : Interval badTest_4352 88 96 :=
  interval_of_check badTest_4352 88 8 (by decide +kernel)

theorem badTest_4352_block_12 : Interval badTest_4352 96 104 :=
  interval_of_check badTest_4352 96 8 (by decide +kernel)

theorem badTest_4352_block_13 : Interval badTest_4352 104 112 :=
  interval_of_check badTest_4352 104 8 (by decide +kernel)

theorem badTest_4352_block_14 : Interval badTest_4352 112 120 :=
  interval_of_check badTest_4352 112 8 (by decide +kernel)

theorem badTest_4352_block_15 : Interval badTest_4352 120 128 :=
  interval_of_check badTest_4352 120 8 (by decide +kernel)

theorem badTest_4352_block_16 : Interval badTest_4352 128 136 :=
  interval_of_check badTest_4352 128 8 (by decide +kernel)

theorem badTest_4352_block_17 : Interval badTest_4352 136 144 :=
  interval_of_check badTest_4352 136 8 (by decide +kernel)

theorem badTest_4352_block_18 : Interval badTest_4352 144 152 :=
  interval_of_check badTest_4352 144 8 (by decide +kernel)

theorem badTest_4352_block_19 : Interval badTest_4352 152 160 :=
  interval_of_check badTest_4352 152 8 (by decide +kernel)

theorem badTest_4352_block_20 : Interval badTest_4352 160 168 :=
  interval_of_check badTest_4352 160 8 (by decide +kernel)

theorem badTest_4352_block_21 : Interval badTest_4352 168 176 :=
  interval_of_check badTest_4352 168 8 (by decide +kernel)

theorem badTest_4352_block_22 : Interval badTest_4352 176 184 :=
  interval_of_check badTest_4352 176 8 (by decide +kernel)

theorem badTest_4352_block_23 : Interval badTest_4352 184 192 :=
  interval_of_check badTest_4352 184 8 (by decide +kernel)

theorem badTest_4352_block_24 : Interval badTest_4352 192 200 :=
  interval_of_check badTest_4352 192 8 (by decide +kernel)

theorem badTest_4352_block_25 : Interval badTest_4352 200 208 :=
  interval_of_check badTest_4352 200 8 (by decide +kernel)

theorem badTest_4352_block_26 : Interval badTest_4352 208 216 :=
  interval_of_check badTest_4352 208 8 (by decide +kernel)

theorem badTest_4352_block_27 : Interval badTest_4352 216 224 :=
  interval_of_check badTest_4352 216 8 (by decide +kernel)

theorem badTest_4352_block_28 : Interval badTest_4352 224 232 :=
  interval_of_check badTest_4352 224 8 (by decide +kernel)

theorem badTest_4352_block_29 : Interval badTest_4352 232 240 :=
  interval_of_check badTest_4352 232 8 (by decide +kernel)

theorem badTest_4352_block_30 : Interval badTest_4352 240 248 :=
  interval_of_check badTest_4352 240 8 (by decide +kernel)

theorem badTest_4352_block_31 : Interval badTest_4352 248 256 :=
  interval_of_check badTest_4352 248 8 (by decide +kernel)

theorem badTest_4352_complete : Interval badTest_4352 0 256 :=
  (interval_append badTest_4352 0 128 256
  (interval_append badTest_4352 0 64 128
  (interval_append badTest_4352 0 32 64
  (interval_append badTest_4352 0 16 32
  (interval_append badTest_4352 0 8 16
  badTest_4352_block_0
  badTest_4352_block_1)
  (interval_append badTest_4352 16 24 32
  badTest_4352_block_2
  badTest_4352_block_3))
  (interval_append badTest_4352 32 48 64
  (interval_append badTest_4352 32 40 48
  badTest_4352_block_4
  badTest_4352_block_5)
  (interval_append badTest_4352 48 56 64
  badTest_4352_block_6
  badTest_4352_block_7)))
  (interval_append badTest_4352 64 96 128
  (interval_append badTest_4352 64 80 96
  (interval_append badTest_4352 64 72 80
  badTest_4352_block_8
  badTest_4352_block_9)
  (interval_append badTest_4352 80 88 96
  badTest_4352_block_10
  badTest_4352_block_11))
  (interval_append badTest_4352 96 112 128
  (interval_append badTest_4352 96 104 112
  badTest_4352_block_12
  badTest_4352_block_13)
  (interval_append badTest_4352 112 120 128
  badTest_4352_block_14
  badTest_4352_block_15))))
  (interval_append badTest_4352 128 192 256
  (interval_append badTest_4352 128 160 192
  (interval_append badTest_4352 128 144 160
  (interval_append badTest_4352 128 136 144
  badTest_4352_block_16
  badTest_4352_block_17)
  (interval_append badTest_4352 144 152 160
  badTest_4352_block_18
  badTest_4352_block_19))
  (interval_append badTest_4352 160 176 192
  (interval_append badTest_4352 160 168 176
  badTest_4352_block_20
  badTest_4352_block_21)
  (interval_append badTest_4352 176 184 192
  badTest_4352_block_22
  badTest_4352_block_23)))
  (interval_append badTest_4352 192 224 256
  (interval_append badTest_4352 192 208 224
  (interval_append badTest_4352 192 200 208
  badTest_4352_block_24
  badTest_4352_block_25)
  (interval_append badTest_4352 208 216 224
  badTest_4352_block_26
  badTest_4352_block_27))
  (interval_append badTest_4352 224 240 256
  (interval_append badTest_4352 224 232 240
  badTest_4352_block_28
  badTest_4352_block_29)
  (interval_append badTest_4352 240 248 256
  badTest_4352_block_30
  badTest_4352_block_31)))))
theorem badTestInterval4352 : Interval badTest 4352 4608 := by
  intro i hlo hhi
  have h := badTest_4352_complete (i-4352) (Nat.zero_le _) (by omega)
  simpa only [badTest_4352, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad018 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_4608 (i : Nat) := badTest (i+4608)
theorem badTest_4608_block_0 : Interval badTest_4608 0 8 :=
  interval_of_check badTest_4608 0 8 (by decide +kernel)

theorem badTest_4608_block_1 : Interval badTest_4608 8 16 :=
  interval_of_check badTest_4608 8 8 (by decide +kernel)

theorem badTest_4608_block_2 : Interval badTest_4608 16 24 :=
  interval_of_check badTest_4608 16 8 (by decide +kernel)

theorem badTest_4608_block_3 : Interval badTest_4608 24 32 :=
  interval_of_check badTest_4608 24 8 (by decide +kernel)

theorem badTest_4608_block_4 : Interval badTest_4608 32 40 :=
  interval_of_check badTest_4608 32 8 (by decide +kernel)

theorem badTest_4608_block_5 : Interval badTest_4608 40 48 :=
  interval_of_check badTest_4608 40 8 (by decide +kernel)

theorem badTest_4608_block_6 : Interval badTest_4608 48 56 :=
  interval_of_check badTest_4608 48 8 (by decide +kernel)

theorem badTest_4608_block_7 : Interval badTest_4608 56 64 :=
  interval_of_check badTest_4608 56 8 (by decide +kernel)

theorem badTest_4608_block_8 : Interval badTest_4608 64 72 :=
  interval_of_check badTest_4608 64 8 (by decide +kernel)

theorem badTest_4608_block_9 : Interval badTest_4608 72 80 :=
  interval_of_check badTest_4608 72 8 (by decide +kernel)

theorem badTest_4608_block_10 : Interval badTest_4608 80 88 :=
  interval_of_check badTest_4608 80 8 (by decide +kernel)

theorem badTest_4608_block_11 : Interval badTest_4608 88 96 :=
  interval_of_check badTest_4608 88 8 (by decide +kernel)

theorem badTest_4608_block_12 : Interval badTest_4608 96 104 :=
  interval_of_check badTest_4608 96 8 (by decide +kernel)

theorem badTest_4608_block_13 : Interval badTest_4608 104 112 :=
  interval_of_check badTest_4608 104 8 (by decide +kernel)

theorem badTest_4608_block_14 : Interval badTest_4608 112 120 :=
  interval_of_check badTest_4608 112 8 (by decide +kernel)

theorem badTest_4608_block_15 : Interval badTest_4608 120 128 :=
  interval_of_check badTest_4608 120 8 (by decide +kernel)

theorem badTest_4608_block_16 : Interval badTest_4608 128 136 :=
  interval_of_check badTest_4608 128 8 (by decide +kernel)

theorem badTest_4608_block_17 : Interval badTest_4608 136 144 :=
  interval_of_check badTest_4608 136 8 (by decide +kernel)

theorem badTest_4608_block_18 : Interval badTest_4608 144 152 :=
  interval_of_check badTest_4608 144 8 (by decide +kernel)

theorem badTest_4608_block_19 : Interval badTest_4608 152 160 :=
  interval_of_check badTest_4608 152 8 (by decide +kernel)

theorem badTest_4608_block_20 : Interval badTest_4608 160 168 :=
  interval_of_check badTest_4608 160 8 (by decide +kernel)

theorem badTest_4608_block_21 : Interval badTest_4608 168 176 :=
  interval_of_check badTest_4608 168 8 (by decide +kernel)

theorem badTest_4608_block_22 : Interval badTest_4608 176 184 :=
  interval_of_check badTest_4608 176 8 (by decide +kernel)

theorem badTest_4608_block_23 : Interval badTest_4608 184 192 :=
  interval_of_check badTest_4608 184 8 (by decide +kernel)

theorem badTest_4608_block_24 : Interval badTest_4608 192 200 :=
  interval_of_check badTest_4608 192 8 (by decide +kernel)

theorem badTest_4608_block_25 : Interval badTest_4608 200 208 :=
  interval_of_check badTest_4608 200 8 (by decide +kernel)

theorem badTest_4608_block_26 : Interval badTest_4608 208 216 :=
  interval_of_check badTest_4608 208 8 (by decide +kernel)

theorem badTest_4608_block_27 : Interval badTest_4608 216 224 :=
  interval_of_check badTest_4608 216 8 (by decide +kernel)

theorem badTest_4608_block_28 : Interval badTest_4608 224 232 :=
  interval_of_check badTest_4608 224 8 (by decide +kernel)

theorem badTest_4608_block_29 : Interval badTest_4608 232 240 :=
  interval_of_check badTest_4608 232 8 (by decide +kernel)

theorem badTest_4608_block_30 : Interval badTest_4608 240 248 :=
  interval_of_check badTest_4608 240 8 (by decide +kernel)

theorem badTest_4608_block_31 : Interval badTest_4608 248 256 :=
  interval_of_check badTest_4608 248 8 (by decide +kernel)

theorem badTest_4608_complete : Interval badTest_4608 0 256 :=
  (interval_append badTest_4608 0 128 256
  (interval_append badTest_4608 0 64 128
  (interval_append badTest_4608 0 32 64
  (interval_append badTest_4608 0 16 32
  (interval_append badTest_4608 0 8 16
  badTest_4608_block_0
  badTest_4608_block_1)
  (interval_append badTest_4608 16 24 32
  badTest_4608_block_2
  badTest_4608_block_3))
  (interval_append badTest_4608 32 48 64
  (interval_append badTest_4608 32 40 48
  badTest_4608_block_4
  badTest_4608_block_5)
  (interval_append badTest_4608 48 56 64
  badTest_4608_block_6
  badTest_4608_block_7)))
  (interval_append badTest_4608 64 96 128
  (interval_append badTest_4608 64 80 96
  (interval_append badTest_4608 64 72 80
  badTest_4608_block_8
  badTest_4608_block_9)
  (interval_append badTest_4608 80 88 96
  badTest_4608_block_10
  badTest_4608_block_11))
  (interval_append badTest_4608 96 112 128
  (interval_append badTest_4608 96 104 112
  badTest_4608_block_12
  badTest_4608_block_13)
  (interval_append badTest_4608 112 120 128
  badTest_4608_block_14
  badTest_4608_block_15))))
  (interval_append badTest_4608 128 192 256
  (interval_append badTest_4608 128 160 192
  (interval_append badTest_4608 128 144 160
  (interval_append badTest_4608 128 136 144
  badTest_4608_block_16
  badTest_4608_block_17)
  (interval_append badTest_4608 144 152 160
  badTest_4608_block_18
  badTest_4608_block_19))
  (interval_append badTest_4608 160 176 192
  (interval_append badTest_4608 160 168 176
  badTest_4608_block_20
  badTest_4608_block_21)
  (interval_append badTest_4608 176 184 192
  badTest_4608_block_22
  badTest_4608_block_23)))
  (interval_append badTest_4608 192 224 256
  (interval_append badTest_4608 192 208 224
  (interval_append badTest_4608 192 200 208
  badTest_4608_block_24
  badTest_4608_block_25)
  (interval_append badTest_4608 208 216 224
  badTest_4608_block_26
  badTest_4608_block_27))
  (interval_append badTest_4608 224 240 256
  (interval_append badTest_4608 224 232 240
  badTest_4608_block_28
  badTest_4608_block_29)
  (interval_append badTest_4608 240 248 256
  badTest_4608_block_30
  badTest_4608_block_31)))))
theorem badTestInterval4608 : Interval badTest 4608 4864 := by
  intro i hlo hhi
  have h := badTest_4608_complete (i-4608) (Nat.zero_le _) (by omega)
  simpa only [badTest_4608, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad019 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_4864 (i : Nat) := badTest (i+4864)
theorem badTest_4864_block_0 : Interval badTest_4864 0 8 :=
  interval_of_check badTest_4864 0 8 (by decide +kernel)

theorem badTest_4864_block_1 : Interval badTest_4864 8 16 :=
  interval_of_check badTest_4864 8 8 (by decide +kernel)

theorem badTest_4864_block_2 : Interval badTest_4864 16 24 :=
  interval_of_check badTest_4864 16 8 (by decide +kernel)

theorem badTest_4864_block_3 : Interval badTest_4864 24 32 :=
  interval_of_check badTest_4864 24 8 (by decide +kernel)

theorem badTest_4864_block_4 : Interval badTest_4864 32 40 :=
  interval_of_check badTest_4864 32 8 (by decide +kernel)

theorem badTest_4864_block_5 : Interval badTest_4864 40 48 :=
  interval_of_check badTest_4864 40 8 (by decide +kernel)

theorem badTest_4864_block_6 : Interval badTest_4864 48 56 :=
  interval_of_check badTest_4864 48 8 (by decide +kernel)

theorem badTest_4864_block_7 : Interval badTest_4864 56 64 :=
  interval_of_check badTest_4864 56 8 (by decide +kernel)

theorem badTest_4864_block_8 : Interval badTest_4864 64 72 :=
  interval_of_check badTest_4864 64 8 (by decide +kernel)

theorem badTest_4864_block_9 : Interval badTest_4864 72 80 :=
  interval_of_check badTest_4864 72 8 (by decide +kernel)

theorem badTest_4864_block_10 : Interval badTest_4864 80 88 :=
  interval_of_check badTest_4864 80 8 (by decide +kernel)

theorem badTest_4864_block_11 : Interval badTest_4864 88 96 :=
  interval_of_check badTest_4864 88 8 (by decide +kernel)

theorem badTest_4864_block_12 : Interval badTest_4864 96 104 :=
  interval_of_check badTest_4864 96 8 (by decide +kernel)

theorem badTest_4864_block_13 : Interval badTest_4864 104 112 :=
  interval_of_check badTest_4864 104 8 (by decide +kernel)

theorem badTest_4864_block_14 : Interval badTest_4864 112 120 :=
  interval_of_check badTest_4864 112 8 (by decide +kernel)

theorem badTest_4864_block_15 : Interval badTest_4864 120 128 :=
  interval_of_check badTest_4864 120 8 (by decide +kernel)

theorem badTest_4864_block_16 : Interval badTest_4864 128 136 :=
  interval_of_check badTest_4864 128 8 (by decide +kernel)

theorem badTest_4864_block_17 : Interval badTest_4864 136 144 :=
  interval_of_check badTest_4864 136 8 (by decide +kernel)

theorem badTest_4864_block_18 : Interval badTest_4864 144 152 :=
  interval_of_check badTest_4864 144 8 (by decide +kernel)

theorem badTest_4864_block_19 : Interval badTest_4864 152 160 :=
  interval_of_check badTest_4864 152 8 (by decide +kernel)

theorem badTest_4864_block_20 : Interval badTest_4864 160 168 :=
  interval_of_check badTest_4864 160 8 (by decide +kernel)

theorem badTest_4864_block_21 : Interval badTest_4864 168 176 :=
  interval_of_check badTest_4864 168 8 (by decide +kernel)

theorem badTest_4864_block_22 : Interval badTest_4864 176 184 :=
  interval_of_check badTest_4864 176 8 (by decide +kernel)

theorem badTest_4864_block_23 : Interval badTest_4864 184 192 :=
  interval_of_check badTest_4864 184 8 (by decide +kernel)

theorem badTest_4864_block_24 : Interval badTest_4864 192 200 :=
  interval_of_check badTest_4864 192 8 (by decide +kernel)

theorem badTest_4864_block_25 : Interval badTest_4864 200 208 :=
  interval_of_check badTest_4864 200 8 (by decide +kernel)

theorem badTest_4864_block_26 : Interval badTest_4864 208 216 :=
  interval_of_check badTest_4864 208 8 (by decide +kernel)

theorem badTest_4864_block_27 : Interval badTest_4864 216 224 :=
  interval_of_check badTest_4864 216 8 (by decide +kernel)

theorem badTest_4864_block_28 : Interval badTest_4864 224 232 :=
  interval_of_check badTest_4864 224 8 (by decide +kernel)

theorem badTest_4864_block_29 : Interval badTest_4864 232 240 :=
  interval_of_check badTest_4864 232 8 (by decide +kernel)

theorem badTest_4864_block_30 : Interval badTest_4864 240 248 :=
  interval_of_check badTest_4864 240 8 (by decide +kernel)

theorem badTest_4864_block_31 : Interval badTest_4864 248 256 :=
  interval_of_check badTest_4864 248 8 (by decide +kernel)

theorem badTest_4864_complete : Interval badTest_4864 0 256 :=
  (interval_append badTest_4864 0 128 256
  (interval_append badTest_4864 0 64 128
  (interval_append badTest_4864 0 32 64
  (interval_append badTest_4864 0 16 32
  (interval_append badTest_4864 0 8 16
  badTest_4864_block_0
  badTest_4864_block_1)
  (interval_append badTest_4864 16 24 32
  badTest_4864_block_2
  badTest_4864_block_3))
  (interval_append badTest_4864 32 48 64
  (interval_append badTest_4864 32 40 48
  badTest_4864_block_4
  badTest_4864_block_5)
  (interval_append badTest_4864 48 56 64
  badTest_4864_block_6
  badTest_4864_block_7)))
  (interval_append badTest_4864 64 96 128
  (interval_append badTest_4864 64 80 96
  (interval_append badTest_4864 64 72 80
  badTest_4864_block_8
  badTest_4864_block_9)
  (interval_append badTest_4864 80 88 96
  badTest_4864_block_10
  badTest_4864_block_11))
  (interval_append badTest_4864 96 112 128
  (interval_append badTest_4864 96 104 112
  badTest_4864_block_12
  badTest_4864_block_13)
  (interval_append badTest_4864 112 120 128
  badTest_4864_block_14
  badTest_4864_block_15))))
  (interval_append badTest_4864 128 192 256
  (interval_append badTest_4864 128 160 192
  (interval_append badTest_4864 128 144 160
  (interval_append badTest_4864 128 136 144
  badTest_4864_block_16
  badTest_4864_block_17)
  (interval_append badTest_4864 144 152 160
  badTest_4864_block_18
  badTest_4864_block_19))
  (interval_append badTest_4864 160 176 192
  (interval_append badTest_4864 160 168 176
  badTest_4864_block_20
  badTest_4864_block_21)
  (interval_append badTest_4864 176 184 192
  badTest_4864_block_22
  badTest_4864_block_23)))
  (interval_append badTest_4864 192 224 256
  (interval_append badTest_4864 192 208 224
  (interval_append badTest_4864 192 200 208
  badTest_4864_block_24
  badTest_4864_block_25)
  (interval_append badTest_4864 208 216 224
  badTest_4864_block_26
  badTest_4864_block_27))
  (interval_append badTest_4864 224 240 256
  (interval_append badTest_4864 224 232 240
  badTest_4864_block_28
  badTest_4864_block_29)
  (interval_append badTest_4864 240 248 256
  badTest_4864_block_30
  badTest_4864_block_31)))))
theorem badTestInterval4864 : Interval badTest 4864 5120 := by
  intro i hlo hhi
  have h := badTest_4864_complete (i-4864) (Nat.zero_le _) (by omega)
  simpa only [badTest_4864, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad020 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad021 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad022 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad023 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad024 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad025 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
