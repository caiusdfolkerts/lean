module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheBad026 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad027 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad028 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad029 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad030 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad031 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad032 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad033 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad034 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad035 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad036 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad037 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad038 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad039 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad040 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad041 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
