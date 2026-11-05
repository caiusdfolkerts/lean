module
prelude
public import RootedSixBase01GrowthCacheData

/- RootedSixBase01GrowthCacheBad004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad010 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad011 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad012 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad013 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad014 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad015 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad016 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad017 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad018 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad019 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
