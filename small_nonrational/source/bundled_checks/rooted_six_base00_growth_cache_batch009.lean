module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheBad058 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad059 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

theorem badTest_15104_block_17 : Interval badTest_15104 136 144 :=
  interval_of_check badTest_15104 136 8 (by decide +kernel)

theorem badTest_15104_block_18 : Interval badTest_15104 144 152 :=
  interval_of_check badTest_15104 144 8 (by decide +kernel)

theorem badTest_15104_block_19 : Interval badTest_15104 152 160 :=
  interval_of_check badTest_15104 152 8 (by decide +kernel)

theorem badTest_15104_block_20 : Interval badTest_15104 160 168 :=
  interval_of_check badTest_15104 160 8 (by decide +kernel)

theorem badTest_15104_block_21 : Interval badTest_15104 168 176 :=
  interval_of_check badTest_15104 168 8 (by decide +kernel)

theorem badTest_15104_block_22 : Interval badTest_15104 176 184 :=
  interval_of_check badTest_15104 176 8 (by decide +kernel)

theorem badTest_15104_block_23 : Interval badTest_15104 184 192 :=
  interval_of_check badTest_15104 184 8 (by decide +kernel)

theorem badTest_15104_block_24 : Interval badTest_15104 192 200 :=
  interval_of_check badTest_15104 192 8 (by decide +kernel)

theorem badTest_15104_block_25 : Interval badTest_15104 200 208 :=
  interval_of_check badTest_15104 200 8 (by decide +kernel)

theorem badTest_15104_block_26 : Interval badTest_15104 208 216 :=
  interval_of_check badTest_15104 208 8 (by decide +kernel)

theorem badTest_15104_block_27 : Interval badTest_15104 216 224 :=
  interval_of_check badTest_15104 216 8 (by decide +kernel)

theorem badTest_15104_block_28 : Interval badTest_15104 224 232 :=
  interval_of_check badTest_15104 224 8 (by decide +kernel)

theorem badTest_15104_block_29 : Interval badTest_15104 232 240 :=
  interval_of_check badTest_15104 232 8 (by decide +kernel)

theorem badTest_15104_block_30 : Interval badTest_15104 240 248 :=
  interval_of_check badTest_15104 240 8 (by decide +kernel)

theorem badTest_15104_block_31 : Interval badTest_15104 248 256 :=
  interval_of_check badTest_15104 248 8 (by decide +kernel)

theorem badTest_15104_complete : Interval badTest_15104 0 256 :=
  (interval_append badTest_15104 0 128 256
  (interval_append badTest_15104 0 64 128
  (interval_append badTest_15104 0 32 64
  (interval_append badTest_15104 0 16 32
  (interval_append badTest_15104 0 8 16
  badTest_15104_block_0
  badTest_15104_block_1)
  (interval_append badTest_15104 16 24 32
  badTest_15104_block_2
  badTest_15104_block_3))
  (interval_append badTest_15104 32 48 64
  (interval_append badTest_15104 32 40 48
  badTest_15104_block_4
  badTest_15104_block_5)
  (interval_append badTest_15104 48 56 64
  badTest_15104_block_6
  badTest_15104_block_7)))
  (interval_append badTest_15104 64 96 128
  (interval_append badTest_15104 64 80 96
  (interval_append badTest_15104 64 72 80
  badTest_15104_block_8
  badTest_15104_block_9)
  (interval_append badTest_15104 80 88 96
  badTest_15104_block_10
  badTest_15104_block_11))
  (interval_append badTest_15104 96 112 128
  (interval_append badTest_15104 96 104 112
  badTest_15104_block_12
  badTest_15104_block_13)
  (interval_append badTest_15104 112 120 128
  badTest_15104_block_14
  badTest_15104_block_15))))
  (interval_append badTest_15104 128 192 256
  (interval_append badTest_15104 128 160 192
  (interval_append badTest_15104 128 144 160
  (interval_append badTest_15104 128 136 144
  badTest_15104_block_16
  badTest_15104_block_17)
  (interval_append badTest_15104 144 152 160
  badTest_15104_block_18
  badTest_15104_block_19))
  (interval_append badTest_15104 160 176 192
  (interval_append badTest_15104 160 168 176
  badTest_15104_block_20
  badTest_15104_block_21)
  (interval_append badTest_15104 176 184 192
  badTest_15104_block_22
  badTest_15104_block_23)))
  (interval_append badTest_15104 192 224 256
  (interval_append badTest_15104 192 208 224
  (interval_append badTest_15104 192 200 208
  badTest_15104_block_24
  badTest_15104_block_25)
  (interval_append badTest_15104 208 216 224
  badTest_15104_block_26
  badTest_15104_block_27))
  (interval_append badTest_15104 224 240 256
  (interval_append badTest_15104 224 232 240
  badTest_15104_block_28
  badTest_15104_block_29)
  (interval_append badTest_15104 240 248 256
  badTest_15104_block_30
  badTest_15104_block_31)))))
theorem badTestInterval15104 : Interval badTest 15104 15360 := by
  intro i hlo hhi
  have h := badTest_15104_complete (i-15104) (Nat.zero_le _) (by omega)
  simpa only [badTest_15104, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad060 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_15360 (i : Nat) := badTest (i+15360)
theorem badTest_15360_block_0 : Interval badTest_15360 0 8 :=
  interval_of_check badTest_15360 0 8 (by decide +kernel)

theorem badTest_15360_block_1 : Interval badTest_15360 8 16 :=
  interval_of_check badTest_15360 8 8 (by decide +kernel)

theorem badTest_15360_block_2 : Interval badTest_15360 16 24 :=
  interval_of_check badTest_15360 16 8 (by decide +kernel)

theorem badTest_15360_block_3 : Interval badTest_15360 24 32 :=
  interval_of_check badTest_15360 24 8 (by decide +kernel)

theorem badTest_15360_block_4 : Interval badTest_15360 32 40 :=
  interval_of_check badTest_15360 32 8 (by decide +kernel)

theorem badTest_15360_block_5 : Interval badTest_15360 40 48 :=
  interval_of_check badTest_15360 40 8 (by decide +kernel)

theorem badTest_15360_block_6 : Interval badTest_15360 48 56 :=
  interval_of_check badTest_15360 48 8 (by decide +kernel)

theorem badTest_15360_block_7 : Interval badTest_15360 56 64 :=
  interval_of_check badTest_15360 56 8 (by decide +kernel)

theorem badTest_15360_block_8 : Interval badTest_15360 64 72 :=
  interval_of_check badTest_15360 64 8 (by decide +kernel)

theorem badTest_15360_block_9 : Interval badTest_15360 72 80 :=
  interval_of_check badTest_15360 72 8 (by decide +kernel)

theorem badTest_15360_block_10 : Interval badTest_15360 80 88 :=
  interval_of_check badTest_15360 80 8 (by decide +kernel)

theorem badTest_15360_block_11 : Interval badTest_15360 88 96 :=
  interval_of_check badTest_15360 88 8 (by decide +kernel)

theorem badTest_15360_block_12 : Interval badTest_15360 96 104 :=
  interval_of_check badTest_15360 96 8 (by decide +kernel)

theorem badTest_15360_block_13 : Interval badTest_15360 104 112 :=
  interval_of_check badTest_15360 104 8 (by decide +kernel)

theorem badTest_15360_block_14 : Interval badTest_15360 112 120 :=
  interval_of_check badTest_15360 112 8 (by decide +kernel)

theorem badTest_15360_block_15 : Interval badTest_15360 120 128 :=
  interval_of_check badTest_15360 120 8 (by decide +kernel)

theorem badTest_15360_block_16 : Interval badTest_15360 128 136 :=
  interval_of_check badTest_15360 128 8 (by decide +kernel)

theorem badTest_15360_block_17 : Interval badTest_15360 136 144 :=
  interval_of_check badTest_15360 136 8 (by decide +kernel)

theorem badTest_15360_block_18 : Interval badTest_15360 144 152 :=
  interval_of_check badTest_15360 144 8 (by decide +kernel)

theorem badTest_15360_block_19 : Interval badTest_15360 152 160 :=
  interval_of_check badTest_15360 152 8 (by decide +kernel)

theorem badTest_15360_block_20 : Interval badTest_15360 160 168 :=
  interval_of_check badTest_15360 160 8 (by decide +kernel)

theorem badTest_15360_block_21 : Interval badTest_15360 168 176 :=
  interval_of_check badTest_15360 168 8 (by decide +kernel)

theorem badTest_15360_block_22 : Interval badTest_15360 176 184 :=
  interval_of_check badTest_15360 176 8 (by decide +kernel)

theorem badTest_15360_block_23 : Interval badTest_15360 184 192 :=
  interval_of_check badTest_15360 184 8 (by decide +kernel)

theorem badTest_15360_block_24 : Interval badTest_15360 192 200 :=
  interval_of_check badTest_15360 192 8 (by decide +kernel)

theorem badTest_15360_block_25 : Interval badTest_15360 200 208 :=
  interval_of_check badTest_15360 200 8 (by decide +kernel)

theorem badTest_15360_block_26 : Interval badTest_15360 208 216 :=
  interval_of_check badTest_15360 208 8 (by decide +kernel)

theorem badTest_15360_block_27 : Interval badTest_15360 216 224 :=
  interval_of_check badTest_15360 216 8 (by decide +kernel)

theorem badTest_15360_block_28 : Interval badTest_15360 224 232 :=
  interval_of_check badTest_15360 224 8 (by decide +kernel)

theorem badTest_15360_block_29 : Interval badTest_15360 232 240 :=
  interval_of_check badTest_15360 232 8 (by decide +kernel)

theorem badTest_15360_block_30 : Interval badTest_15360 240 248 :=
  interval_of_check badTest_15360 240 8 (by decide +kernel)

theorem badTest_15360_block_31 : Interval badTest_15360 248 256 :=
  interval_of_check badTest_15360 248 8 (by decide +kernel)

theorem badTest_15360_complete : Interval badTest_15360 0 256 :=
  (interval_append badTest_15360 0 128 256
  (interval_append badTest_15360 0 64 128
  (interval_append badTest_15360 0 32 64
  (interval_append badTest_15360 0 16 32
  (interval_append badTest_15360 0 8 16
  badTest_15360_block_0
  badTest_15360_block_1)
  (interval_append badTest_15360 16 24 32
  badTest_15360_block_2
  badTest_15360_block_3))
  (interval_append badTest_15360 32 48 64
  (interval_append badTest_15360 32 40 48
  badTest_15360_block_4
  badTest_15360_block_5)
  (interval_append badTest_15360 48 56 64
  badTest_15360_block_6
  badTest_15360_block_7)))
  (interval_append badTest_15360 64 96 128
  (interval_append badTest_15360 64 80 96
  (interval_append badTest_15360 64 72 80
  badTest_15360_block_8
  badTest_15360_block_9)
  (interval_append badTest_15360 80 88 96
  badTest_15360_block_10
  badTest_15360_block_11))
  (interval_append badTest_15360 96 112 128
  (interval_append badTest_15360 96 104 112
  badTest_15360_block_12
  badTest_15360_block_13)
  (interval_append badTest_15360 112 120 128
  badTest_15360_block_14
  badTest_15360_block_15))))
  (interval_append badTest_15360 128 192 256
  (interval_append badTest_15360 128 160 192
  (interval_append badTest_15360 128 144 160
  (interval_append badTest_15360 128 136 144
  badTest_15360_block_16
  badTest_15360_block_17)
  (interval_append badTest_15360 144 152 160
  badTest_15360_block_18
  badTest_15360_block_19))
  (interval_append badTest_15360 160 176 192
  (interval_append badTest_15360 160 168 176
  badTest_15360_block_20
  badTest_15360_block_21)
  (interval_append badTest_15360 176 184 192
  badTest_15360_block_22
  badTest_15360_block_23)))
  (interval_append badTest_15360 192 224 256
  (interval_append badTest_15360 192 208 224
  (interval_append badTest_15360 192 200 208
  badTest_15360_block_24
  badTest_15360_block_25)
  (interval_append badTest_15360 208 216 224
  badTest_15360_block_26
  badTest_15360_block_27))
  (interval_append badTest_15360 224 240 256
  (interval_append badTest_15360 224 232 240
  badTest_15360_block_28
  badTest_15360_block_29)
  (interval_append badTest_15360 240 248 256
  badTest_15360_block_30
  badTest_15360_block_31)))))
theorem badTestInterval15360 : Interval badTest 15360 15616 := by
  intro i hlo hhi
  have h := badTest_15360_complete (i-15360) (Nat.zero_le _) (by omega)
  simpa only [badTest_15360, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad061 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_15616 (i : Nat) := badTest (i+15616)
theorem badTest_15616_block_0 : Interval badTest_15616 0 8 :=
  interval_of_check badTest_15616 0 8 (by decide +kernel)

theorem badTest_15616_block_1 : Interval badTest_15616 8 16 :=
  interval_of_check badTest_15616 8 8 (by decide +kernel)

theorem badTest_15616_block_2 : Interval badTest_15616 16 24 :=
  interval_of_check badTest_15616 16 8 (by decide +kernel)

theorem badTest_15616_block_3 : Interval badTest_15616 24 32 :=
  interval_of_check badTest_15616 24 8 (by decide +kernel)

theorem badTest_15616_block_4 : Interval badTest_15616 32 40 :=
  interval_of_check badTest_15616 32 8 (by decide +kernel)

theorem badTest_15616_block_5 : Interval badTest_15616 40 48 :=
  interval_of_check badTest_15616 40 8 (by decide +kernel)

theorem badTest_15616_block_6 : Interval badTest_15616 48 56 :=
  interval_of_check badTest_15616 48 8 (by decide +kernel)

theorem badTest_15616_block_7 : Interval badTest_15616 56 64 :=
  interval_of_check badTest_15616 56 8 (by decide +kernel)

theorem badTest_15616_block_8 : Interval badTest_15616 64 72 :=
  interval_of_check badTest_15616 64 8 (by decide +kernel)

theorem badTest_15616_block_9 : Interval badTest_15616 72 80 :=
  interval_of_check badTest_15616 72 8 (by decide +kernel)

theorem badTest_15616_block_10 : Interval badTest_15616 80 88 :=
  interval_of_check badTest_15616 80 8 (by decide +kernel)

theorem badTest_15616_block_11 : Interval badTest_15616 88 96 :=
  interval_of_check badTest_15616 88 8 (by decide +kernel)

theorem badTest_15616_block_12 : Interval badTest_15616 96 104 :=
  interval_of_check badTest_15616 96 8 (by decide +kernel)

theorem badTest_15616_block_13 : Interval badTest_15616 104 112 :=
  interval_of_check badTest_15616 104 8 (by decide +kernel)

theorem badTest_15616_block_14 : Interval badTest_15616 112 120 :=
  interval_of_check badTest_15616 112 8 (by decide +kernel)

theorem badTest_15616_block_15 : Interval badTest_15616 120 128 :=
  interval_of_check badTest_15616 120 8 (by decide +kernel)

theorem badTest_15616_block_16 : Interval badTest_15616 128 136 :=
  interval_of_check badTest_15616 128 8 (by decide +kernel)

theorem badTest_15616_block_17 : Interval badTest_15616 136 144 :=
  interval_of_check badTest_15616 136 8 (by decide +kernel)

theorem badTest_15616_block_18 : Interval badTest_15616 144 152 :=
  interval_of_check badTest_15616 144 8 (by decide +kernel)

theorem badTest_15616_block_19 : Interval badTest_15616 152 160 :=
  interval_of_check badTest_15616 152 8 (by decide +kernel)

theorem badTest_15616_block_20 : Interval badTest_15616 160 168 :=
  interval_of_check badTest_15616 160 8 (by decide +kernel)

theorem badTest_15616_block_21 : Interval badTest_15616 168 176 :=
  interval_of_check badTest_15616 168 8 (by decide +kernel)

theorem badTest_15616_block_22 : Interval badTest_15616 176 184 :=
  interval_of_check badTest_15616 176 8 (by decide +kernel)

theorem badTest_15616_block_23 : Interval badTest_15616 184 192 :=
  interval_of_check badTest_15616 184 8 (by decide +kernel)

theorem badTest_15616_block_24 : Interval badTest_15616 192 200 :=
  interval_of_check badTest_15616 192 8 (by decide +kernel)

theorem badTest_15616_block_25 : Interval badTest_15616 200 208 :=
  interval_of_check badTest_15616 200 8 (by decide +kernel)

theorem badTest_15616_block_26 : Interval badTest_15616 208 216 :=
  interval_of_check badTest_15616 208 8 (by decide +kernel)

theorem badTest_15616_block_27 : Interval badTest_15616 216 224 :=
  interval_of_check badTest_15616 216 8 (by decide +kernel)

theorem badTest_15616_block_28 : Interval badTest_15616 224 232 :=
  interval_of_check badTest_15616 224 8 (by decide +kernel)

theorem badTest_15616_block_29 : Interval badTest_15616 232 240 :=
  interval_of_check badTest_15616 232 8 (by decide +kernel)

theorem badTest_15616_block_30 : Interval badTest_15616 240 248 :=
  interval_of_check badTest_15616 240 8 (by decide +kernel)

theorem badTest_15616_block_31 : Interval badTest_15616 248 256 :=
  interval_of_check badTest_15616 248 8 (by decide +kernel)

theorem badTest_15616_complete : Interval badTest_15616 0 256 :=
  (interval_append badTest_15616 0 128 256
  (interval_append badTest_15616 0 64 128
  (interval_append badTest_15616 0 32 64
  (interval_append badTest_15616 0 16 32
  (interval_append badTest_15616 0 8 16
  badTest_15616_block_0
  badTest_15616_block_1)
  (interval_append badTest_15616 16 24 32
  badTest_15616_block_2
  badTest_15616_block_3))
  (interval_append badTest_15616 32 48 64
  (interval_append badTest_15616 32 40 48
  badTest_15616_block_4
  badTest_15616_block_5)
  (interval_append badTest_15616 48 56 64
  badTest_15616_block_6
  badTest_15616_block_7)))
  (interval_append badTest_15616 64 96 128
  (interval_append badTest_15616 64 80 96
  (interval_append badTest_15616 64 72 80
  badTest_15616_block_8
  badTest_15616_block_9)
  (interval_append badTest_15616 80 88 96
  badTest_15616_block_10
  badTest_15616_block_11))
  (interval_append badTest_15616 96 112 128
  (interval_append badTest_15616 96 104 112
  badTest_15616_block_12
  badTest_15616_block_13)
  (interval_append badTest_15616 112 120 128
  badTest_15616_block_14
  badTest_15616_block_15))))
  (interval_append badTest_15616 128 192 256
  (interval_append badTest_15616 128 160 192
  (interval_append badTest_15616 128 144 160
  (interval_append badTest_15616 128 136 144
  badTest_15616_block_16
  badTest_15616_block_17)
  (interval_append badTest_15616 144 152 160
  badTest_15616_block_18
  badTest_15616_block_19))
  (interval_append badTest_15616 160 176 192
  (interval_append badTest_15616 160 168 176
  badTest_15616_block_20
  badTest_15616_block_21)
  (interval_append badTest_15616 176 184 192
  badTest_15616_block_22
  badTest_15616_block_23)))
  (interval_append badTest_15616 192 224 256
  (interval_append badTest_15616 192 208 224
  (interval_append badTest_15616 192 200 208
  badTest_15616_block_24
  badTest_15616_block_25)
  (interval_append badTest_15616 208 216 224
  badTest_15616_block_26
  badTest_15616_block_27))
  (interval_append badTest_15616 224 240 256
  (interval_append badTest_15616 224 232 240
  badTest_15616_block_28
  badTest_15616_block_29)
  (interval_append badTest_15616 240 248 256
  badTest_15616_block_30
  badTest_15616_block_31)))))
theorem badTestInterval15616 : Interval badTest 15616 15872 := by
  intro i hlo hhi
  have h := badTest_15616_complete (i-15616) (Nat.zero_le _) (by omega)
  simpa only [badTest_15616, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad062 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_15872 (i : Nat) := badTest (i+15872)
theorem badTest_15872_block_0 : Interval badTest_15872 0 8 :=
  interval_of_check badTest_15872 0 8 (by decide +kernel)

theorem badTest_15872_block_1 : Interval badTest_15872 8 16 :=
  interval_of_check badTest_15872 8 8 (by decide +kernel)

theorem badTest_15872_block_2 : Interval badTest_15872 16 24 :=
  interval_of_check badTest_15872 16 8 (by decide +kernel)

theorem badTest_15872_block_3 : Interval badTest_15872 24 32 :=
  interval_of_check badTest_15872 24 8 (by decide +kernel)

theorem badTest_15872_block_4 : Interval badTest_15872 32 40 :=
  interval_of_check badTest_15872 32 8 (by decide +kernel)

theorem badTest_15872_block_5 : Interval badTest_15872 40 48 :=
  interval_of_check badTest_15872 40 8 (by decide +kernel)

theorem badTest_15872_block_6 : Interval badTest_15872 48 56 :=
  interval_of_check badTest_15872 48 8 (by decide +kernel)

theorem badTest_15872_block_7 : Interval badTest_15872 56 64 :=
  interval_of_check badTest_15872 56 8 (by decide +kernel)

theorem badTest_15872_block_8 : Interval badTest_15872 64 72 :=
  interval_of_check badTest_15872 64 8 (by decide +kernel)

theorem badTest_15872_block_9 : Interval badTest_15872 72 80 :=
  interval_of_check badTest_15872 72 8 (by decide +kernel)

theorem badTest_15872_block_10 : Interval badTest_15872 80 88 :=
  interval_of_check badTest_15872 80 8 (by decide +kernel)

theorem badTest_15872_block_11 : Interval badTest_15872 88 96 :=
  interval_of_check badTest_15872 88 8 (by decide +kernel)

theorem badTest_15872_block_12 : Interval badTest_15872 96 104 :=
  interval_of_check badTest_15872 96 8 (by decide +kernel)

theorem badTest_15872_block_13 : Interval badTest_15872 104 112 :=
  interval_of_check badTest_15872 104 8 (by decide +kernel)

theorem badTest_15872_block_14 : Interval badTest_15872 112 120 :=
  interval_of_check badTest_15872 112 8 (by decide +kernel)

theorem badTest_15872_block_15 : Interval badTest_15872 120 128 :=
  interval_of_check badTest_15872 120 8 (by decide +kernel)

theorem badTest_15872_block_16 : Interval badTest_15872 128 136 :=
  interval_of_check badTest_15872 128 8 (by decide +kernel)

theorem badTest_15872_block_17 : Interval badTest_15872 136 144 :=
  interval_of_check badTest_15872 136 8 (by decide +kernel)

theorem badTest_15872_block_18 : Interval badTest_15872 144 152 :=
  interval_of_check badTest_15872 144 8 (by decide +kernel)

theorem badTest_15872_block_19 : Interval badTest_15872 152 160 :=
  interval_of_check badTest_15872 152 8 (by decide +kernel)

theorem badTest_15872_block_20 : Interval badTest_15872 160 168 :=
  interval_of_check badTest_15872 160 8 (by decide +kernel)

theorem badTest_15872_block_21 : Interval badTest_15872 168 176 :=
  interval_of_check badTest_15872 168 8 (by decide +kernel)

theorem badTest_15872_block_22 : Interval badTest_15872 176 184 :=
  interval_of_check badTest_15872 176 8 (by decide +kernel)

theorem badTest_15872_block_23 : Interval badTest_15872 184 192 :=
  interval_of_check badTest_15872 184 8 (by decide +kernel)

theorem badTest_15872_block_24 : Interval badTest_15872 192 200 :=
  interval_of_check badTest_15872 192 8 (by decide +kernel)

theorem badTest_15872_block_25 : Interval badTest_15872 200 208 :=
  interval_of_check badTest_15872 200 8 (by decide +kernel)

theorem badTest_15872_block_26 : Interval badTest_15872 208 216 :=
  interval_of_check badTest_15872 208 8 (by decide +kernel)

theorem badTest_15872_block_27 : Interval badTest_15872 216 224 :=
  interval_of_check badTest_15872 216 8 (by decide +kernel)

theorem badTest_15872_block_28 : Interval badTest_15872 224 232 :=
  interval_of_check badTest_15872 224 8 (by decide +kernel)

theorem badTest_15872_block_29 : Interval badTest_15872 232 240 :=
  interval_of_check badTest_15872 232 8 (by decide +kernel)

theorem badTest_15872_block_30 : Interval badTest_15872 240 248 :=
  interval_of_check badTest_15872 240 8 (by decide +kernel)

theorem badTest_15872_block_31 : Interval badTest_15872 248 256 :=
  interval_of_check badTest_15872 248 8 (by decide +kernel)

theorem badTest_15872_complete : Interval badTest_15872 0 256 :=
  (interval_append badTest_15872 0 128 256
  (interval_append badTest_15872 0 64 128
  (interval_append badTest_15872 0 32 64
  (interval_append badTest_15872 0 16 32
  (interval_append badTest_15872 0 8 16
  badTest_15872_block_0
  badTest_15872_block_1)
  (interval_append badTest_15872 16 24 32
  badTest_15872_block_2
  badTest_15872_block_3))
  (interval_append badTest_15872 32 48 64
  (interval_append badTest_15872 32 40 48
  badTest_15872_block_4
  badTest_15872_block_5)
  (interval_append badTest_15872 48 56 64
  badTest_15872_block_6
  badTest_15872_block_7)))
  (interval_append badTest_15872 64 96 128
  (interval_append badTest_15872 64 80 96
  (interval_append badTest_15872 64 72 80
  badTest_15872_block_8
  badTest_15872_block_9)
  (interval_append badTest_15872 80 88 96
  badTest_15872_block_10
  badTest_15872_block_11))
  (interval_append badTest_15872 96 112 128
  (interval_append badTest_15872 96 104 112
  badTest_15872_block_12
  badTest_15872_block_13)
  (interval_append badTest_15872 112 120 128
  badTest_15872_block_14
  badTest_15872_block_15))))
  (interval_append badTest_15872 128 192 256
  (interval_append badTest_15872 128 160 192
  (interval_append badTest_15872 128 144 160
  (interval_append badTest_15872 128 136 144
  badTest_15872_block_16
  badTest_15872_block_17)
  (interval_append badTest_15872 144 152 160
  badTest_15872_block_18
  badTest_15872_block_19))
  (interval_append badTest_15872 160 176 192
  (interval_append badTest_15872 160 168 176
  badTest_15872_block_20
  badTest_15872_block_21)
  (interval_append badTest_15872 176 184 192
  badTest_15872_block_22
  badTest_15872_block_23)))
  (interval_append badTest_15872 192 224 256
  (interval_append badTest_15872 192 208 224
  (interval_append badTest_15872 192 200 208
  badTest_15872_block_24
  badTest_15872_block_25)
  (interval_append badTest_15872 208 216 224
  badTest_15872_block_26
  badTest_15872_block_27))
  (interval_append badTest_15872 224 240 256
  (interval_append badTest_15872 224 232 240
  badTest_15872_block_28
  badTest_15872_block_29)
  (interval_append badTest_15872 240 248 256
  badTest_15872_block_30
  badTest_15872_block_31)))))
theorem badTestInterval15872 : Interval badTest 15872 16128 := by
  intro i hlo hhi
  have h := badTest_15872_complete (i-15872) (Nat.zero_le _) (by omega)
  simpa only [badTest_15872, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad063 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_16128 (i : Nat) := badTest (i+16128)
theorem badTest_16128_block_0 : Interval badTest_16128 0 8 :=
  interval_of_check badTest_16128 0 8 (by decide +kernel)

theorem badTest_16128_block_1 : Interval badTest_16128 8 16 :=
  interval_of_check badTest_16128 8 8 (by decide +kernel)

theorem badTest_16128_block_2 : Interval badTest_16128 16 24 :=
  interval_of_check badTest_16128 16 8 (by decide +kernel)

theorem badTest_16128_block_3 : Interval badTest_16128 24 32 :=
  interval_of_check badTest_16128 24 8 (by decide +kernel)

theorem badTest_16128_block_4 : Interval badTest_16128 32 40 :=
  interval_of_check badTest_16128 32 8 (by decide +kernel)

theorem badTest_16128_block_5 : Interval badTest_16128 40 48 :=
  interval_of_check badTest_16128 40 8 (by decide +kernel)

theorem badTest_16128_block_6 : Interval badTest_16128 48 56 :=
  interval_of_check badTest_16128 48 8 (by decide +kernel)

theorem badTest_16128_block_7 : Interval badTest_16128 56 64 :=
  interval_of_check badTest_16128 56 8 (by decide +kernel)

theorem badTest_16128_block_8 : Interval badTest_16128 64 72 :=
  interval_of_check badTest_16128 64 8 (by decide +kernel)

theorem badTest_16128_block_9 : Interval badTest_16128 72 80 :=
  interval_of_check badTest_16128 72 8 (by decide +kernel)

theorem badTest_16128_block_10 : Interval badTest_16128 80 88 :=
  interval_of_check badTest_16128 80 8 (by decide +kernel)

theorem badTest_16128_block_11 : Interval badTest_16128 88 96 :=
  interval_of_check badTest_16128 88 8 (by decide +kernel)

theorem badTest_16128_block_12 : Interval badTest_16128 96 104 :=
  interval_of_check badTest_16128 96 8 (by decide +kernel)

theorem badTest_16128_block_13 : Interval badTest_16128 104 112 :=
  interval_of_check badTest_16128 104 8 (by decide +kernel)

theorem badTest_16128_block_14 : Interval badTest_16128 112 120 :=
  interval_of_check badTest_16128 112 8 (by decide +kernel)

theorem badTest_16128_block_15 : Interval badTest_16128 120 128 :=
  interval_of_check badTest_16128 120 8 (by decide +kernel)

theorem badTest_16128_block_16 : Interval badTest_16128 128 136 :=
  interval_of_check badTest_16128 128 8 (by decide +kernel)

theorem badTest_16128_block_17 : Interval badTest_16128 136 144 :=
  interval_of_check badTest_16128 136 8 (by decide +kernel)

theorem badTest_16128_block_18 : Interval badTest_16128 144 152 :=
  interval_of_check badTest_16128 144 8 (by decide +kernel)

theorem badTest_16128_block_19 : Interval badTest_16128 152 160 :=
  interval_of_check badTest_16128 152 8 (by decide +kernel)

theorem badTest_16128_block_20 : Interval badTest_16128 160 168 :=
  interval_of_check badTest_16128 160 8 (by decide +kernel)

theorem badTest_16128_block_21 : Interval badTest_16128 168 176 :=
  interval_of_check badTest_16128 168 8 (by decide +kernel)

theorem badTest_16128_block_22 : Interval badTest_16128 176 184 :=
  interval_of_check badTest_16128 176 8 (by decide +kernel)

theorem badTest_16128_block_23 : Interval badTest_16128 184 192 :=
  interval_of_check badTest_16128 184 8 (by decide +kernel)

theorem badTest_16128_block_24 : Interval badTest_16128 192 200 :=
  interval_of_check badTest_16128 192 8 (by decide +kernel)

theorem badTest_16128_block_25 : Interval badTest_16128 200 208 :=
  interval_of_check badTest_16128 200 8 (by decide +kernel)

theorem badTest_16128_block_26 : Interval badTest_16128 208 216 :=
  interval_of_check badTest_16128 208 8 (by decide +kernel)

theorem badTest_16128_block_27 : Interval badTest_16128 216 224 :=
  interval_of_check badTest_16128 216 8 (by decide +kernel)

theorem badTest_16128_block_28 : Interval badTest_16128 224 232 :=
  interval_of_check badTest_16128 224 8 (by decide +kernel)

theorem badTest_16128_block_29 : Interval badTest_16128 232 240 :=
  interval_of_check badTest_16128 232 8 (by decide +kernel)

theorem badTest_16128_block_30 : Interval badTest_16128 240 248 :=
  interval_of_check badTest_16128 240 8 (by decide +kernel)

theorem badTest_16128_block_31 : Interval badTest_16128 248 256 :=
  interval_of_check badTest_16128 248 8 (by decide +kernel)

theorem badTest_16128_complete : Interval badTest_16128 0 256 :=
  (interval_append badTest_16128 0 128 256
  (interval_append badTest_16128 0 64 128
  (interval_append badTest_16128 0 32 64
  (interval_append badTest_16128 0 16 32
  (interval_append badTest_16128 0 8 16
  badTest_16128_block_0
  badTest_16128_block_1)
  (interval_append badTest_16128 16 24 32
  badTest_16128_block_2
  badTest_16128_block_3))
  (interval_append badTest_16128 32 48 64
  (interval_append badTest_16128 32 40 48
  badTest_16128_block_4
  badTest_16128_block_5)
  (interval_append badTest_16128 48 56 64
  badTest_16128_block_6
  badTest_16128_block_7)))
  (interval_append badTest_16128 64 96 128
  (interval_append badTest_16128 64 80 96
  (interval_append badTest_16128 64 72 80
  badTest_16128_block_8
  badTest_16128_block_9)
  (interval_append badTest_16128 80 88 96
  badTest_16128_block_10
  badTest_16128_block_11))
  (interval_append badTest_16128 96 112 128
  (interval_append badTest_16128 96 104 112
  badTest_16128_block_12
  badTest_16128_block_13)
  (interval_append badTest_16128 112 120 128
  badTest_16128_block_14
  badTest_16128_block_15))))
  (interval_append badTest_16128 128 192 256
  (interval_append badTest_16128 128 160 192
  (interval_append badTest_16128 128 144 160
  (interval_append badTest_16128 128 136 144
  badTest_16128_block_16
  badTest_16128_block_17)
  (interval_append badTest_16128 144 152 160
  badTest_16128_block_18
  badTest_16128_block_19))
  (interval_append badTest_16128 160 176 192
  (interval_append badTest_16128 160 168 176
  badTest_16128_block_20
  badTest_16128_block_21)
  (interval_append badTest_16128 176 184 192
  badTest_16128_block_22
  badTest_16128_block_23)))
  (interval_append badTest_16128 192 224 256
  (interval_append badTest_16128 192 208 224
  (interval_append badTest_16128 192 200 208
  badTest_16128_block_24
  badTest_16128_block_25)
  (interval_append badTest_16128 208 216 224
  badTest_16128_block_26
  badTest_16128_block_27))
  (interval_append badTest_16128 224 240 256
  (interval_append badTest_16128 224 232 240
  badTest_16128_block_28
  badTest_16128_block_29)
  (interval_append badTest_16128 240 248 256
  badTest_16128_block_30
  badTest_16128_block_31)))))
theorem badTestInterval16128 : Interval badTest 16128 16384 := by
  intro i hlo hhi
  have h := badTest_16128_complete (i-16128) (Nat.zero_le _) (by omega)
  simpa only [badTest_16128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad064 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_16384 (i : Nat) := badTest (i+16384)
theorem badTest_16384_block_0 : Interval badTest_16384 0 8 :=
  interval_of_check badTest_16384 0 8 (by decide +kernel)

theorem badTest_16384_block_1 : Interval badTest_16384 8 16 :=
  interval_of_check badTest_16384 8 8 (by decide +kernel)

theorem badTest_16384_block_2 : Interval badTest_16384 16 24 :=
  interval_of_check badTest_16384 16 8 (by decide +kernel)

theorem badTest_16384_block_3 : Interval badTest_16384 24 32 :=
  interval_of_check badTest_16384 24 8 (by decide +kernel)

theorem badTest_16384_block_4 : Interval badTest_16384 32 40 :=
  interval_of_check badTest_16384 32 8 (by decide +kernel)

theorem badTest_16384_block_5 : Interval badTest_16384 40 48 :=
  interval_of_check badTest_16384 40 8 (by decide +kernel)

theorem badTest_16384_block_6 : Interval badTest_16384 48 56 :=
  interval_of_check badTest_16384 48 8 (by decide +kernel)

theorem badTest_16384_block_7 : Interval badTest_16384 56 64 :=
  interval_of_check badTest_16384 56 8 (by decide +kernel)

theorem badTest_16384_block_8 : Interval badTest_16384 64 72 :=
  interval_of_check badTest_16384 64 8 (by decide +kernel)

theorem badTest_16384_block_9 : Interval badTest_16384 72 80 :=
  interval_of_check badTest_16384 72 8 (by decide +kernel)

theorem badTest_16384_block_10 : Interval badTest_16384 80 88 :=
  interval_of_check badTest_16384 80 8 (by decide +kernel)

theorem badTest_16384_block_11 : Interval badTest_16384 88 96 :=
  interval_of_check badTest_16384 88 8 (by decide +kernel)

theorem badTest_16384_block_12 : Interval badTest_16384 96 104 :=
  interval_of_check badTest_16384 96 8 (by decide +kernel)

theorem badTest_16384_block_13 : Interval badTest_16384 104 112 :=
  interval_of_check badTest_16384 104 8 (by decide +kernel)

theorem badTest_16384_block_14 : Interval badTest_16384 112 120 :=
  interval_of_check badTest_16384 112 8 (by decide +kernel)

theorem badTest_16384_block_15 : Interval badTest_16384 120 128 :=
  interval_of_check badTest_16384 120 8 (by decide +kernel)

theorem badTest_16384_block_16 : Interval badTest_16384 128 136 :=
  interval_of_check badTest_16384 128 8 (by decide +kernel)

theorem badTest_16384_block_17 : Interval badTest_16384 136 144 :=
  interval_of_check badTest_16384 136 8 (by decide +kernel)

theorem badTest_16384_block_18 : Interval badTest_16384 144 152 :=
  interval_of_check badTest_16384 144 8 (by decide +kernel)

theorem badTest_16384_block_19 : Interval badTest_16384 152 160 :=
  interval_of_check badTest_16384 152 8 (by decide +kernel)

theorem badTest_16384_block_20 : Interval badTest_16384 160 168 :=
  interval_of_check badTest_16384 160 8 (by decide +kernel)

theorem badTest_16384_block_21 : Interval badTest_16384 168 176 :=
  interval_of_check badTest_16384 168 8 (by decide +kernel)

theorem badTest_16384_block_22 : Interval badTest_16384 176 184 :=
  interval_of_check badTest_16384 176 8 (by decide +kernel)

theorem badTest_16384_block_23 : Interval badTest_16384 184 192 :=
  interval_of_check badTest_16384 184 8 (by decide +kernel)

theorem badTest_16384_block_24 : Interval badTest_16384 192 200 :=
  interval_of_check badTest_16384 192 8 (by decide +kernel)

theorem badTest_16384_block_25 : Interval badTest_16384 200 208 :=
  interval_of_check badTest_16384 200 8 (by decide +kernel)

theorem badTest_16384_block_26 : Interval badTest_16384 208 216 :=
  interval_of_check badTest_16384 208 8 (by decide +kernel)

theorem badTest_16384_block_27 : Interval badTest_16384 216 224 :=
  interval_of_check badTest_16384 216 8 (by decide +kernel)

theorem badTest_16384_block_28 : Interval badTest_16384 224 232 :=
  interval_of_check badTest_16384 224 8 (by decide +kernel)

theorem badTest_16384_block_29 : Interval badTest_16384 232 240 :=
  interval_of_check badTest_16384 232 8 (by decide +kernel)

theorem badTest_16384_block_30 : Interval badTest_16384 240 248 :=
  interval_of_check badTest_16384 240 8 (by decide +kernel)

theorem badTest_16384_block_31 : Interval badTest_16384 248 256 :=
  interval_of_check badTest_16384 248 8 (by decide +kernel)

theorem badTest_16384_complete : Interval badTest_16384 0 256 :=
  (interval_append badTest_16384 0 128 256
  (interval_append badTest_16384 0 64 128
  (interval_append badTest_16384 0 32 64
  (interval_append badTest_16384 0 16 32
  (interval_append badTest_16384 0 8 16
  badTest_16384_block_0
  badTest_16384_block_1)
  (interval_append badTest_16384 16 24 32
  badTest_16384_block_2
  badTest_16384_block_3))
  (interval_append badTest_16384 32 48 64
  (interval_append badTest_16384 32 40 48
  badTest_16384_block_4
  badTest_16384_block_5)
  (interval_append badTest_16384 48 56 64
  badTest_16384_block_6
  badTest_16384_block_7)))
  (interval_append badTest_16384 64 96 128
  (interval_append badTest_16384 64 80 96
  (interval_append badTest_16384 64 72 80
  badTest_16384_block_8
  badTest_16384_block_9)
  (interval_append badTest_16384 80 88 96
  badTest_16384_block_10
  badTest_16384_block_11))
  (interval_append badTest_16384 96 112 128
  (interval_append badTest_16384 96 104 112
  badTest_16384_block_12
  badTest_16384_block_13)
  (interval_append badTest_16384 112 120 128
  badTest_16384_block_14
  badTest_16384_block_15))))
  (interval_append badTest_16384 128 192 256
  (interval_append badTest_16384 128 160 192
  (interval_append badTest_16384 128 144 160
  (interval_append badTest_16384 128 136 144
  badTest_16384_block_16
  badTest_16384_block_17)
  (interval_append badTest_16384 144 152 160
  badTest_16384_block_18
  badTest_16384_block_19))
  (interval_append badTest_16384 160 176 192
  (interval_append badTest_16384 160 168 176
  badTest_16384_block_20
  badTest_16384_block_21)
  (interval_append badTest_16384 176 184 192
  badTest_16384_block_22
  badTest_16384_block_23)))
  (interval_append badTest_16384 192 224 256
  (interval_append badTest_16384 192 208 224
  (interval_append badTest_16384 192 200 208
  badTest_16384_block_24
  badTest_16384_block_25)
  (interval_append badTest_16384 208 216 224
  badTest_16384_block_26
  badTest_16384_block_27))
  (interval_append badTest_16384 224 240 256
  (interval_append badTest_16384 224 232 240
  badTest_16384_block_28
  badTest_16384_block_29)
  (interval_append badTest_16384 240 248 256
  badTest_16384_block_30
  badTest_16384_block_31)))))
theorem badTestInterval16384 : Interval badTest 16384 16640 := by
  intro i hlo hhi
  have h := badTest_16384_complete (i-16384) (Nat.zero_le _) (by omega)
  simpa only [badTest_16384, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad065 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_16640 (i : Nat) := badTest (i+16640)
theorem badTest_16640_block_0 : Interval badTest_16640 0 8 :=
  interval_of_check badTest_16640 0 8 (by decide +kernel)

theorem badTest_16640_block_1 : Interval badTest_16640 8 16 :=
  interval_of_check badTest_16640 8 8 (by decide +kernel)

theorem badTest_16640_block_2 : Interval badTest_16640 16 24 :=
  interval_of_check badTest_16640 16 8 (by decide +kernel)

theorem badTest_16640_block_3 : Interval badTest_16640 24 32 :=
  interval_of_check badTest_16640 24 8 (by decide +kernel)

theorem badTest_16640_block_4 : Interval badTest_16640 32 40 :=
  interval_of_check badTest_16640 32 8 (by decide +kernel)

theorem badTest_16640_block_5 : Interval badTest_16640 40 48 :=
  interval_of_check badTest_16640 40 8 (by decide +kernel)

theorem badTest_16640_block_6 : Interval badTest_16640 48 56 :=
  interval_of_check badTest_16640 48 8 (by decide +kernel)

theorem badTest_16640_block_7 : Interval badTest_16640 56 64 :=
  interval_of_check badTest_16640 56 8 (by decide +kernel)

theorem badTest_16640_block_8 : Interval badTest_16640 64 72 :=
  interval_of_check badTest_16640 64 8 (by decide +kernel)

theorem badTest_16640_block_9 : Interval badTest_16640 72 80 :=
  interval_of_check badTest_16640 72 8 (by decide +kernel)

theorem badTest_16640_block_10 : Interval badTest_16640 80 88 :=
  interval_of_check badTest_16640 80 8 (by decide +kernel)

theorem badTest_16640_block_11 : Interval badTest_16640 88 96 :=
  interval_of_check badTest_16640 88 8 (by decide +kernel)

theorem badTest_16640_block_12 : Interval badTest_16640 96 104 :=
  interval_of_check badTest_16640 96 8 (by decide +kernel)

theorem badTest_16640_block_13 : Interval badTest_16640 104 112 :=
  interval_of_check badTest_16640 104 8 (by decide +kernel)

theorem badTest_16640_block_14 : Interval badTest_16640 112 120 :=
  interval_of_check badTest_16640 112 8 (by decide +kernel)

theorem badTest_16640_block_15 : Interval badTest_16640 120 128 :=
  interval_of_check badTest_16640 120 8 (by decide +kernel)

theorem badTest_16640_block_16 : Interval badTest_16640 128 136 :=
  interval_of_check badTest_16640 128 8 (by decide +kernel)

theorem badTest_16640_block_17 : Interval badTest_16640 136 144 :=
  interval_of_check badTest_16640 136 8 (by decide +kernel)

theorem badTest_16640_block_18 : Interval badTest_16640 144 152 :=
  interval_of_check badTest_16640 144 8 (by decide +kernel)

theorem badTest_16640_block_19 : Interval badTest_16640 152 160 :=
  interval_of_check badTest_16640 152 8 (by decide +kernel)

theorem badTest_16640_block_20 : Interval badTest_16640 160 168 :=
  interval_of_check badTest_16640 160 8 (by decide +kernel)

theorem badTest_16640_block_21 : Interval badTest_16640 168 176 :=
  interval_of_check badTest_16640 168 8 (by decide +kernel)

theorem badTest_16640_block_22 : Interval badTest_16640 176 184 :=
  interval_of_check badTest_16640 176 8 (by decide +kernel)

theorem badTest_16640_block_23 : Interval badTest_16640 184 192 :=
  interval_of_check badTest_16640 184 8 (by decide +kernel)

theorem badTest_16640_block_24 : Interval badTest_16640 192 200 :=
  interval_of_check badTest_16640 192 8 (by decide +kernel)

theorem badTest_16640_block_25 : Interval badTest_16640 200 208 :=
  interval_of_check badTest_16640 200 8 (by decide +kernel)

theorem badTest_16640_block_26 : Interval badTest_16640 208 216 :=
  interval_of_check badTest_16640 208 8 (by decide +kernel)

theorem badTest_16640_block_27 : Interval badTest_16640 216 224 :=
  interval_of_check badTest_16640 216 8 (by decide +kernel)

theorem badTest_16640_block_28 : Interval badTest_16640 224 232 :=
  interval_of_check badTest_16640 224 8 (by decide +kernel)

theorem badTest_16640_block_29 : Interval badTest_16640 232 240 :=
  interval_of_check badTest_16640 232 8 (by decide +kernel)

theorem badTest_16640_block_30 : Interval badTest_16640 240 248 :=
  interval_of_check badTest_16640 240 8 (by decide +kernel)

theorem badTest_16640_block_31 : Interval badTest_16640 248 256 :=
  interval_of_check badTest_16640 248 8 (by decide +kernel)

theorem badTest_16640_complete : Interval badTest_16640 0 256 :=
  (interval_append badTest_16640 0 128 256
  (interval_append badTest_16640 0 64 128
  (interval_append badTest_16640 0 32 64
  (interval_append badTest_16640 0 16 32
  (interval_append badTest_16640 0 8 16
  badTest_16640_block_0
  badTest_16640_block_1)
  (interval_append badTest_16640 16 24 32
  badTest_16640_block_2
  badTest_16640_block_3))
  (interval_append badTest_16640 32 48 64
  (interval_append badTest_16640 32 40 48
  badTest_16640_block_4
  badTest_16640_block_5)
  (interval_append badTest_16640 48 56 64
  badTest_16640_block_6
  badTest_16640_block_7)))
  (interval_append badTest_16640 64 96 128
  (interval_append badTest_16640 64 80 96
  (interval_append badTest_16640 64 72 80
  badTest_16640_block_8
  badTest_16640_block_9)
  (interval_append badTest_16640 80 88 96
  badTest_16640_block_10
  badTest_16640_block_11))
  (interval_append badTest_16640 96 112 128
  (interval_append badTest_16640 96 104 112
  badTest_16640_block_12
  badTest_16640_block_13)
  (interval_append badTest_16640 112 120 128
  badTest_16640_block_14
  badTest_16640_block_15))))
  (interval_append badTest_16640 128 192 256
  (interval_append badTest_16640 128 160 192
  (interval_append badTest_16640 128 144 160
  (interval_append badTest_16640 128 136 144
  badTest_16640_block_16
  badTest_16640_block_17)
  (interval_append badTest_16640 144 152 160
  badTest_16640_block_18
  badTest_16640_block_19))
  (interval_append badTest_16640 160 176 192
  (interval_append badTest_16640 160 168 176
  badTest_16640_block_20
  badTest_16640_block_21)
  (interval_append badTest_16640 176 184 192
  badTest_16640_block_22
  badTest_16640_block_23)))
  (interval_append badTest_16640 192 224 256
  (interval_append badTest_16640 192 208 224
  (interval_append badTest_16640 192 200 208
  badTest_16640_block_24
  badTest_16640_block_25)
  (interval_append badTest_16640 208 216 224
  badTest_16640_block_26
  badTest_16640_block_27))
  (interval_append badTest_16640 224 240 256
  (interval_append badTest_16640 224 232 240
  badTest_16640_block_28
  badTest_16640_block_29)
  (interval_append badTest_16640 240 248 256
  badTest_16640_block_30
  badTest_16640_block_31)))))
theorem badTestInterval16640 : Interval badTest 16640 16896 := by
  intro i hlo hhi
  have h := badTest_16640_complete (i-16640) (Nat.zero_le _) (by omega)
  simpa only [badTest_16640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad066 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_16896 (i : Nat) := badTest (i+16896)
theorem badTest_16896_block_0 : Interval badTest_16896 0 8 :=
  interval_of_check badTest_16896 0 8 (by decide +kernel)

theorem badTest_16896_block_1 : Interval badTest_16896 8 16 :=
  interval_of_check badTest_16896 8 8 (by decide +kernel)

theorem badTest_16896_block_2 : Interval badTest_16896 16 24 :=
  interval_of_check badTest_16896 16 8 (by decide +kernel)

theorem badTest_16896_block_3 : Interval badTest_16896 24 32 :=
  interval_of_check badTest_16896 24 8 (by decide +kernel)

theorem badTest_16896_block_4 : Interval badTest_16896 32 40 :=
  interval_of_check badTest_16896 32 8 (by decide +kernel)

theorem badTest_16896_block_5 : Interval badTest_16896 40 48 :=
  interval_of_check badTest_16896 40 8 (by decide +kernel)

theorem badTest_16896_block_6 : Interval badTest_16896 48 56 :=
  interval_of_check badTest_16896 48 8 (by decide +kernel)

theorem badTest_16896_block_7 : Interval badTest_16896 56 64 :=
  interval_of_check badTest_16896 56 8 (by decide +kernel)

theorem badTest_16896_block_8 : Interval badTest_16896 64 72 :=
  interval_of_check badTest_16896 64 8 (by decide +kernel)

theorem badTest_16896_block_9 : Interval badTest_16896 72 80 :=
  interval_of_check badTest_16896 72 8 (by decide +kernel)

theorem badTest_16896_block_10 : Interval badTest_16896 80 88 :=
  interval_of_check badTest_16896 80 8 (by decide +kernel)

theorem badTest_16896_block_11 : Interval badTest_16896 88 96 :=
  interval_of_check badTest_16896 88 8 (by decide +kernel)

theorem badTest_16896_block_12 : Interval badTest_16896 96 104 :=
  interval_of_check badTest_16896 96 8 (by decide +kernel)

theorem badTest_16896_block_13 : Interval badTest_16896 104 112 :=
  interval_of_check badTest_16896 104 8 (by decide +kernel)

theorem badTest_16896_block_14 : Interval badTest_16896 112 120 :=
  interval_of_check badTest_16896 112 8 (by decide +kernel)

theorem badTest_16896_block_15 : Interval badTest_16896 120 128 :=
  interval_of_check badTest_16896 120 8 (by decide +kernel)

theorem badTest_16896_block_16 : Interval badTest_16896 128 136 :=
  interval_of_check badTest_16896 128 8 (by decide +kernel)

theorem badTest_16896_block_17 : Interval badTest_16896 136 144 :=
  interval_of_check badTest_16896 136 8 (by decide +kernel)

theorem badTest_16896_block_18 : Interval badTest_16896 144 152 :=
  interval_of_check badTest_16896 144 8 (by decide +kernel)

theorem badTest_16896_block_19 : Interval badTest_16896 152 160 :=
  interval_of_check badTest_16896 152 8 (by decide +kernel)

theorem badTest_16896_block_20 : Interval badTest_16896 160 168 :=
  interval_of_check badTest_16896 160 8 (by decide +kernel)

theorem badTest_16896_block_21 : Interval badTest_16896 168 176 :=
  interval_of_check badTest_16896 168 8 (by decide +kernel)

theorem badTest_16896_block_22 : Interval badTest_16896 176 184 :=
  interval_of_check badTest_16896 176 8 (by decide +kernel)

theorem badTest_16896_block_23 : Interval badTest_16896 184 192 :=
  interval_of_check badTest_16896 184 8 (by decide +kernel)

theorem badTest_16896_block_24 : Interval badTest_16896 192 200 :=
  interval_of_check badTest_16896 192 8 (by decide +kernel)

theorem badTest_16896_block_25 : Interval badTest_16896 200 208 :=
  interval_of_check badTest_16896 200 8 (by decide +kernel)

theorem badTest_16896_block_26 : Interval badTest_16896 208 216 :=
  interval_of_check badTest_16896 208 8 (by decide +kernel)

theorem badTest_16896_block_27 : Interval badTest_16896 216 224 :=
  interval_of_check badTest_16896 216 8 (by decide +kernel)

theorem badTest_16896_block_28 : Interval badTest_16896 224 232 :=
  interval_of_check badTest_16896 224 8 (by decide +kernel)

theorem badTest_16896_block_29 : Interval badTest_16896 232 240 :=
  interval_of_check badTest_16896 232 8 (by decide +kernel)

theorem badTest_16896_block_30 : Interval badTest_16896 240 248 :=
  interval_of_check badTest_16896 240 8 (by decide +kernel)

theorem badTest_16896_block_31 : Interval badTest_16896 248 256 :=
  interval_of_check badTest_16896 248 8 (by decide +kernel)

theorem badTest_16896_complete : Interval badTest_16896 0 256 :=
  (interval_append badTest_16896 0 128 256
  (interval_append badTest_16896 0 64 128
  (interval_append badTest_16896 0 32 64
  (interval_append badTest_16896 0 16 32
  (interval_append badTest_16896 0 8 16
  badTest_16896_block_0
  badTest_16896_block_1)
  (interval_append badTest_16896 16 24 32
  badTest_16896_block_2
  badTest_16896_block_3))
  (interval_append badTest_16896 32 48 64
  (interval_append badTest_16896 32 40 48
  badTest_16896_block_4
  badTest_16896_block_5)
  (interval_append badTest_16896 48 56 64
  badTest_16896_block_6
  badTest_16896_block_7)))
  (interval_append badTest_16896 64 96 128
  (interval_append badTest_16896 64 80 96
  (interval_append badTest_16896 64 72 80
  badTest_16896_block_8
  badTest_16896_block_9)
  (interval_append badTest_16896 80 88 96
  badTest_16896_block_10
  badTest_16896_block_11))
  (interval_append badTest_16896 96 112 128
  (interval_append badTest_16896 96 104 112
  badTest_16896_block_12
  badTest_16896_block_13)
  (interval_append badTest_16896 112 120 128
  badTest_16896_block_14
  badTest_16896_block_15))))
  (interval_append badTest_16896 128 192 256
  (interval_append badTest_16896 128 160 192
  (interval_append badTest_16896 128 144 160
  (interval_append badTest_16896 128 136 144
  badTest_16896_block_16
  badTest_16896_block_17)
  (interval_append badTest_16896 144 152 160
  badTest_16896_block_18
  badTest_16896_block_19))
  (interval_append badTest_16896 160 176 192
  (interval_append badTest_16896 160 168 176
  badTest_16896_block_20
  badTest_16896_block_21)
  (interval_append badTest_16896 176 184 192
  badTest_16896_block_22
  badTest_16896_block_23)))
  (interval_append badTest_16896 192 224 256
  (interval_append badTest_16896 192 208 224
  (interval_append badTest_16896 192 200 208
  badTest_16896_block_24
  badTest_16896_block_25)
  (interval_append badTest_16896 208 216 224
  badTest_16896_block_26
  badTest_16896_block_27))
  (interval_append badTest_16896 224 240 256
  (interval_append badTest_16896 224 232 240
  badTest_16896_block_28
  badTest_16896_block_29)
  (interval_append badTest_16896 240 248 256
  badTest_16896_block_30
  badTest_16896_block_31)))))
theorem badTestInterval16896 : Interval badTest 16896 17152 := by
  intro i hlo hhi
  have h := badTest_16896_complete (i-16896) (Nat.zero_le _) (by omega)
  simpa only [badTest_16896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad067 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_17152 (i : Nat) := badTest (i+17152)
theorem badTest_17152_block_0 : Interval badTest_17152 0 8 :=
  interval_of_check badTest_17152 0 8 (by decide +kernel)

theorem badTest_17152_block_1 : Interval badTest_17152 8 16 :=
  interval_of_check badTest_17152 8 8 (by decide +kernel)

theorem badTest_17152_block_2 : Interval badTest_17152 16 24 :=
  interval_of_check badTest_17152 16 8 (by decide +kernel)

theorem badTest_17152_block_3 : Interval badTest_17152 24 32 :=
  interval_of_check badTest_17152 24 8 (by decide +kernel)

theorem badTest_17152_block_4 : Interval badTest_17152 32 40 :=
  interval_of_check badTest_17152 32 8 (by decide +kernel)

theorem badTest_17152_block_5 : Interval badTest_17152 40 48 :=
  interval_of_check badTest_17152 40 8 (by decide +kernel)

theorem badTest_17152_block_6 : Interval badTest_17152 48 56 :=
  interval_of_check badTest_17152 48 8 (by decide +kernel)

theorem badTest_17152_block_7 : Interval badTest_17152 56 64 :=
  interval_of_check badTest_17152 56 8 (by decide +kernel)

theorem badTest_17152_block_8 : Interval badTest_17152 64 72 :=
  interval_of_check badTest_17152 64 8 (by decide +kernel)

theorem badTest_17152_block_9 : Interval badTest_17152 72 80 :=
  interval_of_check badTest_17152 72 8 (by decide +kernel)

theorem badTest_17152_block_10 : Interval badTest_17152 80 88 :=
  interval_of_check badTest_17152 80 8 (by decide +kernel)

theorem badTest_17152_block_11 : Interval badTest_17152 88 96 :=
  interval_of_check badTest_17152 88 8 (by decide +kernel)

theorem badTest_17152_block_12 : Interval badTest_17152 96 104 :=
  interval_of_check badTest_17152 96 8 (by decide +kernel)

theorem badTest_17152_block_13 : Interval badTest_17152 104 112 :=
  interval_of_check badTest_17152 104 8 (by decide +kernel)

theorem badTest_17152_block_14 : Interval badTest_17152 112 120 :=
  interval_of_check badTest_17152 112 8 (by decide +kernel)

theorem badTest_17152_block_15 : Interval badTest_17152 120 128 :=
  interval_of_check badTest_17152 120 8 (by decide +kernel)

theorem badTest_17152_block_16 : Interval badTest_17152 128 136 :=
  interval_of_check badTest_17152 128 8 (by decide +kernel)

theorem badTest_17152_block_17 : Interval badTest_17152 136 144 :=
  interval_of_check badTest_17152 136 8 (by decide +kernel)

theorem badTest_17152_block_18 : Interval badTest_17152 144 152 :=
  interval_of_check badTest_17152 144 8 (by decide +kernel)

theorem badTest_17152_block_19 : Interval badTest_17152 152 160 :=
  interval_of_check badTest_17152 152 8 (by decide +kernel)

theorem badTest_17152_block_20 : Interval badTest_17152 160 168 :=
  interval_of_check badTest_17152 160 8 (by decide +kernel)

theorem badTest_17152_block_21 : Interval badTest_17152 168 176 :=
  interval_of_check badTest_17152 168 8 (by decide +kernel)

theorem badTest_17152_block_22 : Interval badTest_17152 176 184 :=
  interval_of_check badTest_17152 176 8 (by decide +kernel)

theorem badTest_17152_block_23 : Interval badTest_17152 184 192 :=
  interval_of_check badTest_17152 184 8 (by decide +kernel)

theorem badTest_17152_block_24 : Interval badTest_17152 192 200 :=
  interval_of_check badTest_17152 192 8 (by decide +kernel)

theorem badTest_17152_block_25 : Interval badTest_17152 200 208 :=
  interval_of_check badTest_17152 200 8 (by decide +kernel)

theorem badTest_17152_block_26 : Interval badTest_17152 208 216 :=
  interval_of_check badTest_17152 208 8 (by decide +kernel)

theorem badTest_17152_block_27 : Interval badTest_17152 216 224 :=
  interval_of_check badTest_17152 216 8 (by decide +kernel)

theorem badTest_17152_block_28 : Interval badTest_17152 224 232 :=
  interval_of_check badTest_17152 224 8 (by decide +kernel)

theorem badTest_17152_block_29 : Interval badTest_17152 232 240 :=
  interval_of_check badTest_17152 232 8 (by decide +kernel)

theorem badTest_17152_block_30 : Interval badTest_17152 240 248 :=
  interval_of_check badTest_17152 240 8 (by decide +kernel)

theorem badTest_17152_block_31 : Interval badTest_17152 248 256 :=
  interval_of_check badTest_17152 248 8 (by decide +kernel)

theorem badTest_17152_complete : Interval badTest_17152 0 256 :=
  (interval_append badTest_17152 0 128 256
  (interval_append badTest_17152 0 64 128
  (interval_append badTest_17152 0 32 64
  (interval_append badTest_17152 0 16 32
  (interval_append badTest_17152 0 8 16
  badTest_17152_block_0
  badTest_17152_block_1)
  (interval_append badTest_17152 16 24 32
  badTest_17152_block_2
  badTest_17152_block_3))
  (interval_append badTest_17152 32 48 64
  (interval_append badTest_17152 32 40 48
  badTest_17152_block_4
  badTest_17152_block_5)
  (interval_append badTest_17152 48 56 64
  badTest_17152_block_6
  badTest_17152_block_7)))
  (interval_append badTest_17152 64 96 128
  (interval_append badTest_17152 64 80 96
  (interval_append badTest_17152 64 72 80
  badTest_17152_block_8
  badTest_17152_block_9)
  (interval_append badTest_17152 80 88 96
  badTest_17152_block_10
  badTest_17152_block_11))
  (interval_append badTest_17152 96 112 128
  (interval_append badTest_17152 96 104 112
  badTest_17152_block_12
  badTest_17152_block_13)
  (interval_append badTest_17152 112 120 128
  badTest_17152_block_14
  badTest_17152_block_15))))
  (interval_append badTest_17152 128 192 256
  (interval_append badTest_17152 128 160 192
  (interval_append badTest_17152 128 144 160
  (interval_append badTest_17152 128 136 144
  badTest_17152_block_16
  badTest_17152_block_17)
  (interval_append badTest_17152 144 152 160
  badTest_17152_block_18
  badTest_17152_block_19))
  (interval_append badTest_17152 160 176 192
  (interval_append badTest_17152 160 168 176
  badTest_17152_block_20
  badTest_17152_block_21)
  (interval_append badTest_17152 176 184 192
  badTest_17152_block_22
  badTest_17152_block_23)))
  (interval_append badTest_17152 192 224 256
  (interval_append badTest_17152 192 208 224
  (interval_append badTest_17152 192 200 208
  badTest_17152_block_24
  badTest_17152_block_25)
  (interval_append badTest_17152 208 216 224
  badTest_17152_block_26
  badTest_17152_block_27))
  (interval_append badTest_17152 224 240 256
  (interval_append badTest_17152 224 232 240
  badTest_17152_block_28
  badTest_17152_block_29)
  (interval_append badTest_17152 240 248 256
  badTest_17152_block_30
  badTest_17152_block_31)))))
theorem badTestInterval17152 : Interval badTest 17152 17408 := by
  intro i hlo hhi
  have h := badTest_17152_complete (i-17152) (Nat.zero_le _) (by omega)
  simpa only [badTest_17152, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad068 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_17408 (i : Nat) := badTest (i+17408)
theorem badTest_17408_block_0 : Interval badTest_17408 0 8 :=
  interval_of_check badTest_17408 0 8 (by decide +kernel)

theorem badTest_17408_block_1 : Interval badTest_17408 8 16 :=
  interval_of_check badTest_17408 8 8 (by decide +kernel)

theorem badTest_17408_block_2 : Interval badTest_17408 16 24 :=
  interval_of_check badTest_17408 16 8 (by decide +kernel)

theorem badTest_17408_block_3 : Interval badTest_17408 24 32 :=
  interval_of_check badTest_17408 24 8 (by decide +kernel)

theorem badTest_17408_block_4 : Interval badTest_17408 32 40 :=
  interval_of_check badTest_17408 32 8 (by decide +kernel)

theorem badTest_17408_block_5 : Interval badTest_17408 40 48 :=
  interval_of_check badTest_17408 40 8 (by decide +kernel)

theorem badTest_17408_block_6 : Interval badTest_17408 48 56 :=
  interval_of_check badTest_17408 48 8 (by decide +kernel)

theorem badTest_17408_block_7 : Interval badTest_17408 56 64 :=
  interval_of_check badTest_17408 56 8 (by decide +kernel)

theorem badTest_17408_block_8 : Interval badTest_17408 64 72 :=
  interval_of_check badTest_17408 64 8 (by decide +kernel)

theorem badTest_17408_block_9 : Interval badTest_17408 72 80 :=
  interval_of_check badTest_17408 72 8 (by decide +kernel)

theorem badTest_17408_block_10 : Interval badTest_17408 80 88 :=
  interval_of_check badTest_17408 80 8 (by decide +kernel)

theorem badTest_17408_block_11 : Interval badTest_17408 88 96 :=
  interval_of_check badTest_17408 88 8 (by decide +kernel)

theorem badTest_17408_block_12 : Interval badTest_17408 96 104 :=
  interval_of_check badTest_17408 96 8 (by decide +kernel)

theorem badTest_17408_block_13 : Interval badTest_17408 104 112 :=
  interval_of_check badTest_17408 104 8 (by decide +kernel)

theorem badTest_17408_block_14 : Interval badTest_17408 112 120 :=
  interval_of_check badTest_17408 112 8 (by decide +kernel)

theorem badTest_17408_block_15 : Interval badTest_17408 120 128 :=
  interval_of_check badTest_17408 120 8 (by decide +kernel)

theorem badTest_17408_block_16 : Interval badTest_17408 128 136 :=
  interval_of_check badTest_17408 128 8 (by decide +kernel)

theorem badTest_17408_block_17 : Interval badTest_17408 136 144 :=
  interval_of_check badTest_17408 136 8 (by decide +kernel)

theorem badTest_17408_block_18 : Interval badTest_17408 144 152 :=
  interval_of_check badTest_17408 144 8 (by decide +kernel)

theorem badTest_17408_block_19 : Interval badTest_17408 152 160 :=
  interval_of_check badTest_17408 152 8 (by decide +kernel)

theorem badTest_17408_block_20 : Interval badTest_17408 160 168 :=
  interval_of_check badTest_17408 160 8 (by decide +kernel)

theorem badTest_17408_block_21 : Interval badTest_17408 168 176 :=
  interval_of_check badTest_17408 168 8 (by decide +kernel)

theorem badTest_17408_block_22 : Interval badTest_17408 176 184 :=
  interval_of_check badTest_17408 176 8 (by decide +kernel)

theorem badTest_17408_block_23 : Interval badTest_17408 184 192 :=
  interval_of_check badTest_17408 184 8 (by decide +kernel)

theorem badTest_17408_block_24 : Interval badTest_17408 192 200 :=
  interval_of_check badTest_17408 192 8 (by decide +kernel)

theorem badTest_17408_block_25 : Interval badTest_17408 200 208 :=
  interval_of_check badTest_17408 200 8 (by decide +kernel)

theorem badTest_17408_block_26 : Interval badTest_17408 208 216 :=
  interval_of_check badTest_17408 208 8 (by decide +kernel)

theorem badTest_17408_block_27 : Interval badTest_17408 216 224 :=
  interval_of_check badTest_17408 216 8 (by decide +kernel)

theorem badTest_17408_block_28 : Interval badTest_17408 224 232 :=
  interval_of_check badTest_17408 224 8 (by decide +kernel)

theorem badTest_17408_block_29 : Interval badTest_17408 232 240 :=
  interval_of_check badTest_17408 232 8 (by decide +kernel)

theorem badTest_17408_block_30 : Interval badTest_17408 240 248 :=
  interval_of_check badTest_17408 240 8 (by decide +kernel)

theorem badTest_17408_block_31 : Interval badTest_17408 248 256 :=
  interval_of_check badTest_17408 248 8 (by decide +kernel)

theorem badTest_17408_complete : Interval badTest_17408 0 256 :=
  (interval_append badTest_17408 0 128 256
  (interval_append badTest_17408 0 64 128
  (interval_append badTest_17408 0 32 64
  (interval_append badTest_17408 0 16 32
  (interval_append badTest_17408 0 8 16
  badTest_17408_block_0
  badTest_17408_block_1)
  (interval_append badTest_17408 16 24 32
  badTest_17408_block_2
  badTest_17408_block_3))
  (interval_append badTest_17408 32 48 64
  (interval_append badTest_17408 32 40 48
  badTest_17408_block_4
  badTest_17408_block_5)
  (interval_append badTest_17408 48 56 64
  badTest_17408_block_6
  badTest_17408_block_7)))
  (interval_append badTest_17408 64 96 128
  (interval_append badTest_17408 64 80 96
  (interval_append badTest_17408 64 72 80
  badTest_17408_block_8
  badTest_17408_block_9)
  (interval_append badTest_17408 80 88 96
  badTest_17408_block_10
  badTest_17408_block_11))
  (interval_append badTest_17408 96 112 128
  (interval_append badTest_17408 96 104 112
  badTest_17408_block_12
  badTest_17408_block_13)
  (interval_append badTest_17408 112 120 128
  badTest_17408_block_14
  badTest_17408_block_15))))
  (interval_append badTest_17408 128 192 256
  (interval_append badTest_17408 128 160 192
  (interval_append badTest_17408 128 144 160
  (interval_append badTest_17408 128 136 144
  badTest_17408_block_16
  badTest_17408_block_17)
  (interval_append badTest_17408 144 152 160
  badTest_17408_block_18
  badTest_17408_block_19))
  (interval_append badTest_17408 160 176 192
  (interval_append badTest_17408 160 168 176
  badTest_17408_block_20
  badTest_17408_block_21)
  (interval_append badTest_17408 176 184 192
  badTest_17408_block_22
  badTest_17408_block_23)))
  (interval_append badTest_17408 192 224 256
  (interval_append badTest_17408 192 208 224
  (interval_append badTest_17408 192 200 208
  badTest_17408_block_24
  badTest_17408_block_25)
  (interval_append badTest_17408 208 216 224
  badTest_17408_block_26
  badTest_17408_block_27))
  (interval_append badTest_17408 224 240 256
  (interval_append badTest_17408 224 232 240
  badTest_17408_block_28
  badTest_17408_block_29)
  (interval_append badTest_17408 240 248 256
  badTest_17408_block_30
  badTest_17408_block_31)))))
theorem badTestInterval17408 : Interval badTest 17408 17664 := by
  intro i hlo hhi
  have h := badTest_17408_complete (i-17408) (Nat.zero_le _) (by omega)
  simpa only [badTest_17408, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad069 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_17664 (i : Nat) := badTest (i+17664)
theorem badTest_17664_block_0 : Interval badTest_17664 0 8 :=
  interval_of_check badTest_17664 0 8 (by decide +kernel)

theorem badTest_17664_block_1 : Interval badTest_17664 8 16 :=
  interval_of_check badTest_17664 8 8 (by decide +kernel)

theorem badTest_17664_block_2 : Interval badTest_17664 16 24 :=
  interval_of_check badTest_17664 16 8 (by decide +kernel)

theorem badTest_17664_block_3 : Interval badTest_17664 24 32 :=
  interval_of_check badTest_17664 24 8 (by decide +kernel)

theorem badTest_17664_block_4 : Interval badTest_17664 32 40 :=
  interval_of_check badTest_17664 32 8 (by decide +kernel)

theorem badTest_17664_block_5 : Interval badTest_17664 40 48 :=
  interval_of_check badTest_17664 40 8 (by decide +kernel)

theorem badTest_17664_block_6 : Interval badTest_17664 48 56 :=
  interval_of_check badTest_17664 48 8 (by decide +kernel)

theorem badTest_17664_block_7 : Interval badTest_17664 56 64 :=
  interval_of_check badTest_17664 56 8 (by decide +kernel)

theorem badTest_17664_block_8 : Interval badTest_17664 64 72 :=
  interval_of_check badTest_17664 64 8 (by decide +kernel)

theorem badTest_17664_block_9 : Interval badTest_17664 72 80 :=
  interval_of_check badTest_17664 72 8 (by decide +kernel)

theorem badTest_17664_block_10 : Interval badTest_17664 80 88 :=
  interval_of_check badTest_17664 80 8 (by decide +kernel)

theorem badTest_17664_block_11 : Interval badTest_17664 88 96 :=
  interval_of_check badTest_17664 88 8 (by decide +kernel)

theorem badTest_17664_block_12 : Interval badTest_17664 96 104 :=
  interval_of_check badTest_17664 96 8 (by decide +kernel)

theorem badTest_17664_block_13 : Interval badTest_17664 104 112 :=
  interval_of_check badTest_17664 104 8 (by decide +kernel)

theorem badTest_17664_block_14 : Interval badTest_17664 112 120 :=
  interval_of_check badTest_17664 112 8 (by decide +kernel)

theorem badTest_17664_block_15 : Interval badTest_17664 120 128 :=
  interval_of_check badTest_17664 120 8 (by decide +kernel)

theorem badTest_17664_block_16 : Interval badTest_17664 128 136 :=
  interval_of_check badTest_17664 128 8 (by decide +kernel)

theorem badTest_17664_block_17 : Interval badTest_17664 136 144 :=
  interval_of_check badTest_17664 136 8 (by decide +kernel)

theorem badTest_17664_block_18 : Interval badTest_17664 144 152 :=
  interval_of_check badTest_17664 144 8 (by decide +kernel)

theorem badTest_17664_block_19 : Interval badTest_17664 152 160 :=
  interval_of_check badTest_17664 152 8 (by decide +kernel)

theorem badTest_17664_block_20 : Interval badTest_17664 160 168 :=
  interval_of_check badTest_17664 160 8 (by decide +kernel)

theorem badTest_17664_block_21 : Interval badTest_17664 168 176 :=
  interval_of_check badTest_17664 168 8 (by decide +kernel)

theorem badTest_17664_block_22 : Interval badTest_17664 176 184 :=
  interval_of_check badTest_17664 176 8 (by decide +kernel)

theorem badTest_17664_block_23 : Interval badTest_17664 184 192 :=
  interval_of_check badTest_17664 184 8 (by decide +kernel)

theorem badTest_17664_block_24 : Interval badTest_17664 192 200 :=
  interval_of_check badTest_17664 192 8 (by decide +kernel)

theorem badTest_17664_block_25 : Interval badTest_17664 200 208 :=
  interval_of_check badTest_17664 200 8 (by decide +kernel)

theorem badTest_17664_block_26 : Interval badTest_17664 208 216 :=
  interval_of_check badTest_17664 208 8 (by decide +kernel)

theorem badTest_17664_block_27 : Interval badTest_17664 216 224 :=
  interval_of_check badTest_17664 216 8 (by decide +kernel)

theorem badTest_17664_block_28 : Interval badTest_17664 224 232 :=
  interval_of_check badTest_17664 224 8 (by decide +kernel)

theorem badTest_17664_block_29 : Interval badTest_17664 232 240 :=
  interval_of_check badTest_17664 232 8 (by decide +kernel)

theorem badTest_17664_block_30 : Interval badTest_17664 240 248 :=
  interval_of_check badTest_17664 240 8 (by decide +kernel)

theorem badTest_17664_block_31 : Interval badTest_17664 248 256 :=
  interval_of_check badTest_17664 248 8 (by decide +kernel)

theorem badTest_17664_complete : Interval badTest_17664 0 256 :=
  (interval_append badTest_17664 0 128 256
  (interval_append badTest_17664 0 64 128
  (interval_append badTest_17664 0 32 64
  (interval_append badTest_17664 0 16 32
  (interval_append badTest_17664 0 8 16
  badTest_17664_block_0
  badTest_17664_block_1)
  (interval_append badTest_17664 16 24 32
  badTest_17664_block_2
  badTest_17664_block_3))
  (interval_append badTest_17664 32 48 64
  (interval_append badTest_17664 32 40 48
  badTest_17664_block_4
  badTest_17664_block_5)
  (interval_append badTest_17664 48 56 64
  badTest_17664_block_6
  badTest_17664_block_7)))
  (interval_append badTest_17664 64 96 128
  (interval_append badTest_17664 64 80 96
  (interval_append badTest_17664 64 72 80
  badTest_17664_block_8
  badTest_17664_block_9)
  (interval_append badTest_17664 80 88 96
  badTest_17664_block_10
  badTest_17664_block_11))
  (interval_append badTest_17664 96 112 128
  (interval_append badTest_17664 96 104 112
  badTest_17664_block_12
  badTest_17664_block_13)
  (interval_append badTest_17664 112 120 128
  badTest_17664_block_14
  badTest_17664_block_15))))
  (interval_append badTest_17664 128 192 256
  (interval_append badTest_17664 128 160 192
  (interval_append badTest_17664 128 144 160
  (interval_append badTest_17664 128 136 144
  badTest_17664_block_16
  badTest_17664_block_17)
  (interval_append badTest_17664 144 152 160
  badTest_17664_block_18
  badTest_17664_block_19))
  (interval_append badTest_17664 160 176 192
  (interval_append badTest_17664 160 168 176
  badTest_17664_block_20
  badTest_17664_block_21)
  (interval_append badTest_17664 176 184 192
  badTest_17664_block_22
  badTest_17664_block_23)))
  (interval_append badTest_17664 192 224 256
  (interval_append badTest_17664 192 208 224
  (interval_append badTest_17664 192 200 208
  badTest_17664_block_24
  badTest_17664_block_25)
  (interval_append badTest_17664 208 216 224
  badTest_17664_block_26
  badTest_17664_block_27))
  (interval_append badTest_17664 224 240 256
  (interval_append badTest_17664 224 232 240
  badTest_17664_block_28
  badTest_17664_block_29)
  (interval_append badTest_17664 240 248 256
  badTest_17664_block_30
  badTest_17664_block_31)))))
theorem badTestInterval17664 : Interval badTest 17664 17920 := by
  intro i hlo hhi
  have h := badTest_17664_complete (i-17664) (Nat.zero_le _) (by omega)
  simpa only [badTest_17664, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad070 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_17920 (i : Nat) := badTest (i+17920)
theorem badTest_17920_block_0 : Interval badTest_17920 0 8 :=
  interval_of_check badTest_17920 0 8 (by decide +kernel)

theorem badTest_17920_block_1 : Interval badTest_17920 8 16 :=
  interval_of_check badTest_17920 8 8 (by decide +kernel)

theorem badTest_17920_block_2 : Interval badTest_17920 16 24 :=
  interval_of_check badTest_17920 16 8 (by decide +kernel)

theorem badTest_17920_block_3 : Interval badTest_17920 24 32 :=
  interval_of_check badTest_17920 24 8 (by decide +kernel)

theorem badTest_17920_block_4 : Interval badTest_17920 32 40 :=
  interval_of_check badTest_17920 32 8 (by decide +kernel)

theorem badTest_17920_block_5 : Interval badTest_17920 40 48 :=
  interval_of_check badTest_17920 40 8 (by decide +kernel)

theorem badTest_17920_block_6 : Interval badTest_17920 48 56 :=
  interval_of_check badTest_17920 48 8 (by decide +kernel)

theorem badTest_17920_block_7 : Interval badTest_17920 56 64 :=
  interval_of_check badTest_17920 56 8 (by decide +kernel)

theorem badTest_17920_block_8 : Interval badTest_17920 64 72 :=
  interval_of_check badTest_17920 64 8 (by decide +kernel)

theorem badTest_17920_block_9 : Interval badTest_17920 72 80 :=
  interval_of_check badTest_17920 72 8 (by decide +kernel)

theorem badTest_17920_block_10 : Interval badTest_17920 80 88 :=
  interval_of_check badTest_17920 80 8 (by decide +kernel)

theorem badTest_17920_block_11 : Interval badTest_17920 88 96 :=
  interval_of_check badTest_17920 88 8 (by decide +kernel)

theorem badTest_17920_block_12 : Interval badTest_17920 96 104 :=
  interval_of_check badTest_17920 96 8 (by decide +kernel)

theorem badTest_17920_block_13 : Interval badTest_17920 104 112 :=
  interval_of_check badTest_17920 104 8 (by decide +kernel)

theorem badTest_17920_block_14 : Interval badTest_17920 112 120 :=
  interval_of_check badTest_17920 112 8 (by decide +kernel)

theorem badTest_17920_block_15 : Interval badTest_17920 120 128 :=
  interval_of_check badTest_17920 120 8 (by decide +kernel)

theorem badTest_17920_block_16 : Interval badTest_17920 128 136 :=
  interval_of_check badTest_17920 128 8 (by decide +kernel)

theorem badTest_17920_block_17 : Interval badTest_17920 136 144 :=
  interval_of_check badTest_17920 136 8 (by decide +kernel)

theorem badTest_17920_block_18 : Interval badTest_17920 144 152 :=
  interval_of_check badTest_17920 144 8 (by decide +kernel)

theorem badTest_17920_block_19 : Interval badTest_17920 152 160 :=
  interval_of_check badTest_17920 152 8 (by decide +kernel)

theorem badTest_17920_block_20 : Interval badTest_17920 160 168 :=
  interval_of_check badTest_17920 160 8 (by decide +kernel)

theorem badTest_17920_block_21 : Interval badTest_17920 168 176 :=
  interval_of_check badTest_17920 168 8 (by decide +kernel)

theorem badTest_17920_block_22 : Interval badTest_17920 176 184 :=
  interval_of_check badTest_17920 176 8 (by decide +kernel)

theorem badTest_17920_block_23 : Interval badTest_17920 184 192 :=
  interval_of_check badTest_17920 184 8 (by decide +kernel)

theorem badTest_17920_block_24 : Interval badTest_17920 192 200 :=
  interval_of_check badTest_17920 192 8 (by decide +kernel)

theorem badTest_17920_block_25 : Interval badTest_17920 200 208 :=
  interval_of_check badTest_17920 200 8 (by decide +kernel)

theorem badTest_17920_block_26 : Interval badTest_17920 208 216 :=
  interval_of_check badTest_17920 208 8 (by decide +kernel)

theorem badTest_17920_block_27 : Interval badTest_17920 216 224 :=
  interval_of_check badTest_17920 216 8 (by decide +kernel)

theorem badTest_17920_block_28 : Interval badTest_17920 224 232 :=
  interval_of_check badTest_17920 224 8 (by decide +kernel)

theorem badTest_17920_block_29 : Interval badTest_17920 232 240 :=
  interval_of_check badTest_17920 232 8 (by decide +kernel)

theorem badTest_17920_block_30 : Interval badTest_17920 240 248 :=
  interval_of_check badTest_17920 240 8 (by decide +kernel)

theorem badTest_17920_block_31 : Interval badTest_17920 248 256 :=
  interval_of_check badTest_17920 248 8 (by decide +kernel)

theorem badTest_17920_complete : Interval badTest_17920 0 256 :=
  (interval_append badTest_17920 0 128 256
  (interval_append badTest_17920 0 64 128
  (interval_append badTest_17920 0 32 64
  (interval_append badTest_17920 0 16 32
  (interval_append badTest_17920 0 8 16
  badTest_17920_block_0
  badTest_17920_block_1)
  (interval_append badTest_17920 16 24 32
  badTest_17920_block_2
  badTest_17920_block_3))
  (interval_append badTest_17920 32 48 64
  (interval_append badTest_17920 32 40 48
  badTest_17920_block_4
  badTest_17920_block_5)
  (interval_append badTest_17920 48 56 64
  badTest_17920_block_6
  badTest_17920_block_7)))
  (interval_append badTest_17920 64 96 128
  (interval_append badTest_17920 64 80 96
  (interval_append badTest_17920 64 72 80
  badTest_17920_block_8
  badTest_17920_block_9)
  (interval_append badTest_17920 80 88 96
  badTest_17920_block_10
  badTest_17920_block_11))
  (interval_append badTest_17920 96 112 128
  (interval_append badTest_17920 96 104 112
  badTest_17920_block_12
  badTest_17920_block_13)
  (interval_append badTest_17920 112 120 128
  badTest_17920_block_14
  badTest_17920_block_15))))
  (interval_append badTest_17920 128 192 256
  (interval_append badTest_17920 128 160 192
  (interval_append badTest_17920 128 144 160
  (interval_append badTest_17920 128 136 144
  badTest_17920_block_16
  badTest_17920_block_17)
  (interval_append badTest_17920 144 152 160
  badTest_17920_block_18
  badTest_17920_block_19))
  (interval_append badTest_17920 160 176 192
  (interval_append badTest_17920 160 168 176
  badTest_17920_block_20
  badTest_17920_block_21)
  (interval_append badTest_17920 176 184 192
  badTest_17920_block_22
  badTest_17920_block_23)))
  (interval_append badTest_17920 192 224 256
  (interval_append badTest_17920 192 208 224
  (interval_append badTest_17920 192 200 208
  badTest_17920_block_24
  badTest_17920_block_25)
  (interval_append badTest_17920 208 216 224
  badTest_17920_block_26
  badTest_17920_block_27))
  (interval_append badTest_17920 224 240 256
  (interval_append badTest_17920 224 232 240
  badTest_17920_block_28
  badTest_17920_block_29)
  (interval_append badTest_17920 240 248 256
  badTest_17920_block_30
  badTest_17920_block_31)))))
theorem badTestInterval17920 : Interval badTest 17920 18176 := by
  intro i hlo hhi
  have h := badTest_17920_complete (i-17920) (Nat.zero_le _) (by omega)
  simpa only [badTest_17920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad071 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_18176 (i : Nat) := badTest (i+18176)
theorem badTest_18176_block_0 : Interval badTest_18176 0 8 :=
  interval_of_check badTest_18176 0 8 (by decide +kernel)

theorem badTest_18176_block_1 : Interval badTest_18176 8 16 :=
  interval_of_check badTest_18176 8 8 (by decide +kernel)

theorem badTest_18176_block_2 : Interval badTest_18176 16 24 :=
  interval_of_check badTest_18176 16 8 (by decide +kernel)

theorem badTest_18176_block_3 : Interval badTest_18176 24 32 :=
  interval_of_check badTest_18176 24 8 (by decide +kernel)

theorem badTest_18176_block_4 : Interval badTest_18176 32 40 :=
  interval_of_check badTest_18176 32 8 (by decide +kernel)

theorem badTest_18176_block_5 : Interval badTest_18176 40 48 :=
  interval_of_check badTest_18176 40 8 (by decide +kernel)

theorem badTest_18176_block_6 : Interval badTest_18176 48 56 :=
  interval_of_check badTest_18176 48 8 (by decide +kernel)

theorem badTest_18176_block_7 : Interval badTest_18176 56 64 :=
  interval_of_check badTest_18176 56 8 (by decide +kernel)

theorem badTest_18176_block_8 : Interval badTest_18176 64 72 :=
  interval_of_check badTest_18176 64 8 (by decide +kernel)

theorem badTest_18176_block_9 : Interval badTest_18176 72 80 :=
  interval_of_check badTest_18176 72 8 (by decide +kernel)

theorem badTest_18176_block_10 : Interval badTest_18176 80 88 :=
  interval_of_check badTest_18176 80 8 (by decide +kernel)

theorem badTest_18176_block_11 : Interval badTest_18176 88 96 :=
  interval_of_check badTest_18176 88 8 (by decide +kernel)

theorem badTest_18176_block_12 : Interval badTest_18176 96 104 :=
  interval_of_check badTest_18176 96 8 (by decide +kernel)

theorem badTest_18176_block_13 : Interval badTest_18176 104 112 :=
  interval_of_check badTest_18176 104 8 (by decide +kernel)

theorem badTest_18176_block_14 : Interval badTest_18176 112 120 :=
  interval_of_check badTest_18176 112 8 (by decide +kernel)

theorem badTest_18176_block_15 : Interval badTest_18176 120 128 :=
  interval_of_check badTest_18176 120 8 (by decide +kernel)

theorem badTest_18176_block_16 : Interval badTest_18176 128 136 :=
  interval_of_check badTest_18176 128 8 (by decide +kernel)

theorem badTest_18176_block_17 : Interval badTest_18176 136 144 :=
  interval_of_check badTest_18176 136 8 (by decide +kernel)

theorem badTest_18176_block_18 : Interval badTest_18176 144 152 :=
  interval_of_check badTest_18176 144 8 (by decide +kernel)

theorem badTest_18176_block_19 : Interval badTest_18176 152 160 :=
  interval_of_check badTest_18176 152 8 (by decide +kernel)

theorem badTest_18176_block_20 : Interval badTest_18176 160 168 :=
  interval_of_check badTest_18176 160 8 (by decide +kernel)

theorem badTest_18176_block_21 : Interval badTest_18176 168 176 :=
  interval_of_check badTest_18176 168 8 (by decide +kernel)

theorem badTest_18176_block_22 : Interval badTest_18176 176 184 :=
  interval_of_check badTest_18176 176 8 (by decide +kernel)

theorem badTest_18176_block_23 : Interval badTest_18176 184 192 :=
  interval_of_check badTest_18176 184 8 (by decide +kernel)

theorem badTest_18176_block_24 : Interval badTest_18176 192 200 :=
  interval_of_check badTest_18176 192 8 (by decide +kernel)

theorem badTest_18176_block_25 : Interval badTest_18176 200 208 :=
  interval_of_check badTest_18176 200 8 (by decide +kernel)

theorem badTest_18176_block_26 : Interval badTest_18176 208 216 :=
  interval_of_check badTest_18176 208 8 (by decide +kernel)

theorem badTest_18176_block_27 : Interval badTest_18176 216 224 :=
  interval_of_check badTest_18176 216 8 (by decide +kernel)

theorem badTest_18176_block_28 : Interval badTest_18176 224 232 :=
  interval_of_check badTest_18176 224 8 (by decide +kernel)

theorem badTest_18176_block_29 : Interval badTest_18176 232 240 :=
  interval_of_check badTest_18176 232 8 (by decide +kernel)

theorem badTest_18176_block_30 : Interval badTest_18176 240 248 :=
  interval_of_check badTest_18176 240 8 (by decide +kernel)

theorem badTest_18176_block_31 : Interval badTest_18176 248 256 :=
  interval_of_check badTest_18176 248 8 (by decide +kernel)

theorem badTest_18176_complete : Interval badTest_18176 0 256 :=
  (interval_append badTest_18176 0 128 256
  (interval_append badTest_18176 0 64 128
  (interval_append badTest_18176 0 32 64
  (interval_append badTest_18176 0 16 32
  (interval_append badTest_18176 0 8 16
  badTest_18176_block_0
  badTest_18176_block_1)
  (interval_append badTest_18176 16 24 32
  badTest_18176_block_2
  badTest_18176_block_3))
  (interval_append badTest_18176 32 48 64
  (interval_append badTest_18176 32 40 48
  badTest_18176_block_4
  badTest_18176_block_5)
  (interval_append badTest_18176 48 56 64
  badTest_18176_block_6
  badTest_18176_block_7)))
  (interval_append badTest_18176 64 96 128
  (interval_append badTest_18176 64 80 96
  (interval_append badTest_18176 64 72 80
  badTest_18176_block_8
  badTest_18176_block_9)
  (interval_append badTest_18176 80 88 96
  badTest_18176_block_10
  badTest_18176_block_11))
  (interval_append badTest_18176 96 112 128
  (interval_append badTest_18176 96 104 112
  badTest_18176_block_12
  badTest_18176_block_13)
  (interval_append badTest_18176 112 120 128
  badTest_18176_block_14
  badTest_18176_block_15))))
  (interval_append badTest_18176 128 192 256
  (interval_append badTest_18176 128 160 192
  (interval_append badTest_18176 128 144 160
  (interval_append badTest_18176 128 136 144
  badTest_18176_block_16
  badTest_18176_block_17)
  (interval_append badTest_18176 144 152 160
  badTest_18176_block_18
  badTest_18176_block_19))
  (interval_append badTest_18176 160 176 192
  (interval_append badTest_18176 160 168 176
  badTest_18176_block_20
  badTest_18176_block_21)
  (interval_append badTest_18176 176 184 192
  badTest_18176_block_22
  badTest_18176_block_23)))
  (interval_append badTest_18176 192 224 256
  (interval_append badTest_18176 192 208 224
  (interval_append badTest_18176 192 200 208
  badTest_18176_block_24
  badTest_18176_block_25)
  (interval_append badTest_18176 208 216 224
  badTest_18176_block_26
  badTest_18176_block_27))
  (interval_append badTest_18176 224 240 256
  (interval_append badTest_18176 224 232 240
  badTest_18176_block_28
  badTest_18176_block_29)
  (interval_append badTest_18176 240 248 256
  badTest_18176_block_30
  badTest_18176_block_31)))))
theorem badTestInterval18176 : Interval badTest 18176 18432 := by
  intro i hlo hhi
  have h := badTest_18176_complete (i-18176) (Nat.zero_le _) (by omega)
  simpa only [badTest_18176, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad072 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_18432 (i : Nat) := badTest (i+18432)
theorem badTest_18432_block_0 : Interval badTest_18432 0 8 :=
  interval_of_check badTest_18432 0 8 (by decide +kernel)

theorem badTest_18432_block_1 : Interval badTest_18432 8 16 :=
  interval_of_check badTest_18432 8 8 (by decide +kernel)

theorem badTest_18432_block_2 : Interval badTest_18432 16 24 :=
  interval_of_check badTest_18432 16 8 (by decide +kernel)

theorem badTest_18432_block_3 : Interval badTest_18432 24 32 :=
  interval_of_check badTest_18432 24 8 (by decide +kernel)

theorem badTest_18432_block_4 : Interval badTest_18432 32 40 :=
  interval_of_check badTest_18432 32 8 (by decide +kernel)

theorem badTest_18432_block_5 : Interval badTest_18432 40 48 :=
  interval_of_check badTest_18432 40 8 (by decide +kernel)

theorem badTest_18432_block_6 : Interval badTest_18432 48 56 :=
  interval_of_check badTest_18432 48 8 (by decide +kernel)

theorem badTest_18432_block_7 : Interval badTest_18432 56 64 :=
  interval_of_check badTest_18432 56 8 (by decide +kernel)

theorem badTest_18432_block_8 : Interval badTest_18432 64 72 :=
  interval_of_check badTest_18432 64 8 (by decide +kernel)

theorem badTest_18432_block_9 : Interval badTest_18432 72 80 :=
  interval_of_check badTest_18432 72 8 (by decide +kernel)

theorem badTest_18432_block_10 : Interval badTest_18432 80 88 :=
  interval_of_check badTest_18432 80 8 (by decide +kernel)

theorem badTest_18432_block_11 : Interval badTest_18432 88 96 :=
  interval_of_check badTest_18432 88 8 (by decide +kernel)

theorem badTest_18432_block_12 : Interval badTest_18432 96 104 :=
  interval_of_check badTest_18432 96 8 (by decide +kernel)

theorem badTest_18432_block_13 : Interval badTest_18432 104 112 :=
  interval_of_check badTest_18432 104 8 (by decide +kernel)

theorem badTest_18432_block_14 : Interval badTest_18432 112 120 :=
  interval_of_check badTest_18432 112 8 (by decide +kernel)

theorem badTest_18432_block_15 : Interval badTest_18432 120 128 :=
  interval_of_check badTest_18432 120 8 (by decide +kernel)

theorem badTest_18432_block_16 : Interval badTest_18432 128 136 :=
  interval_of_check badTest_18432 128 8 (by decide +kernel)

theorem badTest_18432_block_17 : Interval badTest_18432 136 144 :=
  interval_of_check badTest_18432 136 8 (by decide +kernel)

theorem badTest_18432_block_18 : Interval badTest_18432 144 152 :=
  interval_of_check badTest_18432 144 8 (by decide +kernel)

theorem badTest_18432_block_19 : Interval badTest_18432 152 160 :=
  interval_of_check badTest_18432 152 8 (by decide +kernel)

theorem badTest_18432_block_20 : Interval badTest_18432 160 168 :=
  interval_of_check badTest_18432 160 8 (by decide +kernel)

theorem badTest_18432_block_21 : Interval badTest_18432 168 176 :=
  interval_of_check badTest_18432 168 8 (by decide +kernel)

theorem badTest_18432_block_22 : Interval badTest_18432 176 184 :=
  interval_of_check badTest_18432 176 8 (by decide +kernel)

theorem badTest_18432_block_23 : Interval badTest_18432 184 192 :=
  interval_of_check badTest_18432 184 8 (by decide +kernel)

theorem badTest_18432_block_24 : Interval badTest_18432 192 200 :=
  interval_of_check badTest_18432 192 8 (by decide +kernel)

theorem badTest_18432_block_25 : Interval badTest_18432 200 208 :=
  interval_of_check badTest_18432 200 8 (by decide +kernel)

theorem badTest_18432_block_26 : Interval badTest_18432 208 216 :=
  interval_of_check badTest_18432 208 8 (by decide +kernel)

theorem badTest_18432_block_27 : Interval badTest_18432 216 224 :=
  interval_of_check badTest_18432 216 8 (by decide +kernel)

theorem badTest_18432_block_28 : Interval badTest_18432 224 232 :=
  interval_of_check badTest_18432 224 8 (by decide +kernel)

theorem badTest_18432_block_29 : Interval badTest_18432 232 240 :=
  interval_of_check badTest_18432 232 8 (by decide +kernel)

theorem badTest_18432_block_30 : Interval badTest_18432 240 248 :=
  interval_of_check badTest_18432 240 8 (by decide +kernel)

theorem badTest_18432_block_31 : Interval badTest_18432 248 256 :=
  interval_of_check badTest_18432 248 8 (by decide +kernel)

theorem badTest_18432_complete : Interval badTest_18432 0 256 :=
  (interval_append badTest_18432 0 128 256
  (interval_append badTest_18432 0 64 128
  (interval_append badTest_18432 0 32 64
  (interval_append badTest_18432 0 16 32
  (interval_append badTest_18432 0 8 16
  badTest_18432_block_0
  badTest_18432_block_1)
  (interval_append badTest_18432 16 24 32
  badTest_18432_block_2
  badTest_18432_block_3))
  (interval_append badTest_18432 32 48 64
  (interval_append badTest_18432 32 40 48
  badTest_18432_block_4
  badTest_18432_block_5)
  (interval_append badTest_18432 48 56 64
  badTest_18432_block_6
  badTest_18432_block_7)))
  (interval_append badTest_18432 64 96 128
  (interval_append badTest_18432 64 80 96
  (interval_append badTest_18432 64 72 80
  badTest_18432_block_8
  badTest_18432_block_9)
  (interval_append badTest_18432 80 88 96
  badTest_18432_block_10
  badTest_18432_block_11))
  (interval_append badTest_18432 96 112 128
  (interval_append badTest_18432 96 104 112
  badTest_18432_block_12
  badTest_18432_block_13)
  (interval_append badTest_18432 112 120 128
  badTest_18432_block_14
  badTest_18432_block_15))))
  (interval_append badTest_18432 128 192 256
  (interval_append badTest_18432 128 160 192
  (interval_append badTest_18432 128 144 160
  (interval_append badTest_18432 128 136 144
  badTest_18432_block_16
  badTest_18432_block_17)
  (interval_append badTest_18432 144 152 160
  badTest_18432_block_18
  badTest_18432_block_19))
  (interval_append badTest_18432 160 176 192
  (interval_append badTest_18432 160 168 176
  badTest_18432_block_20
  badTest_18432_block_21)
  (interval_append badTest_18432 176 184 192
  badTest_18432_block_22
  badTest_18432_block_23)))
  (interval_append badTest_18432 192 224 256
  (interval_append badTest_18432 192 208 224
  (interval_append badTest_18432 192 200 208
  badTest_18432_block_24
  badTest_18432_block_25)
  (interval_append badTest_18432 208 216 224
  badTest_18432_block_26
  badTest_18432_block_27))
  (interval_append badTest_18432 224 240 256
  (interval_append badTest_18432 224 232 240
  badTest_18432_block_28
  badTest_18432_block_29)
  (interval_append badTest_18432 240 248 256
  badTest_18432_block_30
  badTest_18432_block_31)))))
theorem badTestInterval18432 : Interval badTest 18432 18688 := by
  intro i hlo hhi
  have h := badTest_18432_complete (i-18432) (Nat.zero_le _) (by omega)
  simpa only [badTest_18432, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad073 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_18688 (i : Nat) := badTest (i+18688)
theorem badTest_18688_block_0 : Interval badTest_18688 0 8 :=
  interval_of_check badTest_18688 0 8 (by decide +kernel)

theorem badTest_18688_block_1 : Interval badTest_18688 8 16 :=
  interval_of_check badTest_18688 8 8 (by decide +kernel)

theorem badTest_18688_block_2 : Interval badTest_18688 16 24 :=
  interval_of_check badTest_18688 16 8 (by decide +kernel)

theorem badTest_18688_block_3 : Interval badTest_18688 24 32 :=
  interval_of_check badTest_18688 24 8 (by decide +kernel)

theorem badTest_18688_block_4 : Interval badTest_18688 32 40 :=
  interval_of_check badTest_18688 32 8 (by decide +kernel)

theorem badTest_18688_block_5 : Interval badTest_18688 40 48 :=
  interval_of_check badTest_18688 40 8 (by decide +kernel)

theorem badTest_18688_block_6 : Interval badTest_18688 48 56 :=
  interval_of_check badTest_18688 48 8 (by decide +kernel)

theorem badTest_18688_block_7 : Interval badTest_18688 56 64 :=
  interval_of_check badTest_18688 56 8 (by decide +kernel)

theorem badTest_18688_block_8 : Interval badTest_18688 64 72 :=
  interval_of_check badTest_18688 64 8 (by decide +kernel)

theorem badTest_18688_block_9 : Interval badTest_18688 72 80 :=
  interval_of_check badTest_18688 72 8 (by decide +kernel)

theorem badTest_18688_block_10 : Interval badTest_18688 80 88 :=
  interval_of_check badTest_18688 80 8 (by decide +kernel)

theorem badTest_18688_block_11 : Interval badTest_18688 88 96 :=
  interval_of_check badTest_18688 88 8 (by decide +kernel)

theorem badTest_18688_block_12 : Interval badTest_18688 96 104 :=
  interval_of_check badTest_18688 96 8 (by decide +kernel)

theorem badTest_18688_block_13 : Interval badTest_18688 104 112 :=
  interval_of_check badTest_18688 104 8 (by decide +kernel)

theorem badTest_18688_block_14 : Interval badTest_18688 112 120 :=
  interval_of_check badTest_18688 112 8 (by decide +kernel)

theorem badTest_18688_block_15 : Interval badTest_18688 120 128 :=
  interval_of_check badTest_18688 120 8 (by decide +kernel)

theorem badTest_18688_block_16 : Interval badTest_18688 128 136 :=
  interval_of_check badTest_18688 128 8 (by decide +kernel)

theorem badTest_18688_block_17 : Interval badTest_18688 136 144 :=
  interval_of_check badTest_18688 136 8 (by decide +kernel)

theorem badTest_18688_block_18 : Interval badTest_18688 144 152 :=
  interval_of_check badTest_18688 144 8 (by decide +kernel)

theorem badTest_18688_block_19 : Interval badTest_18688 152 160 :=
  interval_of_check badTest_18688 152 8 (by decide +kernel)

theorem badTest_18688_block_20 : Interval badTest_18688 160 168 :=
  interval_of_check badTest_18688 160 8 (by decide +kernel)

theorem badTest_18688_block_21 : Interval badTest_18688 168 176 :=
  interval_of_check badTest_18688 168 8 (by decide +kernel)

theorem badTest_18688_block_22 : Interval badTest_18688 176 184 :=
  interval_of_check badTest_18688 176 8 (by decide +kernel)

theorem badTest_18688_block_23 : Interval badTest_18688 184 192 :=
  interval_of_check badTest_18688 184 8 (by decide +kernel)

theorem badTest_18688_block_24 : Interval badTest_18688 192 200 :=
  interval_of_check badTest_18688 192 8 (by decide +kernel)

theorem badTest_18688_block_25 : Interval badTest_18688 200 208 :=
  interval_of_check badTest_18688 200 8 (by decide +kernel)

theorem badTest_18688_block_26 : Interval badTest_18688 208 216 :=
  interval_of_check badTest_18688 208 8 (by decide +kernel)

theorem badTest_18688_block_27 : Interval badTest_18688 216 224 :=
  interval_of_check badTest_18688 216 8 (by decide +kernel)

theorem badTest_18688_block_28 : Interval badTest_18688 224 232 :=
  interval_of_check badTest_18688 224 8 (by decide +kernel)

theorem badTest_18688_block_29 : Interval badTest_18688 232 240 :=
  interval_of_check badTest_18688 232 8 (by decide +kernel)

theorem badTest_18688_block_30 : Interval badTest_18688 240 248 :=
  interval_of_check badTest_18688 240 8 (by decide +kernel)

theorem badTest_18688_block_31 : Interval badTest_18688 248 256 :=
  interval_of_check badTest_18688 248 8 (by decide +kernel)

theorem badTest_18688_complete : Interval badTest_18688 0 256 :=
  (interval_append badTest_18688 0 128 256
  (interval_append badTest_18688 0 64 128
  (interval_append badTest_18688 0 32 64
  (interval_append badTest_18688 0 16 32
  (interval_append badTest_18688 0 8 16
  badTest_18688_block_0
  badTest_18688_block_1)
  (interval_append badTest_18688 16 24 32
  badTest_18688_block_2
  badTest_18688_block_3))
  (interval_append badTest_18688 32 48 64
  (interval_append badTest_18688 32 40 48
  badTest_18688_block_4
  badTest_18688_block_5)
  (interval_append badTest_18688 48 56 64
  badTest_18688_block_6
  badTest_18688_block_7)))
  (interval_append badTest_18688 64 96 128
  (interval_append badTest_18688 64 80 96
  (interval_append badTest_18688 64 72 80
  badTest_18688_block_8
  badTest_18688_block_9)
  (interval_append badTest_18688 80 88 96
  badTest_18688_block_10
  badTest_18688_block_11))
  (interval_append badTest_18688 96 112 128
  (interval_append badTest_18688 96 104 112
  badTest_18688_block_12
  badTest_18688_block_13)
  (interval_append badTest_18688 112 120 128
  badTest_18688_block_14
  badTest_18688_block_15))))
  (interval_append badTest_18688 128 192 256
  (interval_append badTest_18688 128 160 192
  (interval_append badTest_18688 128 144 160
  (interval_append badTest_18688 128 136 144
  badTest_18688_block_16
  badTest_18688_block_17)
  (interval_append badTest_18688 144 152 160
  badTest_18688_block_18
  badTest_18688_block_19))
  (interval_append badTest_18688 160 176 192
  (interval_append badTest_18688 160 168 176
  badTest_18688_block_20
  badTest_18688_block_21)
  (interval_append badTest_18688 176 184 192
  badTest_18688_block_22
  badTest_18688_block_23)))
  (interval_append badTest_18688 192 224 256
  (interval_append badTest_18688 192 208 224
  (interval_append badTest_18688 192 200 208
  badTest_18688_block_24
  badTest_18688_block_25)
  (interval_append badTest_18688 208 216 224
  badTest_18688_block_26
  badTest_18688_block_27))
  (interval_append badTest_18688 224 240 256
  (interval_append badTest_18688 224 232 240
  badTest_18688_block_28
  badTest_18688_block_29)
  (interval_append badTest_18688 240 248 256
  badTest_18688_block_30
  badTest_18688_block_31)))))
theorem badTestInterval18688 : Interval badTest 18688 18944 := by
  intro i hlo hhi
  have h := badTest_18688_complete (i-18688) (Nat.zero_le _) (by omega)
  simpa only [badTest_18688, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
