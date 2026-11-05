module
prelude
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
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

end Papers.RationalityTen.RootedCaches.RootedSixBase03
