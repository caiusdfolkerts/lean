module
prelude
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
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

end Papers.RationalityTen.RootedCaches.RootedSixBase03
