module
prelude
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
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

end Papers.RationalityTen.RootedCaches.RootedSixBase03
