module
prelude
public import RootedSevenPure009GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure009
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_512 (i : Nat) := badTest (i+512)
theorem badTest_512_block_0 : Interval badTest_512 0 8 :=
  interval_of_check badTest_512 0 8 (by decide +kernel)

theorem badTest_512_block_1 : Interval badTest_512 8 16 :=
  interval_of_check badTest_512 8 8 (by decide +kernel)

theorem badTest_512_block_2 : Interval badTest_512 16 24 :=
  interval_of_check badTest_512 16 8 (by decide +kernel)

theorem badTest_512_block_3 : Interval badTest_512 24 32 :=
  interval_of_check badTest_512 24 8 (by decide +kernel)

theorem badTest_512_block_4 : Interval badTest_512 32 40 :=
  interval_of_check badTest_512 32 8 (by decide +kernel)

theorem badTest_512_block_5 : Interval badTest_512 40 48 :=
  interval_of_check badTest_512 40 8 (by decide +kernel)

theorem badTest_512_block_6 : Interval badTest_512 48 56 :=
  interval_of_check badTest_512 48 8 (by decide +kernel)

theorem badTest_512_block_7 : Interval badTest_512 56 64 :=
  interval_of_check badTest_512 56 8 (by decide +kernel)

theorem badTest_512_block_8 : Interval badTest_512 64 72 :=
  interval_of_check badTest_512 64 8 (by decide +kernel)

theorem badTest_512_block_9 : Interval badTest_512 72 80 :=
  interval_of_check badTest_512 72 8 (by decide +kernel)

theorem badTest_512_block_10 : Interval badTest_512 80 88 :=
  interval_of_check badTest_512 80 8 (by decide +kernel)

theorem badTest_512_block_11 : Interval badTest_512 88 96 :=
  interval_of_check badTest_512 88 8 (by decide +kernel)

theorem badTest_512_block_12 : Interval badTest_512 96 104 :=
  interval_of_check badTest_512 96 8 (by decide +kernel)

theorem badTest_512_block_13 : Interval badTest_512 104 112 :=
  interval_of_check badTest_512 104 8 (by decide +kernel)

theorem badTest_512_block_14 : Interval badTest_512 112 120 :=
  interval_of_check badTest_512 112 8 (by decide +kernel)

theorem badTest_512_block_15 : Interval badTest_512 120 128 :=
  interval_of_check badTest_512 120 8 (by decide +kernel)

theorem badTest_512_block_16 : Interval badTest_512 128 136 :=
  interval_of_check badTest_512 128 8 (by decide +kernel)

theorem badTest_512_block_17 : Interval badTest_512 136 144 :=
  interval_of_check badTest_512 136 8 (by decide +kernel)

theorem badTest_512_block_18 : Interval badTest_512 144 152 :=
  interval_of_check badTest_512 144 8 (by decide +kernel)

theorem badTest_512_block_19 : Interval badTest_512 152 160 :=
  interval_of_check badTest_512 152 8 (by decide +kernel)

theorem badTest_512_block_20 : Interval badTest_512 160 168 :=
  interval_of_check badTest_512 160 8 (by decide +kernel)

theorem badTest_512_block_21 : Interval badTest_512 168 176 :=
  interval_of_check badTest_512 168 8 (by decide +kernel)

theorem badTest_512_block_22 : Interval badTest_512 176 184 :=
  interval_of_check badTest_512 176 8 (by decide +kernel)

theorem badTest_512_block_23 : Interval badTest_512 184 192 :=
  interval_of_check badTest_512 184 8 (by decide +kernel)

theorem badTest_512_block_24 : Interval badTest_512 192 200 :=
  interval_of_check badTest_512 192 8 (by decide +kernel)

theorem badTest_512_block_25 : Interval badTest_512 200 208 :=
  interval_of_check badTest_512 200 8 (by decide +kernel)

theorem badTest_512_block_26 : Interval badTest_512 208 216 :=
  interval_of_check badTest_512 208 8 (by decide +kernel)

theorem badTest_512_block_27 : Interval badTest_512 216 224 :=
  interval_of_check badTest_512 216 8 (by decide +kernel)

theorem badTest_512_block_28 : Interval badTest_512 224 232 :=
  interval_of_check badTest_512 224 8 (by decide +kernel)

theorem badTest_512_block_29 : Interval badTest_512 232 240 :=
  interval_of_check badTest_512 232 8 (by decide +kernel)

theorem badTest_512_block_30 : Interval badTest_512 240 246 :=
  interval_of_check badTest_512 240 6 (by decide +kernel)

theorem badTest_512_complete : Interval badTest_512 0 246 :=
  (interval_append badTest_512 0 120 246
  (interval_append badTest_512 0 56 120
  (interval_append badTest_512 0 24 56
  (interval_append badTest_512 0 8 24
  badTest_512_block_0
  (interval_append badTest_512 8 16 24
  badTest_512_block_1
  badTest_512_block_2))
  (interval_append badTest_512 24 40 56
  (interval_append badTest_512 24 32 40
  badTest_512_block_3
  badTest_512_block_4)
  (interval_append badTest_512 40 48 56
  badTest_512_block_5
  badTest_512_block_6)))
  (interval_append badTest_512 56 88 120
  (interval_append badTest_512 56 72 88
  (interval_append badTest_512 56 64 72
  badTest_512_block_7
  badTest_512_block_8)
  (interval_append badTest_512 72 80 88
  badTest_512_block_9
  badTest_512_block_10))
  (interval_append badTest_512 88 104 120
  (interval_append badTest_512 88 96 104
  badTest_512_block_11
  badTest_512_block_12)
  (interval_append badTest_512 104 112 120
  badTest_512_block_13
  badTest_512_block_14))))
  (interval_append badTest_512 120 184 246
  (interval_append badTest_512 120 152 184
  (interval_append badTest_512 120 136 152
  (interval_append badTest_512 120 128 136
  badTest_512_block_15
  badTest_512_block_16)
  (interval_append badTest_512 136 144 152
  badTest_512_block_17
  badTest_512_block_18))
  (interval_append badTest_512 152 168 184
  (interval_append badTest_512 152 160 168
  badTest_512_block_19
  badTest_512_block_20)
  (interval_append badTest_512 168 176 184
  badTest_512_block_21
  badTest_512_block_22)))
  (interval_append badTest_512 184 216 246
  (interval_append badTest_512 184 200 216
  (interval_append badTest_512 184 192 200
  badTest_512_block_23
  badTest_512_block_24)
  (interval_append badTest_512 200 208 216
  badTest_512_block_25
  badTest_512_block_26))
  (interval_append badTest_512 216 232 246
  (interval_append badTest_512 216 224 232
  badTest_512_block_27
  badTest_512_block_28)
  (interval_append badTest_512 232 240 246
  badTest_512_block_29
  badTest_512_block_30)))))
theorem badTestInterval512 : Interval badTest 512 758 := by
  intro i hlo hhi
  have h := badTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [badTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure009
