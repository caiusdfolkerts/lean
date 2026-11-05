module
prelude
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
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

theorem badTest_5120_block_14 : Interval badTest_5120 112 118 :=
  interval_of_check badTest_5120 112 6 (by decide +kernel)

theorem badTest_5120_complete : Interval badTest_5120 0 118 :=
  (interval_append badTest_5120 0 56 118
  (interval_append badTest_5120 0 24 56
  (interval_append badTest_5120 0 8 24
  badTest_5120_block_0
  (interval_append badTest_5120 8 16 24
  badTest_5120_block_1
  badTest_5120_block_2))
  (interval_append badTest_5120 24 40 56
  (interval_append badTest_5120 24 32 40
  badTest_5120_block_3
  badTest_5120_block_4)
  (interval_append badTest_5120 40 48 56
  badTest_5120_block_5
  badTest_5120_block_6)))
  (interval_append badTest_5120 56 88 118
  (interval_append badTest_5120 56 72 88
  (interval_append badTest_5120 56 64 72
  badTest_5120_block_7
  badTest_5120_block_8)
  (interval_append badTest_5120 72 80 88
  badTest_5120_block_9
  badTest_5120_block_10))
  (interval_append badTest_5120 88 104 118
  (interval_append badTest_5120 88 96 104
  badTest_5120_block_11
  badTest_5120_block_12)
  (interval_append badTest_5120 104 112 118
  badTest_5120_block_13
  badTest_5120_block_14))))
theorem badTestInterval5120 : Interval badTest 5120 5238 := by
  intro i hlo hhi
  have h := badTest_5120_complete (i-5120) (Nat.zero_le _) (by omega)
  simpa only [badTest_5120, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase03
