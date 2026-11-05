module
prelude
public import RootedSmallCacheFacts

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallCache
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def badTest_3200 (i : Nat) := badTest (i+3200)
theorem badTest_3200_block_0 : Interval badTest_3200 0 8 :=
  interval_of_check badTest_3200 0 8 (by decide +kernel)

theorem badTest_3200_block_1 : Interval badTest_3200 8 16 :=
  interval_of_check badTest_3200 8 8 (by decide +kernel)

theorem badTest_3200_block_2 : Interval badTest_3200 16 24 :=
  interval_of_check badTest_3200 16 8 (by decide +kernel)

theorem badTest_3200_block_3 : Interval badTest_3200 24 32 :=
  interval_of_check badTest_3200 24 8 (by decide +kernel)

theorem badTest_3200_block_4 : Interval badTest_3200 32 40 :=
  interval_of_check badTest_3200 32 8 (by decide +kernel)

theorem badTest_3200_block_5 : Interval badTest_3200 40 48 :=
  interval_of_check badTest_3200 40 8 (by decide +kernel)

theorem badTest_3200_block_6 : Interval badTest_3200 48 56 :=
  interval_of_check badTest_3200 48 8 (by decide +kernel)

theorem badTest_3200_block_7 : Interval badTest_3200 56 64 :=
  interval_of_check badTest_3200 56 8 (by decide +kernel)

theorem badTest_3200_block_8 : Interval badTest_3200 64 72 :=
  interval_of_check badTest_3200 64 8 (by decide +kernel)

theorem badTest_3200_block_9 : Interval badTest_3200 72 80 :=
  interval_of_check badTest_3200 72 8 (by decide +kernel)

theorem badTest_3200_block_10 : Interval badTest_3200 80 88 :=
  interval_of_check badTest_3200 80 8 (by decide +kernel)

theorem badTest_3200_block_11 : Interval badTest_3200 88 96 :=
  interval_of_check badTest_3200 88 8 (by decide +kernel)

theorem badTest_3200_block_12 : Interval badTest_3200 96 104 :=
  interval_of_check badTest_3200 96 8 (by decide +kernel)

theorem badTest_3200_block_13 : Interval badTest_3200 104 112 :=
  interval_of_check badTest_3200 104 8 (by decide +kernel)

theorem badTest_3200_block_14 : Interval badTest_3200 112 120 :=
  interval_of_check badTest_3200 112 8 (by decide +kernel)

theorem badTest_3200_block_15 : Interval badTest_3200 120 128 :=
  interval_of_check badTest_3200 120 8 (by decide +kernel)

theorem badTest_3200_complete : Interval badTest_3200 0 128 :=
  (interval_append badTest_3200 0 64 128
  (interval_append badTest_3200 0 32 64
  (interval_append badTest_3200 0 16 32
  (interval_append badTest_3200 0 8 16
  badTest_3200_block_0
  badTest_3200_block_1)
  (interval_append badTest_3200 16 24 32
  badTest_3200_block_2
  badTest_3200_block_3))
  (interval_append badTest_3200 32 48 64
  (interval_append badTest_3200 32 40 48
  badTest_3200_block_4
  badTest_3200_block_5)
  (interval_append badTest_3200 48 56 64
  badTest_3200_block_6
  badTest_3200_block_7)))
  (interval_append badTest_3200 64 96 128
  (interval_append badTest_3200 64 80 96
  (interval_append badTest_3200 64 72 80
  badTest_3200_block_8
  badTest_3200_block_9)
  (interval_append badTest_3200 80 88 96
  badTest_3200_block_10
  badTest_3200_block_11))
  (interval_append badTest_3200 96 112 128
  (interval_append badTest_3200 96 104 112
  badTest_3200_block_12
  badTest_3200_block_13)
  (interval_append badTest_3200 112 120 128
  badTest_3200_block_14
  badTest_3200_block_15))))
theorem badTest_interval_3200 : Interval badTest 3200 3328 := by
  intro i hlo hhi
  have h := badTest_3200_complete (i-3200) (Nat.zero_le _) (by omega)
  simpa only [badTest_3200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
