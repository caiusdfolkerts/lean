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
def badTest_0 (i : Nat) := badTest (i+0)
theorem badTest_0_block_0 : Interval badTest_0 0 8 :=
  interval_of_check badTest_0 0 8 (by decide +kernel)

theorem badTest_0_block_1 : Interval badTest_0 8 16 :=
  interval_of_check badTest_0 8 8 (by decide +kernel)

theorem badTest_0_block_2 : Interval badTest_0 16 24 :=
  interval_of_check badTest_0 16 8 (by decide +kernel)

theorem badTest_0_block_3 : Interval badTest_0 24 32 :=
  interval_of_check badTest_0 24 8 (by decide +kernel)

theorem badTest_0_block_4 : Interval badTest_0 32 40 :=
  interval_of_check badTest_0 32 8 (by decide +kernel)

theorem badTest_0_block_5 : Interval badTest_0 40 48 :=
  interval_of_check badTest_0 40 8 (by decide +kernel)

theorem badTest_0_block_6 : Interval badTest_0 48 56 :=
  interval_of_check badTest_0 48 8 (by decide +kernel)

theorem badTest_0_block_7 : Interval badTest_0 56 64 :=
  interval_of_check badTest_0 56 8 (by decide +kernel)

theorem badTest_0_block_8 : Interval badTest_0 64 72 :=
  interval_of_check badTest_0 64 8 (by decide +kernel)

theorem badTest_0_block_9 : Interval badTest_0 72 80 :=
  interval_of_check badTest_0 72 8 (by decide +kernel)

theorem badTest_0_block_10 : Interval badTest_0 80 88 :=
  interval_of_check badTest_0 80 8 (by decide +kernel)

theorem badTest_0_block_11 : Interval badTest_0 88 96 :=
  interval_of_check badTest_0 88 8 (by decide +kernel)

theorem badTest_0_block_12 : Interval badTest_0 96 104 :=
  interval_of_check badTest_0 96 8 (by decide +kernel)

theorem badTest_0_block_13 : Interval badTest_0 104 112 :=
  interval_of_check badTest_0 104 8 (by decide +kernel)

theorem badTest_0_block_14 : Interval badTest_0 112 120 :=
  interval_of_check badTest_0 112 8 (by decide +kernel)

theorem badTest_0_block_15 : Interval badTest_0 120 128 :=
  interval_of_check badTest_0 120 8 (by decide +kernel)

theorem badTest_0_complete : Interval badTest_0 0 128 :=
  (interval_append badTest_0 0 64 128
  (interval_append badTest_0 0 32 64
  (interval_append badTest_0 0 16 32
  (interval_append badTest_0 0 8 16
  badTest_0_block_0
  badTest_0_block_1)
  (interval_append badTest_0 16 24 32
  badTest_0_block_2
  badTest_0_block_3))
  (interval_append badTest_0 32 48 64
  (interval_append badTest_0 32 40 48
  badTest_0_block_4
  badTest_0_block_5)
  (interval_append badTest_0 48 56 64
  badTest_0_block_6
  badTest_0_block_7)))
  (interval_append badTest_0 64 96 128
  (interval_append badTest_0 64 80 96
  (interval_append badTest_0 64 72 80
  badTest_0_block_8
  badTest_0_block_9)
  (interval_append badTest_0 80 88 96
  badTest_0_block_10
  badTest_0_block_11))
  (interval_append badTest_0 96 112 128
  (interval_append badTest_0 96 104 112
  badTest_0_block_12
  badTest_0_block_13)
  (interval_append badTest_0 112 120 128
  badTest_0_block_14
  badTest_0_block_15))))
theorem badTest_interval_0 : Interval badTest 0 128 := by
  intro i hlo hhi
  have h := badTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [badTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
