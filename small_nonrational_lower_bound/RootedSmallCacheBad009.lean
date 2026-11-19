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
def badTest_1152 (i : Nat) := badTest (i+1152)
theorem badTest_1152_block_0 : Interval badTest_1152 0 8 :=
  interval_of_check badTest_1152 0 8 (by decide +kernel)

theorem badTest_1152_block_1 : Interval badTest_1152 8 16 :=
  interval_of_check badTest_1152 8 8 (by decide +kernel)

theorem badTest_1152_block_2 : Interval badTest_1152 16 24 :=
  interval_of_check badTest_1152 16 8 (by decide +kernel)

theorem badTest_1152_block_3 : Interval badTest_1152 24 32 :=
  interval_of_check badTest_1152 24 8 (by decide +kernel)

theorem badTest_1152_block_4 : Interval badTest_1152 32 40 :=
  interval_of_check badTest_1152 32 8 (by decide +kernel)

theorem badTest_1152_block_5 : Interval badTest_1152 40 48 :=
  interval_of_check badTest_1152 40 8 (by decide +kernel)

theorem badTest_1152_block_6 : Interval badTest_1152 48 56 :=
  interval_of_check badTest_1152 48 8 (by decide +kernel)

theorem badTest_1152_block_7 : Interval badTest_1152 56 64 :=
  interval_of_check badTest_1152 56 8 (by decide +kernel)

theorem badTest_1152_block_8 : Interval badTest_1152 64 72 :=
  interval_of_check badTest_1152 64 8 (by decide +kernel)

theorem badTest_1152_block_9 : Interval badTest_1152 72 80 :=
  interval_of_check badTest_1152 72 8 (by decide +kernel)

theorem badTest_1152_block_10 : Interval badTest_1152 80 88 :=
  interval_of_check badTest_1152 80 8 (by decide +kernel)

theorem badTest_1152_block_11 : Interval badTest_1152 88 96 :=
  interval_of_check badTest_1152 88 8 (by decide +kernel)

theorem badTest_1152_block_12 : Interval badTest_1152 96 104 :=
  interval_of_check badTest_1152 96 8 (by decide +kernel)

theorem badTest_1152_block_13 : Interval badTest_1152 104 112 :=
  interval_of_check badTest_1152 104 8 (by decide +kernel)

theorem badTest_1152_block_14 : Interval badTest_1152 112 120 :=
  interval_of_check badTest_1152 112 8 (by decide +kernel)

theorem badTest_1152_block_15 : Interval badTest_1152 120 128 :=
  interval_of_check badTest_1152 120 8 (by decide +kernel)

theorem badTest_1152_complete : Interval badTest_1152 0 128 :=
  (interval_append badTest_1152 0 64 128
  (interval_append badTest_1152 0 32 64
  (interval_append badTest_1152 0 16 32
  (interval_append badTest_1152 0 8 16
  badTest_1152_block_0
  badTest_1152_block_1)
  (interval_append badTest_1152 16 24 32
  badTest_1152_block_2
  badTest_1152_block_3))
  (interval_append badTest_1152 32 48 64
  (interval_append badTest_1152 32 40 48
  badTest_1152_block_4
  badTest_1152_block_5)
  (interval_append badTest_1152 48 56 64
  badTest_1152_block_6
  badTest_1152_block_7)))
  (interval_append badTest_1152 64 96 128
  (interval_append badTest_1152 64 80 96
  (interval_append badTest_1152 64 72 80
  badTest_1152_block_8
  badTest_1152_block_9)
  (interval_append badTest_1152 80 88 96
  badTest_1152_block_10
  badTest_1152_block_11))
  (interval_append badTest_1152 96 112 128
  (interval_append badTest_1152 96 104 112
  badTest_1152_block_12
  badTest_1152_block_13)
  (interval_append badTest_1152 112 120 128
  badTest_1152_block_14
  badTest_1152_block_15))))
theorem badTest_interval_1152 : Interval badTest 1152 1280 := by
  intro i hlo hhi
  have h := badTest_1152_complete (i-1152) (Nat.zero_le _) (by omega)
  simpa only [badTest_1152, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
