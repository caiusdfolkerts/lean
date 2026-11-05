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

theorem badTest_3328_block_13 : Interval badTest_3328 104 108 :=
  interval_of_check badTest_3328 104 4 (by decide +kernel)

theorem badTest_3328_complete : Interval badTest_3328 0 108 :=
  (interval_append badTest_3328 0 56 108
  (interval_append badTest_3328 0 24 56
  (interval_append badTest_3328 0 8 24
  badTest_3328_block_0
  (interval_append badTest_3328 8 16 24
  badTest_3328_block_1
  badTest_3328_block_2))
  (interval_append badTest_3328 24 40 56
  (interval_append badTest_3328 24 32 40
  badTest_3328_block_3
  badTest_3328_block_4)
  (interval_append badTest_3328 40 48 56
  badTest_3328_block_5
  badTest_3328_block_6)))
  (interval_append badTest_3328 56 80 108
  (interval_append badTest_3328 56 64 80
  badTest_3328_block_7
  (interval_append badTest_3328 64 72 80
  badTest_3328_block_8
  badTest_3328_block_9))
  (interval_append badTest_3328 80 96 108
  (interval_append badTest_3328 80 88 96
  badTest_3328_block_10
  badTest_3328_block_11)
  (interval_append badTest_3328 96 104 108
  badTest_3328_block_12
  badTest_3328_block_13))))
theorem badTest_interval_3328 : Interval badTest 3328 3436 := by
  intro i hlo hhi
  have h := badTest_3328_complete (i-3328) (Nat.zero_le _) (by omega)
  simpa only [badTest_3328, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
