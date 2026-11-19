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
def badTest_640 (i : Nat) := badTest (i+640)
theorem badTest_640_block_0 : Interval badTest_640 0 8 :=
  interval_of_check badTest_640 0 8 (by decide +kernel)

theorem badTest_640_block_1 : Interval badTest_640 8 16 :=
  interval_of_check badTest_640 8 8 (by decide +kernel)

theorem badTest_640_block_2 : Interval badTest_640 16 24 :=
  interval_of_check badTest_640 16 8 (by decide +kernel)

theorem badTest_640_block_3 : Interval badTest_640 24 32 :=
  interval_of_check badTest_640 24 8 (by decide +kernel)

theorem badTest_640_block_4 : Interval badTest_640 32 40 :=
  interval_of_check badTest_640 32 8 (by decide +kernel)

theorem badTest_640_block_5 : Interval badTest_640 40 48 :=
  interval_of_check badTest_640 40 8 (by decide +kernel)

theorem badTest_640_block_6 : Interval badTest_640 48 56 :=
  interval_of_check badTest_640 48 8 (by decide +kernel)

theorem badTest_640_block_7 : Interval badTest_640 56 64 :=
  interval_of_check badTest_640 56 8 (by decide +kernel)

theorem badTest_640_block_8 : Interval badTest_640 64 72 :=
  interval_of_check badTest_640 64 8 (by decide +kernel)

theorem badTest_640_block_9 : Interval badTest_640 72 80 :=
  interval_of_check badTest_640 72 8 (by decide +kernel)

theorem badTest_640_block_10 : Interval badTest_640 80 88 :=
  interval_of_check badTest_640 80 8 (by decide +kernel)

theorem badTest_640_block_11 : Interval badTest_640 88 96 :=
  interval_of_check badTest_640 88 8 (by decide +kernel)

theorem badTest_640_block_12 : Interval badTest_640 96 104 :=
  interval_of_check badTest_640 96 8 (by decide +kernel)

theorem badTest_640_block_13 : Interval badTest_640 104 112 :=
  interval_of_check badTest_640 104 8 (by decide +kernel)

theorem badTest_640_block_14 : Interval badTest_640 112 120 :=
  interval_of_check badTest_640 112 8 (by decide +kernel)

theorem badTest_640_block_15 : Interval badTest_640 120 128 :=
  interval_of_check badTest_640 120 8 (by decide +kernel)

theorem badTest_640_complete : Interval badTest_640 0 128 :=
  (interval_append badTest_640 0 64 128
  (interval_append badTest_640 0 32 64
  (interval_append badTest_640 0 16 32
  (interval_append badTest_640 0 8 16
  badTest_640_block_0
  badTest_640_block_1)
  (interval_append badTest_640 16 24 32
  badTest_640_block_2
  badTest_640_block_3))
  (interval_append badTest_640 32 48 64
  (interval_append badTest_640 32 40 48
  badTest_640_block_4
  badTest_640_block_5)
  (interval_append badTest_640 48 56 64
  badTest_640_block_6
  badTest_640_block_7)))
  (interval_append badTest_640 64 96 128
  (interval_append badTest_640 64 80 96
  (interval_append badTest_640 64 72 80
  badTest_640_block_8
  badTest_640_block_9)
  (interval_append badTest_640 80 88 96
  badTest_640_block_10
  badTest_640_block_11))
  (interval_append badTest_640 96 112 128
  (interval_append badTest_640 96 104 112
  badTest_640_block_12
  badTest_640_block_13)
  (interval_append badTest_640 112 120 128
  badTest_640_block_14
  badTest_640_block_15))))
theorem badTest_interval_640 : Interval badTest 640 768 := by
  intro i hlo hhi
  have h := badTest_640_complete (i-640) (Nat.zero_le _) (by omega)
  simpa only [badTest_640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
