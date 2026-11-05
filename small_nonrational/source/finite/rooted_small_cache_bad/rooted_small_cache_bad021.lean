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
def badTest_2688 (i : Nat) := badTest (i+2688)
theorem badTest_2688_block_0 : Interval badTest_2688 0 8 :=
  interval_of_check badTest_2688 0 8 (by decide +kernel)

theorem badTest_2688_block_1 : Interval badTest_2688 8 16 :=
  interval_of_check badTest_2688 8 8 (by decide +kernel)

theorem badTest_2688_block_2 : Interval badTest_2688 16 24 :=
  interval_of_check badTest_2688 16 8 (by decide +kernel)

theorem badTest_2688_block_3 : Interval badTest_2688 24 32 :=
  interval_of_check badTest_2688 24 8 (by decide +kernel)

theorem badTest_2688_block_4 : Interval badTest_2688 32 40 :=
  interval_of_check badTest_2688 32 8 (by decide +kernel)

theorem badTest_2688_block_5 : Interval badTest_2688 40 48 :=
  interval_of_check badTest_2688 40 8 (by decide +kernel)

theorem badTest_2688_block_6 : Interval badTest_2688 48 56 :=
  interval_of_check badTest_2688 48 8 (by decide +kernel)

theorem badTest_2688_block_7 : Interval badTest_2688 56 64 :=
  interval_of_check badTest_2688 56 8 (by decide +kernel)

theorem badTest_2688_block_8 : Interval badTest_2688 64 72 :=
  interval_of_check badTest_2688 64 8 (by decide +kernel)

theorem badTest_2688_block_9 : Interval badTest_2688 72 80 :=
  interval_of_check badTest_2688 72 8 (by decide +kernel)

theorem badTest_2688_block_10 : Interval badTest_2688 80 88 :=
  interval_of_check badTest_2688 80 8 (by decide +kernel)

theorem badTest_2688_block_11 : Interval badTest_2688 88 96 :=
  interval_of_check badTest_2688 88 8 (by decide +kernel)

theorem badTest_2688_block_12 : Interval badTest_2688 96 104 :=
  interval_of_check badTest_2688 96 8 (by decide +kernel)

theorem badTest_2688_block_13 : Interval badTest_2688 104 112 :=
  interval_of_check badTest_2688 104 8 (by decide +kernel)

theorem badTest_2688_block_14 : Interval badTest_2688 112 120 :=
  interval_of_check badTest_2688 112 8 (by decide +kernel)

theorem badTest_2688_block_15 : Interval badTest_2688 120 128 :=
  interval_of_check badTest_2688 120 8 (by decide +kernel)

theorem badTest_2688_complete : Interval badTest_2688 0 128 :=
  (interval_append badTest_2688 0 64 128
  (interval_append badTest_2688 0 32 64
  (interval_append badTest_2688 0 16 32
  (interval_append badTest_2688 0 8 16
  badTest_2688_block_0
  badTest_2688_block_1)
  (interval_append badTest_2688 16 24 32
  badTest_2688_block_2
  badTest_2688_block_3))
  (interval_append badTest_2688 32 48 64
  (interval_append badTest_2688 32 40 48
  badTest_2688_block_4
  badTest_2688_block_5)
  (interval_append badTest_2688 48 56 64
  badTest_2688_block_6
  badTest_2688_block_7)))
  (interval_append badTest_2688 64 96 128
  (interval_append badTest_2688 64 80 96
  (interval_append badTest_2688 64 72 80
  badTest_2688_block_8
  badTest_2688_block_9)
  (interval_append badTest_2688 80 88 96
  badTest_2688_block_10
  badTest_2688_block_11))
  (interval_append badTest_2688 96 112 128
  (interval_append badTest_2688 96 104 112
  badTest_2688_block_12
  badTest_2688_block_13)
  (interval_append badTest_2688 112 120 128
  badTest_2688_block_14
  badTest_2688_block_15))))
theorem badTest_interval_2688 : Interval badTest 2688 2816 := by
  intro i hlo hhi
  have h := badTest_2688_complete (i-2688) (Nat.zero_le _) (by omega)
  simpa only [badTest_2688, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
