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
def badTest_896 (i : Nat) := badTest (i+896)
theorem badTest_896_block_0 : Interval badTest_896 0 8 :=
  interval_of_check badTest_896 0 8 (by decide +kernel)

theorem badTest_896_block_1 : Interval badTest_896 8 16 :=
  interval_of_check badTest_896 8 8 (by decide +kernel)

theorem badTest_896_block_2 : Interval badTest_896 16 24 :=
  interval_of_check badTest_896 16 8 (by decide +kernel)

theorem badTest_896_block_3 : Interval badTest_896 24 32 :=
  interval_of_check badTest_896 24 8 (by decide +kernel)

theorem badTest_896_block_4 : Interval badTest_896 32 40 :=
  interval_of_check badTest_896 32 8 (by decide +kernel)

theorem badTest_896_block_5 : Interval badTest_896 40 48 :=
  interval_of_check badTest_896 40 8 (by decide +kernel)

theorem badTest_896_block_6 : Interval badTest_896 48 56 :=
  interval_of_check badTest_896 48 8 (by decide +kernel)

theorem badTest_896_block_7 : Interval badTest_896 56 64 :=
  interval_of_check badTest_896 56 8 (by decide +kernel)

theorem badTest_896_block_8 : Interval badTest_896 64 72 :=
  interval_of_check badTest_896 64 8 (by decide +kernel)

theorem badTest_896_block_9 : Interval badTest_896 72 80 :=
  interval_of_check badTest_896 72 8 (by decide +kernel)

theorem badTest_896_block_10 : Interval badTest_896 80 88 :=
  interval_of_check badTest_896 80 8 (by decide +kernel)

theorem badTest_896_block_11 : Interval badTest_896 88 96 :=
  interval_of_check badTest_896 88 8 (by decide +kernel)

theorem badTest_896_block_12 : Interval badTest_896 96 104 :=
  interval_of_check badTest_896 96 8 (by decide +kernel)

theorem badTest_896_block_13 : Interval badTest_896 104 112 :=
  interval_of_check badTest_896 104 8 (by decide +kernel)

theorem badTest_896_block_14 : Interval badTest_896 112 120 :=
  interval_of_check badTest_896 112 8 (by decide +kernel)

theorem badTest_896_block_15 : Interval badTest_896 120 128 :=
  interval_of_check badTest_896 120 8 (by decide +kernel)

theorem badTest_896_complete : Interval badTest_896 0 128 :=
  (interval_append badTest_896 0 64 128
  (interval_append badTest_896 0 32 64
  (interval_append badTest_896 0 16 32
  (interval_append badTest_896 0 8 16
  badTest_896_block_0
  badTest_896_block_1)
  (interval_append badTest_896 16 24 32
  badTest_896_block_2
  badTest_896_block_3))
  (interval_append badTest_896 32 48 64
  (interval_append badTest_896 32 40 48
  badTest_896_block_4
  badTest_896_block_5)
  (interval_append badTest_896 48 56 64
  badTest_896_block_6
  badTest_896_block_7)))
  (interval_append badTest_896 64 96 128
  (interval_append badTest_896 64 80 96
  (interval_append badTest_896 64 72 80
  badTest_896_block_8
  badTest_896_block_9)
  (interval_append badTest_896 80 88 96
  badTest_896_block_10
  badTest_896_block_11))
  (interval_append badTest_896 96 112 128
  (interval_append badTest_896 96 104 112
  badTest_896_block_12
  badTest_896_block_13)
  (interval_append badTest_896 112 120 128
  badTest_896_block_14
  badTest_896_block_15))))
theorem badTest_interval_896 : Interval badTest 896 1024 := by
  intro i hlo hhi
  have h := badTest_896_complete (i-896) (Nat.zero_le _) (by omega)
  simpa only [badTest_896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
