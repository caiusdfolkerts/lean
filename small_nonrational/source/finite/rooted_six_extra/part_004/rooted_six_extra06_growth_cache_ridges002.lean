module
prelude
public import RootedSixExtra06GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_256 (i : Nat) := ridgeTest (i+256)
theorem ridgeTest_256_block_0 : Interval ridgeTest_256 0 8 :=
  interval_of_check ridgeTest_256 0 8 (by decide +kernel)

theorem ridgeTest_256_block_1 : Interval ridgeTest_256 8 16 :=
  interval_of_check ridgeTest_256 8 8 (by decide +kernel)

theorem ridgeTest_256_block_2 : Interval ridgeTest_256 16 24 :=
  interval_of_check ridgeTest_256 16 8 (by decide +kernel)

theorem ridgeTest_256_block_3 : Interval ridgeTest_256 24 32 :=
  interval_of_check ridgeTest_256 24 8 (by decide +kernel)

theorem ridgeTest_256_block_4 : Interval ridgeTest_256 32 40 :=
  interval_of_check ridgeTest_256 32 8 (by decide +kernel)

theorem ridgeTest_256_block_5 : Interval ridgeTest_256 40 48 :=
  interval_of_check ridgeTest_256 40 8 (by decide +kernel)

theorem ridgeTest_256_block_6 : Interval ridgeTest_256 48 56 :=
  interval_of_check ridgeTest_256 48 8 (by decide +kernel)

theorem ridgeTest_256_block_7 : Interval ridgeTest_256 56 64 :=
  interval_of_check ridgeTest_256 56 8 (by decide +kernel)

theorem ridgeTest_256_block_8 : Interval ridgeTest_256 64 72 :=
  interval_of_check ridgeTest_256 64 8 (by decide +kernel)

theorem ridgeTest_256_block_9 : Interval ridgeTest_256 72 80 :=
  interval_of_check ridgeTest_256 72 8 (by decide +kernel)

theorem ridgeTest_256_block_10 : Interval ridgeTest_256 80 88 :=
  interval_of_check ridgeTest_256 80 8 (by decide +kernel)

theorem ridgeTest_256_block_11 : Interval ridgeTest_256 88 96 :=
  interval_of_check ridgeTest_256 88 8 (by decide +kernel)

theorem ridgeTest_256_block_12 : Interval ridgeTest_256 96 104 :=
  interval_of_check ridgeTest_256 96 8 (by decide +kernel)

theorem ridgeTest_256_block_13 : Interval ridgeTest_256 104 112 :=
  interval_of_check ridgeTest_256 104 8 (by decide +kernel)

theorem ridgeTest_256_block_14 : Interval ridgeTest_256 112 120 :=
  interval_of_check ridgeTest_256 112 8 (by decide +kernel)

theorem ridgeTest_256_block_15 : Interval ridgeTest_256 120 128 :=
  interval_of_check ridgeTest_256 120 8 (by decide +kernel)

theorem ridgeTest_256_complete : Interval ridgeTest_256 0 128 :=
  (interval_append ridgeTest_256 0 64 128
  (interval_append ridgeTest_256 0 32 64
  (interval_append ridgeTest_256 0 16 32
  (interval_append ridgeTest_256 0 8 16
  ridgeTest_256_block_0
  ridgeTest_256_block_1)
  (interval_append ridgeTest_256 16 24 32
  ridgeTest_256_block_2
  ridgeTest_256_block_3))
  (interval_append ridgeTest_256 32 48 64
  (interval_append ridgeTest_256 32 40 48
  ridgeTest_256_block_4
  ridgeTest_256_block_5)
  (interval_append ridgeTest_256 48 56 64
  ridgeTest_256_block_6
  ridgeTest_256_block_7)))
  (interval_append ridgeTest_256 64 96 128
  (interval_append ridgeTest_256 64 80 96
  (interval_append ridgeTest_256 64 72 80
  ridgeTest_256_block_8
  ridgeTest_256_block_9)
  (interval_append ridgeTest_256 80 88 96
  ridgeTest_256_block_10
  ridgeTest_256_block_11))
  (interval_append ridgeTest_256 96 112 128
  (interval_append ridgeTest_256 96 104 112
  ridgeTest_256_block_12
  ridgeTest_256_block_13)
  (interval_append ridgeTest_256 112 120 128
  ridgeTest_256_block_14
  ridgeTest_256_block_15))))
theorem ridgeTestInterval256 : Interval ridgeTest 256 384 := by
  intro i hlo hhi
  have h := ridgeTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
