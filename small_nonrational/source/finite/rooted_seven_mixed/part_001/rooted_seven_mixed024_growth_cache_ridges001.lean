module
prelude
public import RootedSevenMixed024GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed024
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_128 (i : Nat) := ridgeTest (i+128)
theorem ridgeTest_128_block_0 : Interval ridgeTest_128 0 8 :=
  interval_of_check ridgeTest_128 0 8 (by decide +kernel)

theorem ridgeTest_128_block_1 : Interval ridgeTest_128 8 16 :=
  interval_of_check ridgeTest_128 8 8 (by decide +kernel)

theorem ridgeTest_128_block_2 : Interval ridgeTest_128 16 24 :=
  interval_of_check ridgeTest_128 16 8 (by decide +kernel)

theorem ridgeTest_128_block_3 : Interval ridgeTest_128 24 32 :=
  interval_of_check ridgeTest_128 24 8 (by decide +kernel)

theorem ridgeTest_128_block_4 : Interval ridgeTest_128 32 40 :=
  interval_of_check ridgeTest_128 32 8 (by decide +kernel)

theorem ridgeTest_128_block_5 : Interval ridgeTest_128 40 48 :=
  interval_of_check ridgeTest_128 40 8 (by decide +kernel)

theorem ridgeTest_128_block_6 : Interval ridgeTest_128 48 56 :=
  interval_of_check ridgeTest_128 48 8 (by decide +kernel)

theorem ridgeTest_128_block_7 : Interval ridgeTest_128 56 64 :=
  interval_of_check ridgeTest_128 56 8 (by decide +kernel)

theorem ridgeTest_128_block_8 : Interval ridgeTest_128 64 72 :=
  interval_of_check ridgeTest_128 64 8 (by decide +kernel)

theorem ridgeTest_128_block_9 : Interval ridgeTest_128 72 80 :=
  interval_of_check ridgeTest_128 72 8 (by decide +kernel)

theorem ridgeTest_128_block_10 : Interval ridgeTest_128 80 88 :=
  interval_of_check ridgeTest_128 80 8 (by decide +kernel)

theorem ridgeTest_128_block_11 : Interval ridgeTest_128 88 96 :=
  interval_of_check ridgeTest_128 88 8 (by decide +kernel)

theorem ridgeTest_128_block_12 : Interval ridgeTest_128 96 104 :=
  interval_of_check ridgeTest_128 96 8 (by decide +kernel)

theorem ridgeTest_128_block_13 : Interval ridgeTest_128 104 112 :=
  interval_of_check ridgeTest_128 104 8 (by decide +kernel)

theorem ridgeTest_128_block_14 : Interval ridgeTest_128 112 120 :=
  interval_of_check ridgeTest_128 112 8 (by decide +kernel)

theorem ridgeTest_128_block_15 : Interval ridgeTest_128 120 128 :=
  interval_of_check ridgeTest_128 120 8 (by decide +kernel)

theorem ridgeTest_128_complete : Interval ridgeTest_128 0 128 :=
  (interval_append ridgeTest_128 0 64 128
  (interval_append ridgeTest_128 0 32 64
  (interval_append ridgeTest_128 0 16 32
  (interval_append ridgeTest_128 0 8 16
  ridgeTest_128_block_0
  ridgeTest_128_block_1)
  (interval_append ridgeTest_128 16 24 32
  ridgeTest_128_block_2
  ridgeTest_128_block_3))
  (interval_append ridgeTest_128 32 48 64
  (interval_append ridgeTest_128 32 40 48
  ridgeTest_128_block_4
  ridgeTest_128_block_5)
  (interval_append ridgeTest_128 48 56 64
  ridgeTest_128_block_6
  ridgeTest_128_block_7)))
  (interval_append ridgeTest_128 64 96 128
  (interval_append ridgeTest_128 64 80 96
  (interval_append ridgeTest_128 64 72 80
  ridgeTest_128_block_8
  ridgeTest_128_block_9)
  (interval_append ridgeTest_128 80 88 96
  ridgeTest_128_block_10
  ridgeTest_128_block_11))
  (interval_append ridgeTest_128 96 112 128
  (interval_append ridgeTest_128 96 104 112
  ridgeTest_128_block_12
  ridgeTest_128_block_13)
  (interval_append ridgeTest_128 112 120 128
  ridgeTest_128_block_14
  ridgeTest_128_block_15))))
theorem ridgeTestInterval128 : Interval ridgeTest 128 256 := by
  intro i hlo hhi
  have h := ridgeTest_128_complete (i-128) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed024
