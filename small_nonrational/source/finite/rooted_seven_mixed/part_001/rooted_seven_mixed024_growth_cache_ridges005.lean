module
prelude
public import RootedSevenMixed024GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed024
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_640 (i : Nat) := ridgeTest (i+640)
theorem ridgeTest_640_block_0 : Interval ridgeTest_640 0 8 :=
  interval_of_check ridgeTest_640 0 8 (by decide +kernel)

theorem ridgeTest_640_block_1 : Interval ridgeTest_640 8 16 :=
  interval_of_check ridgeTest_640 8 8 (by decide +kernel)

theorem ridgeTest_640_block_2 : Interval ridgeTest_640 16 24 :=
  interval_of_check ridgeTest_640 16 8 (by decide +kernel)

theorem ridgeTest_640_block_3 : Interval ridgeTest_640 24 32 :=
  interval_of_check ridgeTest_640 24 8 (by decide +kernel)

theorem ridgeTest_640_block_4 : Interval ridgeTest_640 32 40 :=
  interval_of_check ridgeTest_640 32 8 (by decide +kernel)

theorem ridgeTest_640_block_5 : Interval ridgeTest_640 40 48 :=
  interval_of_check ridgeTest_640 40 8 (by decide +kernel)

theorem ridgeTest_640_block_6 : Interval ridgeTest_640 48 56 :=
  interval_of_check ridgeTest_640 48 8 (by decide +kernel)

theorem ridgeTest_640_block_7 : Interval ridgeTest_640 56 64 :=
  interval_of_check ridgeTest_640 56 8 (by decide +kernel)

theorem ridgeTest_640_block_8 : Interval ridgeTest_640 64 72 :=
  interval_of_check ridgeTest_640 64 8 (by decide +kernel)

theorem ridgeTest_640_block_9 : Interval ridgeTest_640 72 80 :=
  interval_of_check ridgeTest_640 72 8 (by decide +kernel)

theorem ridgeTest_640_block_10 : Interval ridgeTest_640 80 88 :=
  interval_of_check ridgeTest_640 80 8 (by decide +kernel)

theorem ridgeTest_640_block_11 : Interval ridgeTest_640 88 96 :=
  interval_of_check ridgeTest_640 88 8 (by decide +kernel)

theorem ridgeTest_640_block_12 : Interval ridgeTest_640 96 104 :=
  interval_of_check ridgeTest_640 96 8 (by decide +kernel)

theorem ridgeTest_640_block_13 : Interval ridgeTest_640 104 112 :=
  interval_of_check ridgeTest_640 104 8 (by decide +kernel)

theorem ridgeTest_640_block_14 : Interval ridgeTest_640 112 120 :=
  interval_of_check ridgeTest_640 112 8 (by decide +kernel)

theorem ridgeTest_640_block_15 : Interval ridgeTest_640 120 128 :=
  interval_of_check ridgeTest_640 120 8 (by decide +kernel)

theorem ridgeTest_640_complete : Interval ridgeTest_640 0 128 :=
  (interval_append ridgeTest_640 0 64 128
  (interval_append ridgeTest_640 0 32 64
  (interval_append ridgeTest_640 0 16 32
  (interval_append ridgeTest_640 0 8 16
  ridgeTest_640_block_0
  ridgeTest_640_block_1)
  (interval_append ridgeTest_640 16 24 32
  ridgeTest_640_block_2
  ridgeTest_640_block_3))
  (interval_append ridgeTest_640 32 48 64
  (interval_append ridgeTest_640 32 40 48
  ridgeTest_640_block_4
  ridgeTest_640_block_5)
  (interval_append ridgeTest_640 48 56 64
  ridgeTest_640_block_6
  ridgeTest_640_block_7)))
  (interval_append ridgeTest_640 64 96 128
  (interval_append ridgeTest_640 64 80 96
  (interval_append ridgeTest_640 64 72 80
  ridgeTest_640_block_8
  ridgeTest_640_block_9)
  (interval_append ridgeTest_640 80 88 96
  ridgeTest_640_block_10
  ridgeTest_640_block_11))
  (interval_append ridgeTest_640 96 112 128
  (interval_append ridgeTest_640 96 104 112
  ridgeTest_640_block_12
  ridgeTest_640_block_13)
  (interval_append ridgeTest_640 112 120 128
  ridgeTest_640_block_14
  ridgeTest_640_block_15))))
theorem ridgeTestInterval640 : Interval ridgeTest 640 768 := by
  intro i hlo hhi
  have h := ridgeTest_640_complete (i-640) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed024
