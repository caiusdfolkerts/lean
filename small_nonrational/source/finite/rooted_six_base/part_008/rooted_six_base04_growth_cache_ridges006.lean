module
prelude
public import RootedSixBase04GrowthCacheData
public import RootedSixBase04GrowthCacheRidgeSupport832

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_768 (i : Nat) := ridgeTest (i+768)
theorem ridgeTest_768_block_0 : Interval ridgeTest_768 0 8 :=
  interval_of_check ridgeTest_768 0 8 (by decide +kernel)

theorem ridgeTest_768_block_1 : Interval ridgeTest_768 8 16 :=
  interval_of_check ridgeTest_768 8 8 (by decide +kernel)

theorem ridgeTest_768_block_2 : Interval ridgeTest_768 16 24 :=
  interval_of_check ridgeTest_768 16 8 (by decide +kernel)

theorem ridgeTest_768_block_3 : Interval ridgeTest_768 24 32 :=
  interval_of_check ridgeTest_768 24 8 (by decide +kernel)

theorem ridgeTest_768_block_4 : Interval ridgeTest_768 32 40 :=
  interval_of_check ridgeTest_768 32 8 (by decide +kernel)

theorem ridgeTest_768_block_5 : Interval ridgeTest_768 40 48 :=
  interval_of_check ridgeTest_768 40 8 (by decide +kernel)

theorem ridgeTest_768_block_6 : Interval ridgeTest_768 48 56 :=
  interval_of_check ridgeTest_768 48 8 (by decide +kernel)

theorem ridgeTest_768_block_7 : Interval ridgeTest_768 56 64 :=
  interval_of_check ridgeTest_768 56 8 (by decide +kernel)

theorem ridgeTest_768_block_8 : Interval ridgeTest_768 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    exact ridgeTest_large_832
  by_cases h : i = 65
  · subst i
    decide +kernel
  by_cases h : i = 66
  · subst i
    decide +kernel
  by_cases h : i = 67
  · subst i
    decide +kernel
  by_cases h : i = 68
  · subst i
    decide +kernel
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

theorem ridgeTest_768_block_9 : Interval ridgeTest_768 72 80 :=
  interval_of_check ridgeTest_768 72 8 (by decide +kernel)

theorem ridgeTest_768_block_10 : Interval ridgeTest_768 80 88 :=
  interval_of_check ridgeTest_768 80 8 (by decide +kernel)

theorem ridgeTest_768_block_11 : Interval ridgeTest_768 88 96 :=
  interval_of_check ridgeTest_768 88 8 (by decide +kernel)

theorem ridgeTest_768_block_12 : Interval ridgeTest_768 96 104 :=
  interval_of_check ridgeTest_768 96 8 (by decide +kernel)

theorem ridgeTest_768_block_13 : Interval ridgeTest_768 104 112 :=
  interval_of_check ridgeTest_768 104 8 (by decide +kernel)

theorem ridgeTest_768_block_14 : Interval ridgeTest_768 112 120 :=
  interval_of_check ridgeTest_768 112 8 (by decide +kernel)

theorem ridgeTest_768_block_15 : Interval ridgeTest_768 120 128 :=
  interval_of_check ridgeTest_768 120 8 (by decide +kernel)

theorem ridgeTest_768_complete : Interval ridgeTest_768 0 128 :=
  (interval_append ridgeTest_768 0 64 128
  (interval_append ridgeTest_768 0 32 64
  (interval_append ridgeTest_768 0 16 32
  (interval_append ridgeTest_768 0 8 16
  ridgeTest_768_block_0
  ridgeTest_768_block_1)
  (interval_append ridgeTest_768 16 24 32
  ridgeTest_768_block_2
  ridgeTest_768_block_3))
  (interval_append ridgeTest_768 32 48 64
  (interval_append ridgeTest_768 32 40 48
  ridgeTest_768_block_4
  ridgeTest_768_block_5)
  (interval_append ridgeTest_768 48 56 64
  ridgeTest_768_block_6
  ridgeTest_768_block_7)))
  (interval_append ridgeTest_768 64 96 128
  (interval_append ridgeTest_768 64 80 96
  (interval_append ridgeTest_768 64 72 80
  ridgeTest_768_block_8
  ridgeTest_768_block_9)
  (interval_append ridgeTest_768 80 88 96
  ridgeTest_768_block_10
  ridgeTest_768_block_11))
  (interval_append ridgeTest_768 96 112 128
  (interval_append ridgeTest_768 96 104 112
  ridgeTest_768_block_12
  ridgeTest_768_block_13)
  (interval_append ridgeTest_768 112 120 128
  ridgeTest_768_block_14
  ridgeTest_768_block_15))))
theorem ridgeTestInterval768 : Interval ridgeTest 768 896 := by
  intro i hlo hhi
  have h := ridgeTest_768_complete (i-768) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase04
