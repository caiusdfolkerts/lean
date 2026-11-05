module
prelude
public import RootedSixExtra06GrowthCacheData
public import RootedSixExtra06GrowthCacheRidgeSupport896

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_896 (i : Nat) := ridgeTest (i+896)
theorem ridgeTest_896_block_0 : Interval ridgeTest_896 0 8 := by
  intro i hlo hhi
  by_cases h : i = 0
  · subst i
    exact ridgeTest_large_896
  by_cases h : i = 1
  · subst i
    decide +kernel
  by_cases h : i = 2
  · subst i
    decide +kernel
  by_cases h : i = 3
  · subst i
    decide +kernel
  by_cases h : i = 4
  · subst i
    decide +kernel
  by_cases h : i = 5
  · subst i
    decide +kernel
  by_cases h : i = 6
  · subst i
    decide +kernel
  have h : i = 7 := by omega
  subst i
  decide +kernel

theorem ridgeTest_896_block_1 : Interval ridgeTest_896 8 16 :=
  interval_of_check ridgeTest_896 8 8 (by decide +kernel)

theorem ridgeTest_896_block_2 : Interval ridgeTest_896 16 24 :=
  interval_of_check ridgeTest_896 16 8 (by decide +kernel)

theorem ridgeTest_896_block_3 : Interval ridgeTest_896 24 32 :=
  interval_of_check ridgeTest_896 24 8 (by decide +kernel)

theorem ridgeTest_896_block_4 : Interval ridgeTest_896 32 40 :=
  interval_of_check ridgeTest_896 32 8 (by decide +kernel)

theorem ridgeTest_896_block_5 : Interval ridgeTest_896 40 48 :=
  interval_of_check ridgeTest_896 40 8 (by decide +kernel)

theorem ridgeTest_896_block_6 : Interval ridgeTest_896 48 56 :=
  interval_of_check ridgeTest_896 48 8 (by decide +kernel)

theorem ridgeTest_896_block_7 : Interval ridgeTest_896 56 64 :=
  interval_of_check ridgeTest_896 56 8 (by decide +kernel)

theorem ridgeTest_896_block_8 : Interval ridgeTest_896 64 72 :=
  interval_of_check ridgeTest_896 64 8 (by decide +kernel)

theorem ridgeTest_896_block_9 : Interval ridgeTest_896 72 80 :=
  interval_of_check ridgeTest_896 72 8 (by decide +kernel)

theorem ridgeTest_896_block_10 : Interval ridgeTest_896 80 88 :=
  interval_of_check ridgeTest_896 80 8 (by decide +kernel)

theorem ridgeTest_896_block_11 : Interval ridgeTest_896 88 96 :=
  interval_of_check ridgeTest_896 88 8 (by decide +kernel)

theorem ridgeTest_896_block_12 : Interval ridgeTest_896 96 104 :=
  interval_of_check ridgeTest_896 96 8 (by decide +kernel)

theorem ridgeTest_896_block_13 : Interval ridgeTest_896 104 112 :=
  interval_of_check ridgeTest_896 104 8 (by decide +kernel)

theorem ridgeTest_896_block_14 : Interval ridgeTest_896 112 120 :=
  interval_of_check ridgeTest_896 112 8 (by decide +kernel)

theorem ridgeTest_896_block_15 : Interval ridgeTest_896 120 128 :=
  interval_of_check ridgeTest_896 120 8 (by decide +kernel)

theorem ridgeTest_896_complete : Interval ridgeTest_896 0 128 :=
  (interval_append ridgeTest_896 0 64 128
  (interval_append ridgeTest_896 0 32 64
  (interval_append ridgeTest_896 0 16 32
  (interval_append ridgeTest_896 0 8 16
  ridgeTest_896_block_0
  ridgeTest_896_block_1)
  (interval_append ridgeTest_896 16 24 32
  ridgeTest_896_block_2
  ridgeTest_896_block_3))
  (interval_append ridgeTest_896 32 48 64
  (interval_append ridgeTest_896 32 40 48
  ridgeTest_896_block_4
  ridgeTest_896_block_5)
  (interval_append ridgeTest_896 48 56 64
  ridgeTest_896_block_6
  ridgeTest_896_block_7)))
  (interval_append ridgeTest_896 64 96 128
  (interval_append ridgeTest_896 64 80 96
  (interval_append ridgeTest_896 64 72 80
  ridgeTest_896_block_8
  ridgeTest_896_block_9)
  (interval_append ridgeTest_896 80 88 96
  ridgeTest_896_block_10
  ridgeTest_896_block_11))
  (interval_append ridgeTest_896 96 112 128
  (interval_append ridgeTest_896 96 104 112
  ridgeTest_896_block_12
  ridgeTest_896_block_13)
  (interval_append ridgeTest_896 112 120 128
  ridgeTest_896_block_14
  ridgeTest_896_block_15))))
theorem ridgeTestInterval896 : Interval ridgeTest 896 1024 := by
  intro i hlo hhi
  have h := ridgeTest_896_complete (i-896) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
