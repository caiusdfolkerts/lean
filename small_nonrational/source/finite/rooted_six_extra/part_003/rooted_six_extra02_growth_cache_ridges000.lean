module
prelude
public import RootedSixExtra02GrowthCacheData
public import RootedSixExtra02GrowthCacheRidgeSupport7
public import RootedSixExtra02GrowthCacheRidgeSupport11
public import RootedSixExtra02GrowthCacheRidgeSupport42
public import RootedSixExtra02GrowthCacheRidgeSupport56
public import RootedSixExtra02GrowthCacheRidgeSupport67
public import RootedSixExtra02GrowthCacheRidgeSupport74
public import RootedSixExtra02GrowthCacheRidgeSupport104

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_0 (i : Nat) := ridgeTest (i+0)
theorem ridgeTest_0_block_0 : Interval ridgeTest_0 0 8 := by
  intro i hlo hhi
  by_cases h : i = 0
  · subst i
    decide +kernel
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
  exact ridgeTest_large_7

theorem ridgeTest_0_block_1 : Interval ridgeTest_0 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    decide +kernel
  by_cases h : i = 9
  · subst i
    decide +kernel
  by_cases h : i = 10
  · subst i
    decide +kernel
  by_cases h : i = 11
  · subst i
    exact ridgeTest_large_11
  by_cases h : i = 12
  · subst i
    decide +kernel
  by_cases h : i = 13
  · subst i
    decide +kernel
  by_cases h : i = 14
  · subst i
    decide +kernel
  have h : i = 15 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_2 : Interval ridgeTest_0 16 24 :=
  interval_of_check ridgeTest_0 16 8 (by decide +kernel)

theorem ridgeTest_0_block_3 : Interval ridgeTest_0 24 32 :=
  interval_of_check ridgeTest_0 24 8 (by decide +kernel)

theorem ridgeTest_0_block_4 : Interval ridgeTest_0 32 40 :=
  interval_of_check ridgeTest_0 32 8 (by decide +kernel)

theorem ridgeTest_0_block_5 : Interval ridgeTest_0 40 48 := by
  intro i hlo hhi
  by_cases h : i = 40
  · subst i
    decide +kernel
  by_cases h : i = 41
  · subst i
    decide +kernel
  by_cases h : i = 42
  · subst i
    exact ridgeTest_large_42
  by_cases h : i = 43
  · subst i
    decide +kernel
  by_cases h : i = 44
  · subst i
    decide +kernel
  by_cases h : i = 45
  · subst i
    decide +kernel
  by_cases h : i = 46
  · subst i
    decide +kernel
  have h : i = 47 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_6 : Interval ridgeTest_0 48 56 :=
  interval_of_check ridgeTest_0 48 8 (by decide +kernel)

theorem ridgeTest_0_block_7 : Interval ridgeTest_0 56 64 := by
  intro i hlo hhi
  by_cases h : i = 56
  · subst i
    exact ridgeTest_large_56
  by_cases h : i = 57
  · subst i
    decide +kernel
  by_cases h : i = 58
  · subst i
    decide +kernel
  by_cases h : i = 59
  · subst i
    decide +kernel
  by_cases h : i = 60
  · subst i
    decide +kernel
  by_cases h : i = 61
  · subst i
    decide +kernel
  by_cases h : i = 62
  · subst i
    decide +kernel
  have h : i = 63 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_8 : Interval ridgeTest_0 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    decide +kernel
  by_cases h : i = 65
  · subst i
    decide +kernel
  by_cases h : i = 66
  · subst i
    decide +kernel
  by_cases h : i = 67
  · subst i
    exact ridgeTest_large_67
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

theorem ridgeTest_0_block_9 : Interval ridgeTest_0 72 80 := by
  intro i hlo hhi
  by_cases h : i = 72
  · subst i
    decide +kernel
  by_cases h : i = 73
  · subst i
    decide +kernel
  by_cases h : i = 74
  · subst i
    exact ridgeTest_large_74
  by_cases h : i = 75
  · subst i
    decide +kernel
  by_cases h : i = 76
  · subst i
    decide +kernel
  by_cases h : i = 77
  · subst i
    decide +kernel
  by_cases h : i = 78
  · subst i
    decide +kernel
  have h : i = 79 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_10 : Interval ridgeTest_0 80 88 :=
  interval_of_check ridgeTest_0 80 8 (by decide +kernel)

theorem ridgeTest_0_block_11 : Interval ridgeTest_0 88 96 :=
  interval_of_check ridgeTest_0 88 8 (by decide +kernel)

theorem ridgeTest_0_block_12 : Interval ridgeTest_0 96 104 :=
  interval_of_check ridgeTest_0 96 8 (by decide +kernel)

theorem ridgeTest_0_block_13 : Interval ridgeTest_0 104 112 := by
  intro i hlo hhi
  by_cases h : i = 104
  · subst i
    exact ridgeTest_large_104
  by_cases h : i = 105
  · subst i
    decide +kernel
  by_cases h : i = 106
  · subst i
    decide +kernel
  by_cases h : i = 107
  · subst i
    decide +kernel
  by_cases h : i = 108
  · subst i
    decide +kernel
  by_cases h : i = 109
  · subst i
    decide +kernel
  by_cases h : i = 110
  · subst i
    decide +kernel
  have h : i = 111 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_14 : Interval ridgeTest_0 112 120 :=
  interval_of_check ridgeTest_0 112 8 (by decide +kernel)

theorem ridgeTest_0_block_15 : Interval ridgeTest_0 120 128 :=
  interval_of_check ridgeTest_0 120 8 (by decide +kernel)

theorem ridgeTest_0_complete : Interval ridgeTest_0 0 128 :=
  (interval_append ridgeTest_0 0 64 128
  (interval_append ridgeTest_0 0 32 64
  (interval_append ridgeTest_0 0 16 32
  (interval_append ridgeTest_0 0 8 16
  ridgeTest_0_block_0
  ridgeTest_0_block_1)
  (interval_append ridgeTest_0 16 24 32
  ridgeTest_0_block_2
  ridgeTest_0_block_3))
  (interval_append ridgeTest_0 32 48 64
  (interval_append ridgeTest_0 32 40 48
  ridgeTest_0_block_4
  ridgeTest_0_block_5)
  (interval_append ridgeTest_0 48 56 64
  ridgeTest_0_block_6
  ridgeTest_0_block_7)))
  (interval_append ridgeTest_0 64 96 128
  (interval_append ridgeTest_0 64 80 96
  (interval_append ridgeTest_0 64 72 80
  ridgeTest_0_block_8
  ridgeTest_0_block_9)
  (interval_append ridgeTest_0 80 88 96
  ridgeTest_0_block_10
  ridgeTest_0_block_11))
  (interval_append ridgeTest_0 96 112 128
  (interval_append ridgeTest_0 96 104 112
  ridgeTest_0_block_12
  ridgeTest_0_block_13)
  (interval_append ridgeTest_0 112 120 128
  ridgeTest_0_block_14
  ridgeTest_0_block_15))))
theorem ridgeTestInterval0 : Interval ridgeTest 0 128 := by
  intro i hlo hhi
  have h := ridgeTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
