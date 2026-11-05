module
prelude
public import RootedSixExtra00GrowthCacheData
public import RootedSixExtra00GrowthCacheRidgeSupport7
public import RootedSixExtra00GrowthCacheRidgeSupport11
public import RootedSixExtra00GrowthCacheRidgeSupport13
public import RootedSixExtra00GrowthCacheRidgeSupport22
public import RootedSixExtra00GrowthCacheRidgeSupport26
public import RootedSixExtra00GrowthCacheRidgeSupport44
public import RootedSixExtra00GrowthCacheRidgeSupport52
public import RootedSixExtra00GrowthCacheRidgeSupport56
public import RootedSixExtra00GrowthCacheRidgeSupport67
public import RootedSixExtra00GrowthCacheRidgeSupport69
public import RootedSixExtra00GrowthCacheRidgeSupport70
public import RootedSixExtra00GrowthCacheRidgeSupport73
public import RootedSixExtra00GrowthCacheRidgeSupport74
public import RootedSixExtra00GrowthCacheRidgeSupport76
public import RootedSixExtra00GrowthCacheRidgeSupport82
public import RootedSixExtra00GrowthCacheRidgeSupport84
public import RootedSixExtra00GrowthCacheRidgeSupport88
public import RootedSixExtra00GrowthCacheRidgeSupport100
public import RootedSixExtra00GrowthCacheRidgeSupport104
public import RootedSixExtra00GrowthCacheRidgeSupport112

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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
    exact ridgeTest_large_13
  by_cases h : i = 14
  · subst i
    decide +kernel
  have h : i = 15 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_2 : Interval ridgeTest_0 16 24 := by
  intro i hlo hhi
  by_cases h : i = 16
  · subst i
    decide +kernel
  by_cases h : i = 17
  · subst i
    decide +kernel
  by_cases h : i = 18
  · subst i
    decide +kernel
  by_cases h : i = 19
  · subst i
    decide +kernel
  by_cases h : i = 20
  · subst i
    decide +kernel
  by_cases h : i = 21
  · subst i
    decide +kernel
  by_cases h : i = 22
  · subst i
    exact ridgeTest_large_22
  have h : i = 23 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_3 : Interval ridgeTest_0 24 32 := by
  intro i hlo hhi
  by_cases h : i = 24
  · subst i
    decide +kernel
  by_cases h : i = 25
  · subst i
    decide +kernel
  by_cases h : i = 26
  · subst i
    exact ridgeTest_large_26
  by_cases h : i = 27
  · subst i
    decide +kernel
  by_cases h : i = 28
  · subst i
    decide +kernel
  by_cases h : i = 29
  · subst i
    decide +kernel
  by_cases h : i = 30
  · subst i
    decide +kernel
  have h : i = 31 := by omega
  subst i
  decide +kernel

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
    decide +kernel
  by_cases h : i = 43
  · subst i
    decide +kernel
  by_cases h : i = 44
  · subst i
    exact ridgeTest_large_44
  by_cases h : i = 45
  · subst i
    decide +kernel
  by_cases h : i = 46
  · subst i
    decide +kernel
  have h : i = 47 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_6 : Interval ridgeTest_0 48 56 := by
  intro i hlo hhi
  by_cases h : i = 48
  · subst i
    decide +kernel
  by_cases h : i = 49
  · subst i
    decide +kernel
  by_cases h : i = 50
  · subst i
    decide +kernel
  by_cases h : i = 51
  · subst i
    decide +kernel
  by_cases h : i = 52
  · subst i
    exact ridgeTest_large_52
  by_cases h : i = 53
  · subst i
    decide +kernel
  by_cases h : i = 54
  · subst i
    decide +kernel
  have h : i = 55 := by omega
  subst i
  decide +kernel

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
    exact ridgeTest_large_69
  by_cases h : i = 70
  · subst i
    exact ridgeTest_large_70
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
    exact ridgeTest_large_73
  by_cases h : i = 74
  · subst i
    exact ridgeTest_large_74
  by_cases h : i = 75
  · subst i
    decide +kernel
  by_cases h : i = 76
  · subst i
    exact ridgeTest_large_76
  by_cases h : i = 77
  · subst i
    decide +kernel
  by_cases h : i = 78
  · subst i
    decide +kernel
  have h : i = 79 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_10 : Interval ridgeTest_0 80 88 := by
  intro i hlo hhi
  by_cases h : i = 80
  · subst i
    decide +kernel
  by_cases h : i = 81
  · subst i
    decide +kernel
  by_cases h : i = 82
  · subst i
    exact ridgeTest_large_82
  by_cases h : i = 83
  · subst i
    decide +kernel
  by_cases h : i = 84
  · subst i
    exact ridgeTest_large_84
  by_cases h : i = 85
  · subst i
    decide +kernel
  by_cases h : i = 86
  · subst i
    decide +kernel
  have h : i = 87 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_11 : Interval ridgeTest_0 88 96 := by
  intro i hlo hhi
  by_cases h : i = 88
  · subst i
    exact ridgeTest_large_88
  by_cases h : i = 89
  · subst i
    decide +kernel
  by_cases h : i = 90
  · subst i
    decide +kernel
  by_cases h : i = 91
  · subst i
    decide +kernel
  by_cases h : i = 92
  · subst i
    decide +kernel
  by_cases h : i = 93
  · subst i
    decide +kernel
  by_cases h : i = 94
  · subst i
    decide +kernel
  have h : i = 95 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_12 : Interval ridgeTest_0 96 104 := by
  intro i hlo hhi
  by_cases h : i = 96
  · subst i
    decide +kernel
  by_cases h : i = 97
  · subst i
    decide +kernel
  by_cases h : i = 98
  · subst i
    decide +kernel
  by_cases h : i = 99
  · subst i
    decide +kernel
  by_cases h : i = 100
  · subst i
    exact ridgeTest_large_100
  by_cases h : i = 101
  · subst i
    decide +kernel
  by_cases h : i = 102
  · subst i
    decide +kernel
  have h : i = 103 := by omega
  subst i
  decide +kernel

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

theorem ridgeTest_0_block_14 : Interval ridgeTest_0 112 120 := by
  intro i hlo hhi
  by_cases h : i = 112
  · subst i
    exact ridgeTest_large_112
  by_cases h : i = 113
  · subst i
    decide +kernel
  by_cases h : i = 114
  · subst i
    decide +kernel
  by_cases h : i = 115
  · subst i
    decide +kernel
  by_cases h : i = 116
  · subst i
    decide +kernel
  by_cases h : i = 117
  · subst i
    decide +kernel
  by_cases h : i = 118
  · subst i
    decide +kernel
  have h : i = 119 := by omega
  subst i
  decide +kernel

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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
