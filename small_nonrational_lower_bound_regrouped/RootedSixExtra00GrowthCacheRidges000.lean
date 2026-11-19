module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
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
cert_ridgeTest_8 0
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

cert_ridgeTest_block_12 0 4 32 40
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

cert_ridgeTest_block_13 0 7 56 56 64 57 58 59 60 61 62 63
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

cert_ridgeTest_block_11 0 9 72 80 73 73 74 74 75 76 76 77 78 79
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

cert_ridgeTest_block_13 0 11 88 88 96 89 90 91 92 93 94 95
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

cert_ridgeTest_block_13 0 13 104 104 112 105 106 107 108 109 110 111
cert_ridgeTest_block_13 0 14 112 112 120 113 114 115 116 117 118 119
cert_ridgeTest_block_12 0 15 120 128
cert_ridgeTest_complete_7 0
cert_ridgeTestInterval_5 0 128
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
