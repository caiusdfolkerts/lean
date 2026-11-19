module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
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
    decide +kernel
  by_cases h : i = 14
  · subst i
    decide +kernel
  have h : i = 15 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_12 0 2 16 24
cert_ridgeTest_block_12 0 3 24 32
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

cert_ridgeTest_block_12 0 6 48 56
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

cert_ridgeTest_block_12 0 10 80 88
cert_ridgeTest_block_12 0 11 88 96
cert_ridgeTest_block_12 0 12 96 104
cert_ridgeTest_block_13 0 13 104 104 112 105 106 107 108 109 110 111
cert_ridgeTest_block_12 0 14 112 120
cert_ridgeTest_block_12 0 15 120 128
cert_ridgeTest_complete_7 0
cert_ridgeTestInterval_5 0 128
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
