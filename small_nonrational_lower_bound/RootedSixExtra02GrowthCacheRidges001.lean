module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra02GrowthCacheData
public import RootedSixExtra02GrowthCacheRidgeSupport131
public import RootedSixExtra02GrowthCacheRidgeSupport138
public import RootedSixExtra02GrowthCacheRidgeSupport168
public import RootedSixExtra02GrowthCacheRidgeSupport193
public import RootedSixExtra02GrowthCacheRidgeSupport194
public import RootedSixExtra02GrowthCacheRidgeSupport196
public import RootedSixExtra02GrowthCacheRidgeSupport200
public import RootedSixExtra02GrowthCacheRidgeSupport208
public import RootedSixExtra02GrowthCacheRidgeSupport224

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_8 128
theorem ridgeTest_128_block_0 : Interval ridgeTest_128 0 8 := by
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
    exact ridgeTest_large_131
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

theorem ridgeTest_128_block_1 : Interval ridgeTest_128 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    decide +kernel
  by_cases h : i = 9
  · subst i
    decide +kernel
  by_cases h : i = 10
  · subst i
    exact ridgeTest_large_138
  by_cases h : i = 11
  · subst i
    decide +kernel
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

cert_ridgeTest_block_12 128 2 16 24
cert_ridgeTest_block_12 128 3 24 32
cert_ridgeTest_block_12 128 4 32 40
cert_ridgeTest_block_13 128 5 40 168 48 41 42 43 44 45 46 47
cert_ridgeTest_block_12 128 6 48 56
cert_ridgeTest_block_12 128 7 56 64
cert_ridgeTest_block_11 128 8 64 72 65 193 66 194 67 68 196 69 70 71
cert_ridgeTest_block_13 128 9 72 200 80 73 74 75 76 77 78 79
cert_ridgeTest_block_13 128 10 80 208 88 81 82 83 84 85 86 87
cert_ridgeTest_block_12 128 11 88 96
cert_ridgeTest_block_13 128 12 96 224 104 97 98 99 100 101 102 103
cert_ridgeTest_block_12 128 13 104 112
cert_ridgeTest_block_12 128 14 112 120
cert_ridgeTest_block_12 128 15 120 128
cert_ridgeTest_complete_7 128
cert_ridgeTestInterval_5 128 256
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
