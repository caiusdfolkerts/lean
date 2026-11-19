module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheData
public import RootedSixExtra00GrowthCacheRidgeSupport131
public import RootedSixExtra00GrowthCacheRidgeSupport133
public import RootedSixExtra00GrowthCacheRidgeSupport134
public import RootedSixExtra00GrowthCacheRidgeSupport137
public import RootedSixExtra00GrowthCacheRidgeSupport138
public import RootedSixExtra00GrowthCacheRidgeSupport140
public import RootedSixExtra00GrowthCacheRidgeSupport146
public import RootedSixExtra00GrowthCacheRidgeSupport148
public import RootedSixExtra00GrowthCacheRidgeSupport152
public import RootedSixExtra00GrowthCacheRidgeSupport164
public import RootedSixExtra00GrowthCacheRidgeSupport168
public import RootedSixExtra00GrowthCacheRidgeSupport176
public import RootedSixExtra00GrowthCacheRidgeSupport193
public import RootedSixExtra00GrowthCacheRidgeSupport194
public import RootedSixExtra00GrowthCacheRidgeSupport196
public import RootedSixExtra00GrowthCacheRidgeSupport200
public import RootedSixExtra00GrowthCacheRidgeSupport208
public import RootedSixExtra00GrowthCacheRidgeSupport224

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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
    exact ridgeTest_large_133
  by_cases h : i = 6
  · subst i
    exact ridgeTest_large_134
  have h : i = 7 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_11 128 1 8 16 9 137 10 138 11 12 140 13 14 15
theorem ridgeTest_128_block_2 : Interval ridgeTest_128 16 24 := by
  intro i hlo hhi
  by_cases h : i = 16
  · subst i
    decide +kernel
  by_cases h : i = 17
  · subst i
    decide +kernel
  by_cases h : i = 18
  · subst i
    exact ridgeTest_large_146
  by_cases h : i = 19
  · subst i
    decide +kernel
  by_cases h : i = 20
  · subst i
    exact ridgeTest_large_148
  by_cases h : i = 21
  · subst i
    decide +kernel
  by_cases h : i = 22
  · subst i
    decide +kernel
  have h : i = 23 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_13 128 3 24 152 32 25 26 27 28 29 30 31
theorem ridgeTest_128_block_4 : Interval ridgeTest_128 32 40 := by
  intro i hlo hhi
  by_cases h : i = 32
  · subst i
    decide +kernel
  by_cases h : i = 33
  · subst i
    decide +kernel
  by_cases h : i = 34
  · subst i
    decide +kernel
  by_cases h : i = 35
  · subst i
    decide +kernel
  by_cases h : i = 36
  · subst i
    exact ridgeTest_large_164
  by_cases h : i = 37
  · subst i
    decide +kernel
  by_cases h : i = 38
  · subst i
    decide +kernel
  have h : i = 39 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_13 128 5 40 168 48 41 42 43 44 45 46 47
cert_ridgeTest_block_13 128 6 48 176 56 49 50 51 52 53 54 55
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
