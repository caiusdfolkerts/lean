module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheData
public import RootedSixExtra00GrowthCacheRidgeSupport259
public import RootedSixExtra00GrowthCacheRidgeSupport261
public import RootedSixExtra00GrowthCacheRidgeSupport262
public import RootedSixExtra00GrowthCacheRidgeSupport265
public import RootedSixExtra00GrowthCacheRidgeSupport266
public import RootedSixExtra00GrowthCacheRidgeSupport268
public import RootedSixExtra00GrowthCacheRidgeSupport274
public import RootedSixExtra00GrowthCacheRidgeSupport276
public import RootedSixExtra00GrowthCacheRidgeSupport280
public import RootedSixExtra00GrowthCacheRidgeSupport292
public import RootedSixExtra00GrowthCacheRidgeSupport296
public import RootedSixExtra00GrowthCacheRidgeSupport304
public import RootedSixExtra00GrowthCacheRidgeSupport321
public import RootedSixExtra00GrowthCacheRidgeSupport322
public import RootedSixExtra00GrowthCacheRidgeSupport324
public import RootedSixExtra00GrowthCacheRidgeSupport328
public import RootedSixExtra00GrowthCacheRidgeSupport336
public import RootedSixExtra00GrowthCacheRidgeSupport352

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_8 256
theorem ridgeTest_256_block_0 : Interval ridgeTest_256 0 8 := by
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
    exact ridgeTest_large_259
  by_cases h : i = 4
  · subst i
    decide +kernel
  by_cases h : i = 5
  · subst i
    exact ridgeTest_large_261
  by_cases h : i = 6
  · subst i
    exact ridgeTest_large_262
  have h : i = 7 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_11 256 1 8 16 9 265 10 266 11 12 268 13 14 15
theorem ridgeTest_256_block_2 : Interval ridgeTest_256 16 24 := by
  intro i hlo hhi
  by_cases h : i = 16
  · subst i
    decide +kernel
  by_cases h : i = 17
  · subst i
    decide +kernel
  by_cases h : i = 18
  · subst i
    exact ridgeTest_large_274
  by_cases h : i = 19
  · subst i
    decide +kernel
  by_cases h : i = 20
  · subst i
    exact ridgeTest_large_276
  by_cases h : i = 21
  · subst i
    decide +kernel
  by_cases h : i = 22
  · subst i
    decide +kernel
  have h : i = 23 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_13 256 3 24 280 32 25 26 27 28 29 30 31
theorem ridgeTest_256_block_4 : Interval ridgeTest_256 32 40 := by
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
    exact ridgeTest_large_292
  by_cases h : i = 37
  · subst i
    decide +kernel
  by_cases h : i = 38
  · subst i
    decide +kernel
  have h : i = 39 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_13 256 5 40 296 48 41 42 43 44 45 46 47
cert_ridgeTest_block_13 256 6 48 304 56 49 50 51 52 53 54 55
cert_ridgeTest_block_12 256 7 56 64
cert_ridgeTest_block_11 256 8 64 72 65 321 66 322 67 68 324 69 70 71
cert_ridgeTest_block_13 256 9 72 328 80 73 74 75 76 77 78 79
cert_ridgeTest_block_13 256 10 80 336 88 81 82 83 84 85 86 87
cert_ridgeTest_block_12 256 11 88 96
cert_ridgeTest_block_13 256 12 96 352 104 97 98 99 100 101 102 103
cert_ridgeTest_block_12 256 13 104 112
cert_ridgeTest_block_12 256 14 112 120
cert_ridgeTest_block_12 256 15 120 128
cert_ridgeTest_complete_7 256
cert_ridgeTestInterval_5 256 384
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
