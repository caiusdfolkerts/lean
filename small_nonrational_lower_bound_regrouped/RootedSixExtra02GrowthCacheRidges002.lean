module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra02GrowthCacheData
public import RootedSixExtra02GrowthCacheRidgeSupport259
public import RootedSixExtra02GrowthCacheRidgeSupport266
public import RootedSixExtra02GrowthCacheRidgeSupport296
public import RootedSixExtra02GrowthCacheRidgeSupport321
public import RootedSixExtra02GrowthCacheRidgeSupport322
public import RootedSixExtra02GrowthCacheRidgeSupport324
public import RootedSixExtra02GrowthCacheRidgeSupport328
public import RootedSixExtra02GrowthCacheRidgeSupport336
public import RootedSixExtra02GrowthCacheRidgeSupport352

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
    decide +kernel
  by_cases h : i = 6
  · subst i
    decide +kernel
  have h : i = 7 := by omega
  subst i
  decide +kernel

theorem ridgeTest_256_block_1 : Interval ridgeTest_256 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    decide +kernel
  by_cases h : i = 9
  · subst i
    decide +kernel
  by_cases h : i = 10
  · subst i
    exact ridgeTest_large_266
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

cert_ridgeTest_block_12 256 2 16 24
cert_ridgeTest_block_12 256 3 24 32
cert_ridgeTest_block_12 256 4 32 40
cert_ridgeTest_block_13 256 5 40 296 48 41 42 43 44 45 46 47
cert_ridgeTest_block_12 256 6 48 56
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
