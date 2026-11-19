module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheData
public import RootedSixExtra00GrowthCacheRidgeSupport385
public import RootedSixExtra00GrowthCacheRidgeSupport386
public import RootedSixExtra00GrowthCacheRidgeSupport388
public import RootedSixExtra00GrowthCacheRidgeSupport392
public import RootedSixExtra00GrowthCacheRidgeSupport400
public import RootedSixExtra00GrowthCacheRidgeSupport416
public import RootedSixExtra00GrowthCacheRidgeSupport448
public import RootedSixExtra00GrowthCacheRidgeSupport452
public import RootedSixExtra00GrowthCacheRidgeSupport456

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_8 384
cert_ridgeTest_block_11 384 0 0 8 1 385 2 386 3 4 388 5 6 7
cert_ridgeTest_block_13 384 1 8 392 16 9 10 11 12 13 14 15
cert_ridgeTest_block_13 384 2 16 400 24 17 18 19 20 21 22 23
cert_ridgeTest_block_12 384 3 24 32
cert_ridgeTest_block_13 384 4 32 416 40 33 34 35 36 37 38 39
cert_ridgeTest_block_12 384 5 40 48
cert_ridgeTest_block_12 384 6 48 56
cert_ridgeTest_block_12 384 7 56 64
theorem ridgeTest_384_block_8 : Interval ridgeTest_384 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    exact ridgeTest_large_448
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
    exact ridgeTest_large_452
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_13 384 9 72 456 80 73 74 75 76 77 78 79
cert_ridgeTest_block_12 384 10 80 88
cert_ridgeTest_block_12 384 11 88 96
cert_ridgeTest_block_12 384 12 96 104
cert_ridgeTest_block_12 384 13 104 112
cert_ridgeTest_block_12 384 14 112 120
cert_ridgeTest_block_12 384 15 120 128
cert_ridgeTest_complete_7 384
cert_ridgeTestInterval_5 384 512
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
