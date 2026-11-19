module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheData
public import RootedSixExtra00GrowthCacheRidgeSupport769
public import RootedSixExtra00GrowthCacheRidgeSupport770
public import RootedSixExtra00GrowthCacheRidgeSupport772
public import RootedSixExtra00GrowthCacheRidgeSupport776
public import RootedSixExtra00GrowthCacheRidgeSupport784
public import RootedSixExtra00GrowthCacheRidgeSupport800
public import RootedSixExtra00GrowthCacheRidgeSupport832
public import RootedSixExtra00GrowthCacheRidgeSupport836
public import RootedSixExtra00GrowthCacheRidgeSupport840

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_8 768
cert_ridgeTest_block_11 768 0 0 8 1 769 2 770 3 4 772 5 6 7
cert_ridgeTest_block_13 768 1 8 776 16 9 10 11 12 13 14 15
cert_ridgeTest_block_13 768 2 16 784 24 17 18 19 20 21 22 23
cert_ridgeTest_block_12 768 3 24 32
cert_ridgeTest_block_13 768 4 32 800 40 33 34 35 36 37 38 39
cert_ridgeTest_block_12 768 5 40 48
cert_ridgeTest_block_12 768 6 48 56
cert_ridgeTest_block_12 768 7 56 64
theorem ridgeTest_768_block_8 : Interval ridgeTest_768 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    exact ridgeTest_large_832
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
    exact ridgeTest_large_836
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_13 768 9 72 840 80 73 74 75 76 77 78 79
cert_ridgeTest_block_12 768 10 80 88
cert_ridgeTest_block_12 768 11 88 96
cert_ridgeTest_block_12 768 12 96 104
cert_ridgeTest_block_12 768 13 104 112
cert_ridgeTest_block_12 768 14 112 120
cert_ridgeTest_block_12 768 15 120 128
cert_ridgeTest_complete_7 768
cert_ridgeTestInterval_5 768 896
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
