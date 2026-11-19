module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheData
public import RootedSixExtra00GrowthCacheRidgeSupport641
public import RootedSixExtra00GrowthCacheRidgeSupport642
public import RootedSixExtra00GrowthCacheRidgeSupport644
public import RootedSixExtra00GrowthCacheRidgeSupport648
public import RootedSixExtra00GrowthCacheRidgeSupport656
public import RootedSixExtra00GrowthCacheRidgeSupport672
public import RootedSixExtra00GrowthCacheRidgeSupport704
public import RootedSixExtra00GrowthCacheRidgeSupport708
public import RootedSixExtra00GrowthCacheRidgeSupport712

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_8 640
cert_ridgeTest_block_11 640 0 0 8 1 641 2 642 3 4 644 5 6 7
cert_ridgeTest_block_13 640 1 8 648 16 9 10 11 12 13 14 15
cert_ridgeTest_block_13 640 2 16 656 24 17 18 19 20 21 22 23
cert_ridgeTest_block_12 640 3 24 32
cert_ridgeTest_block_13 640 4 32 672 40 33 34 35 36 37 38 39
cert_ridgeTest_block_12 640 5 40 48
cert_ridgeTest_block_12 640 6 48 56
cert_ridgeTest_block_12 640 7 56 64
theorem ridgeTest_640_block_8 : Interval ridgeTest_640 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    exact ridgeTest_large_704
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
    exact ridgeTest_large_708
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_13 640 9 72 712 80 73 74 75 76 77 78 79
cert_ridgeTest_block_12 640 10 80 88
cert_ridgeTest_block_12 640 11 88 96
cert_ridgeTest_block_12 640 12 96 104
cert_ridgeTest_block_12 640 13 104 112
cert_ridgeTest_block_12 640 14 112 120
cert_ridgeTest_block_12 640 15 120 128
cert_ridgeTest_complete_7 640
cert_ridgeTestInterval_5 640 768
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
