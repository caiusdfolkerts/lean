module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheData
public import RootedSixExtra00GrowthCacheRidgeSupport896
public import RootedSixExtra00GrowthCacheRidgeSupport900
public import RootedSixExtra00GrowthCacheRidgeSupport904
public import RootedSixExtra00GrowthCacheRidgeSupport960

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_8 896
theorem ridgeTest_896_block_0 : Interval ridgeTest_896 0 8 := by
  intro i hlo hhi
  by_cases h : i = 0
  · subst i
    exact ridgeTest_large_896
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
    exact ridgeTest_large_900
  by_cases h : i = 5
  · subst i
    decide +kernel
  by_cases h : i = 6
  · subst i
    decide +kernel
  have h : i = 7 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_13 896 1 8 904 16 9 10 11 12 13 14 15
cert_ridgeTest_block_12 896 2 16 24
cert_ridgeTest_block_12 896 3 24 32
cert_ridgeTest_block_12 896 4 32 40
cert_ridgeTest_block_12 896 5 40 48
cert_ridgeTest_block_12 896 6 48 56
cert_ridgeTest_block_12 896 7 56 64
cert_ridgeTest_block_13 896 8 64 960 72 65 66 67 68 69 70 71
cert_ridgeTest_block_12 896 9 72 80
cert_ridgeTest_block_12 896 10 80 88
cert_ridgeTest_block_12 896 11 88 96
cert_ridgeTest_block_12 896 12 96 104
cert_ridgeTest_block_12 896 13 104 112
cert_ridgeTest_block_12 896 14 112 120
cert_ridgeTest_block_12 896 15 120 128
cert_ridgeTest_complete_7 896
cert_ridgeTestInterval_5 896 1024
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
