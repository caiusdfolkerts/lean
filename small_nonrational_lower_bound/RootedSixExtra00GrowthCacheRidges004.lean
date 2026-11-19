module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheData
public import RootedSixExtra00GrowthCacheRidgeSupport515
public import RootedSixExtra00GrowthCacheRidgeSupport517
public import RootedSixExtra00GrowthCacheRidgeSupport518
public import RootedSixExtra00GrowthCacheRidgeSupport521
public import RootedSixExtra00GrowthCacheRidgeSupport522
public import RootedSixExtra00GrowthCacheRidgeSupport524
public import RootedSixExtra00GrowthCacheRidgeSupport530
public import RootedSixExtra00GrowthCacheRidgeSupport532
public import RootedSixExtra00GrowthCacheRidgeSupport536
public import RootedSixExtra00GrowthCacheRidgeSupport548
public import RootedSixExtra00GrowthCacheRidgeSupport552
public import RootedSixExtra00GrowthCacheRidgeSupport560
public import RootedSixExtra00GrowthCacheRidgeSupport577
public import RootedSixExtra00GrowthCacheRidgeSupport578
public import RootedSixExtra00GrowthCacheRidgeSupport580
public import RootedSixExtra00GrowthCacheRidgeSupport584
public import RootedSixExtra00GrowthCacheRidgeSupport592
public import RootedSixExtra00GrowthCacheRidgeSupport608

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_8 512
theorem ridgeTest_512_block_0 : Interval ridgeTest_512 0 8 := by
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
    exact ridgeTest_large_515
  by_cases h : i = 4
  · subst i
    decide +kernel
  by_cases h : i = 5
  · subst i
    exact ridgeTest_large_517
  by_cases h : i = 6
  · subst i
    exact ridgeTest_large_518
  have h : i = 7 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_11 512 1 8 16 9 521 10 522 11 12 524 13 14 15
theorem ridgeTest_512_block_2 : Interval ridgeTest_512 16 24 := by
  intro i hlo hhi
  by_cases h : i = 16
  · subst i
    decide +kernel
  by_cases h : i = 17
  · subst i
    decide +kernel
  by_cases h : i = 18
  · subst i
    exact ridgeTest_large_530
  by_cases h : i = 19
  · subst i
    decide +kernel
  by_cases h : i = 20
  · subst i
    exact ridgeTest_large_532
  by_cases h : i = 21
  · subst i
    decide +kernel
  by_cases h : i = 22
  · subst i
    decide +kernel
  have h : i = 23 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_13 512 3 24 536 32 25 26 27 28 29 30 31
theorem ridgeTest_512_block_4 : Interval ridgeTest_512 32 40 := by
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
    exact ridgeTest_large_548
  by_cases h : i = 37
  · subst i
    decide +kernel
  by_cases h : i = 38
  · subst i
    decide +kernel
  have h : i = 39 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_13 512 5 40 552 48 41 42 43 44 45 46 47
cert_ridgeTest_block_13 512 6 48 560 56 49 50 51 52 53 54 55
cert_ridgeTest_block_12 512 7 56 64
cert_ridgeTest_block_11 512 8 64 72 65 577 66 578 67 68 580 69 70 71
cert_ridgeTest_block_13 512 9 72 584 80 73 74 75 76 77 78 79
cert_ridgeTest_block_13 512 10 80 592 88 81 82 83 84 85 86 87
cert_ridgeTest_block_12 512 11 88 96
cert_ridgeTest_block_13 512 12 96 608 104 97 98 99 100 101 102 103
cert_ridgeTest_block_12 512 13 104 112
cert_ridgeTest_block_12 512 14 112 120
cert_ridgeTest_block_12 512 15 120 128
cert_ridgeTest_complete_7 512
cert_ridgeTestInterval_5 512 640
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
