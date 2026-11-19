module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra02GrowthCacheData
public import RootedSixExtra02GrowthCacheRidgeSupport515
public import RootedSixExtra02GrowthCacheRidgeSupport522
public import RootedSixExtra02GrowthCacheRidgeSupport552
public import RootedSixExtra02GrowthCacheRidgeSupport577
public import RootedSixExtra02GrowthCacheRidgeSupport578
public import RootedSixExtra02GrowthCacheRidgeSupport580
public import RootedSixExtra02GrowthCacheRidgeSupport584
public import RootedSixExtra02GrowthCacheRidgeSupport592
public import RootedSixExtra02GrowthCacheRidgeSupport608

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
    decide +kernel
  by_cases h : i = 6
  · subst i
    decide +kernel
  have h : i = 7 := by omega
  subst i
  decide +kernel

theorem ridgeTest_512_block_1 : Interval ridgeTest_512 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    decide +kernel
  by_cases h : i = 9
  · subst i
    decide +kernel
  by_cases h : i = 10
  · subst i
    exact ridgeTest_large_522
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

cert_ridgeTest_block_12 512 2 16 24
cert_ridgeTest_block_12 512 3 24 32
cert_ridgeTest_block_12 512 4 32 40
cert_ridgeTest_block_13 512 5 40 552 48 41 42 43 44 45 46 47
cert_ridgeTest_block_12 512 6 48 56
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
