module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02GrowthCacheRidgeSupport515
public import RootedSixBase02GrowthCacheRidgeSupport517
public import RootedSixBase02GrowthCacheRidgeSupport518
public import RootedSixBase02GrowthCacheRidgeSupport521
public import RootedSixBase02GrowthCacheRidgeSupport522
public import RootedSixBase02GrowthCacheRidgeSupport536
public import RootedSixBase02GrowthCacheRidgeSupport546
public import RootedSixBase02GrowthCacheRidgeSupport552
public import RootedSixBase02GrowthCacheRidgeSupport560
public import RootedSixBase02GrowthCacheRidgeSupport577
public import RootedSixBase02GrowthCacheRidgeSupport578
public import RootedSixBase02GrowthCacheRidgeSupport580
public import RootedSixBase02GrowthCacheRidgeSupport584
public import RootedSixBase02GrowthCacheRidgeSupport592
public import RootedSixBase02GrowthCacheRidgeSupport608

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_7 512
cert_ridgeTest_block_7 512 0 0 8 1 2 3 515 4 5 517 6 518 7
theorem ridgeTest_512_block_1 : Interval ridgeTest_512 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    decide +kernel
  by_cases h : i = 9
  · subst i
    exact ridgeTest_large_521
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

cert_ridgeTest_block_9 512 2 16 24
cert_ridgeTest_block_10 512 3 24 536 32 25 26 27 28 29 30 31
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
    exact ridgeTest_large_546
  by_cases h : i = 35
  · subst i
    decide +kernel
  by_cases h : i = 36
  · subst i
    decide +kernel
  by_cases h : i = 37
  · subst i
    decide +kernel
  by_cases h : i = 38
  · subst i
    decide +kernel
  have h : i = 39 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_10 512 5 40 552 48 41 42 43 44 45 46 47
cert_ridgeTest_block_10 512 6 48 560 56 49 50 51 52 53 54 55
cert_ridgeTest_block_9 512 7 56 64
cert_ridgeTest_block_6 512 8 64 72 65 577 66 578 67 68 580 69 70 71
cert_ridgeTest_block_10 512 9 72 584 80 73 74 75 76 77 78 79
cert_ridgeTest_block_10 512 10 80 592 88 81 82 83 84 85 86 87
cert_ridgeTest_block_9 512 11 88 96
cert_ridgeTest_block_10 512 12 96 608 104 97 98 99 100 101 102 103
cert_ridgeTest_block_9 512 13 104 112
cert_ridgeTest_block_9 512 14 112 120
cert_ridgeTest_block_9 512 15 120 128
cert_ridgeTest_complete_6 512
cert_ridgeTestInterval_4 512 640
end Papers.RationalityTen.RootedCaches.RootedSixBase02
