module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02GrowthCacheRidgeSupport7
public import RootedSixBase02GrowthCacheRidgeSupport11
public import RootedSixBase02GrowthCacheRidgeSupport42
public import RootedSixBase02GrowthCacheRidgeSupport56
public import RootedSixBase02GrowthCacheRidgeSupport67
public import RootedSixBase02GrowthCacheRidgeSupport69
public import RootedSixBase02GrowthCacheRidgeSupport70
public import RootedSixBase02GrowthCacheRidgeSupport73
public import RootedSixBase02GrowthCacheRidgeSupport74
public import RootedSixBase02GrowthCacheRidgeSupport88
public import RootedSixBase02GrowthCacheRidgeSupport98
public import RootedSixBase02GrowthCacheRidgeSupport104
public import RootedSixBase02GrowthCacheRidgeSupport112

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_7 0
theorem ridgeTest_0_block_0 : Interval ridgeTest_0 0 8 := by
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
    decide +kernel
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
  exact ridgeTest_large_7

theorem ridgeTest_0_block_1 : Interval ridgeTest_0 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    decide +kernel
  by_cases h : i = 9
  · subst i
    decide +kernel
  by_cases h : i = 10
  · subst i
    decide +kernel
  by_cases h : i = 11
  · subst i
    exact ridgeTest_large_11
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

cert_ridgeTest_block_9 0 2 16 24
cert_ridgeTest_block_9 0 3 24 32
cert_ridgeTest_block_9 0 4 32 40
theorem ridgeTest_0_block_5 : Interval ridgeTest_0 40 48 := by
  intro i hlo hhi
  by_cases h : i = 40
  · subst i
    decide +kernel
  by_cases h : i = 41
  · subst i
    decide +kernel
  by_cases h : i = 42
  · subst i
    exact ridgeTest_large_42
  by_cases h : i = 43
  · subst i
    decide +kernel
  by_cases h : i = 44
  · subst i
    decide +kernel
  by_cases h : i = 45
  · subst i
    decide +kernel
  by_cases h : i = 46
  · subst i
    decide +kernel
  have h : i = 47 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_9 0 6 48 56
cert_ridgeTest_block_10 0 7 56 56 64 57 58 59 60 61 62 63
cert_ridgeTest_block_7 0 8 64 72 65 66 67 67 68 69 69 70 70 71
theorem ridgeTest_0_block_9 : Interval ridgeTest_0 72 80 := by
  intro i hlo hhi
  by_cases h : i = 72
  · subst i
    decide +kernel
  by_cases h : i = 73
  · subst i
    exact ridgeTest_large_73
  by_cases h : i = 74
  · subst i
    exact ridgeTest_large_74
  by_cases h : i = 75
  · subst i
    decide +kernel
  by_cases h : i = 76
  · subst i
    decide +kernel
  by_cases h : i = 77
  · subst i
    decide +kernel
  by_cases h : i = 78
  · subst i
    decide +kernel
  have h : i = 79 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_9 0 10 80 88
cert_ridgeTest_block_10 0 11 88 88 96 89 90 91 92 93 94 95
theorem ridgeTest_0_block_12 : Interval ridgeTest_0 96 104 := by
  intro i hlo hhi
  by_cases h : i = 96
  · subst i
    decide +kernel
  by_cases h : i = 97
  · subst i
    decide +kernel
  by_cases h : i = 98
  · subst i
    exact ridgeTest_large_98
  by_cases h : i = 99
  · subst i
    decide +kernel
  by_cases h : i = 100
  · subst i
    decide +kernel
  by_cases h : i = 101
  · subst i
    decide +kernel
  by_cases h : i = 102
  · subst i
    decide +kernel
  have h : i = 103 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_10 0 13 104 104 112 105 106 107 108 109 110 111
cert_ridgeTest_block_10 0 14 112 112 120 113 114 115 116 117 118 119
cert_ridgeTest_block_9 0 15 120 128
cert_ridgeTest_complete_6 0
cert_ridgeTestInterval_4 0 128
end Papers.RationalityTen.RootedCaches.RootedSixBase02
