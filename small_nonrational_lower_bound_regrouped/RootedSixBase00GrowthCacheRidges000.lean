module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase00GrowthCacheData
public import RootedSixBase00GrowthCacheRidgeSupport7
public import RootedSixBase00GrowthCacheRidgeSupport11
public import RootedSixBase00GrowthCacheRidgeSupport13
public import RootedSixBase00GrowthCacheRidgeSupport22
public import RootedSixBase00GrowthCacheRidgeSupport26
public import RootedSixBase00GrowthCacheRidgeSupport44
public import RootedSixBase00GrowthCacheRidgeSupport52
public import RootedSixBase00GrowthCacheRidgeSupport56
public import RootedSixBase00GrowthCacheRidgeSupport67
public import RootedSixBase00GrowthCacheRidgeSupport69
public import RootedSixBase00GrowthCacheRidgeSupport70
public import RootedSixBase00GrowthCacheRidgeSupport73
public import RootedSixBase00GrowthCacheRidgeSupport74
public import RootedSixBase00GrowthCacheRidgeSupport76
public import RootedSixBase00GrowthCacheRidgeSupport82
public import RootedSixBase00GrowthCacheRidgeSupport84
public import RootedSixBase00GrowthCacheRidgeSupport88
public import RootedSixBase00GrowthCacheRidgeSupport100
public import RootedSixBase00GrowthCacheRidgeSupport104
public import RootedSixBase00GrowthCacheRidgeSupport112

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
    exact ridgeTest_large_13
  by_cases h : i = 14
  · subst i
    decide +kernel
  have h : i = 15 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_2 : Interval ridgeTest_0 16 24 := by
  intro i hlo hhi
  by_cases h : i = 16
  · subst i
    decide +kernel
  by_cases h : i = 17
  · subst i
    decide +kernel
  by_cases h : i = 18
  · subst i
    decide +kernel
  by_cases h : i = 19
  · subst i
    decide +kernel
  by_cases h : i = 20
  · subst i
    decide +kernel
  by_cases h : i = 21
  · subst i
    decide +kernel
  by_cases h : i = 22
  · subst i
    exact ridgeTest_large_22
  have h : i = 23 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_3 : Interval ridgeTest_0 24 32 := by
  intro i hlo hhi
  by_cases h : i = 24
  · subst i
    decide +kernel
  by_cases h : i = 25
  · subst i
    decide +kernel
  by_cases h : i = 26
  · subst i
    exact ridgeTest_large_26
  by_cases h : i = 27
  · subst i
    decide +kernel
  by_cases h : i = 28
  · subst i
    decide +kernel
  by_cases h : i = 29
  · subst i
    decide +kernel
  by_cases h : i = 30
  · subst i
    decide +kernel
  have h : i = 31 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_9 0 4 32 40
cert_ridgeTest_block_5 0 5 40 48 41 42 43 44 44 45 46 47
cert_ridgeTest_block_5 0 6 48 56 49 50 51 52 52 53 54 55
cert_ridgeTest_block_10 0 7 56 56 64 57 58 59 60 61 62 63
cert_ridgeTest_block_7 0 8 64 72 65 66 67 67 68 69 69 70 70 71
cert_ridgeTest_block_6 0 9 72 80 73 73 74 74 75 76 76 77 78 79
cert_ridgeTest_block_8 0 10 80 88 81 82 82 83 84 84 85 86 87
cert_ridgeTest_block_10 0 11 88 88 96 89 90 91 92 93 94 95
cert_ridgeTest_block_5 0 12 96 104 97 98 99 100 100 101 102 103
cert_ridgeTest_block_10 0 13 104 104 112 105 106 107 108 109 110 111
cert_ridgeTest_block_10 0 14 112 112 120 113 114 115 116 117 118 119
cert_ridgeTest_block_9 0 15 120 128
cert_ridgeTest_complete_6 0
cert_ridgeTestInterval_4 0 128
end Papers.RationalityTen.RootedCaches.RootedSixBase00
