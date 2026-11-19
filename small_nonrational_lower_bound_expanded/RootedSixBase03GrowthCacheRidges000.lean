module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03GrowthCacheRidgeSupport7
public import RootedSixBase03GrowthCacheRidgeSupport11
public import RootedSixBase03GrowthCacheRidgeSupport38
public import RootedSixBase03GrowthCacheRidgeSupport42
public import RootedSixBase03GrowthCacheRidgeSupport52
public import RootedSixBase03GrowthCacheRidgeSupport56

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
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
theorem ridgeTest_0_block_4 : Interval ridgeTest_0 32 40 := by
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
    decide +kernel
  by_cases h : i = 37
  · subst i
    decide +kernel
  by_cases h : i = 38
  · subst i
    exact ridgeTest_large_38
  have h : i = 39 := by omega
  subst i
  decide +kernel

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

cert_ridgeTest_block_5 0 6 48 56 49 50 51 52 52 53 54 55
cert_ridgeTest_block_10 0 7 56 56 64 57 58 59 60 61 62 63
cert_ridgeTest_block_9 0 8 64 72
cert_ridgeTest_block_9 0 9 72 80
cert_ridgeTest_block_9 0 10 80 88
cert_ridgeTest_block_9 0 11 88 96
cert_ridgeTest_block_9 0 12 96 104
cert_ridgeTest_block_9 0 13 104 112
cert_ridgeTest_block_9 0 14 112 120
cert_ridgeTest_block_9 0 15 120 128
cert_ridgeTest_complete_6 0
cert_ridgeTestInterval_4 0 128
end Papers.RationalityTen.RootedCaches.RootedSixBase03
