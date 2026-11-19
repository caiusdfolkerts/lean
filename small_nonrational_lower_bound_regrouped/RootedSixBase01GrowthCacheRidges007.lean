module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01GrowthCacheRidgeSupport896
public import RootedSixBase01GrowthCacheRidgeSupport897
public import RootedSixBase01GrowthCacheRidgeSupport898
public import RootedSixBase01GrowthCacheRidgeSupport900
public import RootedSixBase01GrowthCacheRidgeSupport904
public import RootedSixBase01GrowthCacheRidgeSupport912
public import RootedSixBase01GrowthCacheRidgeSupport928
public import RootedSixBase01GrowthCacheRidgeSupport960

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_7 896
theorem ridgeTest_896_block_0 : Interval ridgeTest_896 0 8 := by
  intro i hlo hhi
  by_cases h : i = 0
  · subst i
    exact ridgeTest_large_896
  by_cases h : i = 1
  · subst i
    exact ridgeTest_large_897
  by_cases h : i = 2
  · subst i
    exact ridgeTest_large_898
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

cert_ridgeTest_block_10 896 1 8 904 16 9 10 11 12 13 14 15
cert_ridgeTest_block_10 896 2 16 912 24 17 18 19 20 21 22 23
cert_ridgeTest_block_9 896 3 24 32
cert_ridgeTest_block_10 896 4 32 928 40 33 34 35 36 37 38 39
cert_ridgeTest_block_9 896 5 40 48
cert_ridgeTest_block_9 896 6 48 56
cert_ridgeTest_block_9 896 7 56 64
cert_ridgeTest_block_10 896 8 64 960 72 65 66 67 68 69 70 71
cert_ridgeTest_block_9 896 9 72 80
cert_ridgeTest_block_9 896 10 80 88
cert_ridgeTest_block_9 896 11 88 96
cert_ridgeTest_block_9 896 12 96 104
cert_ridgeTest_block_9 896 13 104 112
cert_ridgeTest_block_9 896 14 112 120
cert_ridgeTest_block_9 896 15 120 128
cert_ridgeTest_complete_6 896
cert_ridgeTestInterval_4 896 1024
end Papers.RationalityTen.RootedCaches.RootedSixBase01
