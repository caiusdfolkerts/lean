module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02GrowthCacheRidgeSupport259
public import RootedSixBase02GrowthCacheRidgeSupport261
public import RootedSixBase02GrowthCacheRidgeSupport262
public import RootedSixBase02GrowthCacheRidgeSupport265
public import RootedSixBase02GrowthCacheRidgeSupport266
public import RootedSixBase02GrowthCacheRidgeSupport280
public import RootedSixBase02GrowthCacheRidgeSupport290
public import RootedSixBase02GrowthCacheRidgeSupport296
public import RootedSixBase02GrowthCacheRidgeSupport304
public import RootedSixBase02GrowthCacheRidgeSupport321
public import RootedSixBase02GrowthCacheRidgeSupport322
public import RootedSixBase02GrowthCacheRidgeSupport324
public import RootedSixBase02GrowthCacheRidgeSupport328
public import RootedSixBase02GrowthCacheRidgeSupport336
public import RootedSixBase02GrowthCacheRidgeSupport352

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_7 256
cert_ridgeTest_block_7 256 0 0 8 1 2 3 259 4 5 261 6 262 7
theorem ridgeTest_256_block_1 : Interval ridgeTest_256 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    decide +kernel
  by_cases h : i = 9
  · subst i
    exact ridgeTest_large_265
  by_cases h : i = 10
  · subst i
    exact ridgeTest_large_266
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

cert_ridgeTest_block_9 256 2 16 24
cert_ridgeTest_block_10 256 3 24 280 32 25 26 27 28 29 30 31
theorem ridgeTest_256_block_4 : Interval ridgeTest_256 32 40 := by
  intro i hlo hhi
  by_cases h : i = 32
  · subst i
    decide +kernel
  by_cases h : i = 33
  · subst i
    decide +kernel
  by_cases h : i = 34
  · subst i
    exact ridgeTest_large_290
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

cert_ridgeTest_block_10 256 5 40 296 48 41 42 43 44 45 46 47
cert_ridgeTest_block_10 256 6 48 304 56 49 50 51 52 53 54 55
cert_ridgeTest_block_9 256 7 56 64
cert_ridgeTest_block_6 256 8 64 72 65 321 66 322 67 68 324 69 70 71
cert_ridgeTest_block_10 256 9 72 328 80 73 74 75 76 77 78 79
cert_ridgeTest_block_10 256 10 80 336 88 81 82 83 84 85 86 87
cert_ridgeTest_block_9 256 11 88 96
cert_ridgeTest_block_10 256 12 96 352 104 97 98 99 100 101 102 103
cert_ridgeTest_block_9 256 13 104 112
cert_ridgeTest_block_9 256 14 112 120
cert_ridgeTest_block_9 256 15 120 128
cert_ridgeTest_complete_6 256
cert_ridgeTestInterval_4 256 384
end Papers.RationalityTen.RootedCaches.RootedSixBase02
