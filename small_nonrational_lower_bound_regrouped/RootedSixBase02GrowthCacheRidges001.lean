module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02GrowthCacheRidgeSupport131
public import RootedSixBase02GrowthCacheRidgeSupport133
public import RootedSixBase02GrowthCacheRidgeSupport134
public import RootedSixBase02GrowthCacheRidgeSupport137
public import RootedSixBase02GrowthCacheRidgeSupport138
public import RootedSixBase02GrowthCacheRidgeSupport152
public import RootedSixBase02GrowthCacheRidgeSupport162
public import RootedSixBase02GrowthCacheRidgeSupport168
public import RootedSixBase02GrowthCacheRidgeSupport176
public import RootedSixBase02GrowthCacheRidgeSupport193
public import RootedSixBase02GrowthCacheRidgeSupport194
public import RootedSixBase02GrowthCacheRidgeSupport196
public import RootedSixBase02GrowthCacheRidgeSupport200
public import RootedSixBase02GrowthCacheRidgeSupport208
public import RootedSixBase02GrowthCacheRidgeSupport224

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_7 128
cert_ridgeTest_block_7 128 0 0 8 1 2 3 131 4 5 133 6 134 7
theorem ridgeTest_128_block_1 : Interval ridgeTest_128 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    decide +kernel
  by_cases h : i = 9
  · subst i
    exact ridgeTest_large_137
  by_cases h : i = 10
  · subst i
    exact ridgeTest_large_138
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

cert_ridgeTest_block_9 128 2 16 24
cert_ridgeTest_block_10 128 3 24 152 32 25 26 27 28 29 30 31
theorem ridgeTest_128_block_4 : Interval ridgeTest_128 32 40 := by
  intro i hlo hhi
  by_cases h : i = 32
  · subst i
    decide +kernel
  by_cases h : i = 33
  · subst i
    decide +kernel
  by_cases h : i = 34
  · subst i
    exact ridgeTest_large_162
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

cert_ridgeTest_block_10 128 5 40 168 48 41 42 43 44 45 46 47
cert_ridgeTest_block_10 128 6 48 176 56 49 50 51 52 53 54 55
cert_ridgeTest_block_9 128 7 56 64
cert_ridgeTest_block_6 128 8 64 72 65 193 66 194 67 68 196 69 70 71
cert_ridgeTest_block_10 128 9 72 200 80 73 74 75 76 77 78 79
cert_ridgeTest_block_10 128 10 80 208 88 81 82 83 84 85 86 87
cert_ridgeTest_block_9 128 11 88 96
cert_ridgeTest_block_10 128 12 96 224 104 97 98 99 100 101 102 103
cert_ridgeTest_block_9 128 13 104 112
cert_ridgeTest_block_9 128 14 112 120
cert_ridgeTest_block_9 128 15 120 128
cert_ridgeTest_complete_6 128
cert_ridgeTestInterval_4 128 256
end Papers.RationalityTen.RootedCaches.RootedSixBase02
