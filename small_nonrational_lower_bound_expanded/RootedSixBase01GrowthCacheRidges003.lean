module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01GrowthCacheRidgeSupport385
public import RootedSixBase01GrowthCacheRidgeSupport386
public import RootedSixBase01GrowthCacheRidgeSupport388
public import RootedSixBase01GrowthCacheRidgeSupport392
public import RootedSixBase01GrowthCacheRidgeSupport400
public import RootedSixBase01GrowthCacheRidgeSupport416
public import RootedSixBase01GrowthCacheRidgeSupport448
public import RootedSixBase01GrowthCacheRidgeSupport449
public import RootedSixBase01GrowthCacheRidgeSupport450
public import RootedSixBase01GrowthCacheRidgeSupport452
public import RootedSixBase01GrowthCacheRidgeSupport456
public import RootedSixBase01GrowthCacheRidgeSupport464
public import RootedSixBase01GrowthCacheRidgeSupport480

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_7 384
cert_ridgeTest_block_6 384 0 0 8 1 385 2 386 3 4 388 5 6 7
cert_ridgeTest_block_10 384 1 8 392 16 9 10 11 12 13 14 15
cert_ridgeTest_block_10 384 2 16 400 24 17 18 19 20 21 22 23
cert_ridgeTest_block_9 384 3 24 32
cert_ridgeTest_block_10 384 4 32 416 40 33 34 35 36 37 38 39
cert_ridgeTest_block_9 384 5 40 48
cert_ridgeTest_block_9 384 6 48 56
cert_ridgeTest_block_9 384 7 56 64
theorem ridgeTest_384_block_8 : Interval ridgeTest_384 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    exact ridgeTest_large_448
  by_cases h : i = 65
  · subst i
    exact ridgeTest_large_449
  by_cases h : i = 66
  · subst i
    exact ridgeTest_large_450
  by_cases h : i = 67
  · subst i
    decide +kernel
  by_cases h : i = 68
  · subst i
    exact ridgeTest_large_452
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_10 384 9 72 456 80 73 74 75 76 77 78 79
cert_ridgeTest_block_10 384 10 80 464 88 81 82 83 84 85 86 87
cert_ridgeTest_block_9 384 11 88 96
cert_ridgeTest_block_10 384 12 96 480 104 97 98 99 100 101 102 103
cert_ridgeTest_block_9 384 13 104 112
cert_ridgeTest_block_9 384 14 112 120
cert_ridgeTest_block_9 384 15 120 128
cert_ridgeTest_complete_6 384
cert_ridgeTestInterval_4 384 512
end Papers.RationalityTen.RootedCaches.RootedSixBase01
