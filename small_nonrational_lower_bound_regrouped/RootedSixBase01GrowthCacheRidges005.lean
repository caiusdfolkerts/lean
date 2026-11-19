module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01GrowthCacheRidgeSupport641
public import RootedSixBase01GrowthCacheRidgeSupport642
public import RootedSixBase01GrowthCacheRidgeSupport644
public import RootedSixBase01GrowthCacheRidgeSupport648
public import RootedSixBase01GrowthCacheRidgeSupport656
public import RootedSixBase01GrowthCacheRidgeSupport672
public import RootedSixBase01GrowthCacheRidgeSupport704
public import RootedSixBase01GrowthCacheRidgeSupport705
public import RootedSixBase01GrowthCacheRidgeSupport706
public import RootedSixBase01GrowthCacheRidgeSupport708
public import RootedSixBase01GrowthCacheRidgeSupport712
public import RootedSixBase01GrowthCacheRidgeSupport720
public import RootedSixBase01GrowthCacheRidgeSupport736

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest_7 640
cert_ridgeTest_block_6 640 0 0 8 1 641 2 642 3 4 644 5 6 7
cert_ridgeTest_block_10 640 1 8 648 16 9 10 11 12 13 14 15
cert_ridgeTest_block_10 640 2 16 656 24 17 18 19 20 21 22 23
cert_ridgeTest_block_9 640 3 24 32
cert_ridgeTest_block_10 640 4 32 672 40 33 34 35 36 37 38 39
cert_ridgeTest_block_9 640 5 40 48
cert_ridgeTest_block_9 640 6 48 56
cert_ridgeTest_block_9 640 7 56 64
theorem ridgeTest_640_block_8 : Interval ridgeTest_640 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    exact ridgeTest_large_704
  by_cases h : i = 65
  · subst i
    exact ridgeTest_large_705
  by_cases h : i = 66
  · subst i
    exact ridgeTest_large_706
  by_cases h : i = 67
  · subst i
    decide +kernel
  by_cases h : i = 68
  · subst i
    exact ridgeTest_large_708
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

cert_ridgeTest_block_10 640 9 72 712 80 73 74 75 76 77 78 79
cert_ridgeTest_block_10 640 10 80 720 88 81 82 83 84 85 86 87
cert_ridgeTest_block_9 640 11 88 96
cert_ridgeTest_block_10 640 12 96 736 104 97 98 99 100 101 102 103
cert_ridgeTest_block_9 640 13 104 112
cert_ridgeTest_block_9 640 14 112 120
cert_ridgeTest_block_9 640 15 120 128
cert_ridgeTest_complete_6 640
cert_ridgeTestInterval_4 640 768
end Papers.RationalityTen.RootedCaches.RootedSixBase01
