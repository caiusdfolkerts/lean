module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01GrowthCacheRidgeSupport769
public import RootedSixBase01GrowthCacheRidgeSupport770
public import RootedSixBase01GrowthCacheRidgeSupport772
public import RootedSixBase01GrowthCacheRidgeSupport776
public import RootedSixBase01GrowthCacheRidgeSupport784
public import RootedSixBase01GrowthCacheRidgeSupport800
public import RootedSixBase01GrowthCacheRidgeSupport832
public import RootedSixBase01GrowthCacheRidgeSupport833
public import RootedSixBase01GrowthCacheRidgeSupport834
public import RootedSixBase01GrowthCacheRidgeSupport836
public import RootedSixBase01GrowthCacheRidgeSupport840
public import RootedSixBase01GrowthCacheRidgeSupport848
public import RootedSixBase01GrowthCacheRidgeSupport864

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_768 (i : Nat) := ridgeTest (i+768)
theorem ridgeTest_768_block_0 : Interval ridgeTest_768 0 8 := by
  intro i hlo hhi
  by_cases h : i = 0
  · subst i
    decide +kernel
  by_cases h : i = 1
  · subst i
    exact ridgeTest_large_769
  by_cases h : i = 2
  · subst i
    exact ridgeTest_large_770
  by_cases h : i = 3
  · subst i
    decide +kernel
  by_cases h : i = 4
  · subst i
    exact ridgeTest_large_772
  by_cases h : i = 5
  · subst i
    decide +kernel
  by_cases h : i = 6
  · subst i
    decide +kernel
  have h : i = 7 := by omega
  subst i
  decide +kernel

theorem ridgeTest_768_block_1 : Interval ridgeTest_768 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    exact ridgeTest_large_776
  by_cases h : i = 9
  · subst i
    decide +kernel
  by_cases h : i = 10
  · subst i
    decide +kernel
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

theorem ridgeTest_768_block_2 : Interval ridgeTest_768 16 24 := by
  intro i hlo hhi
  by_cases h : i = 16
  · subst i
    exact ridgeTest_large_784
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
    decide +kernel
  have h : i = 23 := by omega
  subst i
  decide +kernel

theorem ridgeTest_768_block_3 : Interval ridgeTest_768 24 32 :=
  interval_of_check ridgeTest_768 24 8 (by decide +kernel)

theorem ridgeTest_768_block_4 : Interval ridgeTest_768 32 40 := by
  intro i hlo hhi
  by_cases h : i = 32
  · subst i
    exact ridgeTest_large_800
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
    decide +kernel
  have h : i = 39 := by omega
  subst i
  decide +kernel

theorem ridgeTest_768_block_5 : Interval ridgeTest_768 40 48 :=
  interval_of_check ridgeTest_768 40 8 (by decide +kernel)

theorem ridgeTest_768_block_6 : Interval ridgeTest_768 48 56 :=
  interval_of_check ridgeTest_768 48 8 (by decide +kernel)

theorem ridgeTest_768_block_7 : Interval ridgeTest_768 56 64 :=
  interval_of_check ridgeTest_768 56 8 (by decide +kernel)

theorem ridgeTest_768_block_8 : Interval ridgeTest_768 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    exact ridgeTest_large_832
  by_cases h : i = 65
  · subst i
    exact ridgeTest_large_833
  by_cases h : i = 66
  · subst i
    exact ridgeTest_large_834
  by_cases h : i = 67
  · subst i
    decide +kernel
  by_cases h : i = 68
  · subst i
    exact ridgeTest_large_836
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

theorem ridgeTest_768_block_9 : Interval ridgeTest_768 72 80 := by
  intro i hlo hhi
  by_cases h : i = 72
  · subst i
    exact ridgeTest_large_840
  by_cases h : i = 73
  · subst i
    decide +kernel
  by_cases h : i = 74
  · subst i
    decide +kernel
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

theorem ridgeTest_768_block_10 : Interval ridgeTest_768 80 88 := by
  intro i hlo hhi
  by_cases h : i = 80
  · subst i
    exact ridgeTest_large_848
  by_cases h : i = 81
  · subst i
    decide +kernel
  by_cases h : i = 82
  · subst i
    decide +kernel
  by_cases h : i = 83
  · subst i
    decide +kernel
  by_cases h : i = 84
  · subst i
    decide +kernel
  by_cases h : i = 85
  · subst i
    decide +kernel
  by_cases h : i = 86
  · subst i
    decide +kernel
  have h : i = 87 := by omega
  subst i
  decide +kernel

theorem ridgeTest_768_block_11 : Interval ridgeTest_768 88 96 :=
  interval_of_check ridgeTest_768 88 8 (by decide +kernel)

theorem ridgeTest_768_block_12 : Interval ridgeTest_768 96 104 := by
  intro i hlo hhi
  by_cases h : i = 96
  · subst i
    exact ridgeTest_large_864
  by_cases h : i = 97
  · subst i
    decide +kernel
  by_cases h : i = 98
  · subst i
    decide +kernel
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

theorem ridgeTest_768_block_13 : Interval ridgeTest_768 104 112 :=
  interval_of_check ridgeTest_768 104 8 (by decide +kernel)

theorem ridgeTest_768_block_14 : Interval ridgeTest_768 112 120 :=
  interval_of_check ridgeTest_768 112 8 (by decide +kernel)

theorem ridgeTest_768_block_15 : Interval ridgeTest_768 120 128 :=
  interval_of_check ridgeTest_768 120 8 (by decide +kernel)

theorem ridgeTest_768_complete : Interval ridgeTest_768 0 128 :=
  (interval_append ridgeTest_768 0 64 128
  (interval_append ridgeTest_768 0 32 64
  (interval_append ridgeTest_768 0 16 32
  (interval_append ridgeTest_768 0 8 16
  ridgeTest_768_block_0
  ridgeTest_768_block_1)
  (interval_append ridgeTest_768 16 24 32
  ridgeTest_768_block_2
  ridgeTest_768_block_3))
  (interval_append ridgeTest_768 32 48 64
  (interval_append ridgeTest_768 32 40 48
  ridgeTest_768_block_4
  ridgeTest_768_block_5)
  (interval_append ridgeTest_768 48 56 64
  ridgeTest_768_block_6
  ridgeTest_768_block_7)))
  (interval_append ridgeTest_768 64 96 128
  (interval_append ridgeTest_768 64 80 96
  (interval_append ridgeTest_768 64 72 80
  ridgeTest_768_block_8
  ridgeTest_768_block_9)
  (interval_append ridgeTest_768 80 88 96
  ridgeTest_768_block_10
  ridgeTest_768_block_11))
  (interval_append ridgeTest_768 96 112 128
  (interval_append ridgeTest_768 96 104 112
  ridgeTest_768_block_12
  ridgeTest_768_block_13)
  (interval_append ridgeTest_768 112 120 128
  ridgeTest_768_block_14
  ridgeTest_768_block_15))))
theorem ridgeTestInterval768 : Interval ridgeTest 768 896 := by
  intro i hlo hhi
  have h := ridgeTest_768_complete (i-768) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01
