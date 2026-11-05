module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01GrowthCacheRidgeSupport259
public import RootedSixBase01GrowthCacheRidgeSupport261
public import RootedSixBase01GrowthCacheRidgeSupport262
public import RootedSixBase01GrowthCacheRidgeSupport265
public import RootedSixBase01GrowthCacheRidgeSupport266
public import RootedSixBase01GrowthCacheRidgeSupport268
public import RootedSixBase01GrowthCacheRidgeSupport274
public import RootedSixBase01GrowthCacheRidgeSupport276
public import RootedSixBase01GrowthCacheRidgeSupport292
public import RootedSixBase01GrowthCacheRidgeSupport296
public import RootedSixBase01GrowthCacheRidgeSupport304
public import RootedSixBase01GrowthCacheRidgeSupport321
public import RootedSixBase01GrowthCacheRidgeSupport322
public import RootedSixBase01GrowthCacheRidgeSupport324
public import RootedSixBase01GrowthCacheRidgeSupport328
public import RootedSixBase01GrowthCacheRidgeSupport336
public import RootedSixBase01GrowthCacheRidgeSupport352

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_256 (i : Nat) := ridgeTest (i+256)
theorem ridgeTest_256_block_0 : Interval ridgeTest_256 0 8 := by
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
    exact ridgeTest_large_259
  by_cases h : i = 4
  · subst i
    decide +kernel
  by_cases h : i = 5
  · subst i
    exact ridgeTest_large_261
  by_cases h : i = 6
  · subst i
    exact ridgeTest_large_262
  have h : i = 7 := by omega
  subst i
  decide +kernel

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
    exact ridgeTest_large_268
  by_cases h : i = 13
  · subst i
    decide +kernel
  by_cases h : i = 14
  · subst i
    decide +kernel
  have h : i = 15 := by omega
  subst i
  decide +kernel

theorem ridgeTest_256_block_2 : Interval ridgeTest_256 16 24 := by
  intro i hlo hhi
  by_cases h : i = 16
  · subst i
    decide +kernel
  by_cases h : i = 17
  · subst i
    decide +kernel
  by_cases h : i = 18
  · subst i
    exact ridgeTest_large_274
  by_cases h : i = 19
  · subst i
    decide +kernel
  by_cases h : i = 20
  · subst i
    exact ridgeTest_large_276
  by_cases h : i = 21
  · subst i
    decide +kernel
  by_cases h : i = 22
  · subst i
    decide +kernel
  have h : i = 23 := by omega
  subst i
  decide +kernel

theorem ridgeTest_256_block_3 : Interval ridgeTest_256 24 32 :=
  interval_of_check ridgeTest_256 24 8 (by decide +kernel)

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
    decide +kernel
  by_cases h : i = 35
  · subst i
    decide +kernel
  by_cases h : i = 36
  · subst i
    exact ridgeTest_large_292
  by_cases h : i = 37
  · subst i
    decide +kernel
  by_cases h : i = 38
  · subst i
    decide +kernel
  have h : i = 39 := by omega
  subst i
  decide +kernel

theorem ridgeTest_256_block_5 : Interval ridgeTest_256 40 48 := by
  intro i hlo hhi
  by_cases h : i = 40
  · subst i
    exact ridgeTest_large_296
  by_cases h : i = 41
  · subst i
    decide +kernel
  by_cases h : i = 42
  · subst i
    decide +kernel
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

theorem ridgeTest_256_block_6 : Interval ridgeTest_256 48 56 := by
  intro i hlo hhi
  by_cases h : i = 48
  · subst i
    exact ridgeTest_large_304
  by_cases h : i = 49
  · subst i
    decide +kernel
  by_cases h : i = 50
  · subst i
    decide +kernel
  by_cases h : i = 51
  · subst i
    decide +kernel
  by_cases h : i = 52
  · subst i
    decide +kernel
  by_cases h : i = 53
  · subst i
    decide +kernel
  by_cases h : i = 54
  · subst i
    decide +kernel
  have h : i = 55 := by omega
  subst i
  decide +kernel

theorem ridgeTest_256_block_7 : Interval ridgeTest_256 56 64 :=
  interval_of_check ridgeTest_256 56 8 (by decide +kernel)

theorem ridgeTest_256_block_8 : Interval ridgeTest_256 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    decide +kernel
  by_cases h : i = 65
  · subst i
    exact ridgeTest_large_321
  by_cases h : i = 66
  · subst i
    exact ridgeTest_large_322
  by_cases h : i = 67
  · subst i
    decide +kernel
  by_cases h : i = 68
  · subst i
    exact ridgeTest_large_324
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

theorem ridgeTest_256_block_9 : Interval ridgeTest_256 72 80 := by
  intro i hlo hhi
  by_cases h : i = 72
  · subst i
    exact ridgeTest_large_328
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

theorem ridgeTest_256_block_10 : Interval ridgeTest_256 80 88 := by
  intro i hlo hhi
  by_cases h : i = 80
  · subst i
    exact ridgeTest_large_336
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

theorem ridgeTest_256_block_11 : Interval ridgeTest_256 88 96 :=
  interval_of_check ridgeTest_256 88 8 (by decide +kernel)

theorem ridgeTest_256_block_12 : Interval ridgeTest_256 96 104 := by
  intro i hlo hhi
  by_cases h : i = 96
  · subst i
    exact ridgeTest_large_352
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

theorem ridgeTest_256_block_13 : Interval ridgeTest_256 104 112 :=
  interval_of_check ridgeTest_256 104 8 (by decide +kernel)

theorem ridgeTest_256_block_14 : Interval ridgeTest_256 112 120 :=
  interval_of_check ridgeTest_256 112 8 (by decide +kernel)

theorem ridgeTest_256_block_15 : Interval ridgeTest_256 120 128 :=
  interval_of_check ridgeTest_256 120 8 (by decide +kernel)

theorem ridgeTest_256_complete : Interval ridgeTest_256 0 128 :=
  (interval_append ridgeTest_256 0 64 128
  (interval_append ridgeTest_256 0 32 64
  (interval_append ridgeTest_256 0 16 32
  (interval_append ridgeTest_256 0 8 16
  ridgeTest_256_block_0
  ridgeTest_256_block_1)
  (interval_append ridgeTest_256 16 24 32
  ridgeTest_256_block_2
  ridgeTest_256_block_3))
  (interval_append ridgeTest_256 32 48 64
  (interval_append ridgeTest_256 32 40 48
  ridgeTest_256_block_4
  ridgeTest_256_block_5)
  (interval_append ridgeTest_256 48 56 64
  ridgeTest_256_block_6
  ridgeTest_256_block_7)))
  (interval_append ridgeTest_256 64 96 128
  (interval_append ridgeTest_256 64 80 96
  (interval_append ridgeTest_256 64 72 80
  ridgeTest_256_block_8
  ridgeTest_256_block_9)
  (interval_append ridgeTest_256 80 88 96
  ridgeTest_256_block_10
  ridgeTest_256_block_11))
  (interval_append ridgeTest_256 96 112 128
  (interval_append ridgeTest_256 96 104 112
  ridgeTest_256_block_12
  ridgeTest_256_block_13)
  (interval_append ridgeTest_256 112 120 128
  ridgeTest_256_block_14
  ridgeTest_256_block_15))))
theorem ridgeTestInterval256 : Interval ridgeTest 256 384 := by
  intro i hlo hhi
  have h := ridgeTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01
