module
prelude
public import RootedSixBase01GrowthCacheData
public import RootedSixBase01GrowthCacheRidgeSupport131
public import RootedSixBase01GrowthCacheRidgeSupport133
public import RootedSixBase01GrowthCacheRidgeSupport134
public import RootedSixBase01GrowthCacheRidgeSupport137
public import RootedSixBase01GrowthCacheRidgeSupport138
public import RootedSixBase01GrowthCacheRidgeSupport140
public import RootedSixBase01GrowthCacheRidgeSupport146
public import RootedSixBase01GrowthCacheRidgeSupport148
public import RootedSixBase01GrowthCacheRidgeSupport164
public import RootedSixBase01GrowthCacheRidgeSupport168
public import RootedSixBase01GrowthCacheRidgeSupport176
public import RootedSixBase01GrowthCacheRidgeSupport193
public import RootedSixBase01GrowthCacheRidgeSupport194
public import RootedSixBase01GrowthCacheRidgeSupport196
public import RootedSixBase01GrowthCacheRidgeSupport200
public import RootedSixBase01GrowthCacheRidgeSupport208
public import RootedSixBase01GrowthCacheRidgeSupport224

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_128 (i : Nat) := ridgeTest (i+128)
theorem ridgeTest_128_block_0 : Interval ridgeTest_128 0 8 := by
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
    exact ridgeTest_large_131
  by_cases h : i = 4
  · subst i
    decide +kernel
  by_cases h : i = 5
  · subst i
    exact ridgeTest_large_133
  by_cases h : i = 6
  · subst i
    exact ridgeTest_large_134
  have h : i = 7 := by omega
  subst i
  decide +kernel

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
    exact ridgeTest_large_140
  by_cases h : i = 13
  · subst i
    decide +kernel
  by_cases h : i = 14
  · subst i
    decide +kernel
  have h : i = 15 := by omega
  subst i
  decide +kernel

theorem ridgeTest_128_block_2 : Interval ridgeTest_128 16 24 := by
  intro i hlo hhi
  by_cases h : i = 16
  · subst i
    decide +kernel
  by_cases h : i = 17
  · subst i
    decide +kernel
  by_cases h : i = 18
  · subst i
    exact ridgeTest_large_146
  by_cases h : i = 19
  · subst i
    decide +kernel
  by_cases h : i = 20
  · subst i
    exact ridgeTest_large_148
  by_cases h : i = 21
  · subst i
    decide +kernel
  by_cases h : i = 22
  · subst i
    decide +kernel
  have h : i = 23 := by omega
  subst i
  decide +kernel

theorem ridgeTest_128_block_3 : Interval ridgeTest_128 24 32 :=
  interval_of_check ridgeTest_128 24 8 (by decide +kernel)

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
    decide +kernel
  by_cases h : i = 35
  · subst i
    decide +kernel
  by_cases h : i = 36
  · subst i
    exact ridgeTest_large_164
  by_cases h : i = 37
  · subst i
    decide +kernel
  by_cases h : i = 38
  · subst i
    decide +kernel
  have h : i = 39 := by omega
  subst i
  decide +kernel

theorem ridgeTest_128_block_5 : Interval ridgeTest_128 40 48 := by
  intro i hlo hhi
  by_cases h : i = 40
  · subst i
    exact ridgeTest_large_168
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

theorem ridgeTest_128_block_6 : Interval ridgeTest_128 48 56 := by
  intro i hlo hhi
  by_cases h : i = 48
  · subst i
    exact ridgeTest_large_176
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

theorem ridgeTest_128_block_7 : Interval ridgeTest_128 56 64 :=
  interval_of_check ridgeTest_128 56 8 (by decide +kernel)

theorem ridgeTest_128_block_8 : Interval ridgeTest_128 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    decide +kernel
  by_cases h : i = 65
  · subst i
    exact ridgeTest_large_193
  by_cases h : i = 66
  · subst i
    exact ridgeTest_large_194
  by_cases h : i = 67
  · subst i
    decide +kernel
  by_cases h : i = 68
  · subst i
    exact ridgeTest_large_196
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

theorem ridgeTest_128_block_9 : Interval ridgeTest_128 72 80 := by
  intro i hlo hhi
  by_cases h : i = 72
  · subst i
    exact ridgeTest_large_200
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

theorem ridgeTest_128_block_10 : Interval ridgeTest_128 80 88 := by
  intro i hlo hhi
  by_cases h : i = 80
  · subst i
    exact ridgeTest_large_208
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

theorem ridgeTest_128_block_11 : Interval ridgeTest_128 88 96 :=
  interval_of_check ridgeTest_128 88 8 (by decide +kernel)

theorem ridgeTest_128_block_12 : Interval ridgeTest_128 96 104 := by
  intro i hlo hhi
  by_cases h : i = 96
  · subst i
    exact ridgeTest_large_224
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

theorem ridgeTest_128_block_13 : Interval ridgeTest_128 104 112 :=
  interval_of_check ridgeTest_128 104 8 (by decide +kernel)

theorem ridgeTest_128_block_14 : Interval ridgeTest_128 112 120 :=
  interval_of_check ridgeTest_128 112 8 (by decide +kernel)

theorem ridgeTest_128_block_15 : Interval ridgeTest_128 120 128 :=
  interval_of_check ridgeTest_128 120 8 (by decide +kernel)

theorem ridgeTest_128_complete : Interval ridgeTest_128 0 128 :=
  (interval_append ridgeTest_128 0 64 128
  (interval_append ridgeTest_128 0 32 64
  (interval_append ridgeTest_128 0 16 32
  (interval_append ridgeTest_128 0 8 16
  ridgeTest_128_block_0
  ridgeTest_128_block_1)
  (interval_append ridgeTest_128 16 24 32
  ridgeTest_128_block_2
  ridgeTest_128_block_3))
  (interval_append ridgeTest_128 32 48 64
  (interval_append ridgeTest_128 32 40 48
  ridgeTest_128_block_4
  ridgeTest_128_block_5)
  (interval_append ridgeTest_128 48 56 64
  ridgeTest_128_block_6
  ridgeTest_128_block_7)))
  (interval_append ridgeTest_128 64 96 128
  (interval_append ridgeTest_128 64 80 96
  (interval_append ridgeTest_128 64 72 80
  ridgeTest_128_block_8
  ridgeTest_128_block_9)
  (interval_append ridgeTest_128 80 88 96
  ridgeTest_128_block_10
  ridgeTest_128_block_11))
  (interval_append ridgeTest_128 96 112 128
  (interval_append ridgeTest_128 96 104 112
  ridgeTest_128_block_12
  ridgeTest_128_block_13)
  (interval_append ridgeTest_128 112 120 128
  ridgeTest_128_block_14
  ridgeTest_128_block_15))))
theorem ridgeTestInterval128 : Interval ridgeTest 128 256 := by
  intro i hlo hhi
  have h := ridgeTest_128_complete (i-128) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01
