module
prelude
public import RootedSixExtra02GrowthCacheData
public import RootedSixExtra02GrowthCacheRidgeSupport385
public import RootedSixExtra02GrowthCacheRidgeSupport386
public import RootedSixExtra02GrowthCacheRidgeSupport388
public import RootedSixExtra02GrowthCacheRidgeSupport392
public import RootedSixExtra02GrowthCacheRidgeSupport400
public import RootedSixExtra02GrowthCacheRidgeSupport416
public import RootedSixExtra02GrowthCacheRidgeSupport448

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_384 (i : Nat) := ridgeTest (i+384)
theorem ridgeTest_384_block_0 : Interval ridgeTest_384 0 8 := by
  intro i hlo hhi
  by_cases h : i = 0
  · subst i
    decide +kernel
  by_cases h : i = 1
  · subst i
    exact ridgeTest_large_385
  by_cases h : i = 2
  · subst i
    exact ridgeTest_large_386
  by_cases h : i = 3
  · subst i
    decide +kernel
  by_cases h : i = 4
  · subst i
    exact ridgeTest_large_388
  by_cases h : i = 5
  · subst i
    decide +kernel
  by_cases h : i = 6
  · subst i
    decide +kernel
  have h : i = 7 := by omega
  subst i
  decide +kernel

theorem ridgeTest_384_block_1 : Interval ridgeTest_384 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    exact ridgeTest_large_392
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

theorem ridgeTest_384_block_2 : Interval ridgeTest_384 16 24 := by
  intro i hlo hhi
  by_cases h : i = 16
  · subst i
    exact ridgeTest_large_400
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

theorem ridgeTest_384_block_3 : Interval ridgeTest_384 24 32 :=
  interval_of_check ridgeTest_384 24 8 (by decide +kernel)

theorem ridgeTest_384_block_4 : Interval ridgeTest_384 32 40 := by
  intro i hlo hhi
  by_cases h : i = 32
  · subst i
    exact ridgeTest_large_416
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

theorem ridgeTest_384_block_5 : Interval ridgeTest_384 40 48 :=
  interval_of_check ridgeTest_384 40 8 (by decide +kernel)

theorem ridgeTest_384_block_6 : Interval ridgeTest_384 48 56 :=
  interval_of_check ridgeTest_384 48 8 (by decide +kernel)

theorem ridgeTest_384_block_7 : Interval ridgeTest_384 56 64 :=
  interval_of_check ridgeTest_384 56 8 (by decide +kernel)

theorem ridgeTest_384_block_8 : Interval ridgeTest_384 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    exact ridgeTest_large_448
  by_cases h : i = 65
  · subst i
    decide +kernel
  by_cases h : i = 66
  · subst i
    decide +kernel
  by_cases h : i = 67
  · subst i
    decide +kernel
  by_cases h : i = 68
  · subst i
    decide +kernel
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

theorem ridgeTest_384_block_9 : Interval ridgeTest_384 72 80 :=
  interval_of_check ridgeTest_384 72 8 (by decide +kernel)

theorem ridgeTest_384_block_10 : Interval ridgeTest_384 80 88 :=
  interval_of_check ridgeTest_384 80 8 (by decide +kernel)

theorem ridgeTest_384_block_11 : Interval ridgeTest_384 88 96 :=
  interval_of_check ridgeTest_384 88 8 (by decide +kernel)

theorem ridgeTest_384_block_12 : Interval ridgeTest_384 96 104 :=
  interval_of_check ridgeTest_384 96 8 (by decide +kernel)

theorem ridgeTest_384_block_13 : Interval ridgeTest_384 104 112 :=
  interval_of_check ridgeTest_384 104 8 (by decide +kernel)

theorem ridgeTest_384_block_14 : Interval ridgeTest_384 112 120 :=
  interval_of_check ridgeTest_384 112 8 (by decide +kernel)

theorem ridgeTest_384_block_15 : Interval ridgeTest_384 120 128 :=
  interval_of_check ridgeTest_384 120 8 (by decide +kernel)

theorem ridgeTest_384_complete : Interval ridgeTest_384 0 128 :=
  (interval_append ridgeTest_384 0 64 128
  (interval_append ridgeTest_384 0 32 64
  (interval_append ridgeTest_384 0 16 32
  (interval_append ridgeTest_384 0 8 16
  ridgeTest_384_block_0
  ridgeTest_384_block_1)
  (interval_append ridgeTest_384 16 24 32
  ridgeTest_384_block_2
  ridgeTest_384_block_3))
  (interval_append ridgeTest_384 32 48 64
  (interval_append ridgeTest_384 32 40 48
  ridgeTest_384_block_4
  ridgeTest_384_block_5)
  (interval_append ridgeTest_384 48 56 64
  ridgeTest_384_block_6
  ridgeTest_384_block_7)))
  (interval_append ridgeTest_384 64 96 128
  (interval_append ridgeTest_384 64 80 96
  (interval_append ridgeTest_384 64 72 80
  ridgeTest_384_block_8
  ridgeTest_384_block_9)
  (interval_append ridgeTest_384 80 88 96
  ridgeTest_384_block_10
  ridgeTest_384_block_11))
  (interval_append ridgeTest_384 96 112 128
  (interval_append ridgeTest_384 96 104 112
  ridgeTest_384_block_12
  ridgeTest_384_block_13)
  (interval_append ridgeTest_384 112 120 128
  ridgeTest_384_block_14
  ridgeTest_384_block_15))))
theorem ridgeTestInterval384 : Interval ridgeTest 384 512 := by
  intro i hlo hhi
  have h := ridgeTest_384_complete (i-384) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_384, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
