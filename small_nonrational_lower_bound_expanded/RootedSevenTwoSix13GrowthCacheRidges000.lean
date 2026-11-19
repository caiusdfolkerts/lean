module
prelude
public import RootedSevenTwoSix13GrowthCacheData
public import RootedSevenTwoSix13GrowthCacheRidgeSupport7
public import RootedSevenTwoSix13GrowthCacheRidgeSupport88
public import RootedSevenTwoSix13GrowthCacheRidgeSupport104
public import RootedSevenTwoSix13GrowthCacheRidgeSupport112

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_0 (i : Nat) := ridgeTest (i+0)
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

theorem ridgeTest_0_block_1 : Interval ridgeTest_0 8 16 :=
  interval_of_check ridgeTest_0 8 8 (by decide +kernel)

theorem ridgeTest_0_block_2 : Interval ridgeTest_0 16 24 :=
  interval_of_check ridgeTest_0 16 8 (by decide +kernel)

theorem ridgeTest_0_block_3 : Interval ridgeTest_0 24 32 :=
  interval_of_check ridgeTest_0 24 8 (by decide +kernel)

theorem ridgeTest_0_block_4 : Interval ridgeTest_0 32 40 :=
  interval_of_check ridgeTest_0 32 8 (by decide +kernel)

theorem ridgeTest_0_block_5 : Interval ridgeTest_0 40 48 :=
  interval_of_check ridgeTest_0 40 8 (by decide +kernel)

theorem ridgeTest_0_block_6 : Interval ridgeTest_0 48 56 :=
  interval_of_check ridgeTest_0 48 8 (by decide +kernel)

theorem ridgeTest_0_block_7 : Interval ridgeTest_0 56 64 :=
  interval_of_check ridgeTest_0 56 8 (by decide +kernel)

theorem ridgeTest_0_block_8 : Interval ridgeTest_0 64 72 :=
  interval_of_check ridgeTest_0 64 8 (by decide +kernel)

theorem ridgeTest_0_block_9 : Interval ridgeTest_0 72 80 :=
  interval_of_check ridgeTest_0 72 8 (by decide +kernel)

theorem ridgeTest_0_block_10 : Interval ridgeTest_0 80 88 :=
  interval_of_check ridgeTest_0 80 8 (by decide +kernel)

theorem ridgeTest_0_block_11 : Interval ridgeTest_0 88 96 := by
  intro i hlo hhi
  by_cases h : i = 88
  · subst i
    exact ridgeTest_large_88
  by_cases h : i = 89
  · subst i
    decide +kernel
  by_cases h : i = 90
  · subst i
    decide +kernel
  by_cases h : i = 91
  · subst i
    decide +kernel
  by_cases h : i = 92
  · subst i
    decide +kernel
  by_cases h : i = 93
  · subst i
    decide +kernel
  by_cases h : i = 94
  · subst i
    decide +kernel
  have h : i = 95 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_12 : Interval ridgeTest_0 96 104 :=
  interval_of_check ridgeTest_0 96 8 (by decide +kernel)

theorem ridgeTest_0_block_13 : Interval ridgeTest_0 104 112 := by
  intro i hlo hhi
  by_cases h : i = 104
  · subst i
    exact ridgeTest_large_104
  by_cases h : i = 105
  · subst i
    decide +kernel
  by_cases h : i = 106
  · subst i
    decide +kernel
  by_cases h : i = 107
  · subst i
    decide +kernel
  by_cases h : i = 108
  · subst i
    decide +kernel
  by_cases h : i = 109
  · subst i
    decide +kernel
  by_cases h : i = 110
  · subst i
    decide +kernel
  have h : i = 111 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_14 : Interval ridgeTest_0 112 120 := by
  intro i hlo hhi
  by_cases h : i = 112
  · subst i
    exact ridgeTest_large_112
  by_cases h : i = 113
  · subst i
    decide +kernel
  by_cases h : i = 114
  · subst i
    decide +kernel
  by_cases h : i = 115
  · subst i
    decide +kernel
  by_cases h : i = 116
  · subst i
    decide +kernel
  by_cases h : i = 117
  · subst i
    decide +kernel
  by_cases h : i = 118
  · subst i
    decide +kernel
  have h : i = 119 := by omega
  subst i
  decide +kernel

theorem ridgeTest_0_block_15 : Interval ridgeTest_0 120 128 :=
  interval_of_check ridgeTest_0 120 8 (by decide +kernel)

theorem ridgeTest_0_complete : Interval ridgeTest_0 0 128 :=
  (interval_append ridgeTest_0 0 64 128
  (interval_append ridgeTest_0 0 32 64
  (interval_append ridgeTest_0 0 16 32
  (interval_append ridgeTest_0 0 8 16
  ridgeTest_0_block_0
  ridgeTest_0_block_1)
  (interval_append ridgeTest_0 16 24 32
  ridgeTest_0_block_2
  ridgeTest_0_block_3))
  (interval_append ridgeTest_0 32 48 64
  (interval_append ridgeTest_0 32 40 48
  ridgeTest_0_block_4
  ridgeTest_0_block_5)
  (interval_append ridgeTest_0 48 56 64
  ridgeTest_0_block_6
  ridgeTest_0_block_7)))
  (interval_append ridgeTest_0 64 96 128
  (interval_append ridgeTest_0 64 80 96
  (interval_append ridgeTest_0 64 72 80
  ridgeTest_0_block_8
  ridgeTest_0_block_9)
  (interval_append ridgeTest_0 80 88 96
  ridgeTest_0_block_10
  ridgeTest_0_block_11))
  (interval_append ridgeTest_0 96 112 128
  (interval_append ridgeTest_0 96 104 112
  ridgeTest_0_block_12
  ridgeTest_0_block_13)
  (interval_append ridgeTest_0 112 120 128
  ridgeTest_0_block_14
  ridgeTest_0_block_15))))
theorem ridgeTestInterval0 : Interval ridgeTest 0 128 := by
  intro i hlo hhi
  have h := ridgeTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
