module
prelude
public import RootedSixBase03GrowthCacheData
public import RootedSixBase03GrowthCacheRidgeSupport578
public import RootedSixBase03GrowthCacheRidgeSupport580
public import RootedSixBase03GrowthCacheRidgeSupport584
public import RootedSixBase03GrowthCacheRidgeSupport608

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_512 (i : Nat) := ridgeTest (i+512)
theorem ridgeTest_512_block_0 : Interval ridgeTest_512 0 8 :=
  interval_of_check ridgeTest_512 0 8 (by decide +kernel)

theorem ridgeTest_512_block_1 : Interval ridgeTest_512 8 16 :=
  interval_of_check ridgeTest_512 8 8 (by decide +kernel)

theorem ridgeTest_512_block_2 : Interval ridgeTest_512 16 24 :=
  interval_of_check ridgeTest_512 16 8 (by decide +kernel)

theorem ridgeTest_512_block_3 : Interval ridgeTest_512 24 32 :=
  interval_of_check ridgeTest_512 24 8 (by decide +kernel)

theorem ridgeTest_512_block_4 : Interval ridgeTest_512 32 40 :=
  interval_of_check ridgeTest_512 32 8 (by decide +kernel)

theorem ridgeTest_512_block_5 : Interval ridgeTest_512 40 48 :=
  interval_of_check ridgeTest_512 40 8 (by decide +kernel)

theorem ridgeTest_512_block_6 : Interval ridgeTest_512 48 56 :=
  interval_of_check ridgeTest_512 48 8 (by decide +kernel)

theorem ridgeTest_512_block_7 : Interval ridgeTest_512 56 64 :=
  interval_of_check ridgeTest_512 56 8 (by decide +kernel)

theorem ridgeTest_512_block_8 : Interval ridgeTest_512 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    decide +kernel
  by_cases h : i = 65
  · subst i
    decide +kernel
  by_cases h : i = 66
  · subst i
    exact ridgeTest_large_578
  by_cases h : i = 67
  · subst i
    decide +kernel
  by_cases h : i = 68
  · subst i
    exact ridgeTest_large_580
  by_cases h : i = 69
  · subst i
    decide +kernel
  by_cases h : i = 70
  · subst i
    decide +kernel
  have h : i = 71 := by omega
  subst i
  decide +kernel

theorem ridgeTest_512_block_9 : Interval ridgeTest_512 72 80 := by
  intro i hlo hhi
  by_cases h : i = 72
  · subst i
    exact ridgeTest_large_584
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

theorem ridgeTest_512_block_10 : Interval ridgeTest_512 80 88 :=
  interval_of_check ridgeTest_512 80 8 (by decide +kernel)

theorem ridgeTest_512_block_11 : Interval ridgeTest_512 88 96 :=
  interval_of_check ridgeTest_512 88 8 (by decide +kernel)

theorem ridgeTest_512_block_12 : Interval ridgeTest_512 96 104 := by
  intro i hlo hhi
  by_cases h : i = 96
  · subst i
    exact ridgeTest_large_608
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

theorem ridgeTest_512_block_13 : Interval ridgeTest_512 104 112 :=
  interval_of_check ridgeTest_512 104 8 (by decide +kernel)

theorem ridgeTest_512_block_14 : Interval ridgeTest_512 112 120 :=
  interval_of_check ridgeTest_512 112 8 (by decide +kernel)

theorem ridgeTest_512_block_15 : Interval ridgeTest_512 120 128 :=
  interval_of_check ridgeTest_512 120 8 (by decide +kernel)

theorem ridgeTest_512_complete : Interval ridgeTest_512 0 128 :=
  (interval_append ridgeTest_512 0 64 128
  (interval_append ridgeTest_512 0 32 64
  (interval_append ridgeTest_512 0 16 32
  (interval_append ridgeTest_512 0 8 16
  ridgeTest_512_block_0
  ridgeTest_512_block_1)
  (interval_append ridgeTest_512 16 24 32
  ridgeTest_512_block_2
  ridgeTest_512_block_3))
  (interval_append ridgeTest_512 32 48 64
  (interval_append ridgeTest_512 32 40 48
  ridgeTest_512_block_4
  ridgeTest_512_block_5)
  (interval_append ridgeTest_512 48 56 64
  ridgeTest_512_block_6
  ridgeTest_512_block_7)))
  (interval_append ridgeTest_512 64 96 128
  (interval_append ridgeTest_512 64 80 96
  (interval_append ridgeTest_512 64 72 80
  ridgeTest_512_block_8
  ridgeTest_512_block_9)
  (interval_append ridgeTest_512 80 88 96
  ridgeTest_512_block_10
  ridgeTest_512_block_11))
  (interval_append ridgeTest_512 96 112 128
  (interval_append ridgeTest_512 96 104 112
  ridgeTest_512_block_12
  ridgeTest_512_block_13)
  (interval_append ridgeTest_512 112 120 128
  ridgeTest_512_block_14
  ridgeTest_512_block_15))))
theorem ridgeTestInterval512 : Interval ridgeTest 512 640 := by
  intro i hlo hhi
  have h := ridgeTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase03
