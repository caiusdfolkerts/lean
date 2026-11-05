module
prelude
public import RootedSixBase02GrowthCacheData
public import RootedSixBase02GrowthCacheRidgeSupport515
public import RootedSixBase02GrowthCacheRidgeSupport517
public import RootedSixBase02GrowthCacheRidgeSupport518
public import RootedSixBase02GrowthCacheRidgeSupport521
public import RootedSixBase02GrowthCacheRidgeSupport522
public import RootedSixBase02GrowthCacheRidgeSupport536
public import RootedSixBase02GrowthCacheRidgeSupport546
public import RootedSixBase02GrowthCacheRidgeSupport552
public import RootedSixBase02GrowthCacheRidgeSupport560
public import RootedSixBase02GrowthCacheRidgeSupport577
public import RootedSixBase02GrowthCacheRidgeSupport578
public import RootedSixBase02GrowthCacheRidgeSupport580
public import RootedSixBase02GrowthCacheRidgeSupport584
public import RootedSixBase02GrowthCacheRidgeSupport592
public import RootedSixBase02GrowthCacheRidgeSupport608

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_512 (i : Nat) := ridgeTest (i+512)
theorem ridgeTest_512_block_0 : Interval ridgeTest_512 0 8 := by
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
    exact ridgeTest_large_515
  by_cases h : i = 4
  · subst i
    decide +kernel
  by_cases h : i = 5
  · subst i
    exact ridgeTest_large_517
  by_cases h : i = 6
  · subst i
    exact ridgeTest_large_518
  have h : i = 7 := by omega
  subst i
  decide +kernel

theorem ridgeTest_512_block_1 : Interval ridgeTest_512 8 16 := by
  intro i hlo hhi
  by_cases h : i = 8
  · subst i
    decide +kernel
  by_cases h : i = 9
  · subst i
    exact ridgeTest_large_521
  by_cases h : i = 10
  · subst i
    exact ridgeTest_large_522
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

theorem ridgeTest_512_block_2 : Interval ridgeTest_512 16 24 :=
  interval_of_check ridgeTest_512 16 8 (by decide +kernel)

theorem ridgeTest_512_block_3 : Interval ridgeTest_512 24 32 := by
  intro i hlo hhi
  by_cases h : i = 24
  · subst i
    exact ridgeTest_large_536
  by_cases h : i = 25
  · subst i
    decide +kernel
  by_cases h : i = 26
  · subst i
    decide +kernel
  by_cases h : i = 27
  · subst i
    decide +kernel
  by_cases h : i = 28
  · subst i
    decide +kernel
  by_cases h : i = 29
  · subst i
    decide +kernel
  by_cases h : i = 30
  · subst i
    decide +kernel
  have h : i = 31 := by omega
  subst i
  decide +kernel

theorem ridgeTest_512_block_4 : Interval ridgeTest_512 32 40 := by
  intro i hlo hhi
  by_cases h : i = 32
  · subst i
    decide +kernel
  by_cases h : i = 33
  · subst i
    decide +kernel
  by_cases h : i = 34
  · subst i
    exact ridgeTest_large_546
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

theorem ridgeTest_512_block_5 : Interval ridgeTest_512 40 48 := by
  intro i hlo hhi
  by_cases h : i = 40
  · subst i
    exact ridgeTest_large_552
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

theorem ridgeTest_512_block_6 : Interval ridgeTest_512 48 56 := by
  intro i hlo hhi
  by_cases h : i = 48
  · subst i
    exact ridgeTest_large_560
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

theorem ridgeTest_512_block_7 : Interval ridgeTest_512 56 64 :=
  interval_of_check ridgeTest_512 56 8 (by decide +kernel)

theorem ridgeTest_512_block_8 : Interval ridgeTest_512 64 72 := by
  intro i hlo hhi
  by_cases h : i = 64
  · subst i
    decide +kernel
  by_cases h : i = 65
  · subst i
    exact ridgeTest_large_577
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

theorem ridgeTest_512_block_10 : Interval ridgeTest_512 80 88 := by
  intro i hlo hhi
  by_cases h : i = 80
  · subst i
    exact ridgeTest_large_592
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

end Papers.RationalityTen.RootedCaches.RootedSixBase02
