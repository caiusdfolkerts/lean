module
prelude
public import RootedSmallCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallCache
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeTest_128 (i : Nat) := ridgeTest (i+128)
theorem ridgeTest_128_block_0 : Interval ridgeTest_128 0 4 :=
  interval_of_check ridgeTest_128 0 4 (by decide +kernel)

theorem ridgeTest_128_block_1 : Interval ridgeTest_128 4 8 :=
  interval_of_check ridgeTest_128 4 4 (by decide +kernel)

theorem ridgeTest_128_block_2 : Interval ridgeTest_128 8 12 :=
  interval_of_check ridgeTest_128 8 4 (by decide +kernel)

theorem ridgeTest_128_block_3 : Interval ridgeTest_128 12 16 :=
  interval_of_check ridgeTest_128 12 4 (by decide +kernel)

theorem ridgeTest_128_block_4 : Interval ridgeTest_128 16 20 :=
  interval_of_check ridgeTest_128 16 4 (by decide +kernel)

theorem ridgeTest_128_block_5 : Interval ridgeTest_128 20 24 :=
  interval_of_check ridgeTest_128 20 4 (by decide +kernel)

theorem ridgeTest_128_block_6 : Interval ridgeTest_128 24 28 :=
  interval_of_check ridgeTest_128 24 4 (by decide +kernel)

theorem ridgeTest_128_block_7 : Interval ridgeTest_128 28 32 :=
  interval_of_check ridgeTest_128 28 4 (by decide +kernel)

theorem ridgeTest_128_block_8 : Interval ridgeTest_128 32 36 :=
  interval_of_check ridgeTest_128 32 4 (by decide +kernel)

theorem ridgeTest_128_block_9 : Interval ridgeTest_128 36 40 :=
  interval_of_check ridgeTest_128 36 4 (by decide +kernel)

theorem ridgeTest_128_block_10 : Interval ridgeTest_128 40 44 :=
  interval_of_check ridgeTest_128 40 4 (by decide +kernel)

theorem ridgeTest_128_block_11 : Interval ridgeTest_128 44 48 :=
  interval_of_check ridgeTest_128 44 4 (by decide +kernel)

theorem ridgeTest_128_block_12 : Interval ridgeTest_128 48 52 :=
  interval_of_check ridgeTest_128 48 4 (by decide +kernel)

theorem ridgeTest_128_block_13 : Interval ridgeTest_128 52 56 :=
  interval_of_check ridgeTest_128 52 4 (by decide +kernel)

theorem ridgeTest_128_block_14 : Interval ridgeTest_128 56 60 :=
  interval_of_check ridgeTest_128 56 4 (by decide +kernel)

theorem ridgeTest_128_block_15 : Interval ridgeTest_128 60 64 :=
  interval_of_check ridgeTest_128 60 4 (by decide +kernel)

theorem ridgeTest_128_block_16 : Interval ridgeTest_128 64 68 :=
  interval_of_check ridgeTest_128 64 4 (by decide +kernel)

theorem ridgeTest_128_block_17 : Interval ridgeTest_128 68 72 :=
  interval_of_check ridgeTest_128 68 4 (by decide +kernel)

theorem ridgeTest_128_block_18 : Interval ridgeTest_128 72 76 :=
  interval_of_check ridgeTest_128 72 4 (by decide +kernel)

theorem ridgeTest_128_block_19 : Interval ridgeTest_128 76 80 :=
  interval_of_check ridgeTest_128 76 4 (by decide +kernel)

theorem ridgeTest_128_block_20 : Interval ridgeTest_128 80 84 :=
  interval_of_check ridgeTest_128 80 4 (by decide +kernel)

theorem ridgeTest_128_block_21 : Interval ridgeTest_128 84 88 :=
  interval_of_check ridgeTest_128 84 4 (by decide +kernel)

theorem ridgeTest_128_block_22 : Interval ridgeTest_128 88 92 :=
  interval_of_check ridgeTest_128 88 4 (by decide +kernel)

theorem ridgeTest_128_block_23 : Interval ridgeTest_128 92 96 :=
  interval_of_check ridgeTest_128 92 4 (by decide +kernel)

theorem ridgeTest_128_block_24 : Interval ridgeTest_128 96 100 :=
  interval_of_check ridgeTest_128 96 4 (by decide +kernel)

theorem ridgeTest_128_block_25 : Interval ridgeTest_128 100 104 :=
  interval_of_check ridgeTest_128 100 4 (by decide +kernel)

theorem ridgeTest_128_block_26 : Interval ridgeTest_128 104 108 :=
  interval_of_check ridgeTest_128 104 4 (by decide +kernel)

theorem ridgeTest_128_block_27 : Interval ridgeTest_128 108 112 :=
  interval_of_check ridgeTest_128 108 4 (by decide +kernel)

theorem ridgeTest_128_block_28 : Interval ridgeTest_128 112 116 :=
  interval_of_check ridgeTest_128 112 4 (by decide +kernel)

theorem ridgeTest_128_block_29 : Interval ridgeTest_128 116 120 :=
  interval_of_check ridgeTest_128 116 4 (by decide +kernel)

theorem ridgeTest_128_block_30 : Interval ridgeTest_128 120 124 :=
  interval_of_check ridgeTest_128 120 4 (by decide +kernel)

theorem ridgeTest_128_block_31 : Interval ridgeTest_128 124 128 :=
  interval_of_check ridgeTest_128 124 4 (by decide +kernel)

theorem ridgeTest_128_complete : Interval ridgeTest_128 0 128 :=
  (interval_append ridgeTest_128 0 64 128
  (interval_append ridgeTest_128 0 32 64
  (interval_append ridgeTest_128 0 16 32
  (interval_append ridgeTest_128 0 8 16
  (interval_append ridgeTest_128 0 4 8
  ridgeTest_128_block_0
  ridgeTest_128_block_1)
  (interval_append ridgeTest_128 8 12 16
  ridgeTest_128_block_2
  ridgeTest_128_block_3))
  (interval_append ridgeTest_128 16 24 32
  (interval_append ridgeTest_128 16 20 24
  ridgeTest_128_block_4
  ridgeTest_128_block_5)
  (interval_append ridgeTest_128 24 28 32
  ridgeTest_128_block_6
  ridgeTest_128_block_7)))
  (interval_append ridgeTest_128 32 48 64
  (interval_append ridgeTest_128 32 40 48
  (interval_append ridgeTest_128 32 36 40
  ridgeTest_128_block_8
  ridgeTest_128_block_9)
  (interval_append ridgeTest_128 40 44 48
  ridgeTest_128_block_10
  ridgeTest_128_block_11))
  (interval_append ridgeTest_128 48 56 64
  (interval_append ridgeTest_128 48 52 56
  ridgeTest_128_block_12
  ridgeTest_128_block_13)
  (interval_append ridgeTest_128 56 60 64
  ridgeTest_128_block_14
  ridgeTest_128_block_15))))
  (interval_append ridgeTest_128 64 96 128
  (interval_append ridgeTest_128 64 80 96
  (interval_append ridgeTest_128 64 72 80
  (interval_append ridgeTest_128 64 68 72
  ridgeTest_128_block_16
  ridgeTest_128_block_17)
  (interval_append ridgeTest_128 72 76 80
  ridgeTest_128_block_18
  ridgeTest_128_block_19))
  (interval_append ridgeTest_128 80 88 96
  (interval_append ridgeTest_128 80 84 88
  ridgeTest_128_block_20
  ridgeTest_128_block_21)
  (interval_append ridgeTest_128 88 92 96
  ridgeTest_128_block_22
  ridgeTest_128_block_23)))
  (interval_append ridgeTest_128 96 112 128
  (interval_append ridgeTest_128 96 104 112
  (interval_append ridgeTest_128 96 100 104
  ridgeTest_128_block_24
  ridgeTest_128_block_25)
  (interval_append ridgeTest_128 104 108 112
  ridgeTest_128_block_26
  ridgeTest_128_block_27))
  (interval_append ridgeTest_128 112 120 128
  (interval_append ridgeTest_128 112 116 120
  ridgeTest_128_block_28
  ridgeTest_128_block_29)
  (interval_append ridgeTest_128 120 124 128
  ridgeTest_128_block_30
  ridgeTest_128_block_31)))))
theorem ridgeTest_interval_128 : Interval ridgeTest 128 256 := by
  intro i hlo hhi
  have h := ridgeTest_128_complete (i-128) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
