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
def ridgeTest_256 (i : Nat) := ridgeTest (i+256)
theorem ridgeTest_256_block_0 : Interval ridgeTest_256 0 4 :=
  interval_of_check ridgeTest_256 0 4 (by decide +kernel)

theorem ridgeTest_256_block_1 : Interval ridgeTest_256 4 8 :=
  interval_of_check ridgeTest_256 4 4 (by decide +kernel)

theorem ridgeTest_256_block_2 : Interval ridgeTest_256 8 12 :=
  interval_of_check ridgeTest_256 8 4 (by decide +kernel)

theorem ridgeTest_256_block_3 : Interval ridgeTest_256 12 16 :=
  interval_of_check ridgeTest_256 12 4 (by decide +kernel)

theorem ridgeTest_256_block_4 : Interval ridgeTest_256 16 20 :=
  interval_of_check ridgeTest_256 16 4 (by decide +kernel)

theorem ridgeTest_256_block_5 : Interval ridgeTest_256 20 24 :=
  interval_of_check ridgeTest_256 20 4 (by decide +kernel)

theorem ridgeTest_256_block_6 : Interval ridgeTest_256 24 28 :=
  interval_of_check ridgeTest_256 24 4 (by decide +kernel)

theorem ridgeTest_256_block_7 : Interval ridgeTest_256 28 32 :=
  interval_of_check ridgeTest_256 28 4 (by decide +kernel)

theorem ridgeTest_256_block_8 : Interval ridgeTest_256 32 36 :=
  interval_of_check ridgeTest_256 32 4 (by decide +kernel)

theorem ridgeTest_256_block_9 : Interval ridgeTest_256 36 40 :=
  interval_of_check ridgeTest_256 36 4 (by decide +kernel)

theorem ridgeTest_256_block_10 : Interval ridgeTest_256 40 44 :=
  interval_of_check ridgeTest_256 40 4 (by decide +kernel)

theorem ridgeTest_256_block_11 : Interval ridgeTest_256 44 48 :=
  interval_of_check ridgeTest_256 44 4 (by decide +kernel)

theorem ridgeTest_256_block_12 : Interval ridgeTest_256 48 52 :=
  interval_of_check ridgeTest_256 48 4 (by decide +kernel)

theorem ridgeTest_256_block_13 : Interval ridgeTest_256 52 56 :=
  interval_of_check ridgeTest_256 52 4 (by decide +kernel)

theorem ridgeTest_256_block_14 : Interval ridgeTest_256 56 60 :=
  interval_of_check ridgeTest_256 56 4 (by decide +kernel)

theorem ridgeTest_256_block_15 : Interval ridgeTest_256 60 64 :=
  interval_of_check ridgeTest_256 60 4 (by decide +kernel)

theorem ridgeTest_256_block_16 : Interval ridgeTest_256 64 68 :=
  interval_of_check ridgeTest_256 64 4 (by decide +kernel)

theorem ridgeTest_256_block_17 : Interval ridgeTest_256 68 72 :=
  interval_of_check ridgeTest_256 68 4 (by decide +kernel)

theorem ridgeTest_256_block_18 : Interval ridgeTest_256 72 76 :=
  interval_of_check ridgeTest_256 72 4 (by decide +kernel)

theorem ridgeTest_256_block_19 : Interval ridgeTest_256 76 80 :=
  interval_of_check ridgeTest_256 76 4 (by decide +kernel)

theorem ridgeTest_256_block_20 : Interval ridgeTest_256 80 84 :=
  interval_of_check ridgeTest_256 80 4 (by decide +kernel)

theorem ridgeTest_256_block_21 : Interval ridgeTest_256 84 88 :=
  interval_of_check ridgeTest_256 84 4 (by decide +kernel)

theorem ridgeTest_256_block_22 : Interval ridgeTest_256 88 92 :=
  interval_of_check ridgeTest_256 88 4 (by decide +kernel)

theorem ridgeTest_256_block_23 : Interval ridgeTest_256 92 96 :=
  interval_of_check ridgeTest_256 92 4 (by decide +kernel)

theorem ridgeTest_256_block_24 : Interval ridgeTest_256 96 100 :=
  interval_of_check ridgeTest_256 96 4 (by decide +kernel)

theorem ridgeTest_256_block_25 : Interval ridgeTest_256 100 104 :=
  interval_of_check ridgeTest_256 100 4 (by decide +kernel)

theorem ridgeTest_256_block_26 : Interval ridgeTest_256 104 108 :=
  interval_of_check ridgeTest_256 104 4 (by decide +kernel)

theorem ridgeTest_256_block_27 : Interval ridgeTest_256 108 112 :=
  interval_of_check ridgeTest_256 108 4 (by decide +kernel)

theorem ridgeTest_256_block_28 : Interval ridgeTest_256 112 116 :=
  interval_of_check ridgeTest_256 112 4 (by decide +kernel)

theorem ridgeTest_256_block_29 : Interval ridgeTest_256 116 120 :=
  interval_of_check ridgeTest_256 116 4 (by decide +kernel)

theorem ridgeTest_256_block_30 : Interval ridgeTest_256 120 124 :=
  interval_of_check ridgeTest_256 120 4 (by decide +kernel)

theorem ridgeTest_256_block_31 : Interval ridgeTest_256 124 128 :=
  interval_of_check ridgeTest_256 124 4 (by decide +kernel)

theorem ridgeTest_256_complete : Interval ridgeTest_256 0 128 :=
  (interval_append ridgeTest_256 0 64 128
  (interval_append ridgeTest_256 0 32 64
  (interval_append ridgeTest_256 0 16 32
  (interval_append ridgeTest_256 0 8 16
  (interval_append ridgeTest_256 0 4 8
  ridgeTest_256_block_0
  ridgeTest_256_block_1)
  (interval_append ridgeTest_256 8 12 16
  ridgeTest_256_block_2
  ridgeTest_256_block_3))
  (interval_append ridgeTest_256 16 24 32
  (interval_append ridgeTest_256 16 20 24
  ridgeTest_256_block_4
  ridgeTest_256_block_5)
  (interval_append ridgeTest_256 24 28 32
  ridgeTest_256_block_6
  ridgeTest_256_block_7)))
  (interval_append ridgeTest_256 32 48 64
  (interval_append ridgeTest_256 32 40 48
  (interval_append ridgeTest_256 32 36 40
  ridgeTest_256_block_8
  ridgeTest_256_block_9)
  (interval_append ridgeTest_256 40 44 48
  ridgeTest_256_block_10
  ridgeTest_256_block_11))
  (interval_append ridgeTest_256 48 56 64
  (interval_append ridgeTest_256 48 52 56
  ridgeTest_256_block_12
  ridgeTest_256_block_13)
  (interval_append ridgeTest_256 56 60 64
  ridgeTest_256_block_14
  ridgeTest_256_block_15))))
  (interval_append ridgeTest_256 64 96 128
  (interval_append ridgeTest_256 64 80 96
  (interval_append ridgeTest_256 64 72 80
  (interval_append ridgeTest_256 64 68 72
  ridgeTest_256_block_16
  ridgeTest_256_block_17)
  (interval_append ridgeTest_256 72 76 80
  ridgeTest_256_block_18
  ridgeTest_256_block_19))
  (interval_append ridgeTest_256 80 88 96
  (interval_append ridgeTest_256 80 84 88
  ridgeTest_256_block_20
  ridgeTest_256_block_21)
  (interval_append ridgeTest_256 88 92 96
  ridgeTest_256_block_22
  ridgeTest_256_block_23)))
  (interval_append ridgeTest_256 96 112 128
  (interval_append ridgeTest_256 96 104 112
  (interval_append ridgeTest_256 96 100 104
  ridgeTest_256_block_24
  ridgeTest_256_block_25)
  (interval_append ridgeTest_256 104 108 112
  ridgeTest_256_block_26
  ridgeTest_256_block_27))
  (interval_append ridgeTest_256 112 120 128
  (interval_append ridgeTest_256 112 116 120
  ridgeTest_256_block_28
  ridgeTest_256_block_29)
  (interval_append ridgeTest_256 120 124 128
  ridgeTest_256_block_30
  ridgeTest_256_block_31)))))
theorem ridgeTest_interval_256 : Interval ridgeTest 256 384 := by
  intro i hlo hhi
  have h := ridgeTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
