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
def ridgeTest_640 (i : Nat) := ridgeTest (i+640)
theorem ridgeTest_640_block_0 : Interval ridgeTest_640 0 4 :=
  interval_of_check ridgeTest_640 0 4 (by decide +kernel)

theorem ridgeTest_640_block_1 : Interval ridgeTest_640 4 8 :=
  interval_of_check ridgeTest_640 4 4 (by decide +kernel)

theorem ridgeTest_640_block_2 : Interval ridgeTest_640 8 12 :=
  interval_of_check ridgeTest_640 8 4 (by decide +kernel)

theorem ridgeTest_640_block_3 : Interval ridgeTest_640 12 16 :=
  interval_of_check ridgeTest_640 12 4 (by decide +kernel)

theorem ridgeTest_640_block_4 : Interval ridgeTest_640 16 20 :=
  interval_of_check ridgeTest_640 16 4 (by decide +kernel)

theorem ridgeTest_640_block_5 : Interval ridgeTest_640 20 24 :=
  interval_of_check ridgeTest_640 20 4 (by decide +kernel)

theorem ridgeTest_640_block_6 : Interval ridgeTest_640 24 28 :=
  interval_of_check ridgeTest_640 24 4 (by decide +kernel)

theorem ridgeTest_640_block_7 : Interval ridgeTest_640 28 32 :=
  interval_of_check ridgeTest_640 28 4 (by decide +kernel)

theorem ridgeTest_640_block_8 : Interval ridgeTest_640 32 36 :=
  interval_of_check ridgeTest_640 32 4 (by decide +kernel)

theorem ridgeTest_640_block_9 : Interval ridgeTest_640 36 40 :=
  interval_of_check ridgeTest_640 36 4 (by decide +kernel)

theorem ridgeTest_640_block_10 : Interval ridgeTest_640 40 44 :=
  interval_of_check ridgeTest_640 40 4 (by decide +kernel)

theorem ridgeTest_640_block_11 : Interval ridgeTest_640 44 48 :=
  interval_of_check ridgeTest_640 44 4 (by decide +kernel)

theorem ridgeTest_640_block_12 : Interval ridgeTest_640 48 52 :=
  interval_of_check ridgeTest_640 48 4 (by decide +kernel)

theorem ridgeTest_640_block_13 : Interval ridgeTest_640 52 56 :=
  interval_of_check ridgeTest_640 52 4 (by decide +kernel)

theorem ridgeTest_640_block_14 : Interval ridgeTest_640 56 60 :=
  interval_of_check ridgeTest_640 56 4 (by decide +kernel)

theorem ridgeTest_640_block_15 : Interval ridgeTest_640 60 64 :=
  interval_of_check ridgeTest_640 60 4 (by decide +kernel)

theorem ridgeTest_640_block_16 : Interval ridgeTest_640 64 68 :=
  interval_of_check ridgeTest_640 64 4 (by decide +kernel)

theorem ridgeTest_640_block_17 : Interval ridgeTest_640 68 72 :=
  interval_of_check ridgeTest_640 68 4 (by decide +kernel)

theorem ridgeTest_640_block_18 : Interval ridgeTest_640 72 76 :=
  interval_of_check ridgeTest_640 72 4 (by decide +kernel)

theorem ridgeTest_640_block_19 : Interval ridgeTest_640 76 80 :=
  interval_of_check ridgeTest_640 76 4 (by decide +kernel)

theorem ridgeTest_640_block_20 : Interval ridgeTest_640 80 84 :=
  interval_of_check ridgeTest_640 80 4 (by decide +kernel)

theorem ridgeTest_640_block_21 : Interval ridgeTest_640 84 88 :=
  interval_of_check ridgeTest_640 84 4 (by decide +kernel)

theorem ridgeTest_640_block_22 : Interval ridgeTest_640 88 92 :=
  interval_of_check ridgeTest_640 88 4 (by decide +kernel)

theorem ridgeTest_640_block_23 : Interval ridgeTest_640 92 96 :=
  interval_of_check ridgeTest_640 92 4 (by decide +kernel)

theorem ridgeTest_640_block_24 : Interval ridgeTest_640 96 100 :=
  interval_of_check ridgeTest_640 96 4 (by decide +kernel)

theorem ridgeTest_640_block_25 : Interval ridgeTest_640 100 104 :=
  interval_of_check ridgeTest_640 100 4 (by decide +kernel)

theorem ridgeTest_640_block_26 : Interval ridgeTest_640 104 108 :=
  interval_of_check ridgeTest_640 104 4 (by decide +kernel)

theorem ridgeTest_640_block_27 : Interval ridgeTest_640 108 112 :=
  interval_of_check ridgeTest_640 108 4 (by decide +kernel)

theorem ridgeTest_640_block_28 : Interval ridgeTest_640 112 116 :=
  interval_of_check ridgeTest_640 112 4 (by decide +kernel)

theorem ridgeTest_640_block_29 : Interval ridgeTest_640 116 120 :=
  interval_of_check ridgeTest_640 116 4 (by decide +kernel)

theorem ridgeTest_640_block_30 : Interval ridgeTest_640 120 124 :=
  interval_of_check ridgeTest_640 120 4 (by decide +kernel)

theorem ridgeTest_640_block_31 : Interval ridgeTest_640 124 128 :=
  interval_of_check ridgeTest_640 124 4 (by decide +kernel)

theorem ridgeTest_640_complete : Interval ridgeTest_640 0 128 :=
  (interval_append ridgeTest_640 0 64 128
  (interval_append ridgeTest_640 0 32 64
  (interval_append ridgeTest_640 0 16 32
  (interval_append ridgeTest_640 0 8 16
  (interval_append ridgeTest_640 0 4 8
  ridgeTest_640_block_0
  ridgeTest_640_block_1)
  (interval_append ridgeTest_640 8 12 16
  ridgeTest_640_block_2
  ridgeTest_640_block_3))
  (interval_append ridgeTest_640 16 24 32
  (interval_append ridgeTest_640 16 20 24
  ridgeTest_640_block_4
  ridgeTest_640_block_5)
  (interval_append ridgeTest_640 24 28 32
  ridgeTest_640_block_6
  ridgeTest_640_block_7)))
  (interval_append ridgeTest_640 32 48 64
  (interval_append ridgeTest_640 32 40 48
  (interval_append ridgeTest_640 32 36 40
  ridgeTest_640_block_8
  ridgeTest_640_block_9)
  (interval_append ridgeTest_640 40 44 48
  ridgeTest_640_block_10
  ridgeTest_640_block_11))
  (interval_append ridgeTest_640 48 56 64
  (interval_append ridgeTest_640 48 52 56
  ridgeTest_640_block_12
  ridgeTest_640_block_13)
  (interval_append ridgeTest_640 56 60 64
  ridgeTest_640_block_14
  ridgeTest_640_block_15))))
  (interval_append ridgeTest_640 64 96 128
  (interval_append ridgeTest_640 64 80 96
  (interval_append ridgeTest_640 64 72 80
  (interval_append ridgeTest_640 64 68 72
  ridgeTest_640_block_16
  ridgeTest_640_block_17)
  (interval_append ridgeTest_640 72 76 80
  ridgeTest_640_block_18
  ridgeTest_640_block_19))
  (interval_append ridgeTest_640 80 88 96
  (interval_append ridgeTest_640 80 84 88
  ridgeTest_640_block_20
  ridgeTest_640_block_21)
  (interval_append ridgeTest_640 88 92 96
  ridgeTest_640_block_22
  ridgeTest_640_block_23)))
  (interval_append ridgeTest_640 96 112 128
  (interval_append ridgeTest_640 96 104 112
  (interval_append ridgeTest_640 96 100 104
  ridgeTest_640_block_24
  ridgeTest_640_block_25)
  (interval_append ridgeTest_640 104 108 112
  ridgeTest_640_block_26
  ridgeTest_640_block_27))
  (interval_append ridgeTest_640 112 120 128
  (interval_append ridgeTest_640 112 116 120
  ridgeTest_640_block_28
  ridgeTest_640_block_29)
  (interval_append ridgeTest_640 120 124 128
  ridgeTest_640_block_30
  ridgeTest_640_block_31)))))
theorem ridgeTest_interval_640 : Interval ridgeTest 640 768 := by
  intro i hlo hhi
  have h := ridgeTest_640_complete (i-640) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
