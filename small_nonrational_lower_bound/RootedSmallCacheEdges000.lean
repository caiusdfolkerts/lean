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
def edgeTest_0 (i : Nat) := edgeTest (i+0)
theorem edgeTest_0_block_0 : Interval edgeTest_0 0 4 :=
  interval_of_check edgeTest_0 0 4 (by decide +kernel)

theorem edgeTest_0_block_1 : Interval edgeTest_0 4 8 :=
  interval_of_check edgeTest_0 4 4 (by decide +kernel)

theorem edgeTest_0_block_2 : Interval edgeTest_0 8 12 :=
  interval_of_check edgeTest_0 8 4 (by decide +kernel)

theorem edgeTest_0_block_3 : Interval edgeTest_0 12 16 :=
  interval_of_check edgeTest_0 12 4 (by decide +kernel)

theorem edgeTest_0_block_4 : Interval edgeTest_0 16 20 :=
  interval_of_check edgeTest_0 16 4 (by decide +kernel)

theorem edgeTest_0_block_5 : Interval edgeTest_0 20 24 :=
  interval_of_check edgeTest_0 20 4 (by decide +kernel)

theorem edgeTest_0_block_6 : Interval edgeTest_0 24 28 :=
  interval_of_check edgeTest_0 24 4 (by decide +kernel)

theorem edgeTest_0_block_7 : Interval edgeTest_0 28 32 :=
  interval_of_check edgeTest_0 28 4 (by decide +kernel)

theorem edgeTest_0_block_8 : Interval edgeTest_0 32 36 :=
  interval_of_check edgeTest_0 32 4 (by decide +kernel)

theorem edgeTest_0_block_9 : Interval edgeTest_0 36 40 :=
  interval_of_check edgeTest_0 36 4 (by decide +kernel)

theorem edgeTest_0_block_10 : Interval edgeTest_0 40 44 :=
  interval_of_check edgeTest_0 40 4 (by decide +kernel)

theorem edgeTest_0_block_11 : Interval edgeTest_0 44 48 :=
  interval_of_check edgeTest_0 44 4 (by decide +kernel)

theorem edgeTest_0_block_12 : Interval edgeTest_0 48 52 :=
  interval_of_check edgeTest_0 48 4 (by decide +kernel)

theorem edgeTest_0_block_13 : Interval edgeTest_0 52 56 :=
  interval_of_check edgeTest_0 52 4 (by decide +kernel)

theorem edgeTest_0_block_14 : Interval edgeTest_0 56 60 :=
  interval_of_check edgeTest_0 56 4 (by decide +kernel)

theorem edgeTest_0_block_15 : Interval edgeTest_0 60 64 :=
  interval_of_check edgeTest_0 60 4 (by decide +kernel)

theorem edgeTest_0_block_16 : Interval edgeTest_0 64 68 :=
  interval_of_check edgeTest_0 64 4 (by decide +kernel)

theorem edgeTest_0_block_17 : Interval edgeTest_0 68 72 :=
  interval_of_check edgeTest_0 68 4 (by decide +kernel)

theorem edgeTest_0_block_18 : Interval edgeTest_0 72 76 :=
  interval_of_check edgeTest_0 72 4 (by decide +kernel)

theorem edgeTest_0_block_19 : Interval edgeTest_0 76 80 :=
  interval_of_check edgeTest_0 76 4 (by decide +kernel)

theorem edgeTest_0_block_20 : Interval edgeTest_0 80 84 :=
  interval_of_check edgeTest_0 80 4 (by decide +kernel)

theorem edgeTest_0_block_21 : Interval edgeTest_0 84 88 :=
  interval_of_check edgeTest_0 84 4 (by decide +kernel)

theorem edgeTest_0_block_22 : Interval edgeTest_0 88 92 :=
  interval_of_check edgeTest_0 88 4 (by decide +kernel)

theorem edgeTest_0_block_23 : Interval edgeTest_0 92 96 :=
  interval_of_check edgeTest_0 92 4 (by decide +kernel)

theorem edgeTest_0_block_24 : Interval edgeTest_0 96 100 :=
  interval_of_check edgeTest_0 96 4 (by decide +kernel)

theorem edgeTest_0_block_25 : Interval edgeTest_0 100 104 :=
  interval_of_check edgeTest_0 100 4 (by decide +kernel)

theorem edgeTest_0_block_26 : Interval edgeTest_0 104 108 :=
  interval_of_check edgeTest_0 104 4 (by decide +kernel)

theorem edgeTest_0_block_27 : Interval edgeTest_0 108 112 :=
  interval_of_check edgeTest_0 108 4 (by decide +kernel)

theorem edgeTest_0_block_28 : Interval edgeTest_0 112 116 :=
  interval_of_check edgeTest_0 112 4 (by decide +kernel)

theorem edgeTest_0_block_29 : Interval edgeTest_0 116 120 :=
  interval_of_check edgeTest_0 116 4 (by decide +kernel)

theorem edgeTest_0_block_30 : Interval edgeTest_0 120 124 :=
  interval_of_check edgeTest_0 120 4 (by decide +kernel)

theorem edgeTest_0_block_31 : Interval edgeTest_0 124 128 :=
  interval_of_check edgeTest_0 124 4 (by decide +kernel)

theorem edgeTest_0_complete : Interval edgeTest_0 0 128 :=
  (interval_append edgeTest_0 0 64 128
  (interval_append edgeTest_0 0 32 64
  (interval_append edgeTest_0 0 16 32
  (interval_append edgeTest_0 0 8 16
  (interval_append edgeTest_0 0 4 8
  edgeTest_0_block_0
  edgeTest_0_block_1)
  (interval_append edgeTest_0 8 12 16
  edgeTest_0_block_2
  edgeTest_0_block_3))
  (interval_append edgeTest_0 16 24 32
  (interval_append edgeTest_0 16 20 24
  edgeTest_0_block_4
  edgeTest_0_block_5)
  (interval_append edgeTest_0 24 28 32
  edgeTest_0_block_6
  edgeTest_0_block_7)))
  (interval_append edgeTest_0 32 48 64
  (interval_append edgeTest_0 32 40 48
  (interval_append edgeTest_0 32 36 40
  edgeTest_0_block_8
  edgeTest_0_block_9)
  (interval_append edgeTest_0 40 44 48
  edgeTest_0_block_10
  edgeTest_0_block_11))
  (interval_append edgeTest_0 48 56 64
  (interval_append edgeTest_0 48 52 56
  edgeTest_0_block_12
  edgeTest_0_block_13)
  (interval_append edgeTest_0 56 60 64
  edgeTest_0_block_14
  edgeTest_0_block_15))))
  (interval_append edgeTest_0 64 96 128
  (interval_append edgeTest_0 64 80 96
  (interval_append edgeTest_0 64 72 80
  (interval_append edgeTest_0 64 68 72
  edgeTest_0_block_16
  edgeTest_0_block_17)
  (interval_append edgeTest_0 72 76 80
  edgeTest_0_block_18
  edgeTest_0_block_19))
  (interval_append edgeTest_0 80 88 96
  (interval_append edgeTest_0 80 84 88
  edgeTest_0_block_20
  edgeTest_0_block_21)
  (interval_append edgeTest_0 88 92 96
  edgeTest_0_block_22
  edgeTest_0_block_23)))
  (interval_append edgeTest_0 96 112 128
  (interval_append edgeTest_0 96 104 112
  (interval_append edgeTest_0 96 100 104
  edgeTest_0_block_24
  edgeTest_0_block_25)
  (interval_append edgeTest_0 104 108 112
  edgeTest_0_block_26
  edgeTest_0_block_27))
  (interval_append edgeTest_0 112 120 128
  (interval_append edgeTest_0 112 116 120
  edgeTest_0_block_28
  edgeTest_0_block_29)
  (interval_append edgeTest_0 120 124 128
  edgeTest_0_block_30
  edgeTest_0_block_31)))))
theorem edgeTest_interval_0 : Interval edgeTest 0 128 := by
  intro i hlo hhi
  have h := edgeTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [edgeTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
