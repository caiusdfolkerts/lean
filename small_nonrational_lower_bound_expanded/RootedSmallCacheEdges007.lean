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
def edgeTest_896 (i : Nat) := edgeTest (i+896)
theorem edgeTest_896_block_0 : Interval edgeTest_896 0 4 :=
  interval_of_check edgeTest_896 0 4 (by decide +kernel)

theorem edgeTest_896_block_1 : Interval edgeTest_896 4 8 :=
  interval_of_check edgeTest_896 4 4 (by decide +kernel)

theorem edgeTest_896_block_2 : Interval edgeTest_896 8 12 :=
  interval_of_check edgeTest_896 8 4 (by decide +kernel)

theorem edgeTest_896_block_3 : Interval edgeTest_896 12 16 :=
  interval_of_check edgeTest_896 12 4 (by decide +kernel)

theorem edgeTest_896_block_4 : Interval edgeTest_896 16 20 :=
  interval_of_check edgeTest_896 16 4 (by decide +kernel)

theorem edgeTest_896_block_5 : Interval edgeTest_896 20 24 :=
  interval_of_check edgeTest_896 20 4 (by decide +kernel)

theorem edgeTest_896_block_6 : Interval edgeTest_896 24 28 :=
  interval_of_check edgeTest_896 24 4 (by decide +kernel)

theorem edgeTest_896_block_7 : Interval edgeTest_896 28 32 :=
  interval_of_check edgeTest_896 28 4 (by decide +kernel)

theorem edgeTest_896_block_8 : Interval edgeTest_896 32 36 :=
  interval_of_check edgeTest_896 32 4 (by decide +kernel)

theorem edgeTest_896_block_9 : Interval edgeTest_896 36 40 :=
  interval_of_check edgeTest_896 36 4 (by decide +kernel)

theorem edgeTest_896_block_10 : Interval edgeTest_896 40 44 :=
  interval_of_check edgeTest_896 40 4 (by decide +kernel)

theorem edgeTest_896_block_11 : Interval edgeTest_896 44 48 :=
  interval_of_check edgeTest_896 44 4 (by decide +kernel)

theorem edgeTest_896_block_12 : Interval edgeTest_896 48 52 :=
  interval_of_check edgeTest_896 48 4 (by decide +kernel)

theorem edgeTest_896_block_13 : Interval edgeTest_896 52 56 :=
  interval_of_check edgeTest_896 52 4 (by decide +kernel)

theorem edgeTest_896_block_14 : Interval edgeTest_896 56 60 :=
  interval_of_check edgeTest_896 56 4 (by decide +kernel)

theorem edgeTest_896_block_15 : Interval edgeTest_896 60 64 :=
  interval_of_check edgeTest_896 60 4 (by decide +kernel)

theorem edgeTest_896_block_16 : Interval edgeTest_896 64 68 :=
  interval_of_check edgeTest_896 64 4 (by decide +kernel)

theorem edgeTest_896_block_17 : Interval edgeTest_896 68 72 :=
  interval_of_check edgeTest_896 68 4 (by decide +kernel)

theorem edgeTest_896_block_18 : Interval edgeTest_896 72 76 :=
  interval_of_check edgeTest_896 72 4 (by decide +kernel)

theorem edgeTest_896_block_19 : Interval edgeTest_896 76 80 :=
  interval_of_check edgeTest_896 76 4 (by decide +kernel)

theorem edgeTest_896_block_20 : Interval edgeTest_896 80 84 :=
  interval_of_check edgeTest_896 80 4 (by decide +kernel)

theorem edgeTest_896_block_21 : Interval edgeTest_896 84 88 :=
  interval_of_check edgeTest_896 84 4 (by decide +kernel)

theorem edgeTest_896_block_22 : Interval edgeTest_896 88 92 :=
  interval_of_check edgeTest_896 88 4 (by decide +kernel)

theorem edgeTest_896_block_23 : Interval edgeTest_896 92 96 :=
  interval_of_check edgeTest_896 92 4 (by decide +kernel)

theorem edgeTest_896_block_24 : Interval edgeTest_896 96 100 :=
  interval_of_check edgeTest_896 96 4 (by decide +kernel)

theorem edgeTest_896_block_25 : Interval edgeTest_896 100 104 :=
  interval_of_check edgeTest_896 100 4 (by decide +kernel)

theorem edgeTest_896_block_26 : Interval edgeTest_896 104 108 :=
  interval_of_check edgeTest_896 104 4 (by decide +kernel)

theorem edgeTest_896_block_27 : Interval edgeTest_896 108 112 :=
  interval_of_check edgeTest_896 108 4 (by decide +kernel)

theorem edgeTest_896_block_28 : Interval edgeTest_896 112 116 :=
  interval_of_check edgeTest_896 112 4 (by decide +kernel)

theorem edgeTest_896_block_29 : Interval edgeTest_896 116 120 :=
  interval_of_check edgeTest_896 116 4 (by decide +kernel)

theorem edgeTest_896_block_30 : Interval edgeTest_896 120 124 :=
  interval_of_check edgeTest_896 120 4 (by decide +kernel)

theorem edgeTest_896_block_31 : Interval edgeTest_896 124 128 :=
  interval_of_check edgeTest_896 124 4 (by decide +kernel)

theorem edgeTest_896_complete : Interval edgeTest_896 0 128 :=
  (interval_append edgeTest_896 0 64 128
  (interval_append edgeTest_896 0 32 64
  (interval_append edgeTest_896 0 16 32
  (interval_append edgeTest_896 0 8 16
  (interval_append edgeTest_896 0 4 8
  edgeTest_896_block_0
  edgeTest_896_block_1)
  (interval_append edgeTest_896 8 12 16
  edgeTest_896_block_2
  edgeTest_896_block_3))
  (interval_append edgeTest_896 16 24 32
  (interval_append edgeTest_896 16 20 24
  edgeTest_896_block_4
  edgeTest_896_block_5)
  (interval_append edgeTest_896 24 28 32
  edgeTest_896_block_6
  edgeTest_896_block_7)))
  (interval_append edgeTest_896 32 48 64
  (interval_append edgeTest_896 32 40 48
  (interval_append edgeTest_896 32 36 40
  edgeTest_896_block_8
  edgeTest_896_block_9)
  (interval_append edgeTest_896 40 44 48
  edgeTest_896_block_10
  edgeTest_896_block_11))
  (interval_append edgeTest_896 48 56 64
  (interval_append edgeTest_896 48 52 56
  edgeTest_896_block_12
  edgeTest_896_block_13)
  (interval_append edgeTest_896 56 60 64
  edgeTest_896_block_14
  edgeTest_896_block_15))))
  (interval_append edgeTest_896 64 96 128
  (interval_append edgeTest_896 64 80 96
  (interval_append edgeTest_896 64 72 80
  (interval_append edgeTest_896 64 68 72
  edgeTest_896_block_16
  edgeTest_896_block_17)
  (interval_append edgeTest_896 72 76 80
  edgeTest_896_block_18
  edgeTest_896_block_19))
  (interval_append edgeTest_896 80 88 96
  (interval_append edgeTest_896 80 84 88
  edgeTest_896_block_20
  edgeTest_896_block_21)
  (interval_append edgeTest_896 88 92 96
  edgeTest_896_block_22
  edgeTest_896_block_23)))
  (interval_append edgeTest_896 96 112 128
  (interval_append edgeTest_896 96 104 112
  (interval_append edgeTest_896 96 100 104
  edgeTest_896_block_24
  edgeTest_896_block_25)
  (interval_append edgeTest_896 104 108 112
  edgeTest_896_block_26
  edgeTest_896_block_27))
  (interval_append edgeTest_896 112 120 128
  (interval_append edgeTest_896 112 116 120
  edgeTest_896_block_28
  edgeTest_896_block_29)
  (interval_append edgeTest_896 120 124 128
  edgeTest_896_block_30
  edgeTest_896_block_31)))))
theorem edgeTest_interval_896 : Interval edgeTest 896 1024 := by
  intro i hlo hhi
  have h := edgeTest_896_complete (i-896) (Nat.zero_le _) (by omega)
  simpa only [edgeTest_896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
