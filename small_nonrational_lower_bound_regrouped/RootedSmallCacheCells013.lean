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
def cellTest_3328 (i : Nat) := cellTest (i+3328)
theorem cellTest_3328_block_0 : Interval cellTest_3328 0 8 :=
  interval_of_check cellTest_3328 0 8 (by decide +kernel)

theorem cellTest_3328_block_1 : Interval cellTest_3328 8 16 :=
  interval_of_check cellTest_3328 8 8 (by decide +kernel)

theorem cellTest_3328_block_2 : Interval cellTest_3328 16 24 :=
  interval_of_check cellTest_3328 16 8 (by decide +kernel)

theorem cellTest_3328_block_3 : Interval cellTest_3328 24 32 :=
  interval_of_check cellTest_3328 24 8 (by decide +kernel)

theorem cellTest_3328_block_4 : Interval cellTest_3328 32 40 :=
  interval_of_check cellTest_3328 32 8 (by decide +kernel)

theorem cellTest_3328_block_5 : Interval cellTest_3328 40 48 :=
  interval_of_check cellTest_3328 40 8 (by decide +kernel)

theorem cellTest_3328_block_6 : Interval cellTest_3328 48 56 :=
  interval_of_check cellTest_3328 48 8 (by decide +kernel)

theorem cellTest_3328_block_7 : Interval cellTest_3328 56 64 :=
  interval_of_check cellTest_3328 56 8 (by decide +kernel)

theorem cellTest_3328_block_8 : Interval cellTest_3328 64 72 :=
  interval_of_check cellTest_3328 64 8 (by decide +kernel)

theorem cellTest_3328_block_9 : Interval cellTest_3328 72 80 :=
  interval_of_check cellTest_3328 72 8 (by decide +kernel)

theorem cellTest_3328_block_10 : Interval cellTest_3328 80 88 :=
  interval_of_check cellTest_3328 80 8 (by decide +kernel)

theorem cellTest_3328_block_11 : Interval cellTest_3328 88 96 :=
  interval_of_check cellTest_3328 88 8 (by decide +kernel)

theorem cellTest_3328_block_12 : Interval cellTest_3328 96 104 :=
  interval_of_check cellTest_3328 96 8 (by decide +kernel)

theorem cellTest_3328_block_13 : Interval cellTest_3328 104 108 :=
  interval_of_check cellTest_3328 104 4 (by decide +kernel)

theorem cellTest_3328_complete : Interval cellTest_3328 0 108 :=
  (interval_append cellTest_3328 0 56 108
  (interval_append cellTest_3328 0 24 56
  (interval_append cellTest_3328 0 8 24
  cellTest_3328_block_0
  (interval_append cellTest_3328 8 16 24
  cellTest_3328_block_1
  cellTest_3328_block_2))
  (interval_append cellTest_3328 24 40 56
  (interval_append cellTest_3328 24 32 40
  cellTest_3328_block_3
  cellTest_3328_block_4)
  (interval_append cellTest_3328 40 48 56
  cellTest_3328_block_5
  cellTest_3328_block_6)))
  (interval_append cellTest_3328 56 80 108
  (interval_append cellTest_3328 56 64 80
  cellTest_3328_block_7
  (interval_append cellTest_3328 64 72 80
  cellTest_3328_block_8
  cellTest_3328_block_9))
  (interval_append cellTest_3328 80 96 108
  (interval_append cellTest_3328 80 88 96
  cellTest_3328_block_10
  cellTest_3328_block_11)
  (interval_append cellTest_3328 96 104 108
  cellTest_3328_block_12
  cellTest_3328_block_13))))
theorem cellTest_interval_3328 : Interval cellTest 3328 3436 := by
  intro i hlo hhi
  have h := cellTest_3328_complete (i-3328) (Nat.zero_le _) (by omega)
  simpa only [cellTest_3328, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedSmallCache
