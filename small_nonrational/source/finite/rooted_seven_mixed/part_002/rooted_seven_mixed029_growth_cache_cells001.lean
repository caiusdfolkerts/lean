module
prelude
public import RootedSevenMixed029GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed029
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_256 (i : Nat) := cellTest (i+256)
theorem cellTest_256_block_0 : Interval cellTest_256 0 8 :=
  interval_of_check cellTest_256 0 8 (by decide +kernel)

theorem cellTest_256_block_1 : Interval cellTest_256 8 16 :=
  interval_of_check cellTest_256 8 8 (by decide +kernel)

theorem cellTest_256_block_2 : Interval cellTest_256 16 24 :=
  interval_of_check cellTest_256 16 8 (by decide +kernel)

theorem cellTest_256_block_3 : Interval cellTest_256 24 32 :=
  interval_of_check cellTest_256 24 8 (by decide +kernel)

theorem cellTest_256_block_4 : Interval cellTest_256 32 40 :=
  interval_of_check cellTest_256 32 8 (by decide +kernel)

theorem cellTest_256_block_5 : Interval cellTest_256 40 48 :=
  interval_of_check cellTest_256 40 8 (by decide +kernel)

theorem cellTest_256_block_6 : Interval cellTest_256 48 56 :=
  interval_of_check cellTest_256 48 8 (by decide +kernel)

theorem cellTest_256_block_7 : Interval cellTest_256 56 64 :=
  interval_of_check cellTest_256 56 8 (by decide +kernel)

theorem cellTest_256_block_8 : Interval cellTest_256 64 72 :=
  interval_of_check cellTest_256 64 8 (by decide +kernel)

theorem cellTest_256_block_9 : Interval cellTest_256 72 80 :=
  interval_of_check cellTest_256 72 8 (by decide +kernel)

theorem cellTest_256_block_10 : Interval cellTest_256 80 88 :=
  interval_of_check cellTest_256 80 8 (by decide +kernel)

theorem cellTest_256_block_11 : Interval cellTest_256 88 96 :=
  interval_of_check cellTest_256 88 8 (by decide +kernel)

theorem cellTest_256_block_12 : Interval cellTest_256 96 104 :=
  interval_of_check cellTest_256 96 8 (by decide +kernel)

theorem cellTest_256_block_13 : Interval cellTest_256 104 112 :=
  interval_of_check cellTest_256 104 8 (by decide +kernel)

theorem cellTest_256_block_14 : Interval cellTest_256 112 120 :=
  interval_of_check cellTest_256 112 8 (by decide +kernel)

theorem cellTest_256_complete : Interval cellTest_256 0 120 :=
  (interval_append cellTest_256 0 56 120
  (interval_append cellTest_256 0 24 56
  (interval_append cellTest_256 0 8 24
  cellTest_256_block_0
  (interval_append cellTest_256 8 16 24
  cellTest_256_block_1
  cellTest_256_block_2))
  (interval_append cellTest_256 24 40 56
  (interval_append cellTest_256 24 32 40
  cellTest_256_block_3
  cellTest_256_block_4)
  (interval_append cellTest_256 40 48 56
  cellTest_256_block_5
  cellTest_256_block_6)))
  (interval_append cellTest_256 56 88 120
  (interval_append cellTest_256 56 72 88
  (interval_append cellTest_256 56 64 72
  cellTest_256_block_7
  cellTest_256_block_8)
  (interval_append cellTest_256 72 80 88
  cellTest_256_block_9
  cellTest_256_block_10))
  (interval_append cellTest_256 88 104 120
  (interval_append cellTest_256 88 96 104
  cellTest_256_block_11
  cellTest_256_block_12)
  (interval_append cellTest_256 104 112 120
  cellTest_256_block_13
  cellTest_256_block_14))))
theorem cellTestInterval256 : Interval cellTest 256 376 := by
  intro i hlo hhi
  have h := cellTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [cellTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed029
