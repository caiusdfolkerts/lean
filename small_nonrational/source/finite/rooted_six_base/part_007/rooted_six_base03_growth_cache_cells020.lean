module
prelude
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_5120 (i : Nat) := cellTest (i+5120)
theorem cellTest_5120_block_0 : Interval cellTest_5120 0 8 :=
  interval_of_check cellTest_5120 0 8 (by decide +kernel)

theorem cellTest_5120_block_1 : Interval cellTest_5120 8 16 :=
  interval_of_check cellTest_5120 8 8 (by decide +kernel)

theorem cellTest_5120_block_2 : Interval cellTest_5120 16 24 :=
  interval_of_check cellTest_5120 16 8 (by decide +kernel)

theorem cellTest_5120_block_3 : Interval cellTest_5120 24 32 :=
  interval_of_check cellTest_5120 24 8 (by decide +kernel)

theorem cellTest_5120_block_4 : Interval cellTest_5120 32 40 :=
  interval_of_check cellTest_5120 32 8 (by decide +kernel)

theorem cellTest_5120_block_5 : Interval cellTest_5120 40 48 :=
  interval_of_check cellTest_5120 40 8 (by decide +kernel)

theorem cellTest_5120_block_6 : Interval cellTest_5120 48 56 :=
  interval_of_check cellTest_5120 48 8 (by decide +kernel)

theorem cellTest_5120_block_7 : Interval cellTest_5120 56 64 :=
  interval_of_check cellTest_5120 56 8 (by decide +kernel)

theorem cellTest_5120_block_8 : Interval cellTest_5120 64 72 :=
  interval_of_check cellTest_5120 64 8 (by decide +kernel)

theorem cellTest_5120_block_9 : Interval cellTest_5120 72 80 :=
  interval_of_check cellTest_5120 72 8 (by decide +kernel)

theorem cellTest_5120_block_10 : Interval cellTest_5120 80 88 :=
  interval_of_check cellTest_5120 80 8 (by decide +kernel)

theorem cellTest_5120_block_11 : Interval cellTest_5120 88 96 :=
  interval_of_check cellTest_5120 88 8 (by decide +kernel)

theorem cellTest_5120_block_12 : Interval cellTest_5120 96 104 :=
  interval_of_check cellTest_5120 96 8 (by decide +kernel)

theorem cellTest_5120_block_13 : Interval cellTest_5120 104 112 :=
  interval_of_check cellTest_5120 104 8 (by decide +kernel)

theorem cellTest_5120_block_14 : Interval cellTest_5120 112 118 :=
  interval_of_check cellTest_5120 112 6 (by decide +kernel)

theorem cellTest_5120_complete : Interval cellTest_5120 0 118 :=
  (interval_append cellTest_5120 0 56 118
  (interval_append cellTest_5120 0 24 56
  (interval_append cellTest_5120 0 8 24
  cellTest_5120_block_0
  (interval_append cellTest_5120 8 16 24
  cellTest_5120_block_1
  cellTest_5120_block_2))
  (interval_append cellTest_5120 24 40 56
  (interval_append cellTest_5120 24 32 40
  cellTest_5120_block_3
  cellTest_5120_block_4)
  (interval_append cellTest_5120 40 48 56
  cellTest_5120_block_5
  cellTest_5120_block_6)))
  (interval_append cellTest_5120 56 88 118
  (interval_append cellTest_5120 56 72 88
  (interval_append cellTest_5120 56 64 72
  cellTest_5120_block_7
  cellTest_5120_block_8)
  (interval_append cellTest_5120 72 80 88
  cellTest_5120_block_9
  cellTest_5120_block_10))
  (interval_append cellTest_5120 88 104 118
  (interval_append cellTest_5120 88 96 104
  cellTest_5120_block_11
  cellTest_5120_block_12)
  (interval_append cellTest_5120 104 112 118
  cellTest_5120_block_13
  cellTest_5120_block_14))))
theorem cellTestInterval5120 : Interval cellTest 5120 5238 := by
  intro i hlo hhi
  have h := cellTest_5120_complete (i-5120) (Nat.zero_le _) (by omega)
  simpa only [cellTest_5120, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase03
