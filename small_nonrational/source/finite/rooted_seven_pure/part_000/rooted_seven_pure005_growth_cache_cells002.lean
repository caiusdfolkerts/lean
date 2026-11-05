module
prelude
public import RootedSevenPure005GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure005
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_512 (i : Nat) := cellTest (i+512)
theorem cellTest_512_block_0 : Interval cellTest_512 0 8 :=
  interval_of_check cellTest_512 0 8 (by decide +kernel)

theorem cellTest_512_block_1 : Interval cellTest_512 8 16 :=
  interval_of_check cellTest_512 8 8 (by decide +kernel)

theorem cellTest_512_block_2 : Interval cellTest_512 16 24 :=
  interval_of_check cellTest_512 16 8 (by decide +kernel)

theorem cellTest_512_block_3 : Interval cellTest_512 24 32 :=
  interval_of_check cellTest_512 24 8 (by decide +kernel)

theorem cellTest_512_block_4 : Interval cellTest_512 32 40 :=
  interval_of_check cellTest_512 32 8 (by decide +kernel)

theorem cellTest_512_block_5 : Interval cellTest_512 40 48 :=
  interval_of_check cellTest_512 40 8 (by decide +kernel)

theorem cellTest_512_block_6 : Interval cellTest_512 48 56 :=
  interval_of_check cellTest_512 48 8 (by decide +kernel)

theorem cellTest_512_block_7 : Interval cellTest_512 56 64 :=
  interval_of_check cellTest_512 56 8 (by decide +kernel)

theorem cellTest_512_block_8 : Interval cellTest_512 64 72 :=
  interval_of_check cellTest_512 64 8 (by decide +kernel)

theorem cellTest_512_block_9 : Interval cellTest_512 72 74 :=
  interval_of_check cellTest_512 72 2 (by decide +kernel)

theorem cellTest_512_complete : Interval cellTest_512 0 74 :=
  (interval_append cellTest_512 0 40 74
  (interval_append cellTest_512 0 16 40
  (interval_append cellTest_512 0 8 16
  cellTest_512_block_0
  cellTest_512_block_1)
  (interval_append cellTest_512 16 24 40
  cellTest_512_block_2
  (interval_append cellTest_512 24 32 40
  cellTest_512_block_3
  cellTest_512_block_4)))
  (interval_append cellTest_512 40 56 74
  (interval_append cellTest_512 40 48 56
  cellTest_512_block_5
  cellTest_512_block_6)
  (interval_append cellTest_512 56 64 74
  cellTest_512_block_7
  (interval_append cellTest_512 64 72 74
  cellTest_512_block_8
  cellTest_512_block_9))))
theorem cellTestInterval512 : Interval cellTest 512 586 := by
  intro i hlo hhi
  have h := cellTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [cellTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure005
