module
prelude
public import RootedSevenMixed026GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed026
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

theorem cellTest_512_block_5 : Interval cellTest_512 40 44 :=
  interval_of_check cellTest_512 40 4 (by decide +kernel)

theorem cellTest_512_complete : Interval cellTest_512 0 44 :=
  (interval_append cellTest_512 0 24 44
  (interval_append cellTest_512 0 8 24
  cellTest_512_block_0
  (interval_append cellTest_512 8 16 24
  cellTest_512_block_1
  cellTest_512_block_2))
  (interval_append cellTest_512 24 32 44
  cellTest_512_block_3
  (interval_append cellTest_512 32 40 44
  cellTest_512_block_4
  cellTest_512_block_5)))
theorem cellTestInterval512 : Interval cellTest 512 556 := by
  intro i hlo hhi
  have h := cellTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [cellTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed026
