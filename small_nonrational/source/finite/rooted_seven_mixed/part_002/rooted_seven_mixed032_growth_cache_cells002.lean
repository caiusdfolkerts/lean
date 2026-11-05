module
prelude
public import RootedSevenMixed032GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed032
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_512 (i : Nat) := cellTest (i+512)
theorem cellTest_512_block_0 : Interval cellTest_512 0 8 :=
  interval_of_check cellTest_512 0 8 (by decide +kernel)

theorem cellTest_512_block_1 : Interval cellTest_512 8 16 :=
  interval_of_check cellTest_512 8 8 (by decide +kernel)

theorem cellTest_512_block_2 : Interval cellTest_512 16 17 :=
  interval_of_check cellTest_512 16 1 (by decide +kernel)

theorem cellTest_512_complete : Interval cellTest_512 0 17 :=
  (interval_append cellTest_512 0 8 17
  cellTest_512_block_0
  (interval_append cellTest_512 8 16 17
  cellTest_512_block_1
  cellTest_512_block_2))
theorem cellTestInterval512 : Interval cellTest 512 529 := by
  intro i hlo hhi
  have h := cellTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [cellTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed032
