module
prelude
public import RootedSevenMixed032GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed032
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_512 (i : Nat) := wellFormedTest (i+512)
theorem wellFormedTest_512_block_0 : Interval wellFormedTest_512 0 16 :=
  interval_of_check wellFormedTest_512 0 16 (by decide +kernel)

theorem wellFormedTest_512_block_1 : Interval wellFormedTest_512 16 17 :=
  interval_of_check wellFormedTest_512 16 1 (by decide +kernel)

theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 17 :=
  (interval_append wellFormedTest_512 0 16 17
  wellFormedTest_512_block_0
  wellFormedTest_512_block_1)
theorem wellFormedTestInterval512 : Interval wellFormedTest 512 529 := by
  intro i hlo hhi
  have h := wellFormedTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed032
