module
prelude
public import RootedSevenMixed022GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed022
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_512 (i : Nat) := wellFormedTest (i+512)
theorem wellFormedTest_512_block_0 : Interval wellFormedTest_512 0 16 :=
  interval_of_check wellFormedTest_512 0 16 (by decide +kernel)

theorem wellFormedTest_512_block_1 : Interval wellFormedTest_512 16 32 :=
  interval_of_check wellFormedTest_512 16 16 (by decide +kernel)

theorem wellFormedTest_512_block_2 : Interval wellFormedTest_512 32 44 :=
  interval_of_check wellFormedTest_512 32 12 (by decide +kernel)

theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 44 :=
  (interval_append wellFormedTest_512 0 16 44
  wellFormedTest_512_block_0
  (interval_append wellFormedTest_512 16 32 44
  wellFormedTest_512_block_1
  wellFormedTest_512_block_2))
theorem wellFormedTestInterval512 : Interval wellFormedTest 512 556 := by
  intro i hlo hhi
  have h := wellFormedTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed022
