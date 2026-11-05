module
prelude
public import RootedSixExtra04GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_3584 (i : Nat) := wellFormedTest (i+3584)
theorem wellFormedTest_3584_block_0 : Interval wellFormedTest_3584 0 16 :=
  interval_of_check wellFormedTest_3584 0 16 (by decide +kernel)

theorem wellFormedTest_3584_block_1 : Interval wellFormedTest_3584 16 32 :=
  interval_of_check wellFormedTest_3584 16 16 (by decide +kernel)

theorem wellFormedTest_3584_block_2 : Interval wellFormedTest_3584 32 48 :=
  interval_of_check wellFormedTest_3584 32 16 (by decide +kernel)

theorem wellFormedTest_3584_block_3 : Interval wellFormedTest_3584 48 56 :=
  interval_of_check wellFormedTest_3584 48 8 (by decide +kernel)

theorem wellFormedTest_3584_complete : Interval wellFormedTest_3584 0 56 :=
  (interval_append wellFormedTest_3584 0 32 56
  (interval_append wellFormedTest_3584 0 16 32
  wellFormedTest_3584_block_0
  wellFormedTest_3584_block_1)
  (interval_append wellFormedTest_3584 32 48 56
  wellFormedTest_3584_block_2
  wellFormedTest_3584_block_3))
theorem wellFormedTestInterval3584 : Interval wellFormedTest 3584 3640 := by
  intro i hlo hhi
  have h := wellFormedTest_3584_complete (i-3584) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_3584, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra04
