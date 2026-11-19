module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra04GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_3584 (i : Nat) := wellFormedTest (i+3584)
cert_wellFormedTest_block_5 3584 0 0 16 16
cert_wellFormedTest_block_5 3584 1 16 32 16
cert_wellFormedTest_block_5 3584 2 32 48 16
cert_wellFormedTest_block_5 3584 3 48 56 8
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
