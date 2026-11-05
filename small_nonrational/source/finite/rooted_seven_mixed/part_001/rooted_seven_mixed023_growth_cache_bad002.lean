module
prelude
public import RootedSevenMixed023GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed023
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_512 (i : Nat) := badTest (i+512)
theorem badTest_512_block_0 : Interval badTest_512 0 8 :=
  interval_of_check badTest_512 0 8 (by decide +kernel)

theorem badTest_512_block_1 : Interval badTest_512 8 16 :=
  interval_of_check badTest_512 8 8 (by decide +kernel)

theorem badTest_512_block_2 : Interval badTest_512 16 24 :=
  interval_of_check badTest_512 16 8 (by decide +kernel)

theorem badTest_512_block_3 : Interval badTest_512 24 32 :=
  interval_of_check badTest_512 24 8 (by decide +kernel)

theorem badTest_512_block_4 : Interval badTest_512 32 40 :=
  interval_of_check badTest_512 32 8 (by decide +kernel)

theorem badTest_512_block_5 : Interval badTest_512 40 44 :=
  interval_of_check badTest_512 40 4 (by decide +kernel)

theorem badTest_512_complete : Interval badTest_512 0 44 :=
  (interval_append badTest_512 0 24 44
  (interval_append badTest_512 0 8 24
  badTest_512_block_0
  (interval_append badTest_512 8 16 24
  badTest_512_block_1
  badTest_512_block_2))
  (interval_append badTest_512 24 32 44
  badTest_512_block_3
  (interval_append badTest_512 32 40 44
  badTest_512_block_4
  badTest_512_block_5)))
theorem badTestInterval512 : Interval badTest 512 556 := by
  intro i hlo hhi
  have h := badTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [badTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed023
