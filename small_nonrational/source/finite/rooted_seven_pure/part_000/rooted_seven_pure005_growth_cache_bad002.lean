module
prelude
public import RootedSevenPure005GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure005
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

theorem badTest_512_block_5 : Interval badTest_512 40 48 :=
  interval_of_check badTest_512 40 8 (by decide +kernel)

theorem badTest_512_block_6 : Interval badTest_512 48 56 :=
  interval_of_check badTest_512 48 8 (by decide +kernel)

theorem badTest_512_block_7 : Interval badTest_512 56 64 :=
  interval_of_check badTest_512 56 8 (by decide +kernel)

theorem badTest_512_block_8 : Interval badTest_512 64 72 :=
  interval_of_check badTest_512 64 8 (by decide +kernel)

theorem badTest_512_block_9 : Interval badTest_512 72 74 :=
  interval_of_check badTest_512 72 2 (by decide +kernel)

theorem badTest_512_complete : Interval badTest_512 0 74 :=
  (interval_append badTest_512 0 40 74
  (interval_append badTest_512 0 16 40
  (interval_append badTest_512 0 8 16
  badTest_512_block_0
  badTest_512_block_1)
  (interval_append badTest_512 16 24 40
  badTest_512_block_2
  (interval_append badTest_512 24 32 40
  badTest_512_block_3
  badTest_512_block_4)))
  (interval_append badTest_512 40 56 74
  (interval_append badTest_512 40 48 56
  badTest_512_block_5
  badTest_512_block_6)
  (interval_append badTest_512 56 64 74
  badTest_512_block_7
  (interval_append badTest_512 64 72 74
  badTest_512_block_8
  badTest_512_block_9))))
theorem badTestInterval512 : Interval badTest 512 586 := by
  intro i hlo hhi
  have h := badTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [badTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure005
