module
prelude
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_5120 (i : Nat) := wellFormedTest (i+5120)
theorem wellFormedTest_5120_block_0 : Interval wellFormedTest_5120 0 16 :=
  interval_of_check wellFormedTest_5120 0 16 (by decide +kernel)

theorem wellFormedTest_5120_block_1 : Interval wellFormedTest_5120 16 32 :=
  interval_of_check wellFormedTest_5120 16 16 (by decide +kernel)

theorem wellFormedTest_5120_block_2 : Interval wellFormedTest_5120 32 48 :=
  interval_of_check wellFormedTest_5120 32 16 (by decide +kernel)

theorem wellFormedTest_5120_block_3 : Interval wellFormedTest_5120 48 64 :=
  interval_of_check wellFormedTest_5120 48 16 (by decide +kernel)

theorem wellFormedTest_5120_block_4 : Interval wellFormedTest_5120 64 80 :=
  interval_of_check wellFormedTest_5120 64 16 (by decide +kernel)

theorem wellFormedTest_5120_block_5 : Interval wellFormedTest_5120 80 96 :=
  interval_of_check wellFormedTest_5120 80 16 (by decide +kernel)

theorem wellFormedTest_5120_block_6 : Interval wellFormedTest_5120 96 112 :=
  interval_of_check wellFormedTest_5120 96 16 (by decide +kernel)

theorem wellFormedTest_5120_block_7 : Interval wellFormedTest_5120 112 118 :=
  interval_of_check wellFormedTest_5120 112 6 (by decide +kernel)

theorem wellFormedTest_5120_complete : Interval wellFormedTest_5120 0 118 :=
  (interval_append wellFormedTest_5120 0 64 118
  (interval_append wellFormedTest_5120 0 32 64
  (interval_append wellFormedTest_5120 0 16 32
  wellFormedTest_5120_block_0
  wellFormedTest_5120_block_1)
  (interval_append wellFormedTest_5120 32 48 64
  wellFormedTest_5120_block_2
  wellFormedTest_5120_block_3))
  (interval_append wellFormedTest_5120 64 96 118
  (interval_append wellFormedTest_5120 64 80 96
  wellFormedTest_5120_block_4
  wellFormedTest_5120_block_5)
  (interval_append wellFormedTest_5120 96 112 118
  wellFormedTest_5120_block_6
  wellFormedTest_5120_block_7)))
theorem wellFormedTestInterval5120 : Interval wellFormedTest 5120 5238 := by
  intro i hlo hhi
  have h := wellFormedTest_5120_complete (i-5120) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_5120, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase03
