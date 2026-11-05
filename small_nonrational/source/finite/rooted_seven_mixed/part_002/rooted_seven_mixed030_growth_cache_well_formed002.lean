module
prelude
public import RootedSevenMixed030GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed030
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_512 (i : Nat) := wellFormedTest (i+512)
theorem wellFormedTest_512_block_0 : Interval wellFormedTest_512 0 16 :=
  interval_of_check wellFormedTest_512 0 16 (by decide +kernel)

theorem wellFormedTest_512_block_1 : Interval wellFormedTest_512 16 32 :=
  interval_of_check wellFormedTest_512 16 16 (by decide +kernel)

theorem wellFormedTest_512_block_2 : Interval wellFormedTest_512 32 48 :=
  interval_of_check wellFormedTest_512 32 16 (by decide +kernel)

theorem wellFormedTest_512_block_3 : Interval wellFormedTest_512 48 64 :=
  interval_of_check wellFormedTest_512 48 16 (by decide +kernel)

theorem wellFormedTest_512_block_4 : Interval wellFormedTest_512 64 80 :=
  interval_of_check wellFormedTest_512 64 16 (by decide +kernel)

theorem wellFormedTest_512_block_5 : Interval wellFormedTest_512 80 96 :=
  interval_of_check wellFormedTest_512 80 16 (by decide +kernel)

theorem wellFormedTest_512_block_6 : Interval wellFormedTest_512 96 112 :=
  interval_of_check wellFormedTest_512 96 16 (by decide +kernel)

theorem wellFormedTest_512_block_7 : Interval wellFormedTest_512 112 128 :=
  interval_of_check wellFormedTest_512 112 16 (by decide +kernel)

theorem wellFormedTest_512_block_8 : Interval wellFormedTest_512 128 143 :=
  interval_of_check wellFormedTest_512 128 15 (by decide +kernel)

theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 143 :=
  (interval_append wellFormedTest_512 0 64 143
  (interval_append wellFormedTest_512 0 32 64
  (interval_append wellFormedTest_512 0 16 32
  wellFormedTest_512_block_0
  wellFormedTest_512_block_1)
  (interval_append wellFormedTest_512 32 48 64
  wellFormedTest_512_block_2
  wellFormedTest_512_block_3))
  (interval_append wellFormedTest_512 64 96 143
  (interval_append wellFormedTest_512 64 80 96
  wellFormedTest_512_block_4
  wellFormedTest_512_block_5)
  (interval_append wellFormedTest_512 96 112 143
  wellFormedTest_512_block_6
  (interval_append wellFormedTest_512 112 128 143
  wellFormedTest_512_block_7
  wellFormedTest_512_block_8))))
theorem wellFormedTestInterval512 : Interval wellFormedTest 512 655 := by
  intro i hlo hhi
  have h := wellFormedTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed030
