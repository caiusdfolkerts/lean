module
prelude
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_2816 (i : Nat) := wellFormedTest (i+2816)
theorem wellFormedTest_2816_block_0 : Interval wellFormedTest_2816 0 16 :=
  interval_of_check wellFormedTest_2816 0 16 (by decide +kernel)

theorem wellFormedTest_2816_block_1 : Interval wellFormedTest_2816 16 32 :=
  interval_of_check wellFormedTest_2816 16 16 (by decide +kernel)

theorem wellFormedTest_2816_block_2 : Interval wellFormedTest_2816 32 48 :=
  interval_of_check wellFormedTest_2816 32 16 (by decide +kernel)

theorem wellFormedTest_2816_block_3 : Interval wellFormedTest_2816 48 64 :=
  interval_of_check wellFormedTest_2816 48 16 (by decide +kernel)

theorem wellFormedTest_2816_block_4 : Interval wellFormedTest_2816 64 80 :=
  interval_of_check wellFormedTest_2816 64 16 (by decide +kernel)

theorem wellFormedTest_2816_block_5 : Interval wellFormedTest_2816 80 96 :=
  interval_of_check wellFormedTest_2816 80 16 (by decide +kernel)

theorem wellFormedTest_2816_block_6 : Interval wellFormedTest_2816 96 112 :=
  interval_of_check wellFormedTest_2816 96 16 (by decide +kernel)

theorem wellFormedTest_2816_block_7 : Interval wellFormedTest_2816 112 128 :=
  interval_of_check wellFormedTest_2816 112 16 (by decide +kernel)

theorem wellFormedTest_2816_block_8 : Interval wellFormedTest_2816 128 144 :=
  interval_of_check wellFormedTest_2816 128 16 (by decide +kernel)

theorem wellFormedTest_2816_block_9 : Interval wellFormedTest_2816 144 160 :=
  interval_of_check wellFormedTest_2816 144 16 (by decide +kernel)

theorem wellFormedTest_2816_block_10 : Interval wellFormedTest_2816 160 176 :=
  interval_of_check wellFormedTest_2816 160 16 (by decide +kernel)

theorem wellFormedTest_2816_block_11 : Interval wellFormedTest_2816 176 192 :=
  interval_of_check wellFormedTest_2816 176 16 (by decide +kernel)

theorem wellFormedTest_2816_block_12 : Interval wellFormedTest_2816 192 208 :=
  interval_of_check wellFormedTest_2816 192 16 (by decide +kernel)

theorem wellFormedTest_2816_block_13 : Interval wellFormedTest_2816 208 224 :=
  interval_of_check wellFormedTest_2816 208 16 (by decide +kernel)

theorem wellFormedTest_2816_block_14 : Interval wellFormedTest_2816 224 240 :=
  interval_of_check wellFormedTest_2816 224 16 (by decide +kernel)

theorem wellFormedTest_2816_block_15 : Interval wellFormedTest_2816 240 256 :=
  interval_of_check wellFormedTest_2816 240 16 (by decide +kernel)

theorem wellFormedTest_2816_complete : Interval wellFormedTest_2816 0 256 :=
  (interval_append wellFormedTest_2816 0 128 256
  (interval_append wellFormedTest_2816 0 64 128
  (interval_append wellFormedTest_2816 0 32 64
  (interval_append wellFormedTest_2816 0 16 32
  wellFormedTest_2816_block_0
  wellFormedTest_2816_block_1)
  (interval_append wellFormedTest_2816 32 48 64
  wellFormedTest_2816_block_2
  wellFormedTest_2816_block_3))
  (interval_append wellFormedTest_2816 64 96 128
  (interval_append wellFormedTest_2816 64 80 96
  wellFormedTest_2816_block_4
  wellFormedTest_2816_block_5)
  (interval_append wellFormedTest_2816 96 112 128
  wellFormedTest_2816_block_6
  wellFormedTest_2816_block_7)))
  (interval_append wellFormedTest_2816 128 192 256
  (interval_append wellFormedTest_2816 128 160 192
  (interval_append wellFormedTest_2816 128 144 160
  wellFormedTest_2816_block_8
  wellFormedTest_2816_block_9)
  (interval_append wellFormedTest_2816 160 176 192
  wellFormedTest_2816_block_10
  wellFormedTest_2816_block_11))
  (interval_append wellFormedTest_2816 192 224 256
  (interval_append wellFormedTest_2816 192 208 224
  wellFormedTest_2816_block_12
  wellFormedTest_2816_block_13)
  (interval_append wellFormedTest_2816 224 240 256
  wellFormedTest_2816_block_14
  wellFormedTest_2816_block_15))))
theorem wellFormedTestInterval2816 : Interval wellFormedTest 2816 3072 := by
  intro i hlo hhi
  have h := wellFormedTest_2816_complete (i-2816) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_2816, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase03
