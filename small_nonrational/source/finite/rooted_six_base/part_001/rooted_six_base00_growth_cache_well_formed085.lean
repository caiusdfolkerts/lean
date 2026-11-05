module
prelude
public import RootedSixBase00GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_21760 (i : Nat) := wellFormedTest (i+21760)
theorem wellFormedTest_21760_block_0 : Interval wellFormedTest_21760 0 16 :=
  interval_of_check wellFormedTest_21760 0 16 (by decide +kernel)

theorem wellFormedTest_21760_block_1 : Interval wellFormedTest_21760 16 32 :=
  interval_of_check wellFormedTest_21760 16 16 (by decide +kernel)

theorem wellFormedTest_21760_block_2 : Interval wellFormedTest_21760 32 48 :=
  interval_of_check wellFormedTest_21760 32 16 (by decide +kernel)

theorem wellFormedTest_21760_block_3 : Interval wellFormedTest_21760 48 64 :=
  interval_of_check wellFormedTest_21760 48 16 (by decide +kernel)

theorem wellFormedTest_21760_block_4 : Interval wellFormedTest_21760 64 80 :=
  interval_of_check wellFormedTest_21760 64 16 (by decide +kernel)

theorem wellFormedTest_21760_block_5 : Interval wellFormedTest_21760 80 96 :=
  interval_of_check wellFormedTest_21760 80 16 (by decide +kernel)

theorem wellFormedTest_21760_block_6 : Interval wellFormedTest_21760 96 112 :=
  interval_of_check wellFormedTest_21760 96 16 (by decide +kernel)

theorem wellFormedTest_21760_block_7 : Interval wellFormedTest_21760 112 128 :=
  interval_of_check wellFormedTest_21760 112 16 (by decide +kernel)

theorem wellFormedTest_21760_block_8 : Interval wellFormedTest_21760 128 144 :=
  interval_of_check wellFormedTest_21760 128 16 (by decide +kernel)

theorem wellFormedTest_21760_block_9 : Interval wellFormedTest_21760 144 160 :=
  interval_of_check wellFormedTest_21760 144 16 (by decide +kernel)

theorem wellFormedTest_21760_block_10 : Interval wellFormedTest_21760 160 176 :=
  interval_of_check wellFormedTest_21760 160 16 (by decide +kernel)

theorem wellFormedTest_21760_block_11 : Interval wellFormedTest_21760 176 192 :=
  interval_of_check wellFormedTest_21760 176 16 (by decide +kernel)

theorem wellFormedTest_21760_block_12 : Interval wellFormedTest_21760 192 208 :=
  interval_of_check wellFormedTest_21760 192 16 (by decide +kernel)

theorem wellFormedTest_21760_block_13 : Interval wellFormedTest_21760 208 216 :=
  interval_of_check wellFormedTest_21760 208 8 (by decide +kernel)

theorem wellFormedTest_21760_complete : Interval wellFormedTest_21760 0 216 :=
  (interval_append wellFormedTest_21760 0 112 216
  (interval_append wellFormedTest_21760 0 48 112
  (interval_append wellFormedTest_21760 0 16 48
  wellFormedTest_21760_block_0
  (interval_append wellFormedTest_21760 16 32 48
  wellFormedTest_21760_block_1
  wellFormedTest_21760_block_2))
  (interval_append wellFormedTest_21760 48 80 112
  (interval_append wellFormedTest_21760 48 64 80
  wellFormedTest_21760_block_3
  wellFormedTest_21760_block_4)
  (interval_append wellFormedTest_21760 80 96 112
  wellFormedTest_21760_block_5
  wellFormedTest_21760_block_6)))
  (interval_append wellFormedTest_21760 112 160 216
  (interval_append wellFormedTest_21760 112 128 160
  wellFormedTest_21760_block_7
  (interval_append wellFormedTest_21760 128 144 160
  wellFormedTest_21760_block_8
  wellFormedTest_21760_block_9))
  (interval_append wellFormedTest_21760 160 192 216
  (interval_append wellFormedTest_21760 160 176 192
  wellFormedTest_21760_block_10
  wellFormedTest_21760_block_11)
  (interval_append wellFormedTest_21760 192 208 216
  wellFormedTest_21760_block_12
  wellFormedTest_21760_block_13))))
theorem wellFormedTestInterval21760 : Interval wellFormedTest 21760 21976 := by
  intro i hlo hhi
  have h := wellFormedTest_21760_complete (i-21760) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_21760, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00
