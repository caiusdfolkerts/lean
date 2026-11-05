module
prelude
public import RootedSixExtra06GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_1024 (i : Nat) := wellFormedTest (i+1024)
theorem wellFormedTest_1024_block_0 : Interval wellFormedTest_1024 0 16 :=
  interval_of_check wellFormedTest_1024 0 16 (by decide +kernel)

theorem wellFormedTest_1024_block_1 : Interval wellFormedTest_1024 16 32 :=
  interval_of_check wellFormedTest_1024 16 16 (by decide +kernel)

theorem wellFormedTest_1024_block_2 : Interval wellFormedTest_1024 32 48 :=
  interval_of_check wellFormedTest_1024 32 16 (by decide +kernel)

theorem wellFormedTest_1024_block_3 : Interval wellFormedTest_1024 48 64 :=
  interval_of_check wellFormedTest_1024 48 16 (by decide +kernel)

theorem wellFormedTest_1024_block_4 : Interval wellFormedTest_1024 64 80 :=
  interval_of_check wellFormedTest_1024 64 16 (by decide +kernel)

theorem wellFormedTest_1024_block_5 : Interval wellFormedTest_1024 80 96 :=
  interval_of_check wellFormedTest_1024 80 16 (by decide +kernel)

theorem wellFormedTest_1024_block_6 : Interval wellFormedTest_1024 96 112 :=
  interval_of_check wellFormedTest_1024 96 16 (by decide +kernel)

theorem wellFormedTest_1024_block_7 : Interval wellFormedTest_1024 112 128 :=
  interval_of_check wellFormedTest_1024 112 16 (by decide +kernel)

theorem wellFormedTest_1024_block_8 : Interval wellFormedTest_1024 128 144 :=
  interval_of_check wellFormedTest_1024 128 16 (by decide +kernel)

theorem wellFormedTest_1024_block_9 : Interval wellFormedTest_1024 144 160 :=
  interval_of_check wellFormedTest_1024 144 16 (by decide +kernel)

theorem wellFormedTest_1024_block_10 : Interval wellFormedTest_1024 160 176 :=
  interval_of_check wellFormedTest_1024 160 16 (by decide +kernel)

theorem wellFormedTest_1024_block_11 : Interval wellFormedTest_1024 176 192 :=
  interval_of_check wellFormedTest_1024 176 16 (by decide +kernel)

theorem wellFormedTest_1024_block_12 : Interval wellFormedTest_1024 192 208 :=
  interval_of_check wellFormedTest_1024 192 16 (by decide +kernel)

theorem wellFormedTest_1024_block_13 : Interval wellFormedTest_1024 208 224 :=
  interval_of_check wellFormedTest_1024 208 16 (by decide +kernel)

theorem wellFormedTest_1024_block_14 : Interval wellFormedTest_1024 224 240 :=
  interval_of_check wellFormedTest_1024 224 16 (by decide +kernel)

theorem wellFormedTest_1024_block_15 : Interval wellFormedTest_1024 240 256 :=
  interval_of_check wellFormedTest_1024 240 16 (by decide +kernel)

theorem wellFormedTest_1024_complete : Interval wellFormedTest_1024 0 256 :=
  (interval_append wellFormedTest_1024 0 128 256
  (interval_append wellFormedTest_1024 0 64 128
  (interval_append wellFormedTest_1024 0 32 64
  (interval_append wellFormedTest_1024 0 16 32
  wellFormedTest_1024_block_0
  wellFormedTest_1024_block_1)
  (interval_append wellFormedTest_1024 32 48 64
  wellFormedTest_1024_block_2
  wellFormedTest_1024_block_3))
  (interval_append wellFormedTest_1024 64 96 128
  (interval_append wellFormedTest_1024 64 80 96
  wellFormedTest_1024_block_4
  wellFormedTest_1024_block_5)
  (interval_append wellFormedTest_1024 96 112 128
  wellFormedTest_1024_block_6
  wellFormedTest_1024_block_7)))
  (interval_append wellFormedTest_1024 128 192 256
  (interval_append wellFormedTest_1024 128 160 192
  (interval_append wellFormedTest_1024 128 144 160
  wellFormedTest_1024_block_8
  wellFormedTest_1024_block_9)
  (interval_append wellFormedTest_1024 160 176 192
  wellFormedTest_1024_block_10
  wellFormedTest_1024_block_11))
  (interval_append wellFormedTest_1024 192 224 256
  (interval_append wellFormedTest_1024 192 208 224
  wellFormedTest_1024_block_12
  wellFormedTest_1024_block_13)
  (interval_append wellFormedTest_1024 224 240 256
  wellFormedTest_1024_block_14
  wellFormedTest_1024_block_15))))
theorem wellFormedTestInterval1024 : Interval wellFormedTest 1024 1280 := by
  intro i hlo hhi
  have h := wellFormedTest_1024_complete (i-1024) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_1024, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
