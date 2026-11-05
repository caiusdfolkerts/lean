module
prelude
public import RootedSixBase01GrowthCacheData

/- RootedSixBase01GrowthCacheWellFormed008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_2048 (i : Nat) := wellFormedTest (i+2048)
theorem wellFormedTest_2048_block_0 : Interval wellFormedTest_2048 0 16 :=
  interval_of_check wellFormedTest_2048 0 16 (by decide +kernel)

theorem wellFormedTest_2048_block_1 : Interval wellFormedTest_2048 16 32 :=
  interval_of_check wellFormedTest_2048 16 16 (by decide +kernel)

theorem wellFormedTest_2048_block_2 : Interval wellFormedTest_2048 32 48 :=
  interval_of_check wellFormedTest_2048 32 16 (by decide +kernel)

theorem wellFormedTest_2048_block_3 : Interval wellFormedTest_2048 48 64 :=
  interval_of_check wellFormedTest_2048 48 16 (by decide +kernel)

theorem wellFormedTest_2048_block_4 : Interval wellFormedTest_2048 64 80 :=
  interval_of_check wellFormedTest_2048 64 16 (by decide +kernel)

theorem wellFormedTest_2048_block_5 : Interval wellFormedTest_2048 80 96 :=
  interval_of_check wellFormedTest_2048 80 16 (by decide +kernel)

theorem wellFormedTest_2048_block_6 : Interval wellFormedTest_2048 96 112 :=
  interval_of_check wellFormedTest_2048 96 16 (by decide +kernel)

theorem wellFormedTest_2048_block_7 : Interval wellFormedTest_2048 112 128 :=
  interval_of_check wellFormedTest_2048 112 16 (by decide +kernel)

theorem wellFormedTest_2048_block_8 : Interval wellFormedTest_2048 128 144 :=
  interval_of_check wellFormedTest_2048 128 16 (by decide +kernel)

theorem wellFormedTest_2048_block_9 : Interval wellFormedTest_2048 144 160 :=
  interval_of_check wellFormedTest_2048 144 16 (by decide +kernel)

theorem wellFormedTest_2048_block_10 : Interval wellFormedTest_2048 160 176 :=
  interval_of_check wellFormedTest_2048 160 16 (by decide +kernel)

theorem wellFormedTest_2048_block_11 : Interval wellFormedTest_2048 176 192 :=
  interval_of_check wellFormedTest_2048 176 16 (by decide +kernel)

theorem wellFormedTest_2048_block_12 : Interval wellFormedTest_2048 192 208 :=
  interval_of_check wellFormedTest_2048 192 16 (by decide +kernel)

theorem wellFormedTest_2048_block_13 : Interval wellFormedTest_2048 208 224 :=
  interval_of_check wellFormedTest_2048 208 16 (by decide +kernel)

theorem wellFormedTest_2048_block_14 : Interval wellFormedTest_2048 224 240 :=
  interval_of_check wellFormedTest_2048 224 16 (by decide +kernel)

theorem wellFormedTest_2048_block_15 : Interval wellFormedTest_2048 240 256 :=
  interval_of_check wellFormedTest_2048 240 16 (by decide +kernel)

theorem wellFormedTest_2048_complete : Interval wellFormedTest_2048 0 256 :=
  (interval_append wellFormedTest_2048 0 128 256
  (interval_append wellFormedTest_2048 0 64 128
  (interval_append wellFormedTest_2048 0 32 64
  (interval_append wellFormedTest_2048 0 16 32
  wellFormedTest_2048_block_0
  wellFormedTest_2048_block_1)
  (interval_append wellFormedTest_2048 32 48 64
  wellFormedTest_2048_block_2
  wellFormedTest_2048_block_3))
  (interval_append wellFormedTest_2048 64 96 128
  (interval_append wellFormedTest_2048 64 80 96
  wellFormedTest_2048_block_4
  wellFormedTest_2048_block_5)
  (interval_append wellFormedTest_2048 96 112 128
  wellFormedTest_2048_block_6
  wellFormedTest_2048_block_7)))
  (interval_append wellFormedTest_2048 128 192 256
  (interval_append wellFormedTest_2048 128 160 192
  (interval_append wellFormedTest_2048 128 144 160
  wellFormedTest_2048_block_8
  wellFormedTest_2048_block_9)
  (interval_append wellFormedTest_2048 160 176 192
  wellFormedTest_2048_block_10
  wellFormedTest_2048_block_11))
  (interval_append wellFormedTest_2048 192 224 256
  (interval_append wellFormedTest_2048 192 208 224
  wellFormedTest_2048_block_12
  wellFormedTest_2048_block_13)
  (interval_append wellFormedTest_2048 224 240 256
  wellFormedTest_2048_block_14
  wellFormedTest_2048_block_15))))
theorem wellFormedTestInterval2048 : Interval wellFormedTest 2048 2304 := by
  intro i hlo hhi
  have h := wellFormedTest_2048_complete (i-2048) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_2048, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_2304 (i : Nat) := wellFormedTest (i+2304)
theorem wellFormedTest_2304_block_0 : Interval wellFormedTest_2304 0 16 :=
  interval_of_check wellFormedTest_2304 0 16 (by decide +kernel)

theorem wellFormedTest_2304_block_1 : Interval wellFormedTest_2304 16 32 :=
  interval_of_check wellFormedTest_2304 16 16 (by decide +kernel)

theorem wellFormedTest_2304_block_2 : Interval wellFormedTest_2304 32 48 :=
  interval_of_check wellFormedTest_2304 32 16 (by decide +kernel)

theorem wellFormedTest_2304_block_3 : Interval wellFormedTest_2304 48 64 :=
  interval_of_check wellFormedTest_2304 48 16 (by decide +kernel)

theorem wellFormedTest_2304_block_4 : Interval wellFormedTest_2304 64 80 :=
  interval_of_check wellFormedTest_2304 64 16 (by decide +kernel)

theorem wellFormedTest_2304_block_5 : Interval wellFormedTest_2304 80 96 :=
  interval_of_check wellFormedTest_2304 80 16 (by decide +kernel)

theorem wellFormedTest_2304_block_6 : Interval wellFormedTest_2304 96 112 :=
  interval_of_check wellFormedTest_2304 96 16 (by decide +kernel)

theorem wellFormedTest_2304_block_7 : Interval wellFormedTest_2304 112 128 :=
  interval_of_check wellFormedTest_2304 112 16 (by decide +kernel)

theorem wellFormedTest_2304_block_8 : Interval wellFormedTest_2304 128 144 :=
  interval_of_check wellFormedTest_2304 128 16 (by decide +kernel)

theorem wellFormedTest_2304_block_9 : Interval wellFormedTest_2304 144 160 :=
  interval_of_check wellFormedTest_2304 144 16 (by decide +kernel)

theorem wellFormedTest_2304_block_10 : Interval wellFormedTest_2304 160 176 :=
  interval_of_check wellFormedTest_2304 160 16 (by decide +kernel)

theorem wellFormedTest_2304_block_11 : Interval wellFormedTest_2304 176 192 :=
  interval_of_check wellFormedTest_2304 176 16 (by decide +kernel)

theorem wellFormedTest_2304_block_12 : Interval wellFormedTest_2304 192 208 :=
  interval_of_check wellFormedTest_2304 192 16 (by decide +kernel)

theorem wellFormedTest_2304_block_13 : Interval wellFormedTest_2304 208 224 :=
  interval_of_check wellFormedTest_2304 208 16 (by decide +kernel)

theorem wellFormedTest_2304_block_14 : Interval wellFormedTest_2304 224 240 :=
  interval_of_check wellFormedTest_2304 224 16 (by decide +kernel)

theorem wellFormedTest_2304_block_15 : Interval wellFormedTest_2304 240 256 :=
  interval_of_check wellFormedTest_2304 240 16 (by decide +kernel)

theorem wellFormedTest_2304_complete : Interval wellFormedTest_2304 0 256 :=
  (interval_append wellFormedTest_2304 0 128 256
  (interval_append wellFormedTest_2304 0 64 128
  (interval_append wellFormedTest_2304 0 32 64
  (interval_append wellFormedTest_2304 0 16 32
  wellFormedTest_2304_block_0
  wellFormedTest_2304_block_1)
  (interval_append wellFormedTest_2304 32 48 64
  wellFormedTest_2304_block_2
  wellFormedTest_2304_block_3))
  (interval_append wellFormedTest_2304 64 96 128
  (interval_append wellFormedTest_2304 64 80 96
  wellFormedTest_2304_block_4
  wellFormedTest_2304_block_5)
  (interval_append wellFormedTest_2304 96 112 128
  wellFormedTest_2304_block_6
  wellFormedTest_2304_block_7)))
  (interval_append wellFormedTest_2304 128 192 256
  (interval_append wellFormedTest_2304 128 160 192
  (interval_append wellFormedTest_2304 128 144 160
  wellFormedTest_2304_block_8
  wellFormedTest_2304_block_9)
  (interval_append wellFormedTest_2304 160 176 192
  wellFormedTest_2304_block_10
  wellFormedTest_2304_block_11))
  (interval_append wellFormedTest_2304 192 224 256
  (interval_append wellFormedTest_2304 192 208 224
  wellFormedTest_2304_block_12
  wellFormedTest_2304_block_13)
  (interval_append wellFormedTest_2304 224 240 256
  wellFormedTest_2304_block_14
  wellFormedTest_2304_block_15))))
theorem wellFormedTestInterval2304 : Interval wellFormedTest 2304 2560 := by
  intro i hlo hhi
  have h := wellFormedTest_2304_complete (i-2304) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_2304, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed010 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_2560 (i : Nat) := wellFormedTest (i+2560)
theorem wellFormedTest_2560_block_0 : Interval wellFormedTest_2560 0 16 :=
  interval_of_check wellFormedTest_2560 0 16 (by decide +kernel)

theorem wellFormedTest_2560_block_1 : Interval wellFormedTest_2560 16 32 :=
  interval_of_check wellFormedTest_2560 16 16 (by decide +kernel)

theorem wellFormedTest_2560_block_2 : Interval wellFormedTest_2560 32 48 :=
  interval_of_check wellFormedTest_2560 32 16 (by decide +kernel)

theorem wellFormedTest_2560_block_3 : Interval wellFormedTest_2560 48 64 :=
  interval_of_check wellFormedTest_2560 48 16 (by decide +kernel)

theorem wellFormedTest_2560_block_4 : Interval wellFormedTest_2560 64 80 :=
  interval_of_check wellFormedTest_2560 64 16 (by decide +kernel)

theorem wellFormedTest_2560_block_5 : Interval wellFormedTest_2560 80 96 :=
  interval_of_check wellFormedTest_2560 80 16 (by decide +kernel)

theorem wellFormedTest_2560_block_6 : Interval wellFormedTest_2560 96 112 :=
  interval_of_check wellFormedTest_2560 96 16 (by decide +kernel)

theorem wellFormedTest_2560_block_7 : Interval wellFormedTest_2560 112 128 :=
  interval_of_check wellFormedTest_2560 112 16 (by decide +kernel)

theorem wellFormedTest_2560_block_8 : Interval wellFormedTest_2560 128 144 :=
  interval_of_check wellFormedTest_2560 128 16 (by decide +kernel)

theorem wellFormedTest_2560_block_9 : Interval wellFormedTest_2560 144 160 :=
  interval_of_check wellFormedTest_2560 144 16 (by decide +kernel)

theorem wellFormedTest_2560_block_10 : Interval wellFormedTest_2560 160 176 :=
  interval_of_check wellFormedTest_2560 160 16 (by decide +kernel)

theorem wellFormedTest_2560_block_11 : Interval wellFormedTest_2560 176 192 :=
  interval_of_check wellFormedTest_2560 176 16 (by decide +kernel)

theorem wellFormedTest_2560_block_12 : Interval wellFormedTest_2560 192 208 :=
  interval_of_check wellFormedTest_2560 192 16 (by decide +kernel)

theorem wellFormedTest_2560_block_13 : Interval wellFormedTest_2560 208 224 :=
  interval_of_check wellFormedTest_2560 208 16 (by decide +kernel)

theorem wellFormedTest_2560_block_14 : Interval wellFormedTest_2560 224 240 :=
  interval_of_check wellFormedTest_2560 224 16 (by decide +kernel)

theorem wellFormedTest_2560_block_15 : Interval wellFormedTest_2560 240 256 :=
  interval_of_check wellFormedTest_2560 240 16 (by decide +kernel)

theorem wellFormedTest_2560_complete : Interval wellFormedTest_2560 0 256 :=
  (interval_append wellFormedTest_2560 0 128 256
  (interval_append wellFormedTest_2560 0 64 128
  (interval_append wellFormedTest_2560 0 32 64
  (interval_append wellFormedTest_2560 0 16 32
  wellFormedTest_2560_block_0
  wellFormedTest_2560_block_1)
  (interval_append wellFormedTest_2560 32 48 64
  wellFormedTest_2560_block_2
  wellFormedTest_2560_block_3))
  (interval_append wellFormedTest_2560 64 96 128
  (interval_append wellFormedTest_2560 64 80 96
  wellFormedTest_2560_block_4
  wellFormedTest_2560_block_5)
  (interval_append wellFormedTest_2560 96 112 128
  wellFormedTest_2560_block_6
  wellFormedTest_2560_block_7)))
  (interval_append wellFormedTest_2560 128 192 256
  (interval_append wellFormedTest_2560 128 160 192
  (interval_append wellFormedTest_2560 128 144 160
  wellFormedTest_2560_block_8
  wellFormedTest_2560_block_9)
  (interval_append wellFormedTest_2560 160 176 192
  wellFormedTest_2560_block_10
  wellFormedTest_2560_block_11))
  (interval_append wellFormedTest_2560 192 224 256
  (interval_append wellFormedTest_2560 192 208 224
  wellFormedTest_2560_block_12
  wellFormedTest_2560_block_13)
  (interval_append wellFormedTest_2560 224 240 256
  wellFormedTest_2560_block_14
  wellFormedTest_2560_block_15))))
theorem wellFormedTestInterval2560 : Interval wellFormedTest 2560 2816 := by
  intro i hlo hhi
  have h := wellFormedTest_2560_complete (i-2560) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_2560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed011 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed012 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_3072 (i : Nat) := wellFormedTest (i+3072)
theorem wellFormedTest_3072_block_0 : Interval wellFormedTest_3072 0 16 :=
  interval_of_check wellFormedTest_3072 0 16 (by decide +kernel)

theorem wellFormedTest_3072_block_1 : Interval wellFormedTest_3072 16 32 :=
  interval_of_check wellFormedTest_3072 16 16 (by decide +kernel)

theorem wellFormedTest_3072_block_2 : Interval wellFormedTest_3072 32 48 :=
  interval_of_check wellFormedTest_3072 32 16 (by decide +kernel)

theorem wellFormedTest_3072_block_3 : Interval wellFormedTest_3072 48 64 :=
  interval_of_check wellFormedTest_3072 48 16 (by decide +kernel)

theorem wellFormedTest_3072_block_4 : Interval wellFormedTest_3072 64 80 :=
  interval_of_check wellFormedTest_3072 64 16 (by decide +kernel)

theorem wellFormedTest_3072_block_5 : Interval wellFormedTest_3072 80 96 :=
  interval_of_check wellFormedTest_3072 80 16 (by decide +kernel)

theorem wellFormedTest_3072_block_6 : Interval wellFormedTest_3072 96 112 :=
  interval_of_check wellFormedTest_3072 96 16 (by decide +kernel)

theorem wellFormedTest_3072_block_7 : Interval wellFormedTest_3072 112 128 :=
  interval_of_check wellFormedTest_3072 112 16 (by decide +kernel)

theorem wellFormedTest_3072_block_8 : Interval wellFormedTest_3072 128 144 :=
  interval_of_check wellFormedTest_3072 128 16 (by decide +kernel)

theorem wellFormedTest_3072_block_9 : Interval wellFormedTest_3072 144 160 :=
  interval_of_check wellFormedTest_3072 144 16 (by decide +kernel)

theorem wellFormedTest_3072_block_10 : Interval wellFormedTest_3072 160 176 :=
  interval_of_check wellFormedTest_3072 160 16 (by decide +kernel)

theorem wellFormedTest_3072_block_11 : Interval wellFormedTest_3072 176 192 :=
  interval_of_check wellFormedTest_3072 176 16 (by decide +kernel)

theorem wellFormedTest_3072_block_12 : Interval wellFormedTest_3072 192 208 :=
  interval_of_check wellFormedTest_3072 192 16 (by decide +kernel)

theorem wellFormedTest_3072_block_13 : Interval wellFormedTest_3072 208 224 :=
  interval_of_check wellFormedTest_3072 208 16 (by decide +kernel)

theorem wellFormedTest_3072_block_14 : Interval wellFormedTest_3072 224 240 :=
  interval_of_check wellFormedTest_3072 224 16 (by decide +kernel)

theorem wellFormedTest_3072_block_15 : Interval wellFormedTest_3072 240 256 :=
  interval_of_check wellFormedTest_3072 240 16 (by decide +kernel)

theorem wellFormedTest_3072_complete : Interval wellFormedTest_3072 0 256 :=
  (interval_append wellFormedTest_3072 0 128 256
  (interval_append wellFormedTest_3072 0 64 128
  (interval_append wellFormedTest_3072 0 32 64
  (interval_append wellFormedTest_3072 0 16 32
  wellFormedTest_3072_block_0
  wellFormedTest_3072_block_1)
  (interval_append wellFormedTest_3072 32 48 64
  wellFormedTest_3072_block_2
  wellFormedTest_3072_block_3))
  (interval_append wellFormedTest_3072 64 96 128
  (interval_append wellFormedTest_3072 64 80 96
  wellFormedTest_3072_block_4
  wellFormedTest_3072_block_5)
  (interval_append wellFormedTest_3072 96 112 128
  wellFormedTest_3072_block_6
  wellFormedTest_3072_block_7)))
  (interval_append wellFormedTest_3072 128 192 256
  (interval_append wellFormedTest_3072 128 160 192
  (interval_append wellFormedTest_3072 128 144 160
  wellFormedTest_3072_block_8
  wellFormedTest_3072_block_9)
  (interval_append wellFormedTest_3072 160 176 192
  wellFormedTest_3072_block_10
  wellFormedTest_3072_block_11))
  (interval_append wellFormedTest_3072 192 224 256
  (interval_append wellFormedTest_3072 192 208 224
  wellFormedTest_3072_block_12
  wellFormedTest_3072_block_13)
  (interval_append wellFormedTest_3072 224 240 256
  wellFormedTest_3072_block_14
  wellFormedTest_3072_block_15))))
theorem wellFormedTestInterval3072 : Interval wellFormedTest 3072 3328 := by
  intro i hlo hhi
  have h := wellFormedTest_3072_complete (i-3072) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_3072, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed013 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_3328 (i : Nat) := wellFormedTest (i+3328)
theorem wellFormedTest_3328_block_0 : Interval wellFormedTest_3328 0 16 :=
  interval_of_check wellFormedTest_3328 0 16 (by decide +kernel)

theorem wellFormedTest_3328_block_1 : Interval wellFormedTest_3328 16 32 :=
  interval_of_check wellFormedTest_3328 16 16 (by decide +kernel)

theorem wellFormedTest_3328_block_2 : Interval wellFormedTest_3328 32 48 :=
  interval_of_check wellFormedTest_3328 32 16 (by decide +kernel)

theorem wellFormedTest_3328_block_3 : Interval wellFormedTest_3328 48 64 :=
  interval_of_check wellFormedTest_3328 48 16 (by decide +kernel)

theorem wellFormedTest_3328_block_4 : Interval wellFormedTest_3328 64 80 :=
  interval_of_check wellFormedTest_3328 64 16 (by decide +kernel)

theorem wellFormedTest_3328_block_5 : Interval wellFormedTest_3328 80 96 :=
  interval_of_check wellFormedTest_3328 80 16 (by decide +kernel)

theorem wellFormedTest_3328_block_6 : Interval wellFormedTest_3328 96 112 :=
  interval_of_check wellFormedTest_3328 96 16 (by decide +kernel)

theorem wellFormedTest_3328_block_7 : Interval wellFormedTest_3328 112 128 :=
  interval_of_check wellFormedTest_3328 112 16 (by decide +kernel)

theorem wellFormedTest_3328_block_8 : Interval wellFormedTest_3328 128 144 :=
  interval_of_check wellFormedTest_3328 128 16 (by decide +kernel)

theorem wellFormedTest_3328_block_9 : Interval wellFormedTest_3328 144 160 :=
  interval_of_check wellFormedTest_3328 144 16 (by decide +kernel)

theorem wellFormedTest_3328_block_10 : Interval wellFormedTest_3328 160 176 :=
  interval_of_check wellFormedTest_3328 160 16 (by decide +kernel)

theorem wellFormedTest_3328_block_11 : Interval wellFormedTest_3328 176 192 :=
  interval_of_check wellFormedTest_3328 176 16 (by decide +kernel)

theorem wellFormedTest_3328_block_12 : Interval wellFormedTest_3328 192 208 :=
  interval_of_check wellFormedTest_3328 192 16 (by decide +kernel)

theorem wellFormedTest_3328_block_13 : Interval wellFormedTest_3328 208 224 :=
  interval_of_check wellFormedTest_3328 208 16 (by decide +kernel)

theorem wellFormedTest_3328_block_14 : Interval wellFormedTest_3328 224 240 :=
  interval_of_check wellFormedTest_3328 224 16 (by decide +kernel)

theorem wellFormedTest_3328_block_15 : Interval wellFormedTest_3328 240 256 :=
  interval_of_check wellFormedTest_3328 240 16 (by decide +kernel)

theorem wellFormedTest_3328_complete : Interval wellFormedTest_3328 0 256 :=
  (interval_append wellFormedTest_3328 0 128 256
  (interval_append wellFormedTest_3328 0 64 128
  (interval_append wellFormedTest_3328 0 32 64
  (interval_append wellFormedTest_3328 0 16 32
  wellFormedTest_3328_block_0
  wellFormedTest_3328_block_1)
  (interval_append wellFormedTest_3328 32 48 64
  wellFormedTest_3328_block_2
  wellFormedTest_3328_block_3))
  (interval_append wellFormedTest_3328 64 96 128
  (interval_append wellFormedTest_3328 64 80 96
  wellFormedTest_3328_block_4
  wellFormedTest_3328_block_5)
  (interval_append wellFormedTest_3328 96 112 128
  wellFormedTest_3328_block_6
  wellFormedTest_3328_block_7)))
  (interval_append wellFormedTest_3328 128 192 256
  (interval_append wellFormedTest_3328 128 160 192
  (interval_append wellFormedTest_3328 128 144 160
  wellFormedTest_3328_block_8
  wellFormedTest_3328_block_9)
  (interval_append wellFormedTest_3328 160 176 192
  wellFormedTest_3328_block_10
  wellFormedTest_3328_block_11))
  (interval_append wellFormedTest_3328 192 224 256
  (interval_append wellFormedTest_3328 192 208 224
  wellFormedTest_3328_block_12
  wellFormedTest_3328_block_13)
  (interval_append wellFormedTest_3328 224 240 256
  wellFormedTest_3328_block_14
  wellFormedTest_3328_block_15))))
theorem wellFormedTestInterval3328 : Interval wellFormedTest 3328 3584 := by
  intro i hlo hhi
  have h := wellFormedTest_3328_complete (i-3328) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_3328, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed014 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_3584 (i : Nat) := wellFormedTest (i+3584)
theorem wellFormedTest_3584_block_0 : Interval wellFormedTest_3584 0 16 :=
  interval_of_check wellFormedTest_3584 0 16 (by decide +kernel)

theorem wellFormedTest_3584_block_1 : Interval wellFormedTest_3584 16 32 :=
  interval_of_check wellFormedTest_3584 16 16 (by decide +kernel)

theorem wellFormedTest_3584_block_2 : Interval wellFormedTest_3584 32 48 :=
  interval_of_check wellFormedTest_3584 32 16 (by decide +kernel)

theorem wellFormedTest_3584_block_3 : Interval wellFormedTest_3584 48 64 :=
  interval_of_check wellFormedTest_3584 48 16 (by decide +kernel)

theorem wellFormedTest_3584_block_4 : Interval wellFormedTest_3584 64 80 :=
  interval_of_check wellFormedTest_3584 64 16 (by decide +kernel)

theorem wellFormedTest_3584_block_5 : Interval wellFormedTest_3584 80 96 :=
  interval_of_check wellFormedTest_3584 80 16 (by decide +kernel)

theorem wellFormedTest_3584_block_6 : Interval wellFormedTest_3584 96 112 :=
  interval_of_check wellFormedTest_3584 96 16 (by decide +kernel)

theorem wellFormedTest_3584_block_7 : Interval wellFormedTest_3584 112 128 :=
  interval_of_check wellFormedTest_3584 112 16 (by decide +kernel)

theorem wellFormedTest_3584_block_8 : Interval wellFormedTest_3584 128 144 :=
  interval_of_check wellFormedTest_3584 128 16 (by decide +kernel)

theorem wellFormedTest_3584_block_9 : Interval wellFormedTest_3584 144 160 :=
  interval_of_check wellFormedTest_3584 144 16 (by decide +kernel)

theorem wellFormedTest_3584_block_10 : Interval wellFormedTest_3584 160 176 :=
  interval_of_check wellFormedTest_3584 160 16 (by decide +kernel)

theorem wellFormedTest_3584_block_11 : Interval wellFormedTest_3584 176 192 :=
  interval_of_check wellFormedTest_3584 176 16 (by decide +kernel)

theorem wellFormedTest_3584_block_12 : Interval wellFormedTest_3584 192 208 :=
  interval_of_check wellFormedTest_3584 192 16 (by decide +kernel)

theorem wellFormedTest_3584_block_13 : Interval wellFormedTest_3584 208 224 :=
  interval_of_check wellFormedTest_3584 208 16 (by decide +kernel)

theorem wellFormedTest_3584_block_14 : Interval wellFormedTest_3584 224 240 :=
  interval_of_check wellFormedTest_3584 224 16 (by decide +kernel)

theorem wellFormedTest_3584_block_15 : Interval wellFormedTest_3584 240 256 :=
  interval_of_check wellFormedTest_3584 240 16 (by decide +kernel)

theorem wellFormedTest_3584_complete : Interval wellFormedTest_3584 0 256 :=
  (interval_append wellFormedTest_3584 0 128 256
  (interval_append wellFormedTest_3584 0 64 128
  (interval_append wellFormedTest_3584 0 32 64
  (interval_append wellFormedTest_3584 0 16 32
  wellFormedTest_3584_block_0
  wellFormedTest_3584_block_1)
  (interval_append wellFormedTest_3584 32 48 64
  wellFormedTest_3584_block_2
  wellFormedTest_3584_block_3))
  (interval_append wellFormedTest_3584 64 96 128
  (interval_append wellFormedTest_3584 64 80 96
  wellFormedTest_3584_block_4
  wellFormedTest_3584_block_5)
  (interval_append wellFormedTest_3584 96 112 128
  wellFormedTest_3584_block_6
  wellFormedTest_3584_block_7)))
  (interval_append wellFormedTest_3584 128 192 256
  (interval_append wellFormedTest_3584 128 160 192
  (interval_append wellFormedTest_3584 128 144 160
  wellFormedTest_3584_block_8
  wellFormedTest_3584_block_9)
  (interval_append wellFormedTest_3584 160 176 192
  wellFormedTest_3584_block_10
  wellFormedTest_3584_block_11))
  (interval_append wellFormedTest_3584 192 224 256
  (interval_append wellFormedTest_3584 192 208 224
  wellFormedTest_3584_block_12
  wellFormedTest_3584_block_13)
  (interval_append wellFormedTest_3584 224 240 256
  wellFormedTest_3584_block_14
  wellFormedTest_3584_block_15))))
theorem wellFormedTestInterval3584 : Interval wellFormedTest 3584 3840 := by
  intro i hlo hhi
  have h := wellFormedTest_3584_complete (i-3584) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_3584, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed015 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_3840 (i : Nat) := wellFormedTest (i+3840)
theorem wellFormedTest_3840_block_0 : Interval wellFormedTest_3840 0 16 :=
  interval_of_check wellFormedTest_3840 0 16 (by decide +kernel)

theorem wellFormedTest_3840_block_1 : Interval wellFormedTest_3840 16 32 :=
  interval_of_check wellFormedTest_3840 16 16 (by decide +kernel)

theorem wellFormedTest_3840_block_2 : Interval wellFormedTest_3840 32 48 :=
  interval_of_check wellFormedTest_3840 32 16 (by decide +kernel)

theorem wellFormedTest_3840_block_3 : Interval wellFormedTest_3840 48 64 :=
  interval_of_check wellFormedTest_3840 48 16 (by decide +kernel)

theorem wellFormedTest_3840_block_4 : Interval wellFormedTest_3840 64 80 :=
  interval_of_check wellFormedTest_3840 64 16 (by decide +kernel)

theorem wellFormedTest_3840_block_5 : Interval wellFormedTest_3840 80 96 :=
  interval_of_check wellFormedTest_3840 80 16 (by decide +kernel)

theorem wellFormedTest_3840_block_6 : Interval wellFormedTest_3840 96 112 :=
  interval_of_check wellFormedTest_3840 96 16 (by decide +kernel)

theorem wellFormedTest_3840_block_7 : Interval wellFormedTest_3840 112 128 :=
  interval_of_check wellFormedTest_3840 112 16 (by decide +kernel)

theorem wellFormedTest_3840_block_8 : Interval wellFormedTest_3840 128 144 :=
  interval_of_check wellFormedTest_3840 128 16 (by decide +kernel)

theorem wellFormedTest_3840_block_9 : Interval wellFormedTest_3840 144 160 :=
  interval_of_check wellFormedTest_3840 144 16 (by decide +kernel)

theorem wellFormedTest_3840_block_10 : Interval wellFormedTest_3840 160 176 :=
  interval_of_check wellFormedTest_3840 160 16 (by decide +kernel)

theorem wellFormedTest_3840_block_11 : Interval wellFormedTest_3840 176 192 :=
  interval_of_check wellFormedTest_3840 176 16 (by decide +kernel)

theorem wellFormedTest_3840_block_12 : Interval wellFormedTest_3840 192 208 :=
  interval_of_check wellFormedTest_3840 192 16 (by decide +kernel)

theorem wellFormedTest_3840_block_13 : Interval wellFormedTest_3840 208 224 :=
  interval_of_check wellFormedTest_3840 208 16 (by decide +kernel)

theorem wellFormedTest_3840_block_14 : Interval wellFormedTest_3840 224 240 :=
  interval_of_check wellFormedTest_3840 224 16 (by decide +kernel)

theorem wellFormedTest_3840_block_15 : Interval wellFormedTest_3840 240 256 :=
  interval_of_check wellFormedTest_3840 240 16 (by decide +kernel)

theorem wellFormedTest_3840_complete : Interval wellFormedTest_3840 0 256 :=
  (interval_append wellFormedTest_3840 0 128 256
  (interval_append wellFormedTest_3840 0 64 128
  (interval_append wellFormedTest_3840 0 32 64
  (interval_append wellFormedTest_3840 0 16 32
  wellFormedTest_3840_block_0
  wellFormedTest_3840_block_1)
  (interval_append wellFormedTest_3840 32 48 64
  wellFormedTest_3840_block_2
  wellFormedTest_3840_block_3))
  (interval_append wellFormedTest_3840 64 96 128
  (interval_append wellFormedTest_3840 64 80 96
  wellFormedTest_3840_block_4
  wellFormedTest_3840_block_5)
  (interval_append wellFormedTest_3840 96 112 128
  wellFormedTest_3840_block_6
  wellFormedTest_3840_block_7)))
  (interval_append wellFormedTest_3840 128 192 256
  (interval_append wellFormedTest_3840 128 160 192
  (interval_append wellFormedTest_3840 128 144 160
  wellFormedTest_3840_block_8
  wellFormedTest_3840_block_9)
  (interval_append wellFormedTest_3840 160 176 192
  wellFormedTest_3840_block_10
  wellFormedTest_3840_block_11))
  (interval_append wellFormedTest_3840 192 224 256
  (interval_append wellFormedTest_3840 192 208 224
  wellFormedTest_3840_block_12
  wellFormedTest_3840_block_13)
  (interval_append wellFormedTest_3840 224 240 256
  wellFormedTest_3840_block_14
  wellFormedTest_3840_block_15))))
theorem wellFormedTestInterval3840 : Interval wellFormedTest 3840 4096 := by
  intro i hlo hhi
  have h := wellFormedTest_3840_complete (i-3840) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_3840, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed016 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_4096 (i : Nat) := wellFormedTest (i+4096)
theorem wellFormedTest_4096_block_0 : Interval wellFormedTest_4096 0 16 :=
  interval_of_check wellFormedTest_4096 0 16 (by decide +kernel)

theorem wellFormedTest_4096_block_1 : Interval wellFormedTest_4096 16 32 :=
  interval_of_check wellFormedTest_4096 16 16 (by decide +kernel)

theorem wellFormedTest_4096_block_2 : Interval wellFormedTest_4096 32 48 :=
  interval_of_check wellFormedTest_4096 32 16 (by decide +kernel)

theorem wellFormedTest_4096_block_3 : Interval wellFormedTest_4096 48 64 :=
  interval_of_check wellFormedTest_4096 48 16 (by decide +kernel)

theorem wellFormedTest_4096_block_4 : Interval wellFormedTest_4096 64 80 :=
  interval_of_check wellFormedTest_4096 64 16 (by decide +kernel)

theorem wellFormedTest_4096_block_5 : Interval wellFormedTest_4096 80 96 :=
  interval_of_check wellFormedTest_4096 80 16 (by decide +kernel)

theorem wellFormedTest_4096_block_6 : Interval wellFormedTest_4096 96 112 :=
  interval_of_check wellFormedTest_4096 96 16 (by decide +kernel)

theorem wellFormedTest_4096_block_7 : Interval wellFormedTest_4096 112 128 :=
  interval_of_check wellFormedTest_4096 112 16 (by decide +kernel)

theorem wellFormedTest_4096_block_8 : Interval wellFormedTest_4096 128 144 :=
  interval_of_check wellFormedTest_4096 128 16 (by decide +kernel)

theorem wellFormedTest_4096_block_9 : Interval wellFormedTest_4096 144 160 :=
  interval_of_check wellFormedTest_4096 144 16 (by decide +kernel)

theorem wellFormedTest_4096_block_10 : Interval wellFormedTest_4096 160 176 :=
  interval_of_check wellFormedTest_4096 160 16 (by decide +kernel)

theorem wellFormedTest_4096_block_11 : Interval wellFormedTest_4096 176 192 :=
  interval_of_check wellFormedTest_4096 176 16 (by decide +kernel)

theorem wellFormedTest_4096_block_12 : Interval wellFormedTest_4096 192 208 :=
  interval_of_check wellFormedTest_4096 192 16 (by decide +kernel)

theorem wellFormedTest_4096_block_13 : Interval wellFormedTest_4096 208 224 :=
  interval_of_check wellFormedTest_4096 208 16 (by decide +kernel)

theorem wellFormedTest_4096_block_14 : Interval wellFormedTest_4096 224 240 :=
  interval_of_check wellFormedTest_4096 224 16 (by decide +kernel)

theorem wellFormedTest_4096_block_15 : Interval wellFormedTest_4096 240 256 :=
  interval_of_check wellFormedTest_4096 240 16 (by decide +kernel)

theorem wellFormedTest_4096_complete : Interval wellFormedTest_4096 0 256 :=
  (interval_append wellFormedTest_4096 0 128 256
  (interval_append wellFormedTest_4096 0 64 128
  (interval_append wellFormedTest_4096 0 32 64
  (interval_append wellFormedTest_4096 0 16 32
  wellFormedTest_4096_block_0
  wellFormedTest_4096_block_1)
  (interval_append wellFormedTest_4096 32 48 64
  wellFormedTest_4096_block_2
  wellFormedTest_4096_block_3))
  (interval_append wellFormedTest_4096 64 96 128
  (interval_append wellFormedTest_4096 64 80 96
  wellFormedTest_4096_block_4
  wellFormedTest_4096_block_5)
  (interval_append wellFormedTest_4096 96 112 128
  wellFormedTest_4096_block_6
  wellFormedTest_4096_block_7)))
  (interval_append wellFormedTest_4096 128 192 256
  (interval_append wellFormedTest_4096 128 160 192
  (interval_append wellFormedTest_4096 128 144 160
  wellFormedTest_4096_block_8
  wellFormedTest_4096_block_9)
  (interval_append wellFormedTest_4096 160 176 192
  wellFormedTest_4096_block_10
  wellFormedTest_4096_block_11))
  (interval_append wellFormedTest_4096 192 224 256
  (interval_append wellFormedTest_4096 192 208 224
  wellFormedTest_4096_block_12
  wellFormedTest_4096_block_13)
  (interval_append wellFormedTest_4096 224 240 256
  wellFormedTest_4096_block_14
  wellFormedTest_4096_block_15))))
theorem wellFormedTestInterval4096 : Interval wellFormedTest 4096 4352 := by
  intro i hlo hhi
  have h := wellFormedTest_4096_complete (i-4096) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_4096, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed017 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_4352 (i : Nat) := wellFormedTest (i+4352)
theorem wellFormedTest_4352_block_0 : Interval wellFormedTest_4352 0 16 :=
  interval_of_check wellFormedTest_4352 0 16 (by decide +kernel)

theorem wellFormedTest_4352_block_1 : Interval wellFormedTest_4352 16 32 :=
  interval_of_check wellFormedTest_4352 16 16 (by decide +kernel)

theorem wellFormedTest_4352_block_2 : Interval wellFormedTest_4352 32 48 :=
  interval_of_check wellFormedTest_4352 32 16 (by decide +kernel)

theorem wellFormedTest_4352_block_3 : Interval wellFormedTest_4352 48 64 :=
  interval_of_check wellFormedTest_4352 48 16 (by decide +kernel)

theorem wellFormedTest_4352_block_4 : Interval wellFormedTest_4352 64 80 :=
  interval_of_check wellFormedTest_4352 64 16 (by decide +kernel)

theorem wellFormedTest_4352_block_5 : Interval wellFormedTest_4352 80 96 :=
  interval_of_check wellFormedTest_4352 80 16 (by decide +kernel)

theorem wellFormedTest_4352_block_6 : Interval wellFormedTest_4352 96 112 :=
  interval_of_check wellFormedTest_4352 96 16 (by decide +kernel)

theorem wellFormedTest_4352_block_7 : Interval wellFormedTest_4352 112 128 :=
  interval_of_check wellFormedTest_4352 112 16 (by decide +kernel)

theorem wellFormedTest_4352_block_8 : Interval wellFormedTest_4352 128 144 :=
  interval_of_check wellFormedTest_4352 128 16 (by decide +kernel)

theorem wellFormedTest_4352_block_9 : Interval wellFormedTest_4352 144 160 :=
  interval_of_check wellFormedTest_4352 144 16 (by decide +kernel)

theorem wellFormedTest_4352_block_10 : Interval wellFormedTest_4352 160 176 :=
  interval_of_check wellFormedTest_4352 160 16 (by decide +kernel)

theorem wellFormedTest_4352_block_11 : Interval wellFormedTest_4352 176 192 :=
  interval_of_check wellFormedTest_4352 176 16 (by decide +kernel)

theorem wellFormedTest_4352_block_12 : Interval wellFormedTest_4352 192 208 :=
  interval_of_check wellFormedTest_4352 192 16 (by decide +kernel)

theorem wellFormedTest_4352_block_13 : Interval wellFormedTest_4352 208 224 :=
  interval_of_check wellFormedTest_4352 208 16 (by decide +kernel)

theorem wellFormedTest_4352_block_14 : Interval wellFormedTest_4352 224 240 :=
  interval_of_check wellFormedTest_4352 224 16 (by decide +kernel)

theorem wellFormedTest_4352_block_15 : Interval wellFormedTest_4352 240 256 :=
  interval_of_check wellFormedTest_4352 240 16 (by decide +kernel)

theorem wellFormedTest_4352_complete : Interval wellFormedTest_4352 0 256 :=
  (interval_append wellFormedTest_4352 0 128 256
  (interval_append wellFormedTest_4352 0 64 128
  (interval_append wellFormedTest_4352 0 32 64
  (interval_append wellFormedTest_4352 0 16 32
  wellFormedTest_4352_block_0
  wellFormedTest_4352_block_1)
  (interval_append wellFormedTest_4352 32 48 64
  wellFormedTest_4352_block_2
  wellFormedTest_4352_block_3))
  (interval_append wellFormedTest_4352 64 96 128
  (interval_append wellFormedTest_4352 64 80 96
  wellFormedTest_4352_block_4
  wellFormedTest_4352_block_5)
  (interval_append wellFormedTest_4352 96 112 128
  wellFormedTest_4352_block_6
  wellFormedTest_4352_block_7)))
  (interval_append wellFormedTest_4352 128 192 256
  (interval_append wellFormedTest_4352 128 160 192
  (interval_append wellFormedTest_4352 128 144 160
  wellFormedTest_4352_block_8
  wellFormedTest_4352_block_9)
  (interval_append wellFormedTest_4352 160 176 192
  wellFormedTest_4352_block_10
  wellFormedTest_4352_block_11))
  (interval_append wellFormedTest_4352 192 224 256
  (interval_append wellFormedTest_4352 192 208 224
  wellFormedTest_4352_block_12
  wellFormedTest_4352_block_13)
  (interval_append wellFormedTest_4352 224 240 256
  wellFormedTest_4352_block_14
  wellFormedTest_4352_block_15))))
theorem wellFormedTestInterval4352 : Interval wellFormedTest 4352 4608 := by
  intro i hlo hhi
  have h := wellFormedTest_4352_complete (i-4352) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_4352, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed018 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_4608 (i : Nat) := wellFormedTest (i+4608)
theorem wellFormedTest_4608_block_0 : Interval wellFormedTest_4608 0 16 :=
  interval_of_check wellFormedTest_4608 0 16 (by decide +kernel)

theorem wellFormedTest_4608_block_1 : Interval wellFormedTest_4608 16 32 :=
  interval_of_check wellFormedTest_4608 16 16 (by decide +kernel)

theorem wellFormedTest_4608_block_2 : Interval wellFormedTest_4608 32 48 :=
  interval_of_check wellFormedTest_4608 32 16 (by decide +kernel)

theorem wellFormedTest_4608_block_3 : Interval wellFormedTest_4608 48 64 :=
  interval_of_check wellFormedTest_4608 48 16 (by decide +kernel)

theorem wellFormedTest_4608_block_4 : Interval wellFormedTest_4608 64 80 :=
  interval_of_check wellFormedTest_4608 64 16 (by decide +kernel)

theorem wellFormedTest_4608_block_5 : Interval wellFormedTest_4608 80 96 :=
  interval_of_check wellFormedTest_4608 80 16 (by decide +kernel)

theorem wellFormedTest_4608_block_6 : Interval wellFormedTest_4608 96 112 :=
  interval_of_check wellFormedTest_4608 96 16 (by decide +kernel)

theorem wellFormedTest_4608_block_7 : Interval wellFormedTest_4608 112 128 :=
  interval_of_check wellFormedTest_4608 112 16 (by decide +kernel)

theorem wellFormedTest_4608_block_8 : Interval wellFormedTest_4608 128 144 :=
  interval_of_check wellFormedTest_4608 128 16 (by decide +kernel)

theorem wellFormedTest_4608_block_9 : Interval wellFormedTest_4608 144 160 :=
  interval_of_check wellFormedTest_4608 144 16 (by decide +kernel)

theorem wellFormedTest_4608_block_10 : Interval wellFormedTest_4608 160 176 :=
  interval_of_check wellFormedTest_4608 160 16 (by decide +kernel)

theorem wellFormedTest_4608_block_11 : Interval wellFormedTest_4608 176 192 :=
  interval_of_check wellFormedTest_4608 176 16 (by decide +kernel)

theorem wellFormedTest_4608_block_12 : Interval wellFormedTest_4608 192 208 :=
  interval_of_check wellFormedTest_4608 192 16 (by decide +kernel)

theorem wellFormedTest_4608_block_13 : Interval wellFormedTest_4608 208 224 :=
  interval_of_check wellFormedTest_4608 208 16 (by decide +kernel)

theorem wellFormedTest_4608_block_14 : Interval wellFormedTest_4608 224 240 :=
  interval_of_check wellFormedTest_4608 224 16 (by decide +kernel)

theorem wellFormedTest_4608_block_15 : Interval wellFormedTest_4608 240 256 :=
  interval_of_check wellFormedTest_4608 240 16 (by decide +kernel)

theorem wellFormedTest_4608_complete : Interval wellFormedTest_4608 0 256 :=
  (interval_append wellFormedTest_4608 0 128 256
  (interval_append wellFormedTest_4608 0 64 128
  (interval_append wellFormedTest_4608 0 32 64
  (interval_append wellFormedTest_4608 0 16 32
  wellFormedTest_4608_block_0
  wellFormedTest_4608_block_1)
  (interval_append wellFormedTest_4608 32 48 64
  wellFormedTest_4608_block_2
  wellFormedTest_4608_block_3))
  (interval_append wellFormedTest_4608 64 96 128
  (interval_append wellFormedTest_4608 64 80 96
  wellFormedTest_4608_block_4
  wellFormedTest_4608_block_5)
  (interval_append wellFormedTest_4608 96 112 128
  wellFormedTest_4608_block_6
  wellFormedTest_4608_block_7)))
  (interval_append wellFormedTest_4608 128 192 256
  (interval_append wellFormedTest_4608 128 160 192
  (interval_append wellFormedTest_4608 128 144 160
  wellFormedTest_4608_block_8
  wellFormedTest_4608_block_9)
  (interval_append wellFormedTest_4608 160 176 192
  wellFormedTest_4608_block_10
  wellFormedTest_4608_block_11))
  (interval_append wellFormedTest_4608 192 224 256
  (interval_append wellFormedTest_4608 192 208 224
  wellFormedTest_4608_block_12
  wellFormedTest_4608_block_13)
  (interval_append wellFormedTest_4608 224 240 256
  wellFormedTest_4608_block_14
  wellFormedTest_4608_block_15))))
theorem wellFormedTestInterval4608 : Interval wellFormedTest 4608 4864 := by
  intro i hlo hhi
  have h := wellFormedTest_4608_complete (i-4608) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_4608, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed019 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_4864 (i : Nat) := wellFormedTest (i+4864)
theorem wellFormedTest_4864_block_0 : Interval wellFormedTest_4864 0 16 :=
  interval_of_check wellFormedTest_4864 0 16 (by decide +kernel)

theorem wellFormedTest_4864_block_1 : Interval wellFormedTest_4864 16 32 :=
  interval_of_check wellFormedTest_4864 16 16 (by decide +kernel)

theorem wellFormedTest_4864_block_2 : Interval wellFormedTest_4864 32 48 :=
  interval_of_check wellFormedTest_4864 32 16 (by decide +kernel)

theorem wellFormedTest_4864_block_3 : Interval wellFormedTest_4864 48 64 :=
  interval_of_check wellFormedTest_4864 48 16 (by decide +kernel)

theorem wellFormedTest_4864_block_4 : Interval wellFormedTest_4864 64 80 :=
  interval_of_check wellFormedTest_4864 64 16 (by decide +kernel)

theorem wellFormedTest_4864_block_5 : Interval wellFormedTest_4864 80 96 :=
  interval_of_check wellFormedTest_4864 80 16 (by decide +kernel)

theorem wellFormedTest_4864_block_6 : Interval wellFormedTest_4864 96 112 :=
  interval_of_check wellFormedTest_4864 96 16 (by decide +kernel)

theorem wellFormedTest_4864_block_7 : Interval wellFormedTest_4864 112 128 :=
  interval_of_check wellFormedTest_4864 112 16 (by decide +kernel)

theorem wellFormedTest_4864_block_8 : Interval wellFormedTest_4864 128 144 :=
  interval_of_check wellFormedTest_4864 128 16 (by decide +kernel)

theorem wellFormedTest_4864_block_9 : Interval wellFormedTest_4864 144 160 :=
  interval_of_check wellFormedTest_4864 144 16 (by decide +kernel)

theorem wellFormedTest_4864_block_10 : Interval wellFormedTest_4864 160 176 :=
  interval_of_check wellFormedTest_4864 160 16 (by decide +kernel)

theorem wellFormedTest_4864_block_11 : Interval wellFormedTest_4864 176 192 :=
  interval_of_check wellFormedTest_4864 176 16 (by decide +kernel)

theorem wellFormedTest_4864_block_12 : Interval wellFormedTest_4864 192 208 :=
  interval_of_check wellFormedTest_4864 192 16 (by decide +kernel)

theorem wellFormedTest_4864_block_13 : Interval wellFormedTest_4864 208 224 :=
  interval_of_check wellFormedTest_4864 208 16 (by decide +kernel)

theorem wellFormedTest_4864_block_14 : Interval wellFormedTest_4864 224 240 :=
  interval_of_check wellFormedTest_4864 224 16 (by decide +kernel)

theorem wellFormedTest_4864_block_15 : Interval wellFormedTest_4864 240 256 :=
  interval_of_check wellFormedTest_4864 240 16 (by decide +kernel)

theorem wellFormedTest_4864_complete : Interval wellFormedTest_4864 0 256 :=
  (interval_append wellFormedTest_4864 0 128 256
  (interval_append wellFormedTest_4864 0 64 128
  (interval_append wellFormedTest_4864 0 32 64
  (interval_append wellFormedTest_4864 0 16 32
  wellFormedTest_4864_block_0
  wellFormedTest_4864_block_1)
  (interval_append wellFormedTest_4864 32 48 64
  wellFormedTest_4864_block_2
  wellFormedTest_4864_block_3))
  (interval_append wellFormedTest_4864 64 96 128
  (interval_append wellFormedTest_4864 64 80 96
  wellFormedTest_4864_block_4
  wellFormedTest_4864_block_5)
  (interval_append wellFormedTest_4864 96 112 128
  wellFormedTest_4864_block_6
  wellFormedTest_4864_block_7)))
  (interval_append wellFormedTest_4864 128 192 256
  (interval_append wellFormedTest_4864 128 160 192
  (interval_append wellFormedTest_4864 128 144 160
  wellFormedTest_4864_block_8
  wellFormedTest_4864_block_9)
  (interval_append wellFormedTest_4864 160 176 192
  wellFormedTest_4864_block_10
  wellFormedTest_4864_block_11))
  (interval_append wellFormedTest_4864 192 224 256
  (interval_append wellFormedTest_4864 192 208 224
  wellFormedTest_4864_block_12
  wellFormedTest_4864_block_13)
  (interval_append wellFormedTest_4864 224 240 256
  wellFormedTest_4864_block_14
  wellFormedTest_4864_block_15))))
theorem wellFormedTestInterval4864 : Interval wellFormedTest 4864 5120 := by
  intro i hlo hhi
  have h := wellFormedTest_4864_complete (i-4864) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_4864, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed020 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

theorem wellFormedTest_5120_block_7 : Interval wellFormedTest_5120 112 128 :=
  interval_of_check wellFormedTest_5120 112 16 (by decide +kernel)

theorem wellFormedTest_5120_block_8 : Interval wellFormedTest_5120 128 144 :=
  interval_of_check wellFormedTest_5120 128 16 (by decide +kernel)

theorem wellFormedTest_5120_block_9 : Interval wellFormedTest_5120 144 160 :=
  interval_of_check wellFormedTest_5120 144 16 (by decide +kernel)

theorem wellFormedTest_5120_block_10 : Interval wellFormedTest_5120 160 176 :=
  interval_of_check wellFormedTest_5120 160 16 (by decide +kernel)

theorem wellFormedTest_5120_block_11 : Interval wellFormedTest_5120 176 192 :=
  interval_of_check wellFormedTest_5120 176 16 (by decide +kernel)

theorem wellFormedTest_5120_block_12 : Interval wellFormedTest_5120 192 208 :=
  interval_of_check wellFormedTest_5120 192 16 (by decide +kernel)

theorem wellFormedTest_5120_block_13 : Interval wellFormedTest_5120 208 224 :=
  interval_of_check wellFormedTest_5120 208 16 (by decide +kernel)

theorem wellFormedTest_5120_block_14 : Interval wellFormedTest_5120 224 240 :=
  interval_of_check wellFormedTest_5120 224 16 (by decide +kernel)

theorem wellFormedTest_5120_block_15 : Interval wellFormedTest_5120 240 256 :=
  interval_of_check wellFormedTest_5120 240 16 (by decide +kernel)

theorem wellFormedTest_5120_complete : Interval wellFormedTest_5120 0 256 :=
  (interval_append wellFormedTest_5120 0 128 256
  (interval_append wellFormedTest_5120 0 64 128
  (interval_append wellFormedTest_5120 0 32 64
  (interval_append wellFormedTest_5120 0 16 32
  wellFormedTest_5120_block_0
  wellFormedTest_5120_block_1)
  (interval_append wellFormedTest_5120 32 48 64
  wellFormedTest_5120_block_2
  wellFormedTest_5120_block_3))
  (interval_append wellFormedTest_5120 64 96 128
  (interval_append wellFormedTest_5120 64 80 96
  wellFormedTest_5120_block_4
  wellFormedTest_5120_block_5)
  (interval_append wellFormedTest_5120 96 112 128
  wellFormedTest_5120_block_6
  wellFormedTest_5120_block_7)))
  (interval_append wellFormedTest_5120 128 192 256
  (interval_append wellFormedTest_5120 128 160 192
  (interval_append wellFormedTest_5120 128 144 160
  wellFormedTest_5120_block_8
  wellFormedTest_5120_block_9)
  (interval_append wellFormedTest_5120 160 176 192
  wellFormedTest_5120_block_10
  wellFormedTest_5120_block_11))
  (interval_append wellFormedTest_5120 192 224 256
  (interval_append wellFormedTest_5120 192 208 224
  wellFormedTest_5120_block_12
  wellFormedTest_5120_block_13)
  (interval_append wellFormedTest_5120 224 240 256
  wellFormedTest_5120_block_14
  wellFormedTest_5120_block_15))))
theorem wellFormedTestInterval5120 : Interval wellFormedTest 5120 5376 := by
  intro i hlo hhi
  have h := wellFormedTest_5120_complete (i-5120) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_5120, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed021 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_5376 (i : Nat) := wellFormedTest (i+5376)
theorem wellFormedTest_5376_block_0 : Interval wellFormedTest_5376 0 16 :=
  interval_of_check wellFormedTest_5376 0 16 (by decide +kernel)

theorem wellFormedTest_5376_block_1 : Interval wellFormedTest_5376 16 32 :=
  interval_of_check wellFormedTest_5376 16 16 (by decide +kernel)

theorem wellFormedTest_5376_block_2 : Interval wellFormedTest_5376 32 48 :=
  interval_of_check wellFormedTest_5376 32 16 (by decide +kernel)

theorem wellFormedTest_5376_block_3 : Interval wellFormedTest_5376 48 64 :=
  interval_of_check wellFormedTest_5376 48 16 (by decide +kernel)

theorem wellFormedTest_5376_block_4 : Interval wellFormedTest_5376 64 80 :=
  interval_of_check wellFormedTest_5376 64 16 (by decide +kernel)

theorem wellFormedTest_5376_block_5 : Interval wellFormedTest_5376 80 96 :=
  interval_of_check wellFormedTest_5376 80 16 (by decide +kernel)

theorem wellFormedTest_5376_block_6 : Interval wellFormedTest_5376 96 112 :=
  interval_of_check wellFormedTest_5376 96 16 (by decide +kernel)

theorem wellFormedTest_5376_block_7 : Interval wellFormedTest_5376 112 128 :=
  interval_of_check wellFormedTest_5376 112 16 (by decide +kernel)

theorem wellFormedTest_5376_block_8 : Interval wellFormedTest_5376 128 144 :=
  interval_of_check wellFormedTest_5376 128 16 (by decide +kernel)

theorem wellFormedTest_5376_block_9 : Interval wellFormedTest_5376 144 160 :=
  interval_of_check wellFormedTest_5376 144 16 (by decide +kernel)

theorem wellFormedTest_5376_block_10 : Interval wellFormedTest_5376 160 176 :=
  interval_of_check wellFormedTest_5376 160 16 (by decide +kernel)

theorem wellFormedTest_5376_block_11 : Interval wellFormedTest_5376 176 192 :=
  interval_of_check wellFormedTest_5376 176 16 (by decide +kernel)

theorem wellFormedTest_5376_block_12 : Interval wellFormedTest_5376 192 208 :=
  interval_of_check wellFormedTest_5376 192 16 (by decide +kernel)

theorem wellFormedTest_5376_block_13 : Interval wellFormedTest_5376 208 224 :=
  interval_of_check wellFormedTest_5376 208 16 (by decide +kernel)

theorem wellFormedTest_5376_block_14 : Interval wellFormedTest_5376 224 240 :=
  interval_of_check wellFormedTest_5376 224 16 (by decide +kernel)

theorem wellFormedTest_5376_block_15 : Interval wellFormedTest_5376 240 256 :=
  interval_of_check wellFormedTest_5376 240 16 (by decide +kernel)

theorem wellFormedTest_5376_complete : Interval wellFormedTest_5376 0 256 :=
  (interval_append wellFormedTest_5376 0 128 256
  (interval_append wellFormedTest_5376 0 64 128
  (interval_append wellFormedTest_5376 0 32 64
  (interval_append wellFormedTest_5376 0 16 32
  wellFormedTest_5376_block_0
  wellFormedTest_5376_block_1)
  (interval_append wellFormedTest_5376 32 48 64
  wellFormedTest_5376_block_2
  wellFormedTest_5376_block_3))
  (interval_append wellFormedTest_5376 64 96 128
  (interval_append wellFormedTest_5376 64 80 96
  wellFormedTest_5376_block_4
  wellFormedTest_5376_block_5)
  (interval_append wellFormedTest_5376 96 112 128
  wellFormedTest_5376_block_6
  wellFormedTest_5376_block_7)))
  (interval_append wellFormedTest_5376 128 192 256
  (interval_append wellFormedTest_5376 128 160 192
  (interval_append wellFormedTest_5376 128 144 160
  wellFormedTest_5376_block_8
  wellFormedTest_5376_block_9)
  (interval_append wellFormedTest_5376 160 176 192
  wellFormedTest_5376_block_10
  wellFormedTest_5376_block_11))
  (interval_append wellFormedTest_5376 192 224 256
  (interval_append wellFormedTest_5376 192 208 224
  wellFormedTest_5376_block_12
  wellFormedTest_5376_block_13)
  (interval_append wellFormedTest_5376 224 240 256
  wellFormedTest_5376_block_14
  wellFormedTest_5376_block_15))))
theorem wellFormedTestInterval5376 : Interval wellFormedTest 5376 5632 := by
  intro i hlo hhi
  have h := wellFormedTest_5376_complete (i-5376) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_5376, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed022 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_5632 (i : Nat) := wellFormedTest (i+5632)
theorem wellFormedTest_5632_block_0 : Interval wellFormedTest_5632 0 16 :=
  interval_of_check wellFormedTest_5632 0 16 (by decide +kernel)

theorem wellFormedTest_5632_block_1 : Interval wellFormedTest_5632 16 32 :=
  interval_of_check wellFormedTest_5632 16 16 (by decide +kernel)

theorem wellFormedTest_5632_block_2 : Interval wellFormedTest_5632 32 48 :=
  interval_of_check wellFormedTest_5632 32 16 (by decide +kernel)

theorem wellFormedTest_5632_block_3 : Interval wellFormedTest_5632 48 64 :=
  interval_of_check wellFormedTest_5632 48 16 (by decide +kernel)

theorem wellFormedTest_5632_block_4 : Interval wellFormedTest_5632 64 80 :=
  interval_of_check wellFormedTest_5632 64 16 (by decide +kernel)

theorem wellFormedTest_5632_block_5 : Interval wellFormedTest_5632 80 96 :=
  interval_of_check wellFormedTest_5632 80 16 (by decide +kernel)

theorem wellFormedTest_5632_block_6 : Interval wellFormedTest_5632 96 112 :=
  interval_of_check wellFormedTest_5632 96 16 (by decide +kernel)

theorem wellFormedTest_5632_block_7 : Interval wellFormedTest_5632 112 128 :=
  interval_of_check wellFormedTest_5632 112 16 (by decide +kernel)

theorem wellFormedTest_5632_block_8 : Interval wellFormedTest_5632 128 144 :=
  interval_of_check wellFormedTest_5632 128 16 (by decide +kernel)

theorem wellFormedTest_5632_block_9 : Interval wellFormedTest_5632 144 160 :=
  interval_of_check wellFormedTest_5632 144 16 (by decide +kernel)

theorem wellFormedTest_5632_block_10 : Interval wellFormedTest_5632 160 176 :=
  interval_of_check wellFormedTest_5632 160 16 (by decide +kernel)

theorem wellFormedTest_5632_block_11 : Interval wellFormedTest_5632 176 192 :=
  interval_of_check wellFormedTest_5632 176 16 (by decide +kernel)

theorem wellFormedTest_5632_block_12 : Interval wellFormedTest_5632 192 208 :=
  interval_of_check wellFormedTest_5632 192 16 (by decide +kernel)

theorem wellFormedTest_5632_block_13 : Interval wellFormedTest_5632 208 224 :=
  interval_of_check wellFormedTest_5632 208 16 (by decide +kernel)

theorem wellFormedTest_5632_block_14 : Interval wellFormedTest_5632 224 240 :=
  interval_of_check wellFormedTest_5632 224 16 (by decide +kernel)

theorem wellFormedTest_5632_block_15 : Interval wellFormedTest_5632 240 256 :=
  interval_of_check wellFormedTest_5632 240 16 (by decide +kernel)

theorem wellFormedTest_5632_complete : Interval wellFormedTest_5632 0 256 :=
  (interval_append wellFormedTest_5632 0 128 256
  (interval_append wellFormedTest_5632 0 64 128
  (interval_append wellFormedTest_5632 0 32 64
  (interval_append wellFormedTest_5632 0 16 32
  wellFormedTest_5632_block_0
  wellFormedTest_5632_block_1)
  (interval_append wellFormedTest_5632 32 48 64
  wellFormedTest_5632_block_2
  wellFormedTest_5632_block_3))
  (interval_append wellFormedTest_5632 64 96 128
  (interval_append wellFormedTest_5632 64 80 96
  wellFormedTest_5632_block_4
  wellFormedTest_5632_block_5)
  (interval_append wellFormedTest_5632 96 112 128
  wellFormedTest_5632_block_6
  wellFormedTest_5632_block_7)))
  (interval_append wellFormedTest_5632 128 192 256
  (interval_append wellFormedTest_5632 128 160 192
  (interval_append wellFormedTest_5632 128 144 160
  wellFormedTest_5632_block_8
  wellFormedTest_5632_block_9)
  (interval_append wellFormedTest_5632 160 176 192
  wellFormedTest_5632_block_10
  wellFormedTest_5632_block_11))
  (interval_append wellFormedTest_5632 192 224 256
  (interval_append wellFormedTest_5632 192 208 224
  wellFormedTest_5632_block_12
  wellFormedTest_5632_block_13)
  (interval_append wellFormedTest_5632 224 240 256
  wellFormedTest_5632_block_14
  wellFormedTest_5632_block_15))))
theorem wellFormedTestInterval5632 : Interval wellFormedTest 5632 5888 := by
  intro i hlo hhi
  have h := wellFormedTest_5632_complete (i-5632) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_5632, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed023 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_5888 (i : Nat) := wellFormedTest (i+5888)
theorem wellFormedTest_5888_block_0 : Interval wellFormedTest_5888 0 16 :=
  interval_of_check wellFormedTest_5888 0 16 (by decide +kernel)

theorem wellFormedTest_5888_block_1 : Interval wellFormedTest_5888 16 32 :=
  interval_of_check wellFormedTest_5888 16 16 (by decide +kernel)

theorem wellFormedTest_5888_block_2 : Interval wellFormedTest_5888 32 48 :=
  interval_of_check wellFormedTest_5888 32 16 (by decide +kernel)

theorem wellFormedTest_5888_block_3 : Interval wellFormedTest_5888 48 64 :=
  interval_of_check wellFormedTest_5888 48 16 (by decide +kernel)

theorem wellFormedTest_5888_block_4 : Interval wellFormedTest_5888 64 80 :=
  interval_of_check wellFormedTest_5888 64 16 (by decide +kernel)

theorem wellFormedTest_5888_block_5 : Interval wellFormedTest_5888 80 96 :=
  interval_of_check wellFormedTest_5888 80 16 (by decide +kernel)

theorem wellFormedTest_5888_block_6 : Interval wellFormedTest_5888 96 112 :=
  interval_of_check wellFormedTest_5888 96 16 (by decide +kernel)

theorem wellFormedTest_5888_block_7 : Interval wellFormedTest_5888 112 128 :=
  interval_of_check wellFormedTest_5888 112 16 (by decide +kernel)

theorem wellFormedTest_5888_block_8 : Interval wellFormedTest_5888 128 144 :=
  interval_of_check wellFormedTest_5888 128 16 (by decide +kernel)

theorem wellFormedTest_5888_block_9 : Interval wellFormedTest_5888 144 160 :=
  interval_of_check wellFormedTest_5888 144 16 (by decide +kernel)

theorem wellFormedTest_5888_block_10 : Interval wellFormedTest_5888 160 176 :=
  interval_of_check wellFormedTest_5888 160 16 (by decide +kernel)

theorem wellFormedTest_5888_block_11 : Interval wellFormedTest_5888 176 192 :=
  interval_of_check wellFormedTest_5888 176 16 (by decide +kernel)

theorem wellFormedTest_5888_block_12 : Interval wellFormedTest_5888 192 208 :=
  interval_of_check wellFormedTest_5888 192 16 (by decide +kernel)

theorem wellFormedTest_5888_block_13 : Interval wellFormedTest_5888 208 224 :=
  interval_of_check wellFormedTest_5888 208 16 (by decide +kernel)

theorem wellFormedTest_5888_block_14 : Interval wellFormedTest_5888 224 240 :=
  interval_of_check wellFormedTest_5888 224 16 (by decide +kernel)

theorem wellFormedTest_5888_block_15 : Interval wellFormedTest_5888 240 256 :=
  interval_of_check wellFormedTest_5888 240 16 (by decide +kernel)

theorem wellFormedTest_5888_complete : Interval wellFormedTest_5888 0 256 :=
  (interval_append wellFormedTest_5888 0 128 256
  (interval_append wellFormedTest_5888 0 64 128
  (interval_append wellFormedTest_5888 0 32 64
  (interval_append wellFormedTest_5888 0 16 32
  wellFormedTest_5888_block_0
  wellFormedTest_5888_block_1)
  (interval_append wellFormedTest_5888 32 48 64
  wellFormedTest_5888_block_2
  wellFormedTest_5888_block_3))
  (interval_append wellFormedTest_5888 64 96 128
  (interval_append wellFormedTest_5888 64 80 96
  wellFormedTest_5888_block_4
  wellFormedTest_5888_block_5)
  (interval_append wellFormedTest_5888 96 112 128
  wellFormedTest_5888_block_6
  wellFormedTest_5888_block_7)))
  (interval_append wellFormedTest_5888 128 192 256
  (interval_append wellFormedTest_5888 128 160 192
  (interval_append wellFormedTest_5888 128 144 160
  wellFormedTest_5888_block_8
  wellFormedTest_5888_block_9)
  (interval_append wellFormedTest_5888 160 176 192
  wellFormedTest_5888_block_10
  wellFormedTest_5888_block_11))
  (interval_append wellFormedTest_5888 192 224 256
  (interval_append wellFormedTest_5888 192 208 224
  wellFormedTest_5888_block_12
  wellFormedTest_5888_block_13)
  (interval_append wellFormedTest_5888 224 240 256
  wellFormedTest_5888_block_14
  wellFormedTest_5888_block_15))))
theorem wellFormedTestInterval5888 : Interval wellFormedTest 5888 6144 := by
  intro i hlo hhi
  have h := wellFormedTest_5888_complete (i-5888) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_5888, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
