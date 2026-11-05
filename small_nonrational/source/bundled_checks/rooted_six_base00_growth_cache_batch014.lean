module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheWellFormed052 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_13312 (i : Nat) := wellFormedTest (i+13312)
theorem wellFormedTest_13312_block_0 : Interval wellFormedTest_13312 0 16 :=
  interval_of_check wellFormedTest_13312 0 16 (by decide +kernel)

theorem wellFormedTest_13312_block_1 : Interval wellFormedTest_13312 16 32 :=
  interval_of_check wellFormedTest_13312 16 16 (by decide +kernel)

theorem wellFormedTest_13312_block_2 : Interval wellFormedTest_13312 32 48 :=
  interval_of_check wellFormedTest_13312 32 16 (by decide +kernel)

theorem wellFormedTest_13312_block_3 : Interval wellFormedTest_13312 48 64 :=
  interval_of_check wellFormedTest_13312 48 16 (by decide +kernel)

theorem wellFormedTest_13312_block_4 : Interval wellFormedTest_13312 64 80 :=
  interval_of_check wellFormedTest_13312 64 16 (by decide +kernel)

theorem wellFormedTest_13312_block_5 : Interval wellFormedTest_13312 80 96 :=
  interval_of_check wellFormedTest_13312 80 16 (by decide +kernel)

theorem wellFormedTest_13312_block_6 : Interval wellFormedTest_13312 96 112 :=
  interval_of_check wellFormedTest_13312 96 16 (by decide +kernel)

theorem wellFormedTest_13312_block_7 : Interval wellFormedTest_13312 112 128 :=
  interval_of_check wellFormedTest_13312 112 16 (by decide +kernel)

theorem wellFormedTest_13312_block_8 : Interval wellFormedTest_13312 128 144 :=
  interval_of_check wellFormedTest_13312 128 16 (by decide +kernel)

theorem wellFormedTest_13312_block_9 : Interval wellFormedTest_13312 144 160 :=
  interval_of_check wellFormedTest_13312 144 16 (by decide +kernel)

theorem wellFormedTest_13312_block_10 : Interval wellFormedTest_13312 160 176 :=
  interval_of_check wellFormedTest_13312 160 16 (by decide +kernel)

theorem wellFormedTest_13312_block_11 : Interval wellFormedTest_13312 176 192 :=
  interval_of_check wellFormedTest_13312 176 16 (by decide +kernel)

theorem wellFormedTest_13312_block_12 : Interval wellFormedTest_13312 192 208 :=
  interval_of_check wellFormedTest_13312 192 16 (by decide +kernel)

theorem wellFormedTest_13312_block_13 : Interval wellFormedTest_13312 208 224 :=
  interval_of_check wellFormedTest_13312 208 16 (by decide +kernel)

theorem wellFormedTest_13312_block_14 : Interval wellFormedTest_13312 224 240 :=
  interval_of_check wellFormedTest_13312 224 16 (by decide +kernel)

theorem wellFormedTest_13312_block_15 : Interval wellFormedTest_13312 240 256 :=
  interval_of_check wellFormedTest_13312 240 16 (by decide +kernel)

theorem wellFormedTest_13312_complete : Interval wellFormedTest_13312 0 256 :=
  (interval_append wellFormedTest_13312 0 128 256
  (interval_append wellFormedTest_13312 0 64 128
  (interval_append wellFormedTest_13312 0 32 64
  (interval_append wellFormedTest_13312 0 16 32
  wellFormedTest_13312_block_0
  wellFormedTest_13312_block_1)
  (interval_append wellFormedTest_13312 32 48 64
  wellFormedTest_13312_block_2
  wellFormedTest_13312_block_3))
  (interval_append wellFormedTest_13312 64 96 128
  (interval_append wellFormedTest_13312 64 80 96
  wellFormedTest_13312_block_4
  wellFormedTest_13312_block_5)
  (interval_append wellFormedTest_13312 96 112 128
  wellFormedTest_13312_block_6
  wellFormedTest_13312_block_7)))
  (interval_append wellFormedTest_13312 128 192 256
  (interval_append wellFormedTest_13312 128 160 192
  (interval_append wellFormedTest_13312 128 144 160
  wellFormedTest_13312_block_8
  wellFormedTest_13312_block_9)
  (interval_append wellFormedTest_13312 160 176 192
  wellFormedTest_13312_block_10
  wellFormedTest_13312_block_11))
  (interval_append wellFormedTest_13312 192 224 256
  (interval_append wellFormedTest_13312 192 208 224
  wellFormedTest_13312_block_12
  wellFormedTest_13312_block_13)
  (interval_append wellFormedTest_13312 224 240 256
  wellFormedTest_13312_block_14
  wellFormedTest_13312_block_15))))
theorem wellFormedTestInterval13312 : Interval wellFormedTest 13312 13568 := by
  intro i hlo hhi
  have h := wellFormedTest_13312_complete (i-13312) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_13312, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed053 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_13568 (i : Nat) := wellFormedTest (i+13568)
theorem wellFormedTest_13568_block_0 : Interval wellFormedTest_13568 0 16 :=
  interval_of_check wellFormedTest_13568 0 16 (by decide +kernel)

theorem wellFormedTest_13568_block_1 : Interval wellFormedTest_13568 16 32 :=
  interval_of_check wellFormedTest_13568 16 16 (by decide +kernel)

theorem wellFormedTest_13568_block_2 : Interval wellFormedTest_13568 32 48 :=
  interval_of_check wellFormedTest_13568 32 16 (by decide +kernel)

theorem wellFormedTest_13568_block_3 : Interval wellFormedTest_13568 48 64 :=
  interval_of_check wellFormedTest_13568 48 16 (by decide +kernel)

theorem wellFormedTest_13568_block_4 : Interval wellFormedTest_13568 64 80 :=
  interval_of_check wellFormedTest_13568 64 16 (by decide +kernel)

theorem wellFormedTest_13568_block_5 : Interval wellFormedTest_13568 80 96 :=
  interval_of_check wellFormedTest_13568 80 16 (by decide +kernel)

theorem wellFormedTest_13568_block_6 : Interval wellFormedTest_13568 96 112 :=
  interval_of_check wellFormedTest_13568 96 16 (by decide +kernel)

theorem wellFormedTest_13568_block_7 : Interval wellFormedTest_13568 112 128 :=
  interval_of_check wellFormedTest_13568 112 16 (by decide +kernel)

theorem wellFormedTest_13568_block_8 : Interval wellFormedTest_13568 128 144 :=
  interval_of_check wellFormedTest_13568 128 16 (by decide +kernel)

theorem wellFormedTest_13568_block_9 : Interval wellFormedTest_13568 144 160 :=
  interval_of_check wellFormedTest_13568 144 16 (by decide +kernel)

theorem wellFormedTest_13568_block_10 : Interval wellFormedTest_13568 160 176 :=
  interval_of_check wellFormedTest_13568 160 16 (by decide +kernel)

theorem wellFormedTest_13568_block_11 : Interval wellFormedTest_13568 176 192 :=
  interval_of_check wellFormedTest_13568 176 16 (by decide +kernel)

theorem wellFormedTest_13568_block_12 : Interval wellFormedTest_13568 192 208 :=
  interval_of_check wellFormedTest_13568 192 16 (by decide +kernel)

theorem wellFormedTest_13568_block_13 : Interval wellFormedTest_13568 208 224 :=
  interval_of_check wellFormedTest_13568 208 16 (by decide +kernel)

theorem wellFormedTest_13568_block_14 : Interval wellFormedTest_13568 224 240 :=
  interval_of_check wellFormedTest_13568 224 16 (by decide +kernel)

theorem wellFormedTest_13568_block_15 : Interval wellFormedTest_13568 240 256 :=
  interval_of_check wellFormedTest_13568 240 16 (by decide +kernel)

theorem wellFormedTest_13568_complete : Interval wellFormedTest_13568 0 256 :=
  (interval_append wellFormedTest_13568 0 128 256
  (interval_append wellFormedTest_13568 0 64 128
  (interval_append wellFormedTest_13568 0 32 64
  (interval_append wellFormedTest_13568 0 16 32
  wellFormedTest_13568_block_0
  wellFormedTest_13568_block_1)
  (interval_append wellFormedTest_13568 32 48 64
  wellFormedTest_13568_block_2
  wellFormedTest_13568_block_3))
  (interval_append wellFormedTest_13568 64 96 128
  (interval_append wellFormedTest_13568 64 80 96
  wellFormedTest_13568_block_4
  wellFormedTest_13568_block_5)
  (interval_append wellFormedTest_13568 96 112 128
  wellFormedTest_13568_block_6
  wellFormedTest_13568_block_7)))
  (interval_append wellFormedTest_13568 128 192 256
  (interval_append wellFormedTest_13568 128 160 192
  (interval_append wellFormedTest_13568 128 144 160
  wellFormedTest_13568_block_8
  wellFormedTest_13568_block_9)
  (interval_append wellFormedTest_13568 160 176 192
  wellFormedTest_13568_block_10
  wellFormedTest_13568_block_11))
  (interval_append wellFormedTest_13568 192 224 256
  (interval_append wellFormedTest_13568 192 208 224
  wellFormedTest_13568_block_12
  wellFormedTest_13568_block_13)
  (interval_append wellFormedTest_13568 224 240 256
  wellFormedTest_13568_block_14
  wellFormedTest_13568_block_15))))
theorem wellFormedTestInterval13568 : Interval wellFormedTest 13568 13824 := by
  intro i hlo hhi
  have h := wellFormedTest_13568_complete (i-13568) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_13568, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed054 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_13824 (i : Nat) := wellFormedTest (i+13824)
theorem wellFormedTest_13824_block_0 : Interval wellFormedTest_13824 0 16 :=
  interval_of_check wellFormedTest_13824 0 16 (by decide +kernel)

theorem wellFormedTest_13824_block_1 : Interval wellFormedTest_13824 16 32 :=
  interval_of_check wellFormedTest_13824 16 16 (by decide +kernel)

theorem wellFormedTest_13824_block_2 : Interval wellFormedTest_13824 32 48 :=
  interval_of_check wellFormedTest_13824 32 16 (by decide +kernel)

theorem wellFormedTest_13824_block_3 : Interval wellFormedTest_13824 48 64 :=
  interval_of_check wellFormedTest_13824 48 16 (by decide +kernel)

theorem wellFormedTest_13824_block_4 : Interval wellFormedTest_13824 64 80 :=
  interval_of_check wellFormedTest_13824 64 16 (by decide +kernel)

theorem wellFormedTest_13824_block_5 : Interval wellFormedTest_13824 80 96 :=
  interval_of_check wellFormedTest_13824 80 16 (by decide +kernel)

theorem wellFormedTest_13824_block_6 : Interval wellFormedTest_13824 96 112 :=
  interval_of_check wellFormedTest_13824 96 16 (by decide +kernel)

theorem wellFormedTest_13824_block_7 : Interval wellFormedTest_13824 112 128 :=
  interval_of_check wellFormedTest_13824 112 16 (by decide +kernel)

theorem wellFormedTest_13824_block_8 : Interval wellFormedTest_13824 128 144 :=
  interval_of_check wellFormedTest_13824 128 16 (by decide +kernel)

theorem wellFormedTest_13824_block_9 : Interval wellFormedTest_13824 144 160 :=
  interval_of_check wellFormedTest_13824 144 16 (by decide +kernel)

theorem wellFormedTest_13824_block_10 : Interval wellFormedTest_13824 160 176 :=
  interval_of_check wellFormedTest_13824 160 16 (by decide +kernel)

theorem wellFormedTest_13824_block_11 : Interval wellFormedTest_13824 176 192 :=
  interval_of_check wellFormedTest_13824 176 16 (by decide +kernel)

theorem wellFormedTest_13824_block_12 : Interval wellFormedTest_13824 192 208 :=
  interval_of_check wellFormedTest_13824 192 16 (by decide +kernel)

theorem wellFormedTest_13824_block_13 : Interval wellFormedTest_13824 208 224 :=
  interval_of_check wellFormedTest_13824 208 16 (by decide +kernel)

theorem wellFormedTest_13824_block_14 : Interval wellFormedTest_13824 224 240 :=
  interval_of_check wellFormedTest_13824 224 16 (by decide +kernel)

theorem wellFormedTest_13824_block_15 : Interval wellFormedTest_13824 240 256 :=
  interval_of_check wellFormedTest_13824 240 16 (by decide +kernel)

theorem wellFormedTest_13824_complete : Interval wellFormedTest_13824 0 256 :=
  (interval_append wellFormedTest_13824 0 128 256
  (interval_append wellFormedTest_13824 0 64 128
  (interval_append wellFormedTest_13824 0 32 64
  (interval_append wellFormedTest_13824 0 16 32
  wellFormedTest_13824_block_0
  wellFormedTest_13824_block_1)
  (interval_append wellFormedTest_13824 32 48 64
  wellFormedTest_13824_block_2
  wellFormedTest_13824_block_3))
  (interval_append wellFormedTest_13824 64 96 128
  (interval_append wellFormedTest_13824 64 80 96
  wellFormedTest_13824_block_4
  wellFormedTest_13824_block_5)
  (interval_append wellFormedTest_13824 96 112 128
  wellFormedTest_13824_block_6
  wellFormedTest_13824_block_7)))
  (interval_append wellFormedTest_13824 128 192 256
  (interval_append wellFormedTest_13824 128 160 192
  (interval_append wellFormedTest_13824 128 144 160
  wellFormedTest_13824_block_8
  wellFormedTest_13824_block_9)
  (interval_append wellFormedTest_13824 160 176 192
  wellFormedTest_13824_block_10
  wellFormedTest_13824_block_11))
  (interval_append wellFormedTest_13824 192 224 256
  (interval_append wellFormedTest_13824 192 208 224
  wellFormedTest_13824_block_12
  wellFormedTest_13824_block_13)
  (interval_append wellFormedTest_13824 224 240 256
  wellFormedTest_13824_block_14
  wellFormedTest_13824_block_15))))
theorem wellFormedTestInterval13824 : Interval wellFormedTest 13824 14080 := by
  intro i hlo hhi
  have h := wellFormedTest_13824_complete (i-13824) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_13824, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed055 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_14080 (i : Nat) := wellFormedTest (i+14080)
theorem wellFormedTest_14080_block_0 : Interval wellFormedTest_14080 0 16 :=
  interval_of_check wellFormedTest_14080 0 16 (by decide +kernel)

theorem wellFormedTest_14080_block_1 : Interval wellFormedTest_14080 16 32 :=
  interval_of_check wellFormedTest_14080 16 16 (by decide +kernel)

theorem wellFormedTest_14080_block_2 : Interval wellFormedTest_14080 32 48 :=
  interval_of_check wellFormedTest_14080 32 16 (by decide +kernel)

theorem wellFormedTest_14080_block_3 : Interval wellFormedTest_14080 48 64 :=
  interval_of_check wellFormedTest_14080 48 16 (by decide +kernel)

theorem wellFormedTest_14080_block_4 : Interval wellFormedTest_14080 64 80 :=
  interval_of_check wellFormedTest_14080 64 16 (by decide +kernel)

theorem wellFormedTest_14080_block_5 : Interval wellFormedTest_14080 80 96 :=
  interval_of_check wellFormedTest_14080 80 16 (by decide +kernel)

theorem wellFormedTest_14080_block_6 : Interval wellFormedTest_14080 96 112 :=
  interval_of_check wellFormedTest_14080 96 16 (by decide +kernel)

theorem wellFormedTest_14080_block_7 : Interval wellFormedTest_14080 112 128 :=
  interval_of_check wellFormedTest_14080 112 16 (by decide +kernel)

theorem wellFormedTest_14080_block_8 : Interval wellFormedTest_14080 128 144 :=
  interval_of_check wellFormedTest_14080 128 16 (by decide +kernel)

theorem wellFormedTest_14080_block_9 : Interval wellFormedTest_14080 144 160 :=
  interval_of_check wellFormedTest_14080 144 16 (by decide +kernel)

theorem wellFormedTest_14080_block_10 : Interval wellFormedTest_14080 160 176 :=
  interval_of_check wellFormedTest_14080 160 16 (by decide +kernel)

theorem wellFormedTest_14080_block_11 : Interval wellFormedTest_14080 176 192 :=
  interval_of_check wellFormedTest_14080 176 16 (by decide +kernel)

theorem wellFormedTest_14080_block_12 : Interval wellFormedTest_14080 192 208 :=
  interval_of_check wellFormedTest_14080 192 16 (by decide +kernel)

theorem wellFormedTest_14080_block_13 : Interval wellFormedTest_14080 208 224 :=
  interval_of_check wellFormedTest_14080 208 16 (by decide +kernel)

theorem wellFormedTest_14080_block_14 : Interval wellFormedTest_14080 224 240 :=
  interval_of_check wellFormedTest_14080 224 16 (by decide +kernel)

theorem wellFormedTest_14080_block_15 : Interval wellFormedTest_14080 240 256 :=
  interval_of_check wellFormedTest_14080 240 16 (by decide +kernel)

theorem wellFormedTest_14080_complete : Interval wellFormedTest_14080 0 256 :=
  (interval_append wellFormedTest_14080 0 128 256
  (interval_append wellFormedTest_14080 0 64 128
  (interval_append wellFormedTest_14080 0 32 64
  (interval_append wellFormedTest_14080 0 16 32
  wellFormedTest_14080_block_0
  wellFormedTest_14080_block_1)
  (interval_append wellFormedTest_14080 32 48 64
  wellFormedTest_14080_block_2
  wellFormedTest_14080_block_3))
  (interval_append wellFormedTest_14080 64 96 128
  (interval_append wellFormedTest_14080 64 80 96
  wellFormedTest_14080_block_4
  wellFormedTest_14080_block_5)
  (interval_append wellFormedTest_14080 96 112 128
  wellFormedTest_14080_block_6
  wellFormedTest_14080_block_7)))
  (interval_append wellFormedTest_14080 128 192 256
  (interval_append wellFormedTest_14080 128 160 192
  (interval_append wellFormedTest_14080 128 144 160
  wellFormedTest_14080_block_8
  wellFormedTest_14080_block_9)
  (interval_append wellFormedTest_14080 160 176 192
  wellFormedTest_14080_block_10
  wellFormedTest_14080_block_11))
  (interval_append wellFormedTest_14080 192 224 256
  (interval_append wellFormedTest_14080 192 208 224
  wellFormedTest_14080_block_12
  wellFormedTest_14080_block_13)
  (interval_append wellFormedTest_14080 224 240 256
  wellFormedTest_14080_block_14
  wellFormedTest_14080_block_15))))
theorem wellFormedTestInterval14080 : Interval wellFormedTest 14080 14336 := by
  intro i hlo hhi
  have h := wellFormedTest_14080_complete (i-14080) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_14080, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed056 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_14336 (i : Nat) := wellFormedTest (i+14336)
theorem wellFormedTest_14336_block_0 : Interval wellFormedTest_14336 0 16 :=
  interval_of_check wellFormedTest_14336 0 16 (by decide +kernel)

theorem wellFormedTest_14336_block_1 : Interval wellFormedTest_14336 16 32 :=
  interval_of_check wellFormedTest_14336 16 16 (by decide +kernel)

theorem wellFormedTest_14336_block_2 : Interval wellFormedTest_14336 32 48 :=
  interval_of_check wellFormedTest_14336 32 16 (by decide +kernel)

theorem wellFormedTest_14336_block_3 : Interval wellFormedTest_14336 48 64 :=
  interval_of_check wellFormedTest_14336 48 16 (by decide +kernel)

theorem wellFormedTest_14336_block_4 : Interval wellFormedTest_14336 64 80 :=
  interval_of_check wellFormedTest_14336 64 16 (by decide +kernel)

theorem wellFormedTest_14336_block_5 : Interval wellFormedTest_14336 80 96 :=
  interval_of_check wellFormedTest_14336 80 16 (by decide +kernel)

theorem wellFormedTest_14336_block_6 : Interval wellFormedTest_14336 96 112 :=
  interval_of_check wellFormedTest_14336 96 16 (by decide +kernel)

theorem wellFormedTest_14336_block_7 : Interval wellFormedTest_14336 112 128 :=
  interval_of_check wellFormedTest_14336 112 16 (by decide +kernel)

theorem wellFormedTest_14336_block_8 : Interval wellFormedTest_14336 128 144 :=
  interval_of_check wellFormedTest_14336 128 16 (by decide +kernel)

theorem wellFormedTest_14336_block_9 : Interval wellFormedTest_14336 144 160 :=
  interval_of_check wellFormedTest_14336 144 16 (by decide +kernel)

theorem wellFormedTest_14336_block_10 : Interval wellFormedTest_14336 160 176 :=
  interval_of_check wellFormedTest_14336 160 16 (by decide +kernel)

theorem wellFormedTest_14336_block_11 : Interval wellFormedTest_14336 176 192 :=
  interval_of_check wellFormedTest_14336 176 16 (by decide +kernel)

theorem wellFormedTest_14336_block_12 : Interval wellFormedTest_14336 192 208 :=
  interval_of_check wellFormedTest_14336 192 16 (by decide +kernel)

theorem wellFormedTest_14336_block_13 : Interval wellFormedTest_14336 208 224 :=
  interval_of_check wellFormedTest_14336 208 16 (by decide +kernel)

theorem wellFormedTest_14336_block_14 : Interval wellFormedTest_14336 224 240 :=
  interval_of_check wellFormedTest_14336 224 16 (by decide +kernel)

theorem wellFormedTest_14336_block_15 : Interval wellFormedTest_14336 240 256 :=
  interval_of_check wellFormedTest_14336 240 16 (by decide +kernel)

theorem wellFormedTest_14336_complete : Interval wellFormedTest_14336 0 256 :=
  (interval_append wellFormedTest_14336 0 128 256
  (interval_append wellFormedTest_14336 0 64 128
  (interval_append wellFormedTest_14336 0 32 64
  (interval_append wellFormedTest_14336 0 16 32
  wellFormedTest_14336_block_0
  wellFormedTest_14336_block_1)
  (interval_append wellFormedTest_14336 32 48 64
  wellFormedTest_14336_block_2
  wellFormedTest_14336_block_3))
  (interval_append wellFormedTest_14336 64 96 128
  (interval_append wellFormedTest_14336 64 80 96
  wellFormedTest_14336_block_4
  wellFormedTest_14336_block_5)
  (interval_append wellFormedTest_14336 96 112 128
  wellFormedTest_14336_block_6
  wellFormedTest_14336_block_7)))
  (interval_append wellFormedTest_14336 128 192 256
  (interval_append wellFormedTest_14336 128 160 192
  (interval_append wellFormedTest_14336 128 144 160
  wellFormedTest_14336_block_8
  wellFormedTest_14336_block_9)
  (interval_append wellFormedTest_14336 160 176 192
  wellFormedTest_14336_block_10
  wellFormedTest_14336_block_11))
  (interval_append wellFormedTest_14336 192 224 256
  (interval_append wellFormedTest_14336 192 208 224
  wellFormedTest_14336_block_12
  wellFormedTest_14336_block_13)
  (interval_append wellFormedTest_14336 224 240 256
  wellFormedTest_14336_block_14
  wellFormedTest_14336_block_15))))
theorem wellFormedTestInterval14336 : Interval wellFormedTest 14336 14592 := by
  intro i hlo hhi
  have h := wellFormedTest_14336_complete (i-14336) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_14336, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed057 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_14592 (i : Nat) := wellFormedTest (i+14592)
theorem wellFormedTest_14592_block_0 : Interval wellFormedTest_14592 0 16 :=
  interval_of_check wellFormedTest_14592 0 16 (by decide +kernel)

theorem wellFormedTest_14592_block_1 : Interval wellFormedTest_14592 16 32 :=
  interval_of_check wellFormedTest_14592 16 16 (by decide +kernel)

theorem wellFormedTest_14592_block_2 : Interval wellFormedTest_14592 32 48 :=
  interval_of_check wellFormedTest_14592 32 16 (by decide +kernel)

theorem wellFormedTest_14592_block_3 : Interval wellFormedTest_14592 48 64 :=
  interval_of_check wellFormedTest_14592 48 16 (by decide +kernel)

theorem wellFormedTest_14592_block_4 : Interval wellFormedTest_14592 64 80 :=
  interval_of_check wellFormedTest_14592 64 16 (by decide +kernel)

theorem wellFormedTest_14592_block_5 : Interval wellFormedTest_14592 80 96 :=
  interval_of_check wellFormedTest_14592 80 16 (by decide +kernel)

theorem wellFormedTest_14592_block_6 : Interval wellFormedTest_14592 96 112 :=
  interval_of_check wellFormedTest_14592 96 16 (by decide +kernel)

theorem wellFormedTest_14592_block_7 : Interval wellFormedTest_14592 112 128 :=
  interval_of_check wellFormedTest_14592 112 16 (by decide +kernel)

theorem wellFormedTest_14592_block_8 : Interval wellFormedTest_14592 128 144 :=
  interval_of_check wellFormedTest_14592 128 16 (by decide +kernel)

theorem wellFormedTest_14592_block_9 : Interval wellFormedTest_14592 144 160 :=
  interval_of_check wellFormedTest_14592 144 16 (by decide +kernel)

theorem wellFormedTest_14592_block_10 : Interval wellFormedTest_14592 160 176 :=
  interval_of_check wellFormedTest_14592 160 16 (by decide +kernel)

theorem wellFormedTest_14592_block_11 : Interval wellFormedTest_14592 176 192 :=
  interval_of_check wellFormedTest_14592 176 16 (by decide +kernel)

theorem wellFormedTest_14592_block_12 : Interval wellFormedTest_14592 192 208 :=
  interval_of_check wellFormedTest_14592 192 16 (by decide +kernel)

theorem wellFormedTest_14592_block_13 : Interval wellFormedTest_14592 208 224 :=
  interval_of_check wellFormedTest_14592 208 16 (by decide +kernel)

theorem wellFormedTest_14592_block_14 : Interval wellFormedTest_14592 224 240 :=
  interval_of_check wellFormedTest_14592 224 16 (by decide +kernel)

theorem wellFormedTest_14592_block_15 : Interval wellFormedTest_14592 240 256 :=
  interval_of_check wellFormedTest_14592 240 16 (by decide +kernel)

theorem wellFormedTest_14592_complete : Interval wellFormedTest_14592 0 256 :=
  (interval_append wellFormedTest_14592 0 128 256
  (interval_append wellFormedTest_14592 0 64 128
  (interval_append wellFormedTest_14592 0 32 64
  (interval_append wellFormedTest_14592 0 16 32
  wellFormedTest_14592_block_0
  wellFormedTest_14592_block_1)
  (interval_append wellFormedTest_14592 32 48 64
  wellFormedTest_14592_block_2
  wellFormedTest_14592_block_3))
  (interval_append wellFormedTest_14592 64 96 128
  (interval_append wellFormedTest_14592 64 80 96
  wellFormedTest_14592_block_4
  wellFormedTest_14592_block_5)
  (interval_append wellFormedTest_14592 96 112 128
  wellFormedTest_14592_block_6
  wellFormedTest_14592_block_7)))
  (interval_append wellFormedTest_14592 128 192 256
  (interval_append wellFormedTest_14592 128 160 192
  (interval_append wellFormedTest_14592 128 144 160
  wellFormedTest_14592_block_8
  wellFormedTest_14592_block_9)
  (interval_append wellFormedTest_14592 160 176 192
  wellFormedTest_14592_block_10
  wellFormedTest_14592_block_11))
  (interval_append wellFormedTest_14592 192 224 256
  (interval_append wellFormedTest_14592 192 208 224
  wellFormedTest_14592_block_12
  wellFormedTest_14592_block_13)
  (interval_append wellFormedTest_14592 224 240 256
  wellFormedTest_14592_block_14
  wellFormedTest_14592_block_15))))
theorem wellFormedTestInterval14592 : Interval wellFormedTest 14592 14848 := by
  intro i hlo hhi
  have h := wellFormedTest_14592_complete (i-14592) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_14592, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed058 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_14848 (i : Nat) := wellFormedTest (i+14848)
theorem wellFormedTest_14848_block_0 : Interval wellFormedTest_14848 0 16 :=
  interval_of_check wellFormedTest_14848 0 16 (by decide +kernel)

theorem wellFormedTest_14848_block_1 : Interval wellFormedTest_14848 16 32 :=
  interval_of_check wellFormedTest_14848 16 16 (by decide +kernel)

theorem wellFormedTest_14848_block_2 : Interval wellFormedTest_14848 32 48 :=
  interval_of_check wellFormedTest_14848 32 16 (by decide +kernel)

theorem wellFormedTest_14848_block_3 : Interval wellFormedTest_14848 48 64 :=
  interval_of_check wellFormedTest_14848 48 16 (by decide +kernel)

theorem wellFormedTest_14848_block_4 : Interval wellFormedTest_14848 64 80 :=
  interval_of_check wellFormedTest_14848 64 16 (by decide +kernel)

theorem wellFormedTest_14848_block_5 : Interval wellFormedTest_14848 80 96 :=
  interval_of_check wellFormedTest_14848 80 16 (by decide +kernel)

theorem wellFormedTest_14848_block_6 : Interval wellFormedTest_14848 96 112 :=
  interval_of_check wellFormedTest_14848 96 16 (by decide +kernel)

theorem wellFormedTest_14848_block_7 : Interval wellFormedTest_14848 112 128 :=
  interval_of_check wellFormedTest_14848 112 16 (by decide +kernel)

theorem wellFormedTest_14848_block_8 : Interval wellFormedTest_14848 128 144 :=
  interval_of_check wellFormedTest_14848 128 16 (by decide +kernel)

theorem wellFormedTest_14848_block_9 : Interval wellFormedTest_14848 144 160 :=
  interval_of_check wellFormedTest_14848 144 16 (by decide +kernel)

theorem wellFormedTest_14848_block_10 : Interval wellFormedTest_14848 160 176 :=
  interval_of_check wellFormedTest_14848 160 16 (by decide +kernel)

theorem wellFormedTest_14848_block_11 : Interval wellFormedTest_14848 176 192 :=
  interval_of_check wellFormedTest_14848 176 16 (by decide +kernel)

theorem wellFormedTest_14848_block_12 : Interval wellFormedTest_14848 192 208 :=
  interval_of_check wellFormedTest_14848 192 16 (by decide +kernel)

theorem wellFormedTest_14848_block_13 : Interval wellFormedTest_14848 208 224 :=
  interval_of_check wellFormedTest_14848 208 16 (by decide +kernel)

theorem wellFormedTest_14848_block_14 : Interval wellFormedTest_14848 224 240 :=
  interval_of_check wellFormedTest_14848 224 16 (by decide +kernel)

theorem wellFormedTest_14848_block_15 : Interval wellFormedTest_14848 240 256 :=
  interval_of_check wellFormedTest_14848 240 16 (by decide +kernel)

theorem wellFormedTest_14848_complete : Interval wellFormedTest_14848 0 256 :=
  (interval_append wellFormedTest_14848 0 128 256
  (interval_append wellFormedTest_14848 0 64 128
  (interval_append wellFormedTest_14848 0 32 64
  (interval_append wellFormedTest_14848 0 16 32
  wellFormedTest_14848_block_0
  wellFormedTest_14848_block_1)
  (interval_append wellFormedTest_14848 32 48 64
  wellFormedTest_14848_block_2
  wellFormedTest_14848_block_3))
  (interval_append wellFormedTest_14848 64 96 128
  (interval_append wellFormedTest_14848 64 80 96
  wellFormedTest_14848_block_4
  wellFormedTest_14848_block_5)
  (interval_append wellFormedTest_14848 96 112 128
  wellFormedTest_14848_block_6
  wellFormedTest_14848_block_7)))
  (interval_append wellFormedTest_14848 128 192 256
  (interval_append wellFormedTest_14848 128 160 192
  (interval_append wellFormedTest_14848 128 144 160
  wellFormedTest_14848_block_8
  wellFormedTest_14848_block_9)
  (interval_append wellFormedTest_14848 160 176 192
  wellFormedTest_14848_block_10
  wellFormedTest_14848_block_11))
  (interval_append wellFormedTest_14848 192 224 256
  (interval_append wellFormedTest_14848 192 208 224
  wellFormedTest_14848_block_12
  wellFormedTest_14848_block_13)
  (interval_append wellFormedTest_14848 224 240 256
  wellFormedTest_14848_block_14
  wellFormedTest_14848_block_15))))
theorem wellFormedTestInterval14848 : Interval wellFormedTest 14848 15104 := by
  intro i hlo hhi
  have h := wellFormedTest_14848_complete (i-14848) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_14848, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed059 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_15104 (i : Nat) := wellFormedTest (i+15104)
theorem wellFormedTest_15104_block_0 : Interval wellFormedTest_15104 0 16 :=
  interval_of_check wellFormedTest_15104 0 16 (by decide +kernel)

theorem wellFormedTest_15104_block_1 : Interval wellFormedTest_15104 16 32 :=
  interval_of_check wellFormedTest_15104 16 16 (by decide +kernel)

theorem wellFormedTest_15104_block_2 : Interval wellFormedTest_15104 32 48 :=
  interval_of_check wellFormedTest_15104 32 16 (by decide +kernel)

theorem wellFormedTest_15104_block_3 : Interval wellFormedTest_15104 48 64 :=
  interval_of_check wellFormedTest_15104 48 16 (by decide +kernel)

theorem wellFormedTest_15104_block_4 : Interval wellFormedTest_15104 64 80 :=
  interval_of_check wellFormedTest_15104 64 16 (by decide +kernel)

theorem wellFormedTest_15104_block_5 : Interval wellFormedTest_15104 80 96 :=
  interval_of_check wellFormedTest_15104 80 16 (by decide +kernel)

theorem wellFormedTest_15104_block_6 : Interval wellFormedTest_15104 96 112 :=
  interval_of_check wellFormedTest_15104 96 16 (by decide +kernel)

theorem wellFormedTest_15104_block_7 : Interval wellFormedTest_15104 112 128 :=
  interval_of_check wellFormedTest_15104 112 16 (by decide +kernel)

theorem wellFormedTest_15104_block_8 : Interval wellFormedTest_15104 128 144 :=
  interval_of_check wellFormedTest_15104 128 16 (by decide +kernel)

theorem wellFormedTest_15104_block_9 : Interval wellFormedTest_15104 144 160 :=
  interval_of_check wellFormedTest_15104 144 16 (by decide +kernel)

theorem wellFormedTest_15104_block_10 : Interval wellFormedTest_15104 160 176 :=
  interval_of_check wellFormedTest_15104 160 16 (by decide +kernel)

theorem wellFormedTest_15104_block_11 : Interval wellFormedTest_15104 176 192 :=
  interval_of_check wellFormedTest_15104 176 16 (by decide +kernel)

theorem wellFormedTest_15104_block_12 : Interval wellFormedTest_15104 192 208 :=
  interval_of_check wellFormedTest_15104 192 16 (by decide +kernel)

theorem wellFormedTest_15104_block_13 : Interval wellFormedTest_15104 208 224 :=
  interval_of_check wellFormedTest_15104 208 16 (by decide +kernel)

theorem wellFormedTest_15104_block_14 : Interval wellFormedTest_15104 224 240 :=
  interval_of_check wellFormedTest_15104 224 16 (by decide +kernel)

theorem wellFormedTest_15104_block_15 : Interval wellFormedTest_15104 240 256 :=
  interval_of_check wellFormedTest_15104 240 16 (by decide +kernel)

theorem wellFormedTest_15104_complete : Interval wellFormedTest_15104 0 256 :=
  (interval_append wellFormedTest_15104 0 128 256
  (interval_append wellFormedTest_15104 0 64 128
  (interval_append wellFormedTest_15104 0 32 64
  (interval_append wellFormedTest_15104 0 16 32
  wellFormedTest_15104_block_0
  wellFormedTest_15104_block_1)
  (interval_append wellFormedTest_15104 32 48 64
  wellFormedTest_15104_block_2
  wellFormedTest_15104_block_3))
  (interval_append wellFormedTest_15104 64 96 128
  (interval_append wellFormedTest_15104 64 80 96
  wellFormedTest_15104_block_4
  wellFormedTest_15104_block_5)
  (interval_append wellFormedTest_15104 96 112 128
  wellFormedTest_15104_block_6
  wellFormedTest_15104_block_7)))
  (interval_append wellFormedTest_15104 128 192 256
  (interval_append wellFormedTest_15104 128 160 192
  (interval_append wellFormedTest_15104 128 144 160
  wellFormedTest_15104_block_8
  wellFormedTest_15104_block_9)
  (interval_append wellFormedTest_15104 160 176 192
  wellFormedTest_15104_block_10
  wellFormedTest_15104_block_11))
  (interval_append wellFormedTest_15104 192 224 256
  (interval_append wellFormedTest_15104 192 208 224
  wellFormedTest_15104_block_12
  wellFormedTest_15104_block_13)
  (interval_append wellFormedTest_15104 224 240 256
  wellFormedTest_15104_block_14
  wellFormedTest_15104_block_15))))
theorem wellFormedTestInterval15104 : Interval wellFormedTest 15104 15360 := by
  intro i hlo hhi
  have h := wellFormedTest_15104_complete (i-15104) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_15104, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed060 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_15360 (i : Nat) := wellFormedTest (i+15360)
theorem wellFormedTest_15360_block_0 : Interval wellFormedTest_15360 0 16 :=
  interval_of_check wellFormedTest_15360 0 16 (by decide +kernel)

theorem wellFormedTest_15360_block_1 : Interval wellFormedTest_15360 16 32 :=
  interval_of_check wellFormedTest_15360 16 16 (by decide +kernel)

theorem wellFormedTest_15360_block_2 : Interval wellFormedTest_15360 32 48 :=
  interval_of_check wellFormedTest_15360 32 16 (by decide +kernel)

theorem wellFormedTest_15360_block_3 : Interval wellFormedTest_15360 48 64 :=
  interval_of_check wellFormedTest_15360 48 16 (by decide +kernel)

theorem wellFormedTest_15360_block_4 : Interval wellFormedTest_15360 64 80 :=
  interval_of_check wellFormedTest_15360 64 16 (by decide +kernel)

theorem wellFormedTest_15360_block_5 : Interval wellFormedTest_15360 80 96 :=
  interval_of_check wellFormedTest_15360 80 16 (by decide +kernel)

theorem wellFormedTest_15360_block_6 : Interval wellFormedTest_15360 96 112 :=
  interval_of_check wellFormedTest_15360 96 16 (by decide +kernel)

theorem wellFormedTest_15360_block_7 : Interval wellFormedTest_15360 112 128 :=
  interval_of_check wellFormedTest_15360 112 16 (by decide +kernel)

theorem wellFormedTest_15360_block_8 : Interval wellFormedTest_15360 128 144 :=
  interval_of_check wellFormedTest_15360 128 16 (by decide +kernel)

theorem wellFormedTest_15360_block_9 : Interval wellFormedTest_15360 144 160 :=
  interval_of_check wellFormedTest_15360 144 16 (by decide +kernel)

theorem wellFormedTest_15360_block_10 : Interval wellFormedTest_15360 160 176 :=
  interval_of_check wellFormedTest_15360 160 16 (by decide +kernel)

theorem wellFormedTest_15360_block_11 : Interval wellFormedTest_15360 176 192 :=
  interval_of_check wellFormedTest_15360 176 16 (by decide +kernel)

theorem wellFormedTest_15360_block_12 : Interval wellFormedTest_15360 192 208 :=
  interval_of_check wellFormedTest_15360 192 16 (by decide +kernel)

theorem wellFormedTest_15360_block_13 : Interval wellFormedTest_15360 208 224 :=
  interval_of_check wellFormedTest_15360 208 16 (by decide +kernel)

theorem wellFormedTest_15360_block_14 : Interval wellFormedTest_15360 224 240 :=
  interval_of_check wellFormedTest_15360 224 16 (by decide +kernel)

theorem wellFormedTest_15360_block_15 : Interval wellFormedTest_15360 240 256 :=
  interval_of_check wellFormedTest_15360 240 16 (by decide +kernel)

theorem wellFormedTest_15360_complete : Interval wellFormedTest_15360 0 256 :=
  (interval_append wellFormedTest_15360 0 128 256
  (interval_append wellFormedTest_15360 0 64 128
  (interval_append wellFormedTest_15360 0 32 64
  (interval_append wellFormedTest_15360 0 16 32
  wellFormedTest_15360_block_0
  wellFormedTest_15360_block_1)
  (interval_append wellFormedTest_15360 32 48 64
  wellFormedTest_15360_block_2
  wellFormedTest_15360_block_3))
  (interval_append wellFormedTest_15360 64 96 128
  (interval_append wellFormedTest_15360 64 80 96
  wellFormedTest_15360_block_4
  wellFormedTest_15360_block_5)
  (interval_append wellFormedTest_15360 96 112 128
  wellFormedTest_15360_block_6
  wellFormedTest_15360_block_7)))
  (interval_append wellFormedTest_15360 128 192 256
  (interval_append wellFormedTest_15360 128 160 192
  (interval_append wellFormedTest_15360 128 144 160
  wellFormedTest_15360_block_8
  wellFormedTest_15360_block_9)
  (interval_append wellFormedTest_15360 160 176 192
  wellFormedTest_15360_block_10
  wellFormedTest_15360_block_11))
  (interval_append wellFormedTest_15360 192 224 256
  (interval_append wellFormedTest_15360 192 208 224
  wellFormedTest_15360_block_12
  wellFormedTest_15360_block_13)
  (interval_append wellFormedTest_15360 224 240 256
  wellFormedTest_15360_block_14
  wellFormedTest_15360_block_15))))
theorem wellFormedTestInterval15360 : Interval wellFormedTest 15360 15616 := by
  intro i hlo hhi
  have h := wellFormedTest_15360_complete (i-15360) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_15360, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed061 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_15616 (i : Nat) := wellFormedTest (i+15616)
theorem wellFormedTest_15616_block_0 : Interval wellFormedTest_15616 0 16 :=
  interval_of_check wellFormedTest_15616 0 16 (by decide +kernel)

theorem wellFormedTest_15616_block_1 : Interval wellFormedTest_15616 16 32 :=
  interval_of_check wellFormedTest_15616 16 16 (by decide +kernel)

theorem wellFormedTest_15616_block_2 : Interval wellFormedTest_15616 32 48 :=
  interval_of_check wellFormedTest_15616 32 16 (by decide +kernel)

theorem wellFormedTest_15616_block_3 : Interval wellFormedTest_15616 48 64 :=
  interval_of_check wellFormedTest_15616 48 16 (by decide +kernel)

theorem wellFormedTest_15616_block_4 : Interval wellFormedTest_15616 64 80 :=
  interval_of_check wellFormedTest_15616 64 16 (by decide +kernel)

theorem wellFormedTest_15616_block_5 : Interval wellFormedTest_15616 80 96 :=
  interval_of_check wellFormedTest_15616 80 16 (by decide +kernel)

theorem wellFormedTest_15616_block_6 : Interval wellFormedTest_15616 96 112 :=
  interval_of_check wellFormedTest_15616 96 16 (by decide +kernel)

theorem wellFormedTest_15616_block_7 : Interval wellFormedTest_15616 112 128 :=
  interval_of_check wellFormedTest_15616 112 16 (by decide +kernel)

theorem wellFormedTest_15616_block_8 : Interval wellFormedTest_15616 128 144 :=
  interval_of_check wellFormedTest_15616 128 16 (by decide +kernel)

theorem wellFormedTest_15616_block_9 : Interval wellFormedTest_15616 144 160 :=
  interval_of_check wellFormedTest_15616 144 16 (by decide +kernel)

theorem wellFormedTest_15616_block_10 : Interval wellFormedTest_15616 160 176 :=
  interval_of_check wellFormedTest_15616 160 16 (by decide +kernel)

theorem wellFormedTest_15616_block_11 : Interval wellFormedTest_15616 176 192 :=
  interval_of_check wellFormedTest_15616 176 16 (by decide +kernel)

theorem wellFormedTest_15616_block_12 : Interval wellFormedTest_15616 192 208 :=
  interval_of_check wellFormedTest_15616 192 16 (by decide +kernel)

theorem wellFormedTest_15616_block_13 : Interval wellFormedTest_15616 208 224 :=
  interval_of_check wellFormedTest_15616 208 16 (by decide +kernel)

theorem wellFormedTest_15616_block_14 : Interval wellFormedTest_15616 224 240 :=
  interval_of_check wellFormedTest_15616 224 16 (by decide +kernel)

theorem wellFormedTest_15616_block_15 : Interval wellFormedTest_15616 240 256 :=
  interval_of_check wellFormedTest_15616 240 16 (by decide +kernel)

theorem wellFormedTest_15616_complete : Interval wellFormedTest_15616 0 256 :=
  (interval_append wellFormedTest_15616 0 128 256
  (interval_append wellFormedTest_15616 0 64 128
  (interval_append wellFormedTest_15616 0 32 64
  (interval_append wellFormedTest_15616 0 16 32
  wellFormedTest_15616_block_0
  wellFormedTest_15616_block_1)
  (interval_append wellFormedTest_15616 32 48 64
  wellFormedTest_15616_block_2
  wellFormedTest_15616_block_3))
  (interval_append wellFormedTest_15616 64 96 128
  (interval_append wellFormedTest_15616 64 80 96
  wellFormedTest_15616_block_4
  wellFormedTest_15616_block_5)
  (interval_append wellFormedTest_15616 96 112 128
  wellFormedTest_15616_block_6
  wellFormedTest_15616_block_7)))
  (interval_append wellFormedTest_15616 128 192 256
  (interval_append wellFormedTest_15616 128 160 192
  (interval_append wellFormedTest_15616 128 144 160
  wellFormedTest_15616_block_8
  wellFormedTest_15616_block_9)
  (interval_append wellFormedTest_15616 160 176 192
  wellFormedTest_15616_block_10
  wellFormedTest_15616_block_11))
  (interval_append wellFormedTest_15616 192 224 256
  (interval_append wellFormedTest_15616 192 208 224
  wellFormedTest_15616_block_12
  wellFormedTest_15616_block_13)
  (interval_append wellFormedTest_15616 224 240 256
  wellFormedTest_15616_block_14
  wellFormedTest_15616_block_15))))
theorem wellFormedTestInterval15616 : Interval wellFormedTest 15616 15872 := by
  intro i hlo hhi
  have h := wellFormedTest_15616_complete (i-15616) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_15616, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed062 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_15872 (i : Nat) := wellFormedTest (i+15872)
theorem wellFormedTest_15872_block_0 : Interval wellFormedTest_15872 0 16 :=
  interval_of_check wellFormedTest_15872 0 16 (by decide +kernel)

theorem wellFormedTest_15872_block_1 : Interval wellFormedTest_15872 16 32 :=
  interval_of_check wellFormedTest_15872 16 16 (by decide +kernel)

theorem wellFormedTest_15872_block_2 : Interval wellFormedTest_15872 32 48 :=
  interval_of_check wellFormedTest_15872 32 16 (by decide +kernel)

theorem wellFormedTest_15872_block_3 : Interval wellFormedTest_15872 48 64 :=
  interval_of_check wellFormedTest_15872 48 16 (by decide +kernel)

theorem wellFormedTest_15872_block_4 : Interval wellFormedTest_15872 64 80 :=
  interval_of_check wellFormedTest_15872 64 16 (by decide +kernel)

theorem wellFormedTest_15872_block_5 : Interval wellFormedTest_15872 80 96 :=
  interval_of_check wellFormedTest_15872 80 16 (by decide +kernel)

theorem wellFormedTest_15872_block_6 : Interval wellFormedTest_15872 96 112 :=
  interval_of_check wellFormedTest_15872 96 16 (by decide +kernel)

theorem wellFormedTest_15872_block_7 : Interval wellFormedTest_15872 112 128 :=
  interval_of_check wellFormedTest_15872 112 16 (by decide +kernel)

theorem wellFormedTest_15872_block_8 : Interval wellFormedTest_15872 128 144 :=
  interval_of_check wellFormedTest_15872 128 16 (by decide +kernel)

theorem wellFormedTest_15872_block_9 : Interval wellFormedTest_15872 144 160 :=
  interval_of_check wellFormedTest_15872 144 16 (by decide +kernel)

theorem wellFormedTest_15872_block_10 : Interval wellFormedTest_15872 160 176 :=
  interval_of_check wellFormedTest_15872 160 16 (by decide +kernel)

theorem wellFormedTest_15872_block_11 : Interval wellFormedTest_15872 176 192 :=
  interval_of_check wellFormedTest_15872 176 16 (by decide +kernel)

theorem wellFormedTest_15872_block_12 : Interval wellFormedTest_15872 192 208 :=
  interval_of_check wellFormedTest_15872 192 16 (by decide +kernel)

theorem wellFormedTest_15872_block_13 : Interval wellFormedTest_15872 208 224 :=
  interval_of_check wellFormedTest_15872 208 16 (by decide +kernel)

theorem wellFormedTest_15872_block_14 : Interval wellFormedTest_15872 224 240 :=
  interval_of_check wellFormedTest_15872 224 16 (by decide +kernel)

theorem wellFormedTest_15872_block_15 : Interval wellFormedTest_15872 240 256 :=
  interval_of_check wellFormedTest_15872 240 16 (by decide +kernel)

theorem wellFormedTest_15872_complete : Interval wellFormedTest_15872 0 256 :=
  (interval_append wellFormedTest_15872 0 128 256
  (interval_append wellFormedTest_15872 0 64 128
  (interval_append wellFormedTest_15872 0 32 64
  (interval_append wellFormedTest_15872 0 16 32
  wellFormedTest_15872_block_0
  wellFormedTest_15872_block_1)
  (interval_append wellFormedTest_15872 32 48 64
  wellFormedTest_15872_block_2
  wellFormedTest_15872_block_3))
  (interval_append wellFormedTest_15872 64 96 128
  (interval_append wellFormedTest_15872 64 80 96
  wellFormedTest_15872_block_4
  wellFormedTest_15872_block_5)
  (interval_append wellFormedTest_15872 96 112 128
  wellFormedTest_15872_block_6
  wellFormedTest_15872_block_7)))
  (interval_append wellFormedTest_15872 128 192 256
  (interval_append wellFormedTest_15872 128 160 192
  (interval_append wellFormedTest_15872 128 144 160
  wellFormedTest_15872_block_8
  wellFormedTest_15872_block_9)
  (interval_append wellFormedTest_15872 160 176 192
  wellFormedTest_15872_block_10
  wellFormedTest_15872_block_11))
  (interval_append wellFormedTest_15872 192 224 256
  (interval_append wellFormedTest_15872 192 208 224
  wellFormedTest_15872_block_12
  wellFormedTest_15872_block_13)
  (interval_append wellFormedTest_15872 224 240 256
  wellFormedTest_15872_block_14
  wellFormedTest_15872_block_15))))
theorem wellFormedTestInterval15872 : Interval wellFormedTest 15872 16128 := by
  intro i hlo hhi
  have h := wellFormedTest_15872_complete (i-15872) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_15872, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed063 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_16128 (i : Nat) := wellFormedTest (i+16128)
theorem wellFormedTest_16128_block_0 : Interval wellFormedTest_16128 0 16 :=
  interval_of_check wellFormedTest_16128 0 16 (by decide +kernel)

theorem wellFormedTest_16128_block_1 : Interval wellFormedTest_16128 16 32 :=
  interval_of_check wellFormedTest_16128 16 16 (by decide +kernel)

theorem wellFormedTest_16128_block_2 : Interval wellFormedTest_16128 32 48 :=
  interval_of_check wellFormedTest_16128 32 16 (by decide +kernel)

theorem wellFormedTest_16128_block_3 : Interval wellFormedTest_16128 48 64 :=
  interval_of_check wellFormedTest_16128 48 16 (by decide +kernel)

theorem wellFormedTest_16128_block_4 : Interval wellFormedTest_16128 64 80 :=
  interval_of_check wellFormedTest_16128 64 16 (by decide +kernel)

theorem wellFormedTest_16128_block_5 : Interval wellFormedTest_16128 80 96 :=
  interval_of_check wellFormedTest_16128 80 16 (by decide +kernel)

theorem wellFormedTest_16128_block_6 : Interval wellFormedTest_16128 96 112 :=
  interval_of_check wellFormedTest_16128 96 16 (by decide +kernel)

theorem wellFormedTest_16128_block_7 : Interval wellFormedTest_16128 112 128 :=
  interval_of_check wellFormedTest_16128 112 16 (by decide +kernel)

theorem wellFormedTest_16128_block_8 : Interval wellFormedTest_16128 128 144 :=
  interval_of_check wellFormedTest_16128 128 16 (by decide +kernel)

theorem wellFormedTest_16128_block_9 : Interval wellFormedTest_16128 144 160 :=
  interval_of_check wellFormedTest_16128 144 16 (by decide +kernel)

theorem wellFormedTest_16128_block_10 : Interval wellFormedTest_16128 160 176 :=
  interval_of_check wellFormedTest_16128 160 16 (by decide +kernel)

theorem wellFormedTest_16128_block_11 : Interval wellFormedTest_16128 176 192 :=
  interval_of_check wellFormedTest_16128 176 16 (by decide +kernel)

theorem wellFormedTest_16128_block_12 : Interval wellFormedTest_16128 192 208 :=
  interval_of_check wellFormedTest_16128 192 16 (by decide +kernel)

theorem wellFormedTest_16128_block_13 : Interval wellFormedTest_16128 208 224 :=
  interval_of_check wellFormedTest_16128 208 16 (by decide +kernel)

theorem wellFormedTest_16128_block_14 : Interval wellFormedTest_16128 224 240 :=
  interval_of_check wellFormedTest_16128 224 16 (by decide +kernel)

theorem wellFormedTest_16128_block_15 : Interval wellFormedTest_16128 240 256 :=
  interval_of_check wellFormedTest_16128 240 16 (by decide +kernel)

theorem wellFormedTest_16128_complete : Interval wellFormedTest_16128 0 256 :=
  (interval_append wellFormedTest_16128 0 128 256
  (interval_append wellFormedTest_16128 0 64 128
  (interval_append wellFormedTest_16128 0 32 64
  (interval_append wellFormedTest_16128 0 16 32
  wellFormedTest_16128_block_0
  wellFormedTest_16128_block_1)
  (interval_append wellFormedTest_16128 32 48 64
  wellFormedTest_16128_block_2
  wellFormedTest_16128_block_3))
  (interval_append wellFormedTest_16128 64 96 128
  (interval_append wellFormedTest_16128 64 80 96
  wellFormedTest_16128_block_4
  wellFormedTest_16128_block_5)
  (interval_append wellFormedTest_16128 96 112 128
  wellFormedTest_16128_block_6
  wellFormedTest_16128_block_7)))
  (interval_append wellFormedTest_16128 128 192 256
  (interval_append wellFormedTest_16128 128 160 192
  (interval_append wellFormedTest_16128 128 144 160
  wellFormedTest_16128_block_8
  wellFormedTest_16128_block_9)
  (interval_append wellFormedTest_16128 160 176 192
  wellFormedTest_16128_block_10
  wellFormedTest_16128_block_11))
  (interval_append wellFormedTest_16128 192 224 256
  (interval_append wellFormedTest_16128 192 208 224
  wellFormedTest_16128_block_12
  wellFormedTest_16128_block_13)
  (interval_append wellFormedTest_16128 224 240 256
  wellFormedTest_16128_block_14
  wellFormedTest_16128_block_15))))
theorem wellFormedTestInterval16128 : Interval wellFormedTest 16128 16384 := by
  intro i hlo hhi
  have h := wellFormedTest_16128_complete (i-16128) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_16128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed064 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_16384 (i : Nat) := wellFormedTest (i+16384)
theorem wellFormedTest_16384_block_0 : Interval wellFormedTest_16384 0 16 :=
  interval_of_check wellFormedTest_16384 0 16 (by decide +kernel)

theorem wellFormedTest_16384_block_1 : Interval wellFormedTest_16384 16 32 :=
  interval_of_check wellFormedTest_16384 16 16 (by decide +kernel)

theorem wellFormedTest_16384_block_2 : Interval wellFormedTest_16384 32 48 :=
  interval_of_check wellFormedTest_16384 32 16 (by decide +kernel)

theorem wellFormedTest_16384_block_3 : Interval wellFormedTest_16384 48 64 :=
  interval_of_check wellFormedTest_16384 48 16 (by decide +kernel)

theorem wellFormedTest_16384_block_4 : Interval wellFormedTest_16384 64 80 :=
  interval_of_check wellFormedTest_16384 64 16 (by decide +kernel)

theorem wellFormedTest_16384_block_5 : Interval wellFormedTest_16384 80 96 :=
  interval_of_check wellFormedTest_16384 80 16 (by decide +kernel)

theorem wellFormedTest_16384_block_6 : Interval wellFormedTest_16384 96 112 :=
  interval_of_check wellFormedTest_16384 96 16 (by decide +kernel)

theorem wellFormedTest_16384_block_7 : Interval wellFormedTest_16384 112 128 :=
  interval_of_check wellFormedTest_16384 112 16 (by decide +kernel)

theorem wellFormedTest_16384_block_8 : Interval wellFormedTest_16384 128 144 :=
  interval_of_check wellFormedTest_16384 128 16 (by decide +kernel)

theorem wellFormedTest_16384_block_9 : Interval wellFormedTest_16384 144 160 :=
  interval_of_check wellFormedTest_16384 144 16 (by decide +kernel)

theorem wellFormedTest_16384_block_10 : Interval wellFormedTest_16384 160 176 :=
  interval_of_check wellFormedTest_16384 160 16 (by decide +kernel)

theorem wellFormedTest_16384_block_11 : Interval wellFormedTest_16384 176 192 :=
  interval_of_check wellFormedTest_16384 176 16 (by decide +kernel)

theorem wellFormedTest_16384_block_12 : Interval wellFormedTest_16384 192 208 :=
  interval_of_check wellFormedTest_16384 192 16 (by decide +kernel)

theorem wellFormedTest_16384_block_13 : Interval wellFormedTest_16384 208 224 :=
  interval_of_check wellFormedTest_16384 208 16 (by decide +kernel)

theorem wellFormedTest_16384_block_14 : Interval wellFormedTest_16384 224 240 :=
  interval_of_check wellFormedTest_16384 224 16 (by decide +kernel)

theorem wellFormedTest_16384_block_15 : Interval wellFormedTest_16384 240 256 :=
  interval_of_check wellFormedTest_16384 240 16 (by decide +kernel)

theorem wellFormedTest_16384_complete : Interval wellFormedTest_16384 0 256 :=
  (interval_append wellFormedTest_16384 0 128 256
  (interval_append wellFormedTest_16384 0 64 128
  (interval_append wellFormedTest_16384 0 32 64
  (interval_append wellFormedTest_16384 0 16 32
  wellFormedTest_16384_block_0
  wellFormedTest_16384_block_1)
  (interval_append wellFormedTest_16384 32 48 64
  wellFormedTest_16384_block_2
  wellFormedTest_16384_block_3))
  (interval_append wellFormedTest_16384 64 96 128
  (interval_append wellFormedTest_16384 64 80 96
  wellFormedTest_16384_block_4
  wellFormedTest_16384_block_5)
  (interval_append wellFormedTest_16384 96 112 128
  wellFormedTest_16384_block_6
  wellFormedTest_16384_block_7)))
  (interval_append wellFormedTest_16384 128 192 256
  (interval_append wellFormedTest_16384 128 160 192
  (interval_append wellFormedTest_16384 128 144 160
  wellFormedTest_16384_block_8
  wellFormedTest_16384_block_9)
  (interval_append wellFormedTest_16384 160 176 192
  wellFormedTest_16384_block_10
  wellFormedTest_16384_block_11))
  (interval_append wellFormedTest_16384 192 224 256
  (interval_append wellFormedTest_16384 192 208 224
  wellFormedTest_16384_block_12
  wellFormedTest_16384_block_13)
  (interval_append wellFormedTest_16384 224 240 256
  wellFormedTest_16384_block_14
  wellFormedTest_16384_block_15))))
theorem wellFormedTestInterval16384 : Interval wellFormedTest 16384 16640 := by
  intro i hlo hhi
  have h := wellFormedTest_16384_complete (i-16384) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_16384, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed065 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_16640 (i : Nat) := wellFormedTest (i+16640)
theorem wellFormedTest_16640_block_0 : Interval wellFormedTest_16640 0 16 :=
  interval_of_check wellFormedTest_16640 0 16 (by decide +kernel)

theorem wellFormedTest_16640_block_1 : Interval wellFormedTest_16640 16 32 :=
  interval_of_check wellFormedTest_16640 16 16 (by decide +kernel)

theorem wellFormedTest_16640_block_2 : Interval wellFormedTest_16640 32 48 :=
  interval_of_check wellFormedTest_16640 32 16 (by decide +kernel)

theorem wellFormedTest_16640_block_3 : Interval wellFormedTest_16640 48 64 :=
  interval_of_check wellFormedTest_16640 48 16 (by decide +kernel)

theorem wellFormedTest_16640_block_4 : Interval wellFormedTest_16640 64 80 :=
  interval_of_check wellFormedTest_16640 64 16 (by decide +kernel)

theorem wellFormedTest_16640_block_5 : Interval wellFormedTest_16640 80 96 :=
  interval_of_check wellFormedTest_16640 80 16 (by decide +kernel)

theorem wellFormedTest_16640_block_6 : Interval wellFormedTest_16640 96 112 :=
  interval_of_check wellFormedTest_16640 96 16 (by decide +kernel)

theorem wellFormedTest_16640_block_7 : Interval wellFormedTest_16640 112 128 :=
  interval_of_check wellFormedTest_16640 112 16 (by decide +kernel)

theorem wellFormedTest_16640_block_8 : Interval wellFormedTest_16640 128 144 :=
  interval_of_check wellFormedTest_16640 128 16 (by decide +kernel)

theorem wellFormedTest_16640_block_9 : Interval wellFormedTest_16640 144 160 :=
  interval_of_check wellFormedTest_16640 144 16 (by decide +kernel)

theorem wellFormedTest_16640_block_10 : Interval wellFormedTest_16640 160 176 :=
  interval_of_check wellFormedTest_16640 160 16 (by decide +kernel)

theorem wellFormedTest_16640_block_11 : Interval wellFormedTest_16640 176 192 :=
  interval_of_check wellFormedTest_16640 176 16 (by decide +kernel)

theorem wellFormedTest_16640_block_12 : Interval wellFormedTest_16640 192 208 :=
  interval_of_check wellFormedTest_16640 192 16 (by decide +kernel)

theorem wellFormedTest_16640_block_13 : Interval wellFormedTest_16640 208 224 :=
  interval_of_check wellFormedTest_16640 208 16 (by decide +kernel)

theorem wellFormedTest_16640_block_14 : Interval wellFormedTest_16640 224 240 :=
  interval_of_check wellFormedTest_16640 224 16 (by decide +kernel)

theorem wellFormedTest_16640_block_15 : Interval wellFormedTest_16640 240 256 :=
  interval_of_check wellFormedTest_16640 240 16 (by decide +kernel)

theorem wellFormedTest_16640_complete : Interval wellFormedTest_16640 0 256 :=
  (interval_append wellFormedTest_16640 0 128 256
  (interval_append wellFormedTest_16640 0 64 128
  (interval_append wellFormedTest_16640 0 32 64
  (interval_append wellFormedTest_16640 0 16 32
  wellFormedTest_16640_block_0
  wellFormedTest_16640_block_1)
  (interval_append wellFormedTest_16640 32 48 64
  wellFormedTest_16640_block_2
  wellFormedTest_16640_block_3))
  (interval_append wellFormedTest_16640 64 96 128
  (interval_append wellFormedTest_16640 64 80 96
  wellFormedTest_16640_block_4
  wellFormedTest_16640_block_5)
  (interval_append wellFormedTest_16640 96 112 128
  wellFormedTest_16640_block_6
  wellFormedTest_16640_block_7)))
  (interval_append wellFormedTest_16640 128 192 256
  (interval_append wellFormedTest_16640 128 160 192
  (interval_append wellFormedTest_16640 128 144 160
  wellFormedTest_16640_block_8
  wellFormedTest_16640_block_9)
  (interval_append wellFormedTest_16640 160 176 192
  wellFormedTest_16640_block_10
  wellFormedTest_16640_block_11))
  (interval_append wellFormedTest_16640 192 224 256
  (interval_append wellFormedTest_16640 192 208 224
  wellFormedTest_16640_block_12
  wellFormedTest_16640_block_13)
  (interval_append wellFormedTest_16640 224 240 256
  wellFormedTest_16640_block_14
  wellFormedTest_16640_block_15))))
theorem wellFormedTestInterval16640 : Interval wellFormedTest 16640 16896 := by
  intro i hlo hhi
  have h := wellFormedTest_16640_complete (i-16640) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_16640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed066 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_16896 (i : Nat) := wellFormedTest (i+16896)
theorem wellFormedTest_16896_block_0 : Interval wellFormedTest_16896 0 16 :=
  interval_of_check wellFormedTest_16896 0 16 (by decide +kernel)

theorem wellFormedTest_16896_block_1 : Interval wellFormedTest_16896 16 32 :=
  interval_of_check wellFormedTest_16896 16 16 (by decide +kernel)

theorem wellFormedTest_16896_block_2 : Interval wellFormedTest_16896 32 48 :=
  interval_of_check wellFormedTest_16896 32 16 (by decide +kernel)

theorem wellFormedTest_16896_block_3 : Interval wellFormedTest_16896 48 64 :=
  interval_of_check wellFormedTest_16896 48 16 (by decide +kernel)

theorem wellFormedTest_16896_block_4 : Interval wellFormedTest_16896 64 80 :=
  interval_of_check wellFormedTest_16896 64 16 (by decide +kernel)

theorem wellFormedTest_16896_block_5 : Interval wellFormedTest_16896 80 96 :=
  interval_of_check wellFormedTest_16896 80 16 (by decide +kernel)

theorem wellFormedTest_16896_block_6 : Interval wellFormedTest_16896 96 112 :=
  interval_of_check wellFormedTest_16896 96 16 (by decide +kernel)

theorem wellFormedTest_16896_block_7 : Interval wellFormedTest_16896 112 128 :=
  interval_of_check wellFormedTest_16896 112 16 (by decide +kernel)

theorem wellFormedTest_16896_block_8 : Interval wellFormedTest_16896 128 144 :=
  interval_of_check wellFormedTest_16896 128 16 (by decide +kernel)

theorem wellFormedTest_16896_block_9 : Interval wellFormedTest_16896 144 160 :=
  interval_of_check wellFormedTest_16896 144 16 (by decide +kernel)

theorem wellFormedTest_16896_block_10 : Interval wellFormedTest_16896 160 176 :=
  interval_of_check wellFormedTest_16896 160 16 (by decide +kernel)

theorem wellFormedTest_16896_block_11 : Interval wellFormedTest_16896 176 192 :=
  interval_of_check wellFormedTest_16896 176 16 (by decide +kernel)

theorem wellFormedTest_16896_block_12 : Interval wellFormedTest_16896 192 208 :=
  interval_of_check wellFormedTest_16896 192 16 (by decide +kernel)

theorem wellFormedTest_16896_block_13 : Interval wellFormedTest_16896 208 224 :=
  interval_of_check wellFormedTest_16896 208 16 (by decide +kernel)

theorem wellFormedTest_16896_block_14 : Interval wellFormedTest_16896 224 240 :=
  interval_of_check wellFormedTest_16896 224 16 (by decide +kernel)

theorem wellFormedTest_16896_block_15 : Interval wellFormedTest_16896 240 256 :=
  interval_of_check wellFormedTest_16896 240 16 (by decide +kernel)

theorem wellFormedTest_16896_complete : Interval wellFormedTest_16896 0 256 :=
  (interval_append wellFormedTest_16896 0 128 256
  (interval_append wellFormedTest_16896 0 64 128
  (interval_append wellFormedTest_16896 0 32 64
  (interval_append wellFormedTest_16896 0 16 32
  wellFormedTest_16896_block_0
  wellFormedTest_16896_block_1)
  (interval_append wellFormedTest_16896 32 48 64
  wellFormedTest_16896_block_2
  wellFormedTest_16896_block_3))
  (interval_append wellFormedTest_16896 64 96 128
  (interval_append wellFormedTest_16896 64 80 96
  wellFormedTest_16896_block_4
  wellFormedTest_16896_block_5)
  (interval_append wellFormedTest_16896 96 112 128
  wellFormedTest_16896_block_6
  wellFormedTest_16896_block_7)))
  (interval_append wellFormedTest_16896 128 192 256
  (interval_append wellFormedTest_16896 128 160 192
  (interval_append wellFormedTest_16896 128 144 160
  wellFormedTest_16896_block_8
  wellFormedTest_16896_block_9)
  (interval_append wellFormedTest_16896 160 176 192
  wellFormedTest_16896_block_10
  wellFormedTest_16896_block_11))
  (interval_append wellFormedTest_16896 192 224 256
  (interval_append wellFormedTest_16896 192 208 224
  wellFormedTest_16896_block_12
  wellFormedTest_16896_block_13)
  (interval_append wellFormedTest_16896 224 240 256
  wellFormedTest_16896_block_14
  wellFormedTest_16896_block_15))))
theorem wellFormedTestInterval16896 : Interval wellFormedTest 16896 17152 := by
  intro i hlo hhi
  have h := wellFormedTest_16896_complete (i-16896) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_16896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed067 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_17152 (i : Nat) := wellFormedTest (i+17152)
theorem wellFormedTest_17152_block_0 : Interval wellFormedTest_17152 0 16 :=
  interval_of_check wellFormedTest_17152 0 16 (by decide +kernel)

theorem wellFormedTest_17152_block_1 : Interval wellFormedTest_17152 16 32 :=
  interval_of_check wellFormedTest_17152 16 16 (by decide +kernel)

theorem wellFormedTest_17152_block_2 : Interval wellFormedTest_17152 32 48 :=
  interval_of_check wellFormedTest_17152 32 16 (by decide +kernel)

theorem wellFormedTest_17152_block_3 : Interval wellFormedTest_17152 48 64 :=
  interval_of_check wellFormedTest_17152 48 16 (by decide +kernel)

theorem wellFormedTest_17152_block_4 : Interval wellFormedTest_17152 64 80 :=
  interval_of_check wellFormedTest_17152 64 16 (by decide +kernel)

theorem wellFormedTest_17152_block_5 : Interval wellFormedTest_17152 80 96 :=
  interval_of_check wellFormedTest_17152 80 16 (by decide +kernel)

theorem wellFormedTest_17152_block_6 : Interval wellFormedTest_17152 96 112 :=
  interval_of_check wellFormedTest_17152 96 16 (by decide +kernel)

theorem wellFormedTest_17152_block_7 : Interval wellFormedTest_17152 112 128 :=
  interval_of_check wellFormedTest_17152 112 16 (by decide +kernel)

theorem wellFormedTest_17152_block_8 : Interval wellFormedTest_17152 128 144 :=
  interval_of_check wellFormedTest_17152 128 16 (by decide +kernel)

theorem wellFormedTest_17152_block_9 : Interval wellFormedTest_17152 144 160 :=
  interval_of_check wellFormedTest_17152 144 16 (by decide +kernel)

theorem wellFormedTest_17152_block_10 : Interval wellFormedTest_17152 160 176 :=
  interval_of_check wellFormedTest_17152 160 16 (by decide +kernel)

theorem wellFormedTest_17152_block_11 : Interval wellFormedTest_17152 176 192 :=
  interval_of_check wellFormedTest_17152 176 16 (by decide +kernel)

theorem wellFormedTest_17152_block_12 : Interval wellFormedTest_17152 192 208 :=
  interval_of_check wellFormedTest_17152 192 16 (by decide +kernel)

theorem wellFormedTest_17152_block_13 : Interval wellFormedTest_17152 208 224 :=
  interval_of_check wellFormedTest_17152 208 16 (by decide +kernel)

theorem wellFormedTest_17152_block_14 : Interval wellFormedTest_17152 224 240 :=
  interval_of_check wellFormedTest_17152 224 16 (by decide +kernel)

theorem wellFormedTest_17152_block_15 : Interval wellFormedTest_17152 240 256 :=
  interval_of_check wellFormedTest_17152 240 16 (by decide +kernel)

theorem wellFormedTest_17152_complete : Interval wellFormedTest_17152 0 256 :=
  (interval_append wellFormedTest_17152 0 128 256
  (interval_append wellFormedTest_17152 0 64 128
  (interval_append wellFormedTest_17152 0 32 64
  (interval_append wellFormedTest_17152 0 16 32
  wellFormedTest_17152_block_0
  wellFormedTest_17152_block_1)
  (interval_append wellFormedTest_17152 32 48 64
  wellFormedTest_17152_block_2
  wellFormedTest_17152_block_3))
  (interval_append wellFormedTest_17152 64 96 128
  (interval_append wellFormedTest_17152 64 80 96
  wellFormedTest_17152_block_4
  wellFormedTest_17152_block_5)
  (interval_append wellFormedTest_17152 96 112 128
  wellFormedTest_17152_block_6
  wellFormedTest_17152_block_7)))
  (interval_append wellFormedTest_17152 128 192 256
  (interval_append wellFormedTest_17152 128 160 192
  (interval_append wellFormedTest_17152 128 144 160
  wellFormedTest_17152_block_8
  wellFormedTest_17152_block_9)
  (interval_append wellFormedTest_17152 160 176 192
  wellFormedTest_17152_block_10
  wellFormedTest_17152_block_11))
  (interval_append wellFormedTest_17152 192 224 256
  (interval_append wellFormedTest_17152 192 208 224
  wellFormedTest_17152_block_12
  wellFormedTest_17152_block_13)
  (interval_append wellFormedTest_17152 224 240 256
  wellFormedTest_17152_block_14
  wellFormedTest_17152_block_15))))
theorem wellFormedTestInterval17152 : Interval wellFormedTest 17152 17408 := by
  intro i hlo hhi
  have h := wellFormedTest_17152_complete (i-17152) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_17152, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
