module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheWellFormed068 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_17408 (i : Nat) := wellFormedTest (i+17408)
theorem wellFormedTest_17408_block_0 : Interval wellFormedTest_17408 0 16 :=
  interval_of_check wellFormedTest_17408 0 16 (by decide +kernel)

theorem wellFormedTest_17408_block_1 : Interval wellFormedTest_17408 16 32 :=
  interval_of_check wellFormedTest_17408 16 16 (by decide +kernel)

theorem wellFormedTest_17408_block_2 : Interval wellFormedTest_17408 32 48 :=
  interval_of_check wellFormedTest_17408 32 16 (by decide +kernel)

theorem wellFormedTest_17408_block_3 : Interval wellFormedTest_17408 48 64 :=
  interval_of_check wellFormedTest_17408 48 16 (by decide +kernel)

theorem wellFormedTest_17408_block_4 : Interval wellFormedTest_17408 64 80 :=
  interval_of_check wellFormedTest_17408 64 16 (by decide +kernel)

theorem wellFormedTest_17408_block_5 : Interval wellFormedTest_17408 80 96 :=
  interval_of_check wellFormedTest_17408 80 16 (by decide +kernel)

theorem wellFormedTest_17408_block_6 : Interval wellFormedTest_17408 96 112 :=
  interval_of_check wellFormedTest_17408 96 16 (by decide +kernel)

theorem wellFormedTest_17408_block_7 : Interval wellFormedTest_17408 112 128 :=
  interval_of_check wellFormedTest_17408 112 16 (by decide +kernel)

theorem wellFormedTest_17408_block_8 : Interval wellFormedTest_17408 128 144 :=
  interval_of_check wellFormedTest_17408 128 16 (by decide +kernel)

theorem wellFormedTest_17408_block_9 : Interval wellFormedTest_17408 144 160 :=
  interval_of_check wellFormedTest_17408 144 16 (by decide +kernel)

theorem wellFormedTest_17408_block_10 : Interval wellFormedTest_17408 160 176 :=
  interval_of_check wellFormedTest_17408 160 16 (by decide +kernel)

theorem wellFormedTest_17408_block_11 : Interval wellFormedTest_17408 176 192 :=
  interval_of_check wellFormedTest_17408 176 16 (by decide +kernel)

theorem wellFormedTest_17408_block_12 : Interval wellFormedTest_17408 192 208 :=
  interval_of_check wellFormedTest_17408 192 16 (by decide +kernel)

theorem wellFormedTest_17408_block_13 : Interval wellFormedTest_17408 208 224 :=
  interval_of_check wellFormedTest_17408 208 16 (by decide +kernel)

theorem wellFormedTest_17408_block_14 : Interval wellFormedTest_17408 224 240 :=
  interval_of_check wellFormedTest_17408 224 16 (by decide +kernel)

theorem wellFormedTest_17408_block_15 : Interval wellFormedTest_17408 240 256 :=
  interval_of_check wellFormedTest_17408 240 16 (by decide +kernel)

theorem wellFormedTest_17408_complete : Interval wellFormedTest_17408 0 256 :=
  (interval_append wellFormedTest_17408 0 128 256
  (interval_append wellFormedTest_17408 0 64 128
  (interval_append wellFormedTest_17408 0 32 64
  (interval_append wellFormedTest_17408 0 16 32
  wellFormedTest_17408_block_0
  wellFormedTest_17408_block_1)
  (interval_append wellFormedTest_17408 32 48 64
  wellFormedTest_17408_block_2
  wellFormedTest_17408_block_3))
  (interval_append wellFormedTest_17408 64 96 128
  (interval_append wellFormedTest_17408 64 80 96
  wellFormedTest_17408_block_4
  wellFormedTest_17408_block_5)
  (interval_append wellFormedTest_17408 96 112 128
  wellFormedTest_17408_block_6
  wellFormedTest_17408_block_7)))
  (interval_append wellFormedTest_17408 128 192 256
  (interval_append wellFormedTest_17408 128 160 192
  (interval_append wellFormedTest_17408 128 144 160
  wellFormedTest_17408_block_8
  wellFormedTest_17408_block_9)
  (interval_append wellFormedTest_17408 160 176 192
  wellFormedTest_17408_block_10
  wellFormedTest_17408_block_11))
  (interval_append wellFormedTest_17408 192 224 256
  (interval_append wellFormedTest_17408 192 208 224
  wellFormedTest_17408_block_12
  wellFormedTest_17408_block_13)
  (interval_append wellFormedTest_17408 224 240 256
  wellFormedTest_17408_block_14
  wellFormedTest_17408_block_15))))
theorem wellFormedTestInterval17408 : Interval wellFormedTest 17408 17664 := by
  intro i hlo hhi
  have h := wellFormedTest_17408_complete (i-17408) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_17408, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed069 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_17664 (i : Nat) := wellFormedTest (i+17664)
theorem wellFormedTest_17664_block_0 : Interval wellFormedTest_17664 0 16 :=
  interval_of_check wellFormedTest_17664 0 16 (by decide +kernel)

theorem wellFormedTest_17664_block_1 : Interval wellFormedTest_17664 16 32 :=
  interval_of_check wellFormedTest_17664 16 16 (by decide +kernel)

theorem wellFormedTest_17664_block_2 : Interval wellFormedTest_17664 32 48 :=
  interval_of_check wellFormedTest_17664 32 16 (by decide +kernel)

theorem wellFormedTest_17664_block_3 : Interval wellFormedTest_17664 48 64 :=
  interval_of_check wellFormedTest_17664 48 16 (by decide +kernel)

theorem wellFormedTest_17664_block_4 : Interval wellFormedTest_17664 64 80 :=
  interval_of_check wellFormedTest_17664 64 16 (by decide +kernel)

theorem wellFormedTest_17664_block_5 : Interval wellFormedTest_17664 80 96 :=
  interval_of_check wellFormedTest_17664 80 16 (by decide +kernel)

theorem wellFormedTest_17664_block_6 : Interval wellFormedTest_17664 96 112 :=
  interval_of_check wellFormedTest_17664 96 16 (by decide +kernel)

theorem wellFormedTest_17664_block_7 : Interval wellFormedTest_17664 112 128 :=
  interval_of_check wellFormedTest_17664 112 16 (by decide +kernel)

theorem wellFormedTest_17664_block_8 : Interval wellFormedTest_17664 128 144 :=
  interval_of_check wellFormedTest_17664 128 16 (by decide +kernel)

theorem wellFormedTest_17664_block_9 : Interval wellFormedTest_17664 144 160 :=
  interval_of_check wellFormedTest_17664 144 16 (by decide +kernel)

theorem wellFormedTest_17664_block_10 : Interval wellFormedTest_17664 160 176 :=
  interval_of_check wellFormedTest_17664 160 16 (by decide +kernel)

theorem wellFormedTest_17664_block_11 : Interval wellFormedTest_17664 176 192 :=
  interval_of_check wellFormedTest_17664 176 16 (by decide +kernel)

theorem wellFormedTest_17664_block_12 : Interval wellFormedTest_17664 192 208 :=
  interval_of_check wellFormedTest_17664 192 16 (by decide +kernel)

theorem wellFormedTest_17664_block_13 : Interval wellFormedTest_17664 208 224 :=
  interval_of_check wellFormedTest_17664 208 16 (by decide +kernel)

theorem wellFormedTest_17664_block_14 : Interval wellFormedTest_17664 224 240 :=
  interval_of_check wellFormedTest_17664 224 16 (by decide +kernel)

theorem wellFormedTest_17664_block_15 : Interval wellFormedTest_17664 240 256 :=
  interval_of_check wellFormedTest_17664 240 16 (by decide +kernel)

theorem wellFormedTest_17664_complete : Interval wellFormedTest_17664 0 256 :=
  (interval_append wellFormedTest_17664 0 128 256
  (interval_append wellFormedTest_17664 0 64 128
  (interval_append wellFormedTest_17664 0 32 64
  (interval_append wellFormedTest_17664 0 16 32
  wellFormedTest_17664_block_0
  wellFormedTest_17664_block_1)
  (interval_append wellFormedTest_17664 32 48 64
  wellFormedTest_17664_block_2
  wellFormedTest_17664_block_3))
  (interval_append wellFormedTest_17664 64 96 128
  (interval_append wellFormedTest_17664 64 80 96
  wellFormedTest_17664_block_4
  wellFormedTest_17664_block_5)
  (interval_append wellFormedTest_17664 96 112 128
  wellFormedTest_17664_block_6
  wellFormedTest_17664_block_7)))
  (interval_append wellFormedTest_17664 128 192 256
  (interval_append wellFormedTest_17664 128 160 192
  (interval_append wellFormedTest_17664 128 144 160
  wellFormedTest_17664_block_8
  wellFormedTest_17664_block_9)
  (interval_append wellFormedTest_17664 160 176 192
  wellFormedTest_17664_block_10
  wellFormedTest_17664_block_11))
  (interval_append wellFormedTest_17664 192 224 256
  (interval_append wellFormedTest_17664 192 208 224
  wellFormedTest_17664_block_12
  wellFormedTest_17664_block_13)
  (interval_append wellFormedTest_17664 224 240 256
  wellFormedTest_17664_block_14
  wellFormedTest_17664_block_15))))
theorem wellFormedTestInterval17664 : Interval wellFormedTest 17664 17920 := by
  intro i hlo hhi
  have h := wellFormedTest_17664_complete (i-17664) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_17664, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed070 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_17920 (i : Nat) := wellFormedTest (i+17920)
theorem wellFormedTest_17920_block_0 : Interval wellFormedTest_17920 0 16 :=
  interval_of_check wellFormedTest_17920 0 16 (by decide +kernel)

theorem wellFormedTest_17920_block_1 : Interval wellFormedTest_17920 16 32 :=
  interval_of_check wellFormedTest_17920 16 16 (by decide +kernel)

theorem wellFormedTest_17920_block_2 : Interval wellFormedTest_17920 32 48 :=
  interval_of_check wellFormedTest_17920 32 16 (by decide +kernel)

theorem wellFormedTest_17920_block_3 : Interval wellFormedTest_17920 48 64 :=
  interval_of_check wellFormedTest_17920 48 16 (by decide +kernel)

theorem wellFormedTest_17920_block_4 : Interval wellFormedTest_17920 64 80 :=
  interval_of_check wellFormedTest_17920 64 16 (by decide +kernel)

theorem wellFormedTest_17920_block_5 : Interval wellFormedTest_17920 80 96 :=
  interval_of_check wellFormedTest_17920 80 16 (by decide +kernel)

theorem wellFormedTest_17920_block_6 : Interval wellFormedTest_17920 96 112 :=
  interval_of_check wellFormedTest_17920 96 16 (by decide +kernel)

theorem wellFormedTest_17920_block_7 : Interval wellFormedTest_17920 112 128 :=
  interval_of_check wellFormedTest_17920 112 16 (by decide +kernel)

theorem wellFormedTest_17920_block_8 : Interval wellFormedTest_17920 128 144 :=
  interval_of_check wellFormedTest_17920 128 16 (by decide +kernel)

theorem wellFormedTest_17920_block_9 : Interval wellFormedTest_17920 144 160 :=
  interval_of_check wellFormedTest_17920 144 16 (by decide +kernel)

theorem wellFormedTest_17920_block_10 : Interval wellFormedTest_17920 160 176 :=
  interval_of_check wellFormedTest_17920 160 16 (by decide +kernel)

theorem wellFormedTest_17920_block_11 : Interval wellFormedTest_17920 176 192 :=
  interval_of_check wellFormedTest_17920 176 16 (by decide +kernel)

theorem wellFormedTest_17920_block_12 : Interval wellFormedTest_17920 192 208 :=
  interval_of_check wellFormedTest_17920 192 16 (by decide +kernel)

theorem wellFormedTest_17920_block_13 : Interval wellFormedTest_17920 208 224 :=
  interval_of_check wellFormedTest_17920 208 16 (by decide +kernel)

theorem wellFormedTest_17920_block_14 : Interval wellFormedTest_17920 224 240 :=
  interval_of_check wellFormedTest_17920 224 16 (by decide +kernel)

theorem wellFormedTest_17920_block_15 : Interval wellFormedTest_17920 240 256 :=
  interval_of_check wellFormedTest_17920 240 16 (by decide +kernel)

theorem wellFormedTest_17920_complete : Interval wellFormedTest_17920 0 256 :=
  (interval_append wellFormedTest_17920 0 128 256
  (interval_append wellFormedTest_17920 0 64 128
  (interval_append wellFormedTest_17920 0 32 64
  (interval_append wellFormedTest_17920 0 16 32
  wellFormedTest_17920_block_0
  wellFormedTest_17920_block_1)
  (interval_append wellFormedTest_17920 32 48 64
  wellFormedTest_17920_block_2
  wellFormedTest_17920_block_3))
  (interval_append wellFormedTest_17920 64 96 128
  (interval_append wellFormedTest_17920 64 80 96
  wellFormedTest_17920_block_4
  wellFormedTest_17920_block_5)
  (interval_append wellFormedTest_17920 96 112 128
  wellFormedTest_17920_block_6
  wellFormedTest_17920_block_7)))
  (interval_append wellFormedTest_17920 128 192 256
  (interval_append wellFormedTest_17920 128 160 192
  (interval_append wellFormedTest_17920 128 144 160
  wellFormedTest_17920_block_8
  wellFormedTest_17920_block_9)
  (interval_append wellFormedTest_17920 160 176 192
  wellFormedTest_17920_block_10
  wellFormedTest_17920_block_11))
  (interval_append wellFormedTest_17920 192 224 256
  (interval_append wellFormedTest_17920 192 208 224
  wellFormedTest_17920_block_12
  wellFormedTest_17920_block_13)
  (interval_append wellFormedTest_17920 224 240 256
  wellFormedTest_17920_block_14
  wellFormedTest_17920_block_15))))
theorem wellFormedTestInterval17920 : Interval wellFormedTest 17920 18176 := by
  intro i hlo hhi
  have h := wellFormedTest_17920_complete (i-17920) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_17920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed071 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_18176 (i : Nat) := wellFormedTest (i+18176)
theorem wellFormedTest_18176_block_0 : Interval wellFormedTest_18176 0 16 :=
  interval_of_check wellFormedTest_18176 0 16 (by decide +kernel)

theorem wellFormedTest_18176_block_1 : Interval wellFormedTest_18176 16 32 :=
  interval_of_check wellFormedTest_18176 16 16 (by decide +kernel)

theorem wellFormedTest_18176_block_2 : Interval wellFormedTest_18176 32 48 :=
  interval_of_check wellFormedTest_18176 32 16 (by decide +kernel)

theorem wellFormedTest_18176_block_3 : Interval wellFormedTest_18176 48 64 :=
  interval_of_check wellFormedTest_18176 48 16 (by decide +kernel)

theorem wellFormedTest_18176_block_4 : Interval wellFormedTest_18176 64 80 :=
  interval_of_check wellFormedTest_18176 64 16 (by decide +kernel)

theorem wellFormedTest_18176_block_5 : Interval wellFormedTest_18176 80 96 :=
  interval_of_check wellFormedTest_18176 80 16 (by decide +kernel)

theorem wellFormedTest_18176_block_6 : Interval wellFormedTest_18176 96 112 :=
  interval_of_check wellFormedTest_18176 96 16 (by decide +kernel)

theorem wellFormedTest_18176_block_7 : Interval wellFormedTest_18176 112 128 :=
  interval_of_check wellFormedTest_18176 112 16 (by decide +kernel)

theorem wellFormedTest_18176_block_8 : Interval wellFormedTest_18176 128 144 :=
  interval_of_check wellFormedTest_18176 128 16 (by decide +kernel)

theorem wellFormedTest_18176_block_9 : Interval wellFormedTest_18176 144 160 :=
  interval_of_check wellFormedTest_18176 144 16 (by decide +kernel)

theorem wellFormedTest_18176_block_10 : Interval wellFormedTest_18176 160 176 :=
  interval_of_check wellFormedTest_18176 160 16 (by decide +kernel)

theorem wellFormedTest_18176_block_11 : Interval wellFormedTest_18176 176 192 :=
  interval_of_check wellFormedTest_18176 176 16 (by decide +kernel)

theorem wellFormedTest_18176_block_12 : Interval wellFormedTest_18176 192 208 :=
  interval_of_check wellFormedTest_18176 192 16 (by decide +kernel)

theorem wellFormedTest_18176_block_13 : Interval wellFormedTest_18176 208 224 :=
  interval_of_check wellFormedTest_18176 208 16 (by decide +kernel)

theorem wellFormedTest_18176_block_14 : Interval wellFormedTest_18176 224 240 :=
  interval_of_check wellFormedTest_18176 224 16 (by decide +kernel)

theorem wellFormedTest_18176_block_15 : Interval wellFormedTest_18176 240 256 :=
  interval_of_check wellFormedTest_18176 240 16 (by decide +kernel)

theorem wellFormedTest_18176_complete : Interval wellFormedTest_18176 0 256 :=
  (interval_append wellFormedTest_18176 0 128 256
  (interval_append wellFormedTest_18176 0 64 128
  (interval_append wellFormedTest_18176 0 32 64
  (interval_append wellFormedTest_18176 0 16 32
  wellFormedTest_18176_block_0
  wellFormedTest_18176_block_1)
  (interval_append wellFormedTest_18176 32 48 64
  wellFormedTest_18176_block_2
  wellFormedTest_18176_block_3))
  (interval_append wellFormedTest_18176 64 96 128
  (interval_append wellFormedTest_18176 64 80 96
  wellFormedTest_18176_block_4
  wellFormedTest_18176_block_5)
  (interval_append wellFormedTest_18176 96 112 128
  wellFormedTest_18176_block_6
  wellFormedTest_18176_block_7)))
  (interval_append wellFormedTest_18176 128 192 256
  (interval_append wellFormedTest_18176 128 160 192
  (interval_append wellFormedTest_18176 128 144 160
  wellFormedTest_18176_block_8
  wellFormedTest_18176_block_9)
  (interval_append wellFormedTest_18176 160 176 192
  wellFormedTest_18176_block_10
  wellFormedTest_18176_block_11))
  (interval_append wellFormedTest_18176 192 224 256
  (interval_append wellFormedTest_18176 192 208 224
  wellFormedTest_18176_block_12
  wellFormedTest_18176_block_13)
  (interval_append wellFormedTest_18176 224 240 256
  wellFormedTest_18176_block_14
  wellFormedTest_18176_block_15))))
theorem wellFormedTestInterval18176 : Interval wellFormedTest 18176 18432 := by
  intro i hlo hhi
  have h := wellFormedTest_18176_complete (i-18176) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_18176, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed072 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_18432 (i : Nat) := wellFormedTest (i+18432)
theorem wellFormedTest_18432_block_0 : Interval wellFormedTest_18432 0 16 :=
  interval_of_check wellFormedTest_18432 0 16 (by decide +kernel)

theorem wellFormedTest_18432_block_1 : Interval wellFormedTest_18432 16 32 :=
  interval_of_check wellFormedTest_18432 16 16 (by decide +kernel)

theorem wellFormedTest_18432_block_2 : Interval wellFormedTest_18432 32 48 :=
  interval_of_check wellFormedTest_18432 32 16 (by decide +kernel)

theorem wellFormedTest_18432_block_3 : Interval wellFormedTest_18432 48 64 :=
  interval_of_check wellFormedTest_18432 48 16 (by decide +kernel)

theorem wellFormedTest_18432_block_4 : Interval wellFormedTest_18432 64 80 :=
  interval_of_check wellFormedTest_18432 64 16 (by decide +kernel)

theorem wellFormedTest_18432_block_5 : Interval wellFormedTest_18432 80 96 :=
  interval_of_check wellFormedTest_18432 80 16 (by decide +kernel)

theorem wellFormedTest_18432_block_6 : Interval wellFormedTest_18432 96 112 :=
  interval_of_check wellFormedTest_18432 96 16 (by decide +kernel)

theorem wellFormedTest_18432_block_7 : Interval wellFormedTest_18432 112 128 :=
  interval_of_check wellFormedTest_18432 112 16 (by decide +kernel)

theorem wellFormedTest_18432_block_8 : Interval wellFormedTest_18432 128 144 :=
  interval_of_check wellFormedTest_18432 128 16 (by decide +kernel)

theorem wellFormedTest_18432_block_9 : Interval wellFormedTest_18432 144 160 :=
  interval_of_check wellFormedTest_18432 144 16 (by decide +kernel)

theorem wellFormedTest_18432_block_10 : Interval wellFormedTest_18432 160 176 :=
  interval_of_check wellFormedTest_18432 160 16 (by decide +kernel)

theorem wellFormedTest_18432_block_11 : Interval wellFormedTest_18432 176 192 :=
  interval_of_check wellFormedTest_18432 176 16 (by decide +kernel)

theorem wellFormedTest_18432_block_12 : Interval wellFormedTest_18432 192 208 :=
  interval_of_check wellFormedTest_18432 192 16 (by decide +kernel)

theorem wellFormedTest_18432_block_13 : Interval wellFormedTest_18432 208 224 :=
  interval_of_check wellFormedTest_18432 208 16 (by decide +kernel)

theorem wellFormedTest_18432_block_14 : Interval wellFormedTest_18432 224 240 :=
  interval_of_check wellFormedTest_18432 224 16 (by decide +kernel)

theorem wellFormedTest_18432_block_15 : Interval wellFormedTest_18432 240 256 :=
  interval_of_check wellFormedTest_18432 240 16 (by decide +kernel)

theorem wellFormedTest_18432_complete : Interval wellFormedTest_18432 0 256 :=
  (interval_append wellFormedTest_18432 0 128 256
  (interval_append wellFormedTest_18432 0 64 128
  (interval_append wellFormedTest_18432 0 32 64
  (interval_append wellFormedTest_18432 0 16 32
  wellFormedTest_18432_block_0
  wellFormedTest_18432_block_1)
  (interval_append wellFormedTest_18432 32 48 64
  wellFormedTest_18432_block_2
  wellFormedTest_18432_block_3))
  (interval_append wellFormedTest_18432 64 96 128
  (interval_append wellFormedTest_18432 64 80 96
  wellFormedTest_18432_block_4
  wellFormedTest_18432_block_5)
  (interval_append wellFormedTest_18432 96 112 128
  wellFormedTest_18432_block_6
  wellFormedTest_18432_block_7)))
  (interval_append wellFormedTest_18432 128 192 256
  (interval_append wellFormedTest_18432 128 160 192
  (interval_append wellFormedTest_18432 128 144 160
  wellFormedTest_18432_block_8
  wellFormedTest_18432_block_9)
  (interval_append wellFormedTest_18432 160 176 192
  wellFormedTest_18432_block_10
  wellFormedTest_18432_block_11))
  (interval_append wellFormedTest_18432 192 224 256
  (interval_append wellFormedTest_18432 192 208 224
  wellFormedTest_18432_block_12
  wellFormedTest_18432_block_13)
  (interval_append wellFormedTest_18432 224 240 256
  wellFormedTest_18432_block_14
  wellFormedTest_18432_block_15))))
theorem wellFormedTestInterval18432 : Interval wellFormedTest 18432 18688 := by
  intro i hlo hhi
  have h := wellFormedTest_18432_complete (i-18432) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_18432, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed073 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_18688 (i : Nat) := wellFormedTest (i+18688)
theorem wellFormedTest_18688_block_0 : Interval wellFormedTest_18688 0 16 :=
  interval_of_check wellFormedTest_18688 0 16 (by decide +kernel)

theorem wellFormedTest_18688_block_1 : Interval wellFormedTest_18688 16 32 :=
  interval_of_check wellFormedTest_18688 16 16 (by decide +kernel)

theorem wellFormedTest_18688_block_2 : Interval wellFormedTest_18688 32 48 :=
  interval_of_check wellFormedTest_18688 32 16 (by decide +kernel)

theorem wellFormedTest_18688_block_3 : Interval wellFormedTest_18688 48 64 :=
  interval_of_check wellFormedTest_18688 48 16 (by decide +kernel)

theorem wellFormedTest_18688_block_4 : Interval wellFormedTest_18688 64 80 :=
  interval_of_check wellFormedTest_18688 64 16 (by decide +kernel)

theorem wellFormedTest_18688_block_5 : Interval wellFormedTest_18688 80 96 :=
  interval_of_check wellFormedTest_18688 80 16 (by decide +kernel)

theorem wellFormedTest_18688_block_6 : Interval wellFormedTest_18688 96 112 :=
  interval_of_check wellFormedTest_18688 96 16 (by decide +kernel)

theorem wellFormedTest_18688_block_7 : Interval wellFormedTest_18688 112 128 :=
  interval_of_check wellFormedTest_18688 112 16 (by decide +kernel)

theorem wellFormedTest_18688_block_8 : Interval wellFormedTest_18688 128 144 :=
  interval_of_check wellFormedTest_18688 128 16 (by decide +kernel)

theorem wellFormedTest_18688_block_9 : Interval wellFormedTest_18688 144 160 :=
  interval_of_check wellFormedTest_18688 144 16 (by decide +kernel)

theorem wellFormedTest_18688_block_10 : Interval wellFormedTest_18688 160 176 :=
  interval_of_check wellFormedTest_18688 160 16 (by decide +kernel)

theorem wellFormedTest_18688_block_11 : Interval wellFormedTest_18688 176 192 :=
  interval_of_check wellFormedTest_18688 176 16 (by decide +kernel)

theorem wellFormedTest_18688_block_12 : Interval wellFormedTest_18688 192 208 :=
  interval_of_check wellFormedTest_18688 192 16 (by decide +kernel)

theorem wellFormedTest_18688_block_13 : Interval wellFormedTest_18688 208 224 :=
  interval_of_check wellFormedTest_18688 208 16 (by decide +kernel)

theorem wellFormedTest_18688_block_14 : Interval wellFormedTest_18688 224 240 :=
  interval_of_check wellFormedTest_18688 224 16 (by decide +kernel)

theorem wellFormedTest_18688_block_15 : Interval wellFormedTest_18688 240 256 :=
  interval_of_check wellFormedTest_18688 240 16 (by decide +kernel)

theorem wellFormedTest_18688_complete : Interval wellFormedTest_18688 0 256 :=
  (interval_append wellFormedTest_18688 0 128 256
  (interval_append wellFormedTest_18688 0 64 128
  (interval_append wellFormedTest_18688 0 32 64
  (interval_append wellFormedTest_18688 0 16 32
  wellFormedTest_18688_block_0
  wellFormedTest_18688_block_1)
  (interval_append wellFormedTest_18688 32 48 64
  wellFormedTest_18688_block_2
  wellFormedTest_18688_block_3))
  (interval_append wellFormedTest_18688 64 96 128
  (interval_append wellFormedTest_18688 64 80 96
  wellFormedTest_18688_block_4
  wellFormedTest_18688_block_5)
  (interval_append wellFormedTest_18688 96 112 128
  wellFormedTest_18688_block_6
  wellFormedTest_18688_block_7)))
  (interval_append wellFormedTest_18688 128 192 256
  (interval_append wellFormedTest_18688 128 160 192
  (interval_append wellFormedTest_18688 128 144 160
  wellFormedTest_18688_block_8
  wellFormedTest_18688_block_9)
  (interval_append wellFormedTest_18688 160 176 192
  wellFormedTest_18688_block_10
  wellFormedTest_18688_block_11))
  (interval_append wellFormedTest_18688 192 224 256
  (interval_append wellFormedTest_18688 192 208 224
  wellFormedTest_18688_block_12
  wellFormedTest_18688_block_13)
  (interval_append wellFormedTest_18688 224 240 256
  wellFormedTest_18688_block_14
  wellFormedTest_18688_block_15))))
theorem wellFormedTestInterval18688 : Interval wellFormedTest 18688 18944 := by
  intro i hlo hhi
  have h := wellFormedTest_18688_complete (i-18688) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_18688, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed074 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_18944 (i : Nat) := wellFormedTest (i+18944)
theorem wellFormedTest_18944_block_0 : Interval wellFormedTest_18944 0 16 :=
  interval_of_check wellFormedTest_18944 0 16 (by decide +kernel)

theorem wellFormedTest_18944_block_1 : Interval wellFormedTest_18944 16 32 :=
  interval_of_check wellFormedTest_18944 16 16 (by decide +kernel)

theorem wellFormedTest_18944_block_2 : Interval wellFormedTest_18944 32 48 :=
  interval_of_check wellFormedTest_18944 32 16 (by decide +kernel)

theorem wellFormedTest_18944_block_3 : Interval wellFormedTest_18944 48 64 :=
  interval_of_check wellFormedTest_18944 48 16 (by decide +kernel)

theorem wellFormedTest_18944_block_4 : Interval wellFormedTest_18944 64 80 :=
  interval_of_check wellFormedTest_18944 64 16 (by decide +kernel)

theorem wellFormedTest_18944_block_5 : Interval wellFormedTest_18944 80 96 :=
  interval_of_check wellFormedTest_18944 80 16 (by decide +kernel)

theorem wellFormedTest_18944_block_6 : Interval wellFormedTest_18944 96 112 :=
  interval_of_check wellFormedTest_18944 96 16 (by decide +kernel)

theorem wellFormedTest_18944_block_7 : Interval wellFormedTest_18944 112 128 :=
  interval_of_check wellFormedTest_18944 112 16 (by decide +kernel)

theorem wellFormedTest_18944_block_8 : Interval wellFormedTest_18944 128 144 :=
  interval_of_check wellFormedTest_18944 128 16 (by decide +kernel)

theorem wellFormedTest_18944_block_9 : Interval wellFormedTest_18944 144 160 :=
  interval_of_check wellFormedTest_18944 144 16 (by decide +kernel)

theorem wellFormedTest_18944_block_10 : Interval wellFormedTest_18944 160 176 :=
  interval_of_check wellFormedTest_18944 160 16 (by decide +kernel)

theorem wellFormedTest_18944_block_11 : Interval wellFormedTest_18944 176 192 :=
  interval_of_check wellFormedTest_18944 176 16 (by decide +kernel)

theorem wellFormedTest_18944_block_12 : Interval wellFormedTest_18944 192 208 :=
  interval_of_check wellFormedTest_18944 192 16 (by decide +kernel)

theorem wellFormedTest_18944_block_13 : Interval wellFormedTest_18944 208 224 :=
  interval_of_check wellFormedTest_18944 208 16 (by decide +kernel)

theorem wellFormedTest_18944_block_14 : Interval wellFormedTest_18944 224 240 :=
  interval_of_check wellFormedTest_18944 224 16 (by decide +kernel)

theorem wellFormedTest_18944_block_15 : Interval wellFormedTest_18944 240 256 :=
  interval_of_check wellFormedTest_18944 240 16 (by decide +kernel)

theorem wellFormedTest_18944_complete : Interval wellFormedTest_18944 0 256 :=
  (interval_append wellFormedTest_18944 0 128 256
  (interval_append wellFormedTest_18944 0 64 128
  (interval_append wellFormedTest_18944 0 32 64
  (interval_append wellFormedTest_18944 0 16 32
  wellFormedTest_18944_block_0
  wellFormedTest_18944_block_1)
  (interval_append wellFormedTest_18944 32 48 64
  wellFormedTest_18944_block_2
  wellFormedTest_18944_block_3))
  (interval_append wellFormedTest_18944 64 96 128
  (interval_append wellFormedTest_18944 64 80 96
  wellFormedTest_18944_block_4
  wellFormedTest_18944_block_5)
  (interval_append wellFormedTest_18944 96 112 128
  wellFormedTest_18944_block_6
  wellFormedTest_18944_block_7)))
  (interval_append wellFormedTest_18944 128 192 256
  (interval_append wellFormedTest_18944 128 160 192
  (interval_append wellFormedTest_18944 128 144 160
  wellFormedTest_18944_block_8
  wellFormedTest_18944_block_9)
  (interval_append wellFormedTest_18944 160 176 192
  wellFormedTest_18944_block_10
  wellFormedTest_18944_block_11))
  (interval_append wellFormedTest_18944 192 224 256
  (interval_append wellFormedTest_18944 192 208 224
  wellFormedTest_18944_block_12
  wellFormedTest_18944_block_13)
  (interval_append wellFormedTest_18944 224 240 256
  wellFormedTest_18944_block_14
  wellFormedTest_18944_block_15))))
theorem wellFormedTestInterval18944 : Interval wellFormedTest 18944 19200 := by
  intro i hlo hhi
  have h := wellFormedTest_18944_complete (i-18944) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_18944, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed075 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_19200 (i : Nat) := wellFormedTest (i+19200)
theorem wellFormedTest_19200_block_0 : Interval wellFormedTest_19200 0 16 :=
  interval_of_check wellFormedTest_19200 0 16 (by decide +kernel)

theorem wellFormedTest_19200_block_1 : Interval wellFormedTest_19200 16 32 :=
  interval_of_check wellFormedTest_19200 16 16 (by decide +kernel)

theorem wellFormedTest_19200_block_2 : Interval wellFormedTest_19200 32 48 :=
  interval_of_check wellFormedTest_19200 32 16 (by decide +kernel)

theorem wellFormedTest_19200_block_3 : Interval wellFormedTest_19200 48 64 :=
  interval_of_check wellFormedTest_19200 48 16 (by decide +kernel)

theorem wellFormedTest_19200_block_4 : Interval wellFormedTest_19200 64 80 :=
  interval_of_check wellFormedTest_19200 64 16 (by decide +kernel)

theorem wellFormedTest_19200_block_5 : Interval wellFormedTest_19200 80 96 :=
  interval_of_check wellFormedTest_19200 80 16 (by decide +kernel)

theorem wellFormedTest_19200_block_6 : Interval wellFormedTest_19200 96 112 :=
  interval_of_check wellFormedTest_19200 96 16 (by decide +kernel)

theorem wellFormedTest_19200_block_7 : Interval wellFormedTest_19200 112 128 :=
  interval_of_check wellFormedTest_19200 112 16 (by decide +kernel)

theorem wellFormedTest_19200_block_8 : Interval wellFormedTest_19200 128 144 :=
  interval_of_check wellFormedTest_19200 128 16 (by decide +kernel)

theorem wellFormedTest_19200_block_9 : Interval wellFormedTest_19200 144 160 :=
  interval_of_check wellFormedTest_19200 144 16 (by decide +kernel)

theorem wellFormedTest_19200_block_10 : Interval wellFormedTest_19200 160 176 :=
  interval_of_check wellFormedTest_19200 160 16 (by decide +kernel)

theorem wellFormedTest_19200_block_11 : Interval wellFormedTest_19200 176 192 :=
  interval_of_check wellFormedTest_19200 176 16 (by decide +kernel)

theorem wellFormedTest_19200_block_12 : Interval wellFormedTest_19200 192 208 :=
  interval_of_check wellFormedTest_19200 192 16 (by decide +kernel)

theorem wellFormedTest_19200_block_13 : Interval wellFormedTest_19200 208 224 :=
  interval_of_check wellFormedTest_19200 208 16 (by decide +kernel)

theorem wellFormedTest_19200_block_14 : Interval wellFormedTest_19200 224 240 :=
  interval_of_check wellFormedTest_19200 224 16 (by decide +kernel)

theorem wellFormedTest_19200_block_15 : Interval wellFormedTest_19200 240 256 :=
  interval_of_check wellFormedTest_19200 240 16 (by decide +kernel)

theorem wellFormedTest_19200_complete : Interval wellFormedTest_19200 0 256 :=
  (interval_append wellFormedTest_19200 0 128 256
  (interval_append wellFormedTest_19200 0 64 128
  (interval_append wellFormedTest_19200 0 32 64
  (interval_append wellFormedTest_19200 0 16 32
  wellFormedTest_19200_block_0
  wellFormedTest_19200_block_1)
  (interval_append wellFormedTest_19200 32 48 64
  wellFormedTest_19200_block_2
  wellFormedTest_19200_block_3))
  (interval_append wellFormedTest_19200 64 96 128
  (interval_append wellFormedTest_19200 64 80 96
  wellFormedTest_19200_block_4
  wellFormedTest_19200_block_5)
  (interval_append wellFormedTest_19200 96 112 128
  wellFormedTest_19200_block_6
  wellFormedTest_19200_block_7)))
  (interval_append wellFormedTest_19200 128 192 256
  (interval_append wellFormedTest_19200 128 160 192
  (interval_append wellFormedTest_19200 128 144 160
  wellFormedTest_19200_block_8
  wellFormedTest_19200_block_9)
  (interval_append wellFormedTest_19200 160 176 192
  wellFormedTest_19200_block_10
  wellFormedTest_19200_block_11))
  (interval_append wellFormedTest_19200 192 224 256
  (interval_append wellFormedTest_19200 192 208 224
  wellFormedTest_19200_block_12
  wellFormedTest_19200_block_13)
  (interval_append wellFormedTest_19200 224 240 256
  wellFormedTest_19200_block_14
  wellFormedTest_19200_block_15))))
theorem wellFormedTestInterval19200 : Interval wellFormedTest 19200 19456 := by
  intro i hlo hhi
  have h := wellFormedTest_19200_complete (i-19200) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_19200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed076 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_19456 (i : Nat) := wellFormedTest (i+19456)
theorem wellFormedTest_19456_block_0 : Interval wellFormedTest_19456 0 16 :=
  interval_of_check wellFormedTest_19456 0 16 (by decide +kernel)

theorem wellFormedTest_19456_block_1 : Interval wellFormedTest_19456 16 32 :=
  interval_of_check wellFormedTest_19456 16 16 (by decide +kernel)

theorem wellFormedTest_19456_block_2 : Interval wellFormedTest_19456 32 48 :=
  interval_of_check wellFormedTest_19456 32 16 (by decide +kernel)

theorem wellFormedTest_19456_block_3 : Interval wellFormedTest_19456 48 64 :=
  interval_of_check wellFormedTest_19456 48 16 (by decide +kernel)

theorem wellFormedTest_19456_block_4 : Interval wellFormedTest_19456 64 80 :=
  interval_of_check wellFormedTest_19456 64 16 (by decide +kernel)

theorem wellFormedTest_19456_block_5 : Interval wellFormedTest_19456 80 96 :=
  interval_of_check wellFormedTest_19456 80 16 (by decide +kernel)

theorem wellFormedTest_19456_block_6 : Interval wellFormedTest_19456 96 112 :=
  interval_of_check wellFormedTest_19456 96 16 (by decide +kernel)

theorem wellFormedTest_19456_block_7 : Interval wellFormedTest_19456 112 128 :=
  interval_of_check wellFormedTest_19456 112 16 (by decide +kernel)

theorem wellFormedTest_19456_block_8 : Interval wellFormedTest_19456 128 144 :=
  interval_of_check wellFormedTest_19456 128 16 (by decide +kernel)

theorem wellFormedTest_19456_block_9 : Interval wellFormedTest_19456 144 160 :=
  interval_of_check wellFormedTest_19456 144 16 (by decide +kernel)

theorem wellFormedTest_19456_block_10 : Interval wellFormedTest_19456 160 176 :=
  interval_of_check wellFormedTest_19456 160 16 (by decide +kernel)

theorem wellFormedTest_19456_block_11 : Interval wellFormedTest_19456 176 192 :=
  interval_of_check wellFormedTest_19456 176 16 (by decide +kernel)

theorem wellFormedTest_19456_block_12 : Interval wellFormedTest_19456 192 208 :=
  interval_of_check wellFormedTest_19456 192 16 (by decide +kernel)

theorem wellFormedTest_19456_block_13 : Interval wellFormedTest_19456 208 224 :=
  interval_of_check wellFormedTest_19456 208 16 (by decide +kernel)

theorem wellFormedTest_19456_block_14 : Interval wellFormedTest_19456 224 240 :=
  interval_of_check wellFormedTest_19456 224 16 (by decide +kernel)

theorem wellFormedTest_19456_block_15 : Interval wellFormedTest_19456 240 256 :=
  interval_of_check wellFormedTest_19456 240 16 (by decide +kernel)

theorem wellFormedTest_19456_complete : Interval wellFormedTest_19456 0 256 :=
  (interval_append wellFormedTest_19456 0 128 256
  (interval_append wellFormedTest_19456 0 64 128
  (interval_append wellFormedTest_19456 0 32 64
  (interval_append wellFormedTest_19456 0 16 32
  wellFormedTest_19456_block_0
  wellFormedTest_19456_block_1)
  (interval_append wellFormedTest_19456 32 48 64
  wellFormedTest_19456_block_2
  wellFormedTest_19456_block_3))
  (interval_append wellFormedTest_19456 64 96 128
  (interval_append wellFormedTest_19456 64 80 96
  wellFormedTest_19456_block_4
  wellFormedTest_19456_block_5)
  (interval_append wellFormedTest_19456 96 112 128
  wellFormedTest_19456_block_6
  wellFormedTest_19456_block_7)))
  (interval_append wellFormedTest_19456 128 192 256
  (interval_append wellFormedTest_19456 128 160 192
  (interval_append wellFormedTest_19456 128 144 160
  wellFormedTest_19456_block_8
  wellFormedTest_19456_block_9)
  (interval_append wellFormedTest_19456 160 176 192
  wellFormedTest_19456_block_10
  wellFormedTest_19456_block_11))
  (interval_append wellFormedTest_19456 192 224 256
  (interval_append wellFormedTest_19456 192 208 224
  wellFormedTest_19456_block_12
  wellFormedTest_19456_block_13)
  (interval_append wellFormedTest_19456 224 240 256
  wellFormedTest_19456_block_14
  wellFormedTest_19456_block_15))))
theorem wellFormedTestInterval19456 : Interval wellFormedTest 19456 19712 := by
  intro i hlo hhi
  have h := wellFormedTest_19456_complete (i-19456) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_19456, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed077 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_19712 (i : Nat) := wellFormedTest (i+19712)
theorem wellFormedTest_19712_block_0 : Interval wellFormedTest_19712 0 16 :=
  interval_of_check wellFormedTest_19712 0 16 (by decide +kernel)

theorem wellFormedTest_19712_block_1 : Interval wellFormedTest_19712 16 32 :=
  interval_of_check wellFormedTest_19712 16 16 (by decide +kernel)

theorem wellFormedTest_19712_block_2 : Interval wellFormedTest_19712 32 48 :=
  interval_of_check wellFormedTest_19712 32 16 (by decide +kernel)

theorem wellFormedTest_19712_block_3 : Interval wellFormedTest_19712 48 64 :=
  interval_of_check wellFormedTest_19712 48 16 (by decide +kernel)

theorem wellFormedTest_19712_block_4 : Interval wellFormedTest_19712 64 80 :=
  interval_of_check wellFormedTest_19712 64 16 (by decide +kernel)

theorem wellFormedTest_19712_block_5 : Interval wellFormedTest_19712 80 96 :=
  interval_of_check wellFormedTest_19712 80 16 (by decide +kernel)

theorem wellFormedTest_19712_block_6 : Interval wellFormedTest_19712 96 112 :=
  interval_of_check wellFormedTest_19712 96 16 (by decide +kernel)

theorem wellFormedTest_19712_block_7 : Interval wellFormedTest_19712 112 128 :=
  interval_of_check wellFormedTest_19712 112 16 (by decide +kernel)

theorem wellFormedTest_19712_block_8 : Interval wellFormedTest_19712 128 144 :=
  interval_of_check wellFormedTest_19712 128 16 (by decide +kernel)

theorem wellFormedTest_19712_block_9 : Interval wellFormedTest_19712 144 160 :=
  interval_of_check wellFormedTest_19712 144 16 (by decide +kernel)

theorem wellFormedTest_19712_block_10 : Interval wellFormedTest_19712 160 176 :=
  interval_of_check wellFormedTest_19712 160 16 (by decide +kernel)

theorem wellFormedTest_19712_block_11 : Interval wellFormedTest_19712 176 192 :=
  interval_of_check wellFormedTest_19712 176 16 (by decide +kernel)

theorem wellFormedTest_19712_block_12 : Interval wellFormedTest_19712 192 208 :=
  interval_of_check wellFormedTest_19712 192 16 (by decide +kernel)

theorem wellFormedTest_19712_block_13 : Interval wellFormedTest_19712 208 224 :=
  interval_of_check wellFormedTest_19712 208 16 (by decide +kernel)

theorem wellFormedTest_19712_block_14 : Interval wellFormedTest_19712 224 240 :=
  interval_of_check wellFormedTest_19712 224 16 (by decide +kernel)

theorem wellFormedTest_19712_block_15 : Interval wellFormedTest_19712 240 256 :=
  interval_of_check wellFormedTest_19712 240 16 (by decide +kernel)

theorem wellFormedTest_19712_complete : Interval wellFormedTest_19712 0 256 :=
  (interval_append wellFormedTest_19712 0 128 256
  (interval_append wellFormedTest_19712 0 64 128
  (interval_append wellFormedTest_19712 0 32 64
  (interval_append wellFormedTest_19712 0 16 32
  wellFormedTest_19712_block_0
  wellFormedTest_19712_block_1)
  (interval_append wellFormedTest_19712 32 48 64
  wellFormedTest_19712_block_2
  wellFormedTest_19712_block_3))
  (interval_append wellFormedTest_19712 64 96 128
  (interval_append wellFormedTest_19712 64 80 96
  wellFormedTest_19712_block_4
  wellFormedTest_19712_block_5)
  (interval_append wellFormedTest_19712 96 112 128
  wellFormedTest_19712_block_6
  wellFormedTest_19712_block_7)))
  (interval_append wellFormedTest_19712 128 192 256
  (interval_append wellFormedTest_19712 128 160 192
  (interval_append wellFormedTest_19712 128 144 160
  wellFormedTest_19712_block_8
  wellFormedTest_19712_block_9)
  (interval_append wellFormedTest_19712 160 176 192
  wellFormedTest_19712_block_10
  wellFormedTest_19712_block_11))
  (interval_append wellFormedTest_19712 192 224 256
  (interval_append wellFormedTest_19712 192 208 224
  wellFormedTest_19712_block_12
  wellFormedTest_19712_block_13)
  (interval_append wellFormedTest_19712 224 240 256
  wellFormedTest_19712_block_14
  wellFormedTest_19712_block_15))))
theorem wellFormedTestInterval19712 : Interval wellFormedTest 19712 19968 := by
  intro i hlo hhi
  have h := wellFormedTest_19712_complete (i-19712) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_19712, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed078 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_19968 (i : Nat) := wellFormedTest (i+19968)
theorem wellFormedTest_19968_block_0 : Interval wellFormedTest_19968 0 16 :=
  interval_of_check wellFormedTest_19968 0 16 (by decide +kernel)

theorem wellFormedTest_19968_block_1 : Interval wellFormedTest_19968 16 32 :=
  interval_of_check wellFormedTest_19968 16 16 (by decide +kernel)

theorem wellFormedTest_19968_block_2 : Interval wellFormedTest_19968 32 48 :=
  interval_of_check wellFormedTest_19968 32 16 (by decide +kernel)

theorem wellFormedTest_19968_block_3 : Interval wellFormedTest_19968 48 64 :=
  interval_of_check wellFormedTest_19968 48 16 (by decide +kernel)

theorem wellFormedTest_19968_block_4 : Interval wellFormedTest_19968 64 80 :=
  interval_of_check wellFormedTest_19968 64 16 (by decide +kernel)

theorem wellFormedTest_19968_block_5 : Interval wellFormedTest_19968 80 96 :=
  interval_of_check wellFormedTest_19968 80 16 (by decide +kernel)

theorem wellFormedTest_19968_block_6 : Interval wellFormedTest_19968 96 112 :=
  interval_of_check wellFormedTest_19968 96 16 (by decide +kernel)

theorem wellFormedTest_19968_block_7 : Interval wellFormedTest_19968 112 128 :=
  interval_of_check wellFormedTest_19968 112 16 (by decide +kernel)

theorem wellFormedTest_19968_block_8 : Interval wellFormedTest_19968 128 144 :=
  interval_of_check wellFormedTest_19968 128 16 (by decide +kernel)

theorem wellFormedTest_19968_block_9 : Interval wellFormedTest_19968 144 160 :=
  interval_of_check wellFormedTest_19968 144 16 (by decide +kernel)

theorem wellFormedTest_19968_block_10 : Interval wellFormedTest_19968 160 176 :=
  interval_of_check wellFormedTest_19968 160 16 (by decide +kernel)

theorem wellFormedTest_19968_block_11 : Interval wellFormedTest_19968 176 192 :=
  interval_of_check wellFormedTest_19968 176 16 (by decide +kernel)

theorem wellFormedTest_19968_block_12 : Interval wellFormedTest_19968 192 208 :=
  interval_of_check wellFormedTest_19968 192 16 (by decide +kernel)

theorem wellFormedTest_19968_block_13 : Interval wellFormedTest_19968 208 224 :=
  interval_of_check wellFormedTest_19968 208 16 (by decide +kernel)

theorem wellFormedTest_19968_block_14 : Interval wellFormedTest_19968 224 240 :=
  interval_of_check wellFormedTest_19968 224 16 (by decide +kernel)

theorem wellFormedTest_19968_block_15 : Interval wellFormedTest_19968 240 256 :=
  interval_of_check wellFormedTest_19968 240 16 (by decide +kernel)

theorem wellFormedTest_19968_complete : Interval wellFormedTest_19968 0 256 :=
  (interval_append wellFormedTest_19968 0 128 256
  (interval_append wellFormedTest_19968 0 64 128
  (interval_append wellFormedTest_19968 0 32 64
  (interval_append wellFormedTest_19968 0 16 32
  wellFormedTest_19968_block_0
  wellFormedTest_19968_block_1)
  (interval_append wellFormedTest_19968 32 48 64
  wellFormedTest_19968_block_2
  wellFormedTest_19968_block_3))
  (interval_append wellFormedTest_19968 64 96 128
  (interval_append wellFormedTest_19968 64 80 96
  wellFormedTest_19968_block_4
  wellFormedTest_19968_block_5)
  (interval_append wellFormedTest_19968 96 112 128
  wellFormedTest_19968_block_6
  wellFormedTest_19968_block_7)))
  (interval_append wellFormedTest_19968 128 192 256
  (interval_append wellFormedTest_19968 128 160 192
  (interval_append wellFormedTest_19968 128 144 160
  wellFormedTest_19968_block_8
  wellFormedTest_19968_block_9)
  (interval_append wellFormedTest_19968 160 176 192
  wellFormedTest_19968_block_10
  wellFormedTest_19968_block_11))
  (interval_append wellFormedTest_19968 192 224 256
  (interval_append wellFormedTest_19968 192 208 224
  wellFormedTest_19968_block_12
  wellFormedTest_19968_block_13)
  (interval_append wellFormedTest_19968 224 240 256
  wellFormedTest_19968_block_14
  wellFormedTest_19968_block_15))))
theorem wellFormedTestInterval19968 : Interval wellFormedTest 19968 20224 := by
  intro i hlo hhi
  have h := wellFormedTest_19968_complete (i-19968) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_19968, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed079 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_20224 (i : Nat) := wellFormedTest (i+20224)
theorem wellFormedTest_20224_block_0 : Interval wellFormedTest_20224 0 16 :=
  interval_of_check wellFormedTest_20224 0 16 (by decide +kernel)

theorem wellFormedTest_20224_block_1 : Interval wellFormedTest_20224 16 32 :=
  interval_of_check wellFormedTest_20224 16 16 (by decide +kernel)

theorem wellFormedTest_20224_block_2 : Interval wellFormedTest_20224 32 48 :=
  interval_of_check wellFormedTest_20224 32 16 (by decide +kernel)

theorem wellFormedTest_20224_block_3 : Interval wellFormedTest_20224 48 64 :=
  interval_of_check wellFormedTest_20224 48 16 (by decide +kernel)

theorem wellFormedTest_20224_block_4 : Interval wellFormedTest_20224 64 80 :=
  interval_of_check wellFormedTest_20224 64 16 (by decide +kernel)

theorem wellFormedTest_20224_block_5 : Interval wellFormedTest_20224 80 96 :=
  interval_of_check wellFormedTest_20224 80 16 (by decide +kernel)

theorem wellFormedTest_20224_block_6 : Interval wellFormedTest_20224 96 112 :=
  interval_of_check wellFormedTest_20224 96 16 (by decide +kernel)

theorem wellFormedTest_20224_block_7 : Interval wellFormedTest_20224 112 128 :=
  interval_of_check wellFormedTest_20224 112 16 (by decide +kernel)

theorem wellFormedTest_20224_block_8 : Interval wellFormedTest_20224 128 144 :=
  interval_of_check wellFormedTest_20224 128 16 (by decide +kernel)

theorem wellFormedTest_20224_block_9 : Interval wellFormedTest_20224 144 160 :=
  interval_of_check wellFormedTest_20224 144 16 (by decide +kernel)

theorem wellFormedTest_20224_block_10 : Interval wellFormedTest_20224 160 176 :=
  interval_of_check wellFormedTest_20224 160 16 (by decide +kernel)

theorem wellFormedTest_20224_block_11 : Interval wellFormedTest_20224 176 192 :=
  interval_of_check wellFormedTest_20224 176 16 (by decide +kernel)

theorem wellFormedTest_20224_block_12 : Interval wellFormedTest_20224 192 208 :=
  interval_of_check wellFormedTest_20224 192 16 (by decide +kernel)

theorem wellFormedTest_20224_block_13 : Interval wellFormedTest_20224 208 224 :=
  interval_of_check wellFormedTest_20224 208 16 (by decide +kernel)

theorem wellFormedTest_20224_block_14 : Interval wellFormedTest_20224 224 240 :=
  interval_of_check wellFormedTest_20224 224 16 (by decide +kernel)

theorem wellFormedTest_20224_block_15 : Interval wellFormedTest_20224 240 256 :=
  interval_of_check wellFormedTest_20224 240 16 (by decide +kernel)

theorem wellFormedTest_20224_complete : Interval wellFormedTest_20224 0 256 :=
  (interval_append wellFormedTest_20224 0 128 256
  (interval_append wellFormedTest_20224 0 64 128
  (interval_append wellFormedTest_20224 0 32 64
  (interval_append wellFormedTest_20224 0 16 32
  wellFormedTest_20224_block_0
  wellFormedTest_20224_block_1)
  (interval_append wellFormedTest_20224 32 48 64
  wellFormedTest_20224_block_2
  wellFormedTest_20224_block_3))
  (interval_append wellFormedTest_20224 64 96 128
  (interval_append wellFormedTest_20224 64 80 96
  wellFormedTest_20224_block_4
  wellFormedTest_20224_block_5)
  (interval_append wellFormedTest_20224 96 112 128
  wellFormedTest_20224_block_6
  wellFormedTest_20224_block_7)))
  (interval_append wellFormedTest_20224 128 192 256
  (interval_append wellFormedTest_20224 128 160 192
  (interval_append wellFormedTest_20224 128 144 160
  wellFormedTest_20224_block_8
  wellFormedTest_20224_block_9)
  (interval_append wellFormedTest_20224 160 176 192
  wellFormedTest_20224_block_10
  wellFormedTest_20224_block_11))
  (interval_append wellFormedTest_20224 192 224 256
  (interval_append wellFormedTest_20224 192 208 224
  wellFormedTest_20224_block_12
  wellFormedTest_20224_block_13)
  (interval_append wellFormedTest_20224 224 240 256
  wellFormedTest_20224_block_14
  wellFormedTest_20224_block_15))))
theorem wellFormedTestInterval20224 : Interval wellFormedTest 20224 20480 := by
  intro i hlo hhi
  have h := wellFormedTest_20224_complete (i-20224) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_20224, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed080 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_20480 (i : Nat) := wellFormedTest (i+20480)
theorem wellFormedTest_20480_block_0 : Interval wellFormedTest_20480 0 16 :=
  interval_of_check wellFormedTest_20480 0 16 (by decide +kernel)

theorem wellFormedTest_20480_block_1 : Interval wellFormedTest_20480 16 32 :=
  interval_of_check wellFormedTest_20480 16 16 (by decide +kernel)

theorem wellFormedTest_20480_block_2 : Interval wellFormedTest_20480 32 48 :=
  interval_of_check wellFormedTest_20480 32 16 (by decide +kernel)

theorem wellFormedTest_20480_block_3 : Interval wellFormedTest_20480 48 64 :=
  interval_of_check wellFormedTest_20480 48 16 (by decide +kernel)

theorem wellFormedTest_20480_block_4 : Interval wellFormedTest_20480 64 80 :=
  interval_of_check wellFormedTest_20480 64 16 (by decide +kernel)

theorem wellFormedTest_20480_block_5 : Interval wellFormedTest_20480 80 96 :=
  interval_of_check wellFormedTest_20480 80 16 (by decide +kernel)

theorem wellFormedTest_20480_block_6 : Interval wellFormedTest_20480 96 112 :=
  interval_of_check wellFormedTest_20480 96 16 (by decide +kernel)

theorem wellFormedTest_20480_block_7 : Interval wellFormedTest_20480 112 128 :=
  interval_of_check wellFormedTest_20480 112 16 (by decide +kernel)

theorem wellFormedTest_20480_block_8 : Interval wellFormedTest_20480 128 144 :=
  interval_of_check wellFormedTest_20480 128 16 (by decide +kernel)

theorem wellFormedTest_20480_block_9 : Interval wellFormedTest_20480 144 160 :=
  interval_of_check wellFormedTest_20480 144 16 (by decide +kernel)

theorem wellFormedTest_20480_block_10 : Interval wellFormedTest_20480 160 176 :=
  interval_of_check wellFormedTest_20480 160 16 (by decide +kernel)

theorem wellFormedTest_20480_block_11 : Interval wellFormedTest_20480 176 192 :=
  interval_of_check wellFormedTest_20480 176 16 (by decide +kernel)

theorem wellFormedTest_20480_block_12 : Interval wellFormedTest_20480 192 208 :=
  interval_of_check wellFormedTest_20480 192 16 (by decide +kernel)

theorem wellFormedTest_20480_block_13 : Interval wellFormedTest_20480 208 224 :=
  interval_of_check wellFormedTest_20480 208 16 (by decide +kernel)

theorem wellFormedTest_20480_block_14 : Interval wellFormedTest_20480 224 240 :=
  interval_of_check wellFormedTest_20480 224 16 (by decide +kernel)

theorem wellFormedTest_20480_block_15 : Interval wellFormedTest_20480 240 256 :=
  interval_of_check wellFormedTest_20480 240 16 (by decide +kernel)

theorem wellFormedTest_20480_complete : Interval wellFormedTest_20480 0 256 :=
  (interval_append wellFormedTest_20480 0 128 256
  (interval_append wellFormedTest_20480 0 64 128
  (interval_append wellFormedTest_20480 0 32 64
  (interval_append wellFormedTest_20480 0 16 32
  wellFormedTest_20480_block_0
  wellFormedTest_20480_block_1)
  (interval_append wellFormedTest_20480 32 48 64
  wellFormedTest_20480_block_2
  wellFormedTest_20480_block_3))
  (interval_append wellFormedTest_20480 64 96 128
  (interval_append wellFormedTest_20480 64 80 96
  wellFormedTest_20480_block_4
  wellFormedTest_20480_block_5)
  (interval_append wellFormedTest_20480 96 112 128
  wellFormedTest_20480_block_6
  wellFormedTest_20480_block_7)))
  (interval_append wellFormedTest_20480 128 192 256
  (interval_append wellFormedTest_20480 128 160 192
  (interval_append wellFormedTest_20480 128 144 160
  wellFormedTest_20480_block_8
  wellFormedTest_20480_block_9)
  (interval_append wellFormedTest_20480 160 176 192
  wellFormedTest_20480_block_10
  wellFormedTest_20480_block_11))
  (interval_append wellFormedTest_20480 192 224 256
  (interval_append wellFormedTest_20480 192 208 224
  wellFormedTest_20480_block_12
  wellFormedTest_20480_block_13)
  (interval_append wellFormedTest_20480 224 240 256
  wellFormedTest_20480_block_14
  wellFormedTest_20480_block_15))))
theorem wellFormedTestInterval20480 : Interval wellFormedTest 20480 20736 := by
  intro i hlo hhi
  have h := wellFormedTest_20480_complete (i-20480) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_20480, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed081 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_20736 (i : Nat) := wellFormedTest (i+20736)
theorem wellFormedTest_20736_block_0 : Interval wellFormedTest_20736 0 16 :=
  interval_of_check wellFormedTest_20736 0 16 (by decide +kernel)

theorem wellFormedTest_20736_block_1 : Interval wellFormedTest_20736 16 32 :=
  interval_of_check wellFormedTest_20736 16 16 (by decide +kernel)

theorem wellFormedTest_20736_block_2 : Interval wellFormedTest_20736 32 48 :=
  interval_of_check wellFormedTest_20736 32 16 (by decide +kernel)

theorem wellFormedTest_20736_block_3 : Interval wellFormedTest_20736 48 64 :=
  interval_of_check wellFormedTest_20736 48 16 (by decide +kernel)

theorem wellFormedTest_20736_block_4 : Interval wellFormedTest_20736 64 80 :=
  interval_of_check wellFormedTest_20736 64 16 (by decide +kernel)

theorem wellFormedTest_20736_block_5 : Interval wellFormedTest_20736 80 96 :=
  interval_of_check wellFormedTest_20736 80 16 (by decide +kernel)

theorem wellFormedTest_20736_block_6 : Interval wellFormedTest_20736 96 112 :=
  interval_of_check wellFormedTest_20736 96 16 (by decide +kernel)

theorem wellFormedTest_20736_block_7 : Interval wellFormedTest_20736 112 128 :=
  interval_of_check wellFormedTest_20736 112 16 (by decide +kernel)

theorem wellFormedTest_20736_block_8 : Interval wellFormedTest_20736 128 144 :=
  interval_of_check wellFormedTest_20736 128 16 (by decide +kernel)

theorem wellFormedTest_20736_block_9 : Interval wellFormedTest_20736 144 160 :=
  interval_of_check wellFormedTest_20736 144 16 (by decide +kernel)

theorem wellFormedTest_20736_block_10 : Interval wellFormedTest_20736 160 176 :=
  interval_of_check wellFormedTest_20736 160 16 (by decide +kernel)

theorem wellFormedTest_20736_block_11 : Interval wellFormedTest_20736 176 192 :=
  interval_of_check wellFormedTest_20736 176 16 (by decide +kernel)

theorem wellFormedTest_20736_block_12 : Interval wellFormedTest_20736 192 208 :=
  interval_of_check wellFormedTest_20736 192 16 (by decide +kernel)

theorem wellFormedTest_20736_block_13 : Interval wellFormedTest_20736 208 224 :=
  interval_of_check wellFormedTest_20736 208 16 (by decide +kernel)

theorem wellFormedTest_20736_block_14 : Interval wellFormedTest_20736 224 240 :=
  interval_of_check wellFormedTest_20736 224 16 (by decide +kernel)

theorem wellFormedTest_20736_block_15 : Interval wellFormedTest_20736 240 256 :=
  interval_of_check wellFormedTest_20736 240 16 (by decide +kernel)

theorem wellFormedTest_20736_complete : Interval wellFormedTest_20736 0 256 :=
  (interval_append wellFormedTest_20736 0 128 256
  (interval_append wellFormedTest_20736 0 64 128
  (interval_append wellFormedTest_20736 0 32 64
  (interval_append wellFormedTest_20736 0 16 32
  wellFormedTest_20736_block_0
  wellFormedTest_20736_block_1)
  (interval_append wellFormedTest_20736 32 48 64
  wellFormedTest_20736_block_2
  wellFormedTest_20736_block_3))
  (interval_append wellFormedTest_20736 64 96 128
  (interval_append wellFormedTest_20736 64 80 96
  wellFormedTest_20736_block_4
  wellFormedTest_20736_block_5)
  (interval_append wellFormedTest_20736 96 112 128
  wellFormedTest_20736_block_6
  wellFormedTest_20736_block_7)))
  (interval_append wellFormedTest_20736 128 192 256
  (interval_append wellFormedTest_20736 128 160 192
  (interval_append wellFormedTest_20736 128 144 160
  wellFormedTest_20736_block_8
  wellFormedTest_20736_block_9)
  (interval_append wellFormedTest_20736 160 176 192
  wellFormedTest_20736_block_10
  wellFormedTest_20736_block_11))
  (interval_append wellFormedTest_20736 192 224 256
  (interval_append wellFormedTest_20736 192 208 224
  wellFormedTest_20736_block_12
  wellFormedTest_20736_block_13)
  (interval_append wellFormedTest_20736 224 240 256
  wellFormedTest_20736_block_14
  wellFormedTest_20736_block_15))))
theorem wellFormedTestInterval20736 : Interval wellFormedTest 20736 20992 := by
  intro i hlo hhi
  have h := wellFormedTest_20736_complete (i-20736) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_20736, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed082 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_20992 (i : Nat) := wellFormedTest (i+20992)
theorem wellFormedTest_20992_block_0 : Interval wellFormedTest_20992 0 16 :=
  interval_of_check wellFormedTest_20992 0 16 (by decide +kernel)

theorem wellFormedTest_20992_block_1 : Interval wellFormedTest_20992 16 32 :=
  interval_of_check wellFormedTest_20992 16 16 (by decide +kernel)

theorem wellFormedTest_20992_block_2 : Interval wellFormedTest_20992 32 48 :=
  interval_of_check wellFormedTest_20992 32 16 (by decide +kernel)

theorem wellFormedTest_20992_block_3 : Interval wellFormedTest_20992 48 64 :=
  interval_of_check wellFormedTest_20992 48 16 (by decide +kernel)

theorem wellFormedTest_20992_block_4 : Interval wellFormedTest_20992 64 80 :=
  interval_of_check wellFormedTest_20992 64 16 (by decide +kernel)

theorem wellFormedTest_20992_block_5 : Interval wellFormedTest_20992 80 96 :=
  interval_of_check wellFormedTest_20992 80 16 (by decide +kernel)

theorem wellFormedTest_20992_block_6 : Interval wellFormedTest_20992 96 112 :=
  interval_of_check wellFormedTest_20992 96 16 (by decide +kernel)

theorem wellFormedTest_20992_block_7 : Interval wellFormedTest_20992 112 128 :=
  interval_of_check wellFormedTest_20992 112 16 (by decide +kernel)

theorem wellFormedTest_20992_block_8 : Interval wellFormedTest_20992 128 144 :=
  interval_of_check wellFormedTest_20992 128 16 (by decide +kernel)

theorem wellFormedTest_20992_block_9 : Interval wellFormedTest_20992 144 160 :=
  interval_of_check wellFormedTest_20992 144 16 (by decide +kernel)

theorem wellFormedTest_20992_block_10 : Interval wellFormedTest_20992 160 176 :=
  interval_of_check wellFormedTest_20992 160 16 (by decide +kernel)

theorem wellFormedTest_20992_block_11 : Interval wellFormedTest_20992 176 192 :=
  interval_of_check wellFormedTest_20992 176 16 (by decide +kernel)

theorem wellFormedTest_20992_block_12 : Interval wellFormedTest_20992 192 208 :=
  interval_of_check wellFormedTest_20992 192 16 (by decide +kernel)

theorem wellFormedTest_20992_block_13 : Interval wellFormedTest_20992 208 224 :=
  interval_of_check wellFormedTest_20992 208 16 (by decide +kernel)

theorem wellFormedTest_20992_block_14 : Interval wellFormedTest_20992 224 240 :=
  interval_of_check wellFormedTest_20992 224 16 (by decide +kernel)

theorem wellFormedTest_20992_block_15 : Interval wellFormedTest_20992 240 256 :=
  interval_of_check wellFormedTest_20992 240 16 (by decide +kernel)

theorem wellFormedTest_20992_complete : Interval wellFormedTest_20992 0 256 :=
  (interval_append wellFormedTest_20992 0 128 256
  (interval_append wellFormedTest_20992 0 64 128
  (interval_append wellFormedTest_20992 0 32 64
  (interval_append wellFormedTest_20992 0 16 32
  wellFormedTest_20992_block_0
  wellFormedTest_20992_block_1)
  (interval_append wellFormedTest_20992 32 48 64
  wellFormedTest_20992_block_2
  wellFormedTest_20992_block_3))
  (interval_append wellFormedTest_20992 64 96 128
  (interval_append wellFormedTest_20992 64 80 96
  wellFormedTest_20992_block_4
  wellFormedTest_20992_block_5)
  (interval_append wellFormedTest_20992 96 112 128
  wellFormedTest_20992_block_6
  wellFormedTest_20992_block_7)))
  (interval_append wellFormedTest_20992 128 192 256
  (interval_append wellFormedTest_20992 128 160 192
  (interval_append wellFormedTest_20992 128 144 160
  wellFormedTest_20992_block_8
  wellFormedTest_20992_block_9)
  (interval_append wellFormedTest_20992 160 176 192
  wellFormedTest_20992_block_10
  wellFormedTest_20992_block_11))
  (interval_append wellFormedTest_20992 192 224 256
  (interval_append wellFormedTest_20992 192 208 224
  wellFormedTest_20992_block_12
  wellFormedTest_20992_block_13)
  (interval_append wellFormedTest_20992 224 240 256
  wellFormedTest_20992_block_14
  wellFormedTest_20992_block_15))))
theorem wellFormedTestInterval20992 : Interval wellFormedTest 20992 21248 := by
  intro i hlo hhi
  have h := wellFormedTest_20992_complete (i-20992) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_20992, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed083 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_21248 (i : Nat) := wellFormedTest (i+21248)
theorem wellFormedTest_21248_block_0 : Interval wellFormedTest_21248 0 16 :=
  interval_of_check wellFormedTest_21248 0 16 (by decide +kernel)

theorem wellFormedTest_21248_block_1 : Interval wellFormedTest_21248 16 32 :=
  interval_of_check wellFormedTest_21248 16 16 (by decide +kernel)

theorem wellFormedTest_21248_block_2 : Interval wellFormedTest_21248 32 48 :=
  interval_of_check wellFormedTest_21248 32 16 (by decide +kernel)

theorem wellFormedTest_21248_block_3 : Interval wellFormedTest_21248 48 64 :=
  interval_of_check wellFormedTest_21248 48 16 (by decide +kernel)

theorem wellFormedTest_21248_block_4 : Interval wellFormedTest_21248 64 80 :=
  interval_of_check wellFormedTest_21248 64 16 (by decide +kernel)

theorem wellFormedTest_21248_block_5 : Interval wellFormedTest_21248 80 96 :=
  interval_of_check wellFormedTest_21248 80 16 (by decide +kernel)

theorem wellFormedTest_21248_block_6 : Interval wellFormedTest_21248 96 112 :=
  interval_of_check wellFormedTest_21248 96 16 (by decide +kernel)

theorem wellFormedTest_21248_block_7 : Interval wellFormedTest_21248 112 128 :=
  interval_of_check wellFormedTest_21248 112 16 (by decide +kernel)

theorem wellFormedTest_21248_block_8 : Interval wellFormedTest_21248 128 144 :=
  interval_of_check wellFormedTest_21248 128 16 (by decide +kernel)

theorem wellFormedTest_21248_block_9 : Interval wellFormedTest_21248 144 160 :=
  interval_of_check wellFormedTest_21248 144 16 (by decide +kernel)

theorem wellFormedTest_21248_block_10 : Interval wellFormedTest_21248 160 176 :=
  interval_of_check wellFormedTest_21248 160 16 (by decide +kernel)

theorem wellFormedTest_21248_block_11 : Interval wellFormedTest_21248 176 192 :=
  interval_of_check wellFormedTest_21248 176 16 (by decide +kernel)

theorem wellFormedTest_21248_block_12 : Interval wellFormedTest_21248 192 208 :=
  interval_of_check wellFormedTest_21248 192 16 (by decide +kernel)

theorem wellFormedTest_21248_block_13 : Interval wellFormedTest_21248 208 224 :=
  interval_of_check wellFormedTest_21248 208 16 (by decide +kernel)

theorem wellFormedTest_21248_block_14 : Interval wellFormedTest_21248 224 240 :=
  interval_of_check wellFormedTest_21248 224 16 (by decide +kernel)

theorem wellFormedTest_21248_block_15 : Interval wellFormedTest_21248 240 256 :=
  interval_of_check wellFormedTest_21248 240 16 (by decide +kernel)

theorem wellFormedTest_21248_complete : Interval wellFormedTest_21248 0 256 :=
  (interval_append wellFormedTest_21248 0 128 256
  (interval_append wellFormedTest_21248 0 64 128
  (interval_append wellFormedTest_21248 0 32 64
  (interval_append wellFormedTest_21248 0 16 32
  wellFormedTest_21248_block_0
  wellFormedTest_21248_block_1)
  (interval_append wellFormedTest_21248 32 48 64
  wellFormedTest_21248_block_2
  wellFormedTest_21248_block_3))
  (interval_append wellFormedTest_21248 64 96 128
  (interval_append wellFormedTest_21248 64 80 96
  wellFormedTest_21248_block_4
  wellFormedTest_21248_block_5)
  (interval_append wellFormedTest_21248 96 112 128
  wellFormedTest_21248_block_6
  wellFormedTest_21248_block_7)))
  (interval_append wellFormedTest_21248 128 192 256
  (interval_append wellFormedTest_21248 128 160 192
  (interval_append wellFormedTest_21248 128 144 160
  wellFormedTest_21248_block_8
  wellFormedTest_21248_block_9)
  (interval_append wellFormedTest_21248 160 176 192
  wellFormedTest_21248_block_10
  wellFormedTest_21248_block_11))
  (interval_append wellFormedTest_21248 192 224 256
  (interval_append wellFormedTest_21248 192 208 224
  wellFormedTest_21248_block_12
  wellFormedTest_21248_block_13)
  (interval_append wellFormedTest_21248 224 240 256
  wellFormedTest_21248_block_14
  wellFormedTest_21248_block_15))))
theorem wellFormedTestInterval21248 : Interval wellFormedTest 21248 21504 := by
  intro i hlo hhi
  have h := wellFormedTest_21248_complete (i-21248) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_21248, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
