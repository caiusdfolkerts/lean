module
prelude
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheWellFormed020 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed021 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed022 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed023 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed024 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_6144 (i : Nat) := wellFormedTest (i+6144)
theorem wellFormedTest_6144_block_0 : Interval wellFormedTest_6144 0 16 :=
  interval_of_check wellFormedTest_6144 0 16 (by decide +kernel)

theorem wellFormedTest_6144_block_1 : Interval wellFormedTest_6144 16 32 :=
  interval_of_check wellFormedTest_6144 16 16 (by decide +kernel)

theorem wellFormedTest_6144_block_2 : Interval wellFormedTest_6144 32 48 :=
  interval_of_check wellFormedTest_6144 32 16 (by decide +kernel)

theorem wellFormedTest_6144_block_3 : Interval wellFormedTest_6144 48 64 :=
  interval_of_check wellFormedTest_6144 48 16 (by decide +kernel)

theorem wellFormedTest_6144_block_4 : Interval wellFormedTest_6144 64 80 :=
  interval_of_check wellFormedTest_6144 64 16 (by decide +kernel)

theorem wellFormedTest_6144_block_5 : Interval wellFormedTest_6144 80 96 :=
  interval_of_check wellFormedTest_6144 80 16 (by decide +kernel)

theorem wellFormedTest_6144_block_6 : Interval wellFormedTest_6144 96 112 :=
  interval_of_check wellFormedTest_6144 96 16 (by decide +kernel)

theorem wellFormedTest_6144_block_7 : Interval wellFormedTest_6144 112 128 :=
  interval_of_check wellFormedTest_6144 112 16 (by decide +kernel)

theorem wellFormedTest_6144_block_8 : Interval wellFormedTest_6144 128 144 :=
  interval_of_check wellFormedTest_6144 128 16 (by decide +kernel)

theorem wellFormedTest_6144_block_9 : Interval wellFormedTest_6144 144 160 :=
  interval_of_check wellFormedTest_6144 144 16 (by decide +kernel)

theorem wellFormedTest_6144_block_10 : Interval wellFormedTest_6144 160 176 :=
  interval_of_check wellFormedTest_6144 160 16 (by decide +kernel)

theorem wellFormedTest_6144_block_11 : Interval wellFormedTest_6144 176 192 :=
  interval_of_check wellFormedTest_6144 176 16 (by decide +kernel)

theorem wellFormedTest_6144_block_12 : Interval wellFormedTest_6144 192 208 :=
  interval_of_check wellFormedTest_6144 192 16 (by decide +kernel)

theorem wellFormedTest_6144_block_13 : Interval wellFormedTest_6144 208 224 :=
  interval_of_check wellFormedTest_6144 208 16 (by decide +kernel)

theorem wellFormedTest_6144_block_14 : Interval wellFormedTest_6144 224 240 :=
  interval_of_check wellFormedTest_6144 224 16 (by decide +kernel)

theorem wellFormedTest_6144_block_15 : Interval wellFormedTest_6144 240 256 :=
  interval_of_check wellFormedTest_6144 240 16 (by decide +kernel)

theorem wellFormedTest_6144_complete : Interval wellFormedTest_6144 0 256 :=
  (interval_append wellFormedTest_6144 0 128 256
  (interval_append wellFormedTest_6144 0 64 128
  (interval_append wellFormedTest_6144 0 32 64
  (interval_append wellFormedTest_6144 0 16 32
  wellFormedTest_6144_block_0
  wellFormedTest_6144_block_1)
  (interval_append wellFormedTest_6144 32 48 64
  wellFormedTest_6144_block_2
  wellFormedTest_6144_block_3))
  (interval_append wellFormedTest_6144 64 96 128
  (interval_append wellFormedTest_6144 64 80 96
  wellFormedTest_6144_block_4
  wellFormedTest_6144_block_5)
  (interval_append wellFormedTest_6144 96 112 128
  wellFormedTest_6144_block_6
  wellFormedTest_6144_block_7)))
  (interval_append wellFormedTest_6144 128 192 256
  (interval_append wellFormedTest_6144 128 160 192
  (interval_append wellFormedTest_6144 128 144 160
  wellFormedTest_6144_block_8
  wellFormedTest_6144_block_9)
  (interval_append wellFormedTest_6144 160 176 192
  wellFormedTest_6144_block_10
  wellFormedTest_6144_block_11))
  (interval_append wellFormedTest_6144 192 224 256
  (interval_append wellFormedTest_6144 192 208 224
  wellFormedTest_6144_block_12
  wellFormedTest_6144_block_13)
  (interval_append wellFormedTest_6144 224 240 256
  wellFormedTest_6144_block_14
  wellFormedTest_6144_block_15))))
theorem wellFormedTestInterval6144 : Interval wellFormedTest 6144 6400 := by
  intro i hlo hhi
  have h := wellFormedTest_6144_complete (i-6144) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_6144, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed025 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_6400 (i : Nat) := wellFormedTest (i+6400)
theorem wellFormedTest_6400_block_0 : Interval wellFormedTest_6400 0 16 :=
  interval_of_check wellFormedTest_6400 0 16 (by decide +kernel)

theorem wellFormedTest_6400_block_1 : Interval wellFormedTest_6400 16 32 :=
  interval_of_check wellFormedTest_6400 16 16 (by decide +kernel)

theorem wellFormedTest_6400_block_2 : Interval wellFormedTest_6400 32 48 :=
  interval_of_check wellFormedTest_6400 32 16 (by decide +kernel)

theorem wellFormedTest_6400_block_3 : Interval wellFormedTest_6400 48 64 :=
  interval_of_check wellFormedTest_6400 48 16 (by decide +kernel)

theorem wellFormedTest_6400_block_4 : Interval wellFormedTest_6400 64 80 :=
  interval_of_check wellFormedTest_6400 64 16 (by decide +kernel)

theorem wellFormedTest_6400_block_5 : Interval wellFormedTest_6400 80 96 :=
  interval_of_check wellFormedTest_6400 80 16 (by decide +kernel)

theorem wellFormedTest_6400_block_6 : Interval wellFormedTest_6400 96 112 :=
  interval_of_check wellFormedTest_6400 96 16 (by decide +kernel)

theorem wellFormedTest_6400_block_7 : Interval wellFormedTest_6400 112 128 :=
  interval_of_check wellFormedTest_6400 112 16 (by decide +kernel)

theorem wellFormedTest_6400_block_8 : Interval wellFormedTest_6400 128 144 :=
  interval_of_check wellFormedTest_6400 128 16 (by decide +kernel)

theorem wellFormedTest_6400_block_9 : Interval wellFormedTest_6400 144 160 :=
  interval_of_check wellFormedTest_6400 144 16 (by decide +kernel)

theorem wellFormedTest_6400_block_10 : Interval wellFormedTest_6400 160 176 :=
  interval_of_check wellFormedTest_6400 160 16 (by decide +kernel)

theorem wellFormedTest_6400_block_11 : Interval wellFormedTest_6400 176 192 :=
  interval_of_check wellFormedTest_6400 176 16 (by decide +kernel)

theorem wellFormedTest_6400_block_12 : Interval wellFormedTest_6400 192 208 :=
  interval_of_check wellFormedTest_6400 192 16 (by decide +kernel)

theorem wellFormedTest_6400_block_13 : Interval wellFormedTest_6400 208 224 :=
  interval_of_check wellFormedTest_6400 208 16 (by decide +kernel)

theorem wellFormedTest_6400_block_14 : Interval wellFormedTest_6400 224 240 :=
  interval_of_check wellFormedTest_6400 224 16 (by decide +kernel)

theorem wellFormedTest_6400_block_15 : Interval wellFormedTest_6400 240 256 :=
  interval_of_check wellFormedTest_6400 240 16 (by decide +kernel)

theorem wellFormedTest_6400_complete : Interval wellFormedTest_6400 0 256 :=
  (interval_append wellFormedTest_6400 0 128 256
  (interval_append wellFormedTest_6400 0 64 128
  (interval_append wellFormedTest_6400 0 32 64
  (interval_append wellFormedTest_6400 0 16 32
  wellFormedTest_6400_block_0
  wellFormedTest_6400_block_1)
  (interval_append wellFormedTest_6400 32 48 64
  wellFormedTest_6400_block_2
  wellFormedTest_6400_block_3))
  (interval_append wellFormedTest_6400 64 96 128
  (interval_append wellFormedTest_6400 64 80 96
  wellFormedTest_6400_block_4
  wellFormedTest_6400_block_5)
  (interval_append wellFormedTest_6400 96 112 128
  wellFormedTest_6400_block_6
  wellFormedTest_6400_block_7)))
  (interval_append wellFormedTest_6400 128 192 256
  (interval_append wellFormedTest_6400 128 160 192
  (interval_append wellFormedTest_6400 128 144 160
  wellFormedTest_6400_block_8
  wellFormedTest_6400_block_9)
  (interval_append wellFormedTest_6400 160 176 192
  wellFormedTest_6400_block_10
  wellFormedTest_6400_block_11))
  (interval_append wellFormedTest_6400 192 224 256
  (interval_append wellFormedTest_6400 192 208 224
  wellFormedTest_6400_block_12
  wellFormedTest_6400_block_13)
  (interval_append wellFormedTest_6400 224 240 256
  wellFormedTest_6400_block_14
  wellFormedTest_6400_block_15))))
theorem wellFormedTestInterval6400 : Interval wellFormedTest 6400 6656 := by
  intro i hlo hhi
  have h := wellFormedTest_6400_complete (i-6400) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_6400, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed026 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_6656 (i : Nat) := wellFormedTest (i+6656)
theorem wellFormedTest_6656_block_0 : Interval wellFormedTest_6656 0 16 :=
  interval_of_check wellFormedTest_6656 0 16 (by decide +kernel)

theorem wellFormedTest_6656_block_1 : Interval wellFormedTest_6656 16 32 :=
  interval_of_check wellFormedTest_6656 16 16 (by decide +kernel)

theorem wellFormedTest_6656_block_2 : Interval wellFormedTest_6656 32 48 :=
  interval_of_check wellFormedTest_6656 32 16 (by decide +kernel)

theorem wellFormedTest_6656_block_3 : Interval wellFormedTest_6656 48 64 :=
  interval_of_check wellFormedTest_6656 48 16 (by decide +kernel)

theorem wellFormedTest_6656_block_4 : Interval wellFormedTest_6656 64 80 :=
  interval_of_check wellFormedTest_6656 64 16 (by decide +kernel)

theorem wellFormedTest_6656_block_5 : Interval wellFormedTest_6656 80 96 :=
  interval_of_check wellFormedTest_6656 80 16 (by decide +kernel)

theorem wellFormedTest_6656_block_6 : Interval wellFormedTest_6656 96 112 :=
  interval_of_check wellFormedTest_6656 96 16 (by decide +kernel)

theorem wellFormedTest_6656_block_7 : Interval wellFormedTest_6656 112 128 :=
  interval_of_check wellFormedTest_6656 112 16 (by decide +kernel)

theorem wellFormedTest_6656_block_8 : Interval wellFormedTest_6656 128 144 :=
  interval_of_check wellFormedTest_6656 128 16 (by decide +kernel)

theorem wellFormedTest_6656_block_9 : Interval wellFormedTest_6656 144 160 :=
  interval_of_check wellFormedTest_6656 144 16 (by decide +kernel)

theorem wellFormedTest_6656_block_10 : Interval wellFormedTest_6656 160 176 :=
  interval_of_check wellFormedTest_6656 160 16 (by decide +kernel)

theorem wellFormedTest_6656_block_11 : Interval wellFormedTest_6656 176 192 :=
  interval_of_check wellFormedTest_6656 176 16 (by decide +kernel)

theorem wellFormedTest_6656_block_12 : Interval wellFormedTest_6656 192 208 :=
  interval_of_check wellFormedTest_6656 192 16 (by decide +kernel)

theorem wellFormedTest_6656_block_13 : Interval wellFormedTest_6656 208 224 :=
  interval_of_check wellFormedTest_6656 208 16 (by decide +kernel)

theorem wellFormedTest_6656_block_14 : Interval wellFormedTest_6656 224 240 :=
  interval_of_check wellFormedTest_6656 224 16 (by decide +kernel)

theorem wellFormedTest_6656_block_15 : Interval wellFormedTest_6656 240 256 :=
  interval_of_check wellFormedTest_6656 240 16 (by decide +kernel)

theorem wellFormedTest_6656_complete : Interval wellFormedTest_6656 0 256 :=
  (interval_append wellFormedTest_6656 0 128 256
  (interval_append wellFormedTest_6656 0 64 128
  (interval_append wellFormedTest_6656 0 32 64
  (interval_append wellFormedTest_6656 0 16 32
  wellFormedTest_6656_block_0
  wellFormedTest_6656_block_1)
  (interval_append wellFormedTest_6656 32 48 64
  wellFormedTest_6656_block_2
  wellFormedTest_6656_block_3))
  (interval_append wellFormedTest_6656 64 96 128
  (interval_append wellFormedTest_6656 64 80 96
  wellFormedTest_6656_block_4
  wellFormedTest_6656_block_5)
  (interval_append wellFormedTest_6656 96 112 128
  wellFormedTest_6656_block_6
  wellFormedTest_6656_block_7)))
  (interval_append wellFormedTest_6656 128 192 256
  (interval_append wellFormedTest_6656 128 160 192
  (interval_append wellFormedTest_6656 128 144 160
  wellFormedTest_6656_block_8
  wellFormedTest_6656_block_9)
  (interval_append wellFormedTest_6656 160 176 192
  wellFormedTest_6656_block_10
  wellFormedTest_6656_block_11))
  (interval_append wellFormedTest_6656 192 224 256
  (interval_append wellFormedTest_6656 192 208 224
  wellFormedTest_6656_block_12
  wellFormedTest_6656_block_13)
  (interval_append wellFormedTest_6656 224 240 256
  wellFormedTest_6656_block_14
  wellFormedTest_6656_block_15))))
theorem wellFormedTestInterval6656 : Interval wellFormedTest 6656 6912 := by
  intro i hlo hhi
  have h := wellFormedTest_6656_complete (i-6656) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_6656, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed027 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_6912 (i : Nat) := wellFormedTest (i+6912)
theorem wellFormedTest_6912_block_0 : Interval wellFormedTest_6912 0 16 :=
  interval_of_check wellFormedTest_6912 0 16 (by decide +kernel)

theorem wellFormedTest_6912_block_1 : Interval wellFormedTest_6912 16 32 :=
  interval_of_check wellFormedTest_6912 16 16 (by decide +kernel)

theorem wellFormedTest_6912_block_2 : Interval wellFormedTest_6912 32 48 :=
  interval_of_check wellFormedTest_6912 32 16 (by decide +kernel)

theorem wellFormedTest_6912_block_3 : Interval wellFormedTest_6912 48 64 :=
  interval_of_check wellFormedTest_6912 48 16 (by decide +kernel)

theorem wellFormedTest_6912_block_4 : Interval wellFormedTest_6912 64 80 :=
  interval_of_check wellFormedTest_6912 64 16 (by decide +kernel)

theorem wellFormedTest_6912_block_5 : Interval wellFormedTest_6912 80 96 :=
  interval_of_check wellFormedTest_6912 80 16 (by decide +kernel)

theorem wellFormedTest_6912_block_6 : Interval wellFormedTest_6912 96 112 :=
  interval_of_check wellFormedTest_6912 96 16 (by decide +kernel)

theorem wellFormedTest_6912_block_7 : Interval wellFormedTest_6912 112 128 :=
  interval_of_check wellFormedTest_6912 112 16 (by decide +kernel)

theorem wellFormedTest_6912_block_8 : Interval wellFormedTest_6912 128 144 :=
  interval_of_check wellFormedTest_6912 128 16 (by decide +kernel)

theorem wellFormedTest_6912_block_9 : Interval wellFormedTest_6912 144 160 :=
  interval_of_check wellFormedTest_6912 144 16 (by decide +kernel)

theorem wellFormedTest_6912_block_10 : Interval wellFormedTest_6912 160 176 :=
  interval_of_check wellFormedTest_6912 160 16 (by decide +kernel)

theorem wellFormedTest_6912_block_11 : Interval wellFormedTest_6912 176 192 :=
  interval_of_check wellFormedTest_6912 176 16 (by decide +kernel)

theorem wellFormedTest_6912_block_12 : Interval wellFormedTest_6912 192 208 :=
  interval_of_check wellFormedTest_6912 192 16 (by decide +kernel)

theorem wellFormedTest_6912_block_13 : Interval wellFormedTest_6912 208 224 :=
  interval_of_check wellFormedTest_6912 208 16 (by decide +kernel)

theorem wellFormedTest_6912_block_14 : Interval wellFormedTest_6912 224 240 :=
  interval_of_check wellFormedTest_6912 224 16 (by decide +kernel)

theorem wellFormedTest_6912_block_15 : Interval wellFormedTest_6912 240 256 :=
  interval_of_check wellFormedTest_6912 240 16 (by decide +kernel)

theorem wellFormedTest_6912_complete : Interval wellFormedTest_6912 0 256 :=
  (interval_append wellFormedTest_6912 0 128 256
  (interval_append wellFormedTest_6912 0 64 128
  (interval_append wellFormedTest_6912 0 32 64
  (interval_append wellFormedTest_6912 0 16 32
  wellFormedTest_6912_block_0
  wellFormedTest_6912_block_1)
  (interval_append wellFormedTest_6912 32 48 64
  wellFormedTest_6912_block_2
  wellFormedTest_6912_block_3))
  (interval_append wellFormedTest_6912 64 96 128
  (interval_append wellFormedTest_6912 64 80 96
  wellFormedTest_6912_block_4
  wellFormedTest_6912_block_5)
  (interval_append wellFormedTest_6912 96 112 128
  wellFormedTest_6912_block_6
  wellFormedTest_6912_block_7)))
  (interval_append wellFormedTest_6912 128 192 256
  (interval_append wellFormedTest_6912 128 160 192
  (interval_append wellFormedTest_6912 128 144 160
  wellFormedTest_6912_block_8
  wellFormedTest_6912_block_9)
  (interval_append wellFormedTest_6912 160 176 192
  wellFormedTest_6912_block_10
  wellFormedTest_6912_block_11))
  (interval_append wellFormedTest_6912 192 224 256
  (interval_append wellFormedTest_6912 192 208 224
  wellFormedTest_6912_block_12
  wellFormedTest_6912_block_13)
  (interval_append wellFormedTest_6912 224 240 256
  wellFormedTest_6912_block_14
  wellFormedTest_6912_block_15))))
theorem wellFormedTestInterval6912 : Interval wellFormedTest 6912 7168 := by
  intro i hlo hhi
  have h := wellFormedTest_6912_complete (i-6912) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_6912, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed028 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_7168 (i : Nat) := wellFormedTest (i+7168)
theorem wellFormedTest_7168_block_0 : Interval wellFormedTest_7168 0 16 :=
  interval_of_check wellFormedTest_7168 0 16 (by decide +kernel)

theorem wellFormedTest_7168_block_1 : Interval wellFormedTest_7168 16 32 :=
  interval_of_check wellFormedTest_7168 16 16 (by decide +kernel)

theorem wellFormedTest_7168_block_2 : Interval wellFormedTest_7168 32 48 :=
  interval_of_check wellFormedTest_7168 32 16 (by decide +kernel)

theorem wellFormedTest_7168_block_3 : Interval wellFormedTest_7168 48 64 :=
  interval_of_check wellFormedTest_7168 48 16 (by decide +kernel)

theorem wellFormedTest_7168_block_4 : Interval wellFormedTest_7168 64 80 :=
  interval_of_check wellFormedTest_7168 64 16 (by decide +kernel)

theorem wellFormedTest_7168_block_5 : Interval wellFormedTest_7168 80 96 :=
  interval_of_check wellFormedTest_7168 80 16 (by decide +kernel)

theorem wellFormedTest_7168_block_6 : Interval wellFormedTest_7168 96 112 :=
  interval_of_check wellFormedTest_7168 96 16 (by decide +kernel)

theorem wellFormedTest_7168_block_7 : Interval wellFormedTest_7168 112 128 :=
  interval_of_check wellFormedTest_7168 112 16 (by decide +kernel)

theorem wellFormedTest_7168_block_8 : Interval wellFormedTest_7168 128 144 :=
  interval_of_check wellFormedTest_7168 128 16 (by decide +kernel)

theorem wellFormedTest_7168_block_9 : Interval wellFormedTest_7168 144 160 :=
  interval_of_check wellFormedTest_7168 144 16 (by decide +kernel)

theorem wellFormedTest_7168_block_10 : Interval wellFormedTest_7168 160 176 :=
  interval_of_check wellFormedTest_7168 160 16 (by decide +kernel)

theorem wellFormedTest_7168_block_11 : Interval wellFormedTest_7168 176 192 :=
  interval_of_check wellFormedTest_7168 176 16 (by decide +kernel)

theorem wellFormedTest_7168_block_12 : Interval wellFormedTest_7168 192 208 :=
  interval_of_check wellFormedTest_7168 192 16 (by decide +kernel)

theorem wellFormedTest_7168_block_13 : Interval wellFormedTest_7168 208 224 :=
  interval_of_check wellFormedTest_7168 208 16 (by decide +kernel)

theorem wellFormedTest_7168_block_14 : Interval wellFormedTest_7168 224 240 :=
  interval_of_check wellFormedTest_7168 224 16 (by decide +kernel)

theorem wellFormedTest_7168_block_15 : Interval wellFormedTest_7168 240 256 :=
  interval_of_check wellFormedTest_7168 240 16 (by decide +kernel)

theorem wellFormedTest_7168_complete : Interval wellFormedTest_7168 0 256 :=
  (interval_append wellFormedTest_7168 0 128 256
  (interval_append wellFormedTest_7168 0 64 128
  (interval_append wellFormedTest_7168 0 32 64
  (interval_append wellFormedTest_7168 0 16 32
  wellFormedTest_7168_block_0
  wellFormedTest_7168_block_1)
  (interval_append wellFormedTest_7168 32 48 64
  wellFormedTest_7168_block_2
  wellFormedTest_7168_block_3))
  (interval_append wellFormedTest_7168 64 96 128
  (interval_append wellFormedTest_7168 64 80 96
  wellFormedTest_7168_block_4
  wellFormedTest_7168_block_5)
  (interval_append wellFormedTest_7168 96 112 128
  wellFormedTest_7168_block_6
  wellFormedTest_7168_block_7)))
  (interval_append wellFormedTest_7168 128 192 256
  (interval_append wellFormedTest_7168 128 160 192
  (interval_append wellFormedTest_7168 128 144 160
  wellFormedTest_7168_block_8
  wellFormedTest_7168_block_9)
  (interval_append wellFormedTest_7168 160 176 192
  wellFormedTest_7168_block_10
  wellFormedTest_7168_block_11))
  (interval_append wellFormedTest_7168 192 224 256
  (interval_append wellFormedTest_7168 192 208 224
  wellFormedTest_7168_block_12
  wellFormedTest_7168_block_13)
  (interval_append wellFormedTest_7168 224 240 256
  wellFormedTest_7168_block_14
  wellFormedTest_7168_block_15))))
theorem wellFormedTestInterval7168 : Interval wellFormedTest 7168 7424 := by
  intro i hlo hhi
  have h := wellFormedTest_7168_complete (i-7168) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_7168, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed029 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_7424 (i : Nat) := wellFormedTest (i+7424)
theorem wellFormedTest_7424_block_0 : Interval wellFormedTest_7424 0 16 :=
  interval_of_check wellFormedTest_7424 0 16 (by decide +kernel)

theorem wellFormedTest_7424_block_1 : Interval wellFormedTest_7424 16 32 :=
  interval_of_check wellFormedTest_7424 16 16 (by decide +kernel)

theorem wellFormedTest_7424_block_2 : Interval wellFormedTest_7424 32 48 :=
  interval_of_check wellFormedTest_7424 32 16 (by decide +kernel)

theorem wellFormedTest_7424_block_3 : Interval wellFormedTest_7424 48 64 :=
  interval_of_check wellFormedTest_7424 48 16 (by decide +kernel)

theorem wellFormedTest_7424_block_4 : Interval wellFormedTest_7424 64 80 :=
  interval_of_check wellFormedTest_7424 64 16 (by decide +kernel)

theorem wellFormedTest_7424_block_5 : Interval wellFormedTest_7424 80 96 :=
  interval_of_check wellFormedTest_7424 80 16 (by decide +kernel)

theorem wellFormedTest_7424_block_6 : Interval wellFormedTest_7424 96 112 :=
  interval_of_check wellFormedTest_7424 96 16 (by decide +kernel)

theorem wellFormedTest_7424_block_7 : Interval wellFormedTest_7424 112 128 :=
  interval_of_check wellFormedTest_7424 112 16 (by decide +kernel)

theorem wellFormedTest_7424_block_8 : Interval wellFormedTest_7424 128 144 :=
  interval_of_check wellFormedTest_7424 128 16 (by decide +kernel)

theorem wellFormedTest_7424_block_9 : Interval wellFormedTest_7424 144 160 :=
  interval_of_check wellFormedTest_7424 144 16 (by decide +kernel)

theorem wellFormedTest_7424_block_10 : Interval wellFormedTest_7424 160 176 :=
  interval_of_check wellFormedTest_7424 160 16 (by decide +kernel)

theorem wellFormedTest_7424_block_11 : Interval wellFormedTest_7424 176 192 :=
  interval_of_check wellFormedTest_7424 176 16 (by decide +kernel)

theorem wellFormedTest_7424_block_12 : Interval wellFormedTest_7424 192 208 :=
  interval_of_check wellFormedTest_7424 192 16 (by decide +kernel)

theorem wellFormedTest_7424_block_13 : Interval wellFormedTest_7424 208 224 :=
  interval_of_check wellFormedTest_7424 208 16 (by decide +kernel)

theorem wellFormedTest_7424_block_14 : Interval wellFormedTest_7424 224 240 :=
  interval_of_check wellFormedTest_7424 224 16 (by decide +kernel)

theorem wellFormedTest_7424_block_15 : Interval wellFormedTest_7424 240 256 :=
  interval_of_check wellFormedTest_7424 240 16 (by decide +kernel)

theorem wellFormedTest_7424_complete : Interval wellFormedTest_7424 0 256 :=
  (interval_append wellFormedTest_7424 0 128 256
  (interval_append wellFormedTest_7424 0 64 128
  (interval_append wellFormedTest_7424 0 32 64
  (interval_append wellFormedTest_7424 0 16 32
  wellFormedTest_7424_block_0
  wellFormedTest_7424_block_1)
  (interval_append wellFormedTest_7424 32 48 64
  wellFormedTest_7424_block_2
  wellFormedTest_7424_block_3))
  (interval_append wellFormedTest_7424 64 96 128
  (interval_append wellFormedTest_7424 64 80 96
  wellFormedTest_7424_block_4
  wellFormedTest_7424_block_5)
  (interval_append wellFormedTest_7424 96 112 128
  wellFormedTest_7424_block_6
  wellFormedTest_7424_block_7)))
  (interval_append wellFormedTest_7424 128 192 256
  (interval_append wellFormedTest_7424 128 160 192
  (interval_append wellFormedTest_7424 128 144 160
  wellFormedTest_7424_block_8
  wellFormedTest_7424_block_9)
  (interval_append wellFormedTest_7424 160 176 192
  wellFormedTest_7424_block_10
  wellFormedTest_7424_block_11))
  (interval_append wellFormedTest_7424 192 224 256
  (interval_append wellFormedTest_7424 192 208 224
  wellFormedTest_7424_block_12
  wellFormedTest_7424_block_13)
  (interval_append wellFormedTest_7424 224 240 256
  wellFormedTest_7424_block_14
  wellFormedTest_7424_block_15))))
theorem wellFormedTestInterval7424 : Interval wellFormedTest 7424 7680 := by
  intro i hlo hhi
  have h := wellFormedTest_7424_complete (i-7424) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_7424, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed030 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_7680 (i : Nat) := wellFormedTest (i+7680)
theorem wellFormedTest_7680_block_0 : Interval wellFormedTest_7680 0 16 :=
  interval_of_check wellFormedTest_7680 0 16 (by decide +kernel)

theorem wellFormedTest_7680_block_1 : Interval wellFormedTest_7680 16 32 :=
  interval_of_check wellFormedTest_7680 16 16 (by decide +kernel)

theorem wellFormedTest_7680_block_2 : Interval wellFormedTest_7680 32 48 :=
  interval_of_check wellFormedTest_7680 32 16 (by decide +kernel)

theorem wellFormedTest_7680_block_3 : Interval wellFormedTest_7680 48 64 :=
  interval_of_check wellFormedTest_7680 48 16 (by decide +kernel)

theorem wellFormedTest_7680_block_4 : Interval wellFormedTest_7680 64 80 :=
  interval_of_check wellFormedTest_7680 64 16 (by decide +kernel)

theorem wellFormedTest_7680_block_5 : Interval wellFormedTest_7680 80 96 :=
  interval_of_check wellFormedTest_7680 80 16 (by decide +kernel)

theorem wellFormedTest_7680_block_6 : Interval wellFormedTest_7680 96 112 :=
  interval_of_check wellFormedTest_7680 96 16 (by decide +kernel)

theorem wellFormedTest_7680_block_7 : Interval wellFormedTest_7680 112 128 :=
  interval_of_check wellFormedTest_7680 112 16 (by decide +kernel)

theorem wellFormedTest_7680_block_8 : Interval wellFormedTest_7680 128 144 :=
  interval_of_check wellFormedTest_7680 128 16 (by decide +kernel)

theorem wellFormedTest_7680_block_9 : Interval wellFormedTest_7680 144 160 :=
  interval_of_check wellFormedTest_7680 144 16 (by decide +kernel)

theorem wellFormedTest_7680_block_10 : Interval wellFormedTest_7680 160 176 :=
  interval_of_check wellFormedTest_7680 160 16 (by decide +kernel)

theorem wellFormedTest_7680_block_11 : Interval wellFormedTest_7680 176 192 :=
  interval_of_check wellFormedTest_7680 176 16 (by decide +kernel)

theorem wellFormedTest_7680_block_12 : Interval wellFormedTest_7680 192 208 :=
  interval_of_check wellFormedTest_7680 192 16 (by decide +kernel)

theorem wellFormedTest_7680_block_13 : Interval wellFormedTest_7680 208 224 :=
  interval_of_check wellFormedTest_7680 208 16 (by decide +kernel)

theorem wellFormedTest_7680_block_14 : Interval wellFormedTest_7680 224 240 :=
  interval_of_check wellFormedTest_7680 224 16 (by decide +kernel)

theorem wellFormedTest_7680_block_15 : Interval wellFormedTest_7680 240 256 :=
  interval_of_check wellFormedTest_7680 240 16 (by decide +kernel)

theorem wellFormedTest_7680_complete : Interval wellFormedTest_7680 0 256 :=
  (interval_append wellFormedTest_7680 0 128 256
  (interval_append wellFormedTest_7680 0 64 128
  (interval_append wellFormedTest_7680 0 32 64
  (interval_append wellFormedTest_7680 0 16 32
  wellFormedTest_7680_block_0
  wellFormedTest_7680_block_1)
  (interval_append wellFormedTest_7680 32 48 64
  wellFormedTest_7680_block_2
  wellFormedTest_7680_block_3))
  (interval_append wellFormedTest_7680 64 96 128
  (interval_append wellFormedTest_7680 64 80 96
  wellFormedTest_7680_block_4
  wellFormedTest_7680_block_5)
  (interval_append wellFormedTest_7680 96 112 128
  wellFormedTest_7680_block_6
  wellFormedTest_7680_block_7)))
  (interval_append wellFormedTest_7680 128 192 256
  (interval_append wellFormedTest_7680 128 160 192
  (interval_append wellFormedTest_7680 128 144 160
  wellFormedTest_7680_block_8
  wellFormedTest_7680_block_9)
  (interval_append wellFormedTest_7680 160 176 192
  wellFormedTest_7680_block_10
  wellFormedTest_7680_block_11))
  (interval_append wellFormedTest_7680 192 224 256
  (interval_append wellFormedTest_7680 192 208 224
  wellFormedTest_7680_block_12
  wellFormedTest_7680_block_13)
  (interval_append wellFormedTest_7680 224 240 256
  wellFormedTest_7680_block_14
  wellFormedTest_7680_block_15))))
theorem wellFormedTestInterval7680 : Interval wellFormedTest 7680 7936 := by
  intro i hlo hhi
  have h := wellFormedTest_7680_complete (i-7680) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_7680, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed031 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_7936 (i : Nat) := wellFormedTest (i+7936)
theorem wellFormedTest_7936_block_0 : Interval wellFormedTest_7936 0 16 :=
  interval_of_check wellFormedTest_7936 0 16 (by decide +kernel)

theorem wellFormedTest_7936_block_1 : Interval wellFormedTest_7936 16 32 :=
  interval_of_check wellFormedTest_7936 16 16 (by decide +kernel)

theorem wellFormedTest_7936_block_2 : Interval wellFormedTest_7936 32 48 :=
  interval_of_check wellFormedTest_7936 32 16 (by decide +kernel)

theorem wellFormedTest_7936_block_3 : Interval wellFormedTest_7936 48 64 :=
  interval_of_check wellFormedTest_7936 48 16 (by decide +kernel)

theorem wellFormedTest_7936_block_4 : Interval wellFormedTest_7936 64 80 :=
  interval_of_check wellFormedTest_7936 64 16 (by decide +kernel)

theorem wellFormedTest_7936_block_5 : Interval wellFormedTest_7936 80 96 :=
  interval_of_check wellFormedTest_7936 80 16 (by decide +kernel)

theorem wellFormedTest_7936_block_6 : Interval wellFormedTest_7936 96 112 :=
  interval_of_check wellFormedTest_7936 96 16 (by decide +kernel)

theorem wellFormedTest_7936_block_7 : Interval wellFormedTest_7936 112 128 :=
  interval_of_check wellFormedTest_7936 112 16 (by decide +kernel)

theorem wellFormedTest_7936_block_8 : Interval wellFormedTest_7936 128 144 :=
  interval_of_check wellFormedTest_7936 128 16 (by decide +kernel)

theorem wellFormedTest_7936_block_9 : Interval wellFormedTest_7936 144 160 :=
  interval_of_check wellFormedTest_7936 144 16 (by decide +kernel)

theorem wellFormedTest_7936_block_10 : Interval wellFormedTest_7936 160 176 :=
  interval_of_check wellFormedTest_7936 160 16 (by decide +kernel)

theorem wellFormedTest_7936_block_11 : Interval wellFormedTest_7936 176 192 :=
  interval_of_check wellFormedTest_7936 176 16 (by decide +kernel)

theorem wellFormedTest_7936_block_12 : Interval wellFormedTest_7936 192 208 :=
  interval_of_check wellFormedTest_7936 192 16 (by decide +kernel)

theorem wellFormedTest_7936_block_13 : Interval wellFormedTest_7936 208 224 :=
  interval_of_check wellFormedTest_7936 208 16 (by decide +kernel)

theorem wellFormedTest_7936_block_14 : Interval wellFormedTest_7936 224 240 :=
  interval_of_check wellFormedTest_7936 224 16 (by decide +kernel)

theorem wellFormedTest_7936_block_15 : Interval wellFormedTest_7936 240 256 :=
  interval_of_check wellFormedTest_7936 240 16 (by decide +kernel)

theorem wellFormedTest_7936_complete : Interval wellFormedTest_7936 0 256 :=
  (interval_append wellFormedTest_7936 0 128 256
  (interval_append wellFormedTest_7936 0 64 128
  (interval_append wellFormedTest_7936 0 32 64
  (interval_append wellFormedTest_7936 0 16 32
  wellFormedTest_7936_block_0
  wellFormedTest_7936_block_1)
  (interval_append wellFormedTest_7936 32 48 64
  wellFormedTest_7936_block_2
  wellFormedTest_7936_block_3))
  (interval_append wellFormedTest_7936 64 96 128
  (interval_append wellFormedTest_7936 64 80 96
  wellFormedTest_7936_block_4
  wellFormedTest_7936_block_5)
  (interval_append wellFormedTest_7936 96 112 128
  wellFormedTest_7936_block_6
  wellFormedTest_7936_block_7)))
  (interval_append wellFormedTest_7936 128 192 256
  (interval_append wellFormedTest_7936 128 160 192
  (interval_append wellFormedTest_7936 128 144 160
  wellFormedTest_7936_block_8
  wellFormedTest_7936_block_9)
  (interval_append wellFormedTest_7936 160 176 192
  wellFormedTest_7936_block_10
  wellFormedTest_7936_block_11))
  (interval_append wellFormedTest_7936 192 224 256
  (interval_append wellFormedTest_7936 192 208 224
  wellFormedTest_7936_block_12
  wellFormedTest_7936_block_13)
  (interval_append wellFormedTest_7936 224 240 256
  wellFormedTest_7936_block_14
  wellFormedTest_7936_block_15))))
theorem wellFormedTestInterval7936 : Interval wellFormedTest 7936 8192 := by
  intro i hlo hhi
  have h := wellFormedTest_7936_complete (i-7936) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_7936, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed032 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_8192 (i : Nat) := wellFormedTest (i+8192)
theorem wellFormedTest_8192_block_0 : Interval wellFormedTest_8192 0 16 :=
  interval_of_check wellFormedTest_8192 0 16 (by decide +kernel)

theorem wellFormedTest_8192_block_1 : Interval wellFormedTest_8192 16 32 :=
  interval_of_check wellFormedTest_8192 16 16 (by decide +kernel)

theorem wellFormedTest_8192_block_2 : Interval wellFormedTest_8192 32 48 :=
  interval_of_check wellFormedTest_8192 32 16 (by decide +kernel)

theorem wellFormedTest_8192_block_3 : Interval wellFormedTest_8192 48 64 :=
  interval_of_check wellFormedTest_8192 48 16 (by decide +kernel)

theorem wellFormedTest_8192_block_4 : Interval wellFormedTest_8192 64 80 :=
  interval_of_check wellFormedTest_8192 64 16 (by decide +kernel)

theorem wellFormedTest_8192_block_5 : Interval wellFormedTest_8192 80 96 :=
  interval_of_check wellFormedTest_8192 80 16 (by decide +kernel)

theorem wellFormedTest_8192_block_6 : Interval wellFormedTest_8192 96 112 :=
  interval_of_check wellFormedTest_8192 96 16 (by decide +kernel)

theorem wellFormedTest_8192_block_7 : Interval wellFormedTest_8192 112 128 :=
  interval_of_check wellFormedTest_8192 112 16 (by decide +kernel)

theorem wellFormedTest_8192_block_8 : Interval wellFormedTest_8192 128 144 :=
  interval_of_check wellFormedTest_8192 128 16 (by decide +kernel)

theorem wellFormedTest_8192_block_9 : Interval wellFormedTest_8192 144 160 :=
  interval_of_check wellFormedTest_8192 144 16 (by decide +kernel)

theorem wellFormedTest_8192_block_10 : Interval wellFormedTest_8192 160 176 :=
  interval_of_check wellFormedTest_8192 160 16 (by decide +kernel)

theorem wellFormedTest_8192_block_11 : Interval wellFormedTest_8192 176 192 :=
  interval_of_check wellFormedTest_8192 176 16 (by decide +kernel)

theorem wellFormedTest_8192_block_12 : Interval wellFormedTest_8192 192 208 :=
  interval_of_check wellFormedTest_8192 192 16 (by decide +kernel)

theorem wellFormedTest_8192_block_13 : Interval wellFormedTest_8192 208 224 :=
  interval_of_check wellFormedTest_8192 208 16 (by decide +kernel)

theorem wellFormedTest_8192_block_14 : Interval wellFormedTest_8192 224 240 :=
  interval_of_check wellFormedTest_8192 224 16 (by decide +kernel)

theorem wellFormedTest_8192_block_15 : Interval wellFormedTest_8192 240 256 :=
  interval_of_check wellFormedTest_8192 240 16 (by decide +kernel)

theorem wellFormedTest_8192_complete : Interval wellFormedTest_8192 0 256 :=
  (interval_append wellFormedTest_8192 0 128 256
  (interval_append wellFormedTest_8192 0 64 128
  (interval_append wellFormedTest_8192 0 32 64
  (interval_append wellFormedTest_8192 0 16 32
  wellFormedTest_8192_block_0
  wellFormedTest_8192_block_1)
  (interval_append wellFormedTest_8192 32 48 64
  wellFormedTest_8192_block_2
  wellFormedTest_8192_block_3))
  (interval_append wellFormedTest_8192 64 96 128
  (interval_append wellFormedTest_8192 64 80 96
  wellFormedTest_8192_block_4
  wellFormedTest_8192_block_5)
  (interval_append wellFormedTest_8192 96 112 128
  wellFormedTest_8192_block_6
  wellFormedTest_8192_block_7)))
  (interval_append wellFormedTest_8192 128 192 256
  (interval_append wellFormedTest_8192 128 160 192
  (interval_append wellFormedTest_8192 128 144 160
  wellFormedTest_8192_block_8
  wellFormedTest_8192_block_9)
  (interval_append wellFormedTest_8192 160 176 192
  wellFormedTest_8192_block_10
  wellFormedTest_8192_block_11))
  (interval_append wellFormedTest_8192 192 224 256
  (interval_append wellFormedTest_8192 192 208 224
  wellFormedTest_8192_block_12
  wellFormedTest_8192_block_13)
  (interval_append wellFormedTest_8192 224 240 256
  wellFormedTest_8192_block_14
  wellFormedTest_8192_block_15))))
theorem wellFormedTestInterval8192 : Interval wellFormedTest 8192 8448 := by
  intro i hlo hhi
  have h := wellFormedTest_8192_complete (i-8192) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_8192, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed033 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_8448 (i : Nat) := wellFormedTest (i+8448)
theorem wellFormedTest_8448_block_0 : Interval wellFormedTest_8448 0 16 :=
  interval_of_check wellFormedTest_8448 0 16 (by decide +kernel)

theorem wellFormedTest_8448_block_1 : Interval wellFormedTest_8448 16 32 :=
  interval_of_check wellFormedTest_8448 16 16 (by decide +kernel)

theorem wellFormedTest_8448_block_2 : Interval wellFormedTest_8448 32 48 :=
  interval_of_check wellFormedTest_8448 32 16 (by decide +kernel)

theorem wellFormedTest_8448_block_3 : Interval wellFormedTest_8448 48 64 :=
  interval_of_check wellFormedTest_8448 48 16 (by decide +kernel)

theorem wellFormedTest_8448_block_4 : Interval wellFormedTest_8448 64 80 :=
  interval_of_check wellFormedTest_8448 64 16 (by decide +kernel)

theorem wellFormedTest_8448_block_5 : Interval wellFormedTest_8448 80 96 :=
  interval_of_check wellFormedTest_8448 80 16 (by decide +kernel)

theorem wellFormedTest_8448_block_6 : Interval wellFormedTest_8448 96 112 :=
  interval_of_check wellFormedTest_8448 96 16 (by decide +kernel)

theorem wellFormedTest_8448_block_7 : Interval wellFormedTest_8448 112 128 :=
  interval_of_check wellFormedTest_8448 112 16 (by decide +kernel)

theorem wellFormedTest_8448_block_8 : Interval wellFormedTest_8448 128 144 :=
  interval_of_check wellFormedTest_8448 128 16 (by decide +kernel)

theorem wellFormedTest_8448_block_9 : Interval wellFormedTest_8448 144 160 :=
  interval_of_check wellFormedTest_8448 144 16 (by decide +kernel)

theorem wellFormedTest_8448_block_10 : Interval wellFormedTest_8448 160 176 :=
  interval_of_check wellFormedTest_8448 160 16 (by decide +kernel)

theorem wellFormedTest_8448_block_11 : Interval wellFormedTest_8448 176 192 :=
  interval_of_check wellFormedTest_8448 176 16 (by decide +kernel)

theorem wellFormedTest_8448_block_12 : Interval wellFormedTest_8448 192 208 :=
  interval_of_check wellFormedTest_8448 192 16 (by decide +kernel)

theorem wellFormedTest_8448_block_13 : Interval wellFormedTest_8448 208 224 :=
  interval_of_check wellFormedTest_8448 208 16 (by decide +kernel)

theorem wellFormedTest_8448_block_14 : Interval wellFormedTest_8448 224 240 :=
  interval_of_check wellFormedTest_8448 224 16 (by decide +kernel)

theorem wellFormedTest_8448_block_15 : Interval wellFormedTest_8448 240 256 :=
  interval_of_check wellFormedTest_8448 240 16 (by decide +kernel)

theorem wellFormedTest_8448_complete : Interval wellFormedTest_8448 0 256 :=
  (interval_append wellFormedTest_8448 0 128 256
  (interval_append wellFormedTest_8448 0 64 128
  (interval_append wellFormedTest_8448 0 32 64
  (interval_append wellFormedTest_8448 0 16 32
  wellFormedTest_8448_block_0
  wellFormedTest_8448_block_1)
  (interval_append wellFormedTest_8448 32 48 64
  wellFormedTest_8448_block_2
  wellFormedTest_8448_block_3))
  (interval_append wellFormedTest_8448 64 96 128
  (interval_append wellFormedTest_8448 64 80 96
  wellFormedTest_8448_block_4
  wellFormedTest_8448_block_5)
  (interval_append wellFormedTest_8448 96 112 128
  wellFormedTest_8448_block_6
  wellFormedTest_8448_block_7)))
  (interval_append wellFormedTest_8448 128 192 256
  (interval_append wellFormedTest_8448 128 160 192
  (interval_append wellFormedTest_8448 128 144 160
  wellFormedTest_8448_block_8
  wellFormedTest_8448_block_9)
  (interval_append wellFormedTest_8448 160 176 192
  wellFormedTest_8448_block_10
  wellFormedTest_8448_block_11))
  (interval_append wellFormedTest_8448 192 224 256
  (interval_append wellFormedTest_8448 192 208 224
  wellFormedTest_8448_block_12
  wellFormedTest_8448_block_13)
  (interval_append wellFormedTest_8448 224 240 256
  wellFormedTest_8448_block_14
  wellFormedTest_8448_block_15))))
theorem wellFormedTestInterval8448 : Interval wellFormedTest 8448 8704 := by
  intro i hlo hhi
  have h := wellFormedTest_8448_complete (i-8448) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_8448, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed034 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_8704 (i : Nat) := wellFormedTest (i+8704)
theorem wellFormedTest_8704_block_0 : Interval wellFormedTest_8704 0 16 :=
  interval_of_check wellFormedTest_8704 0 16 (by decide +kernel)

theorem wellFormedTest_8704_block_1 : Interval wellFormedTest_8704 16 32 :=
  interval_of_check wellFormedTest_8704 16 16 (by decide +kernel)

theorem wellFormedTest_8704_block_2 : Interval wellFormedTest_8704 32 48 :=
  interval_of_check wellFormedTest_8704 32 16 (by decide +kernel)

theorem wellFormedTest_8704_block_3 : Interval wellFormedTest_8704 48 64 :=
  interval_of_check wellFormedTest_8704 48 16 (by decide +kernel)

theorem wellFormedTest_8704_block_4 : Interval wellFormedTest_8704 64 80 :=
  interval_of_check wellFormedTest_8704 64 16 (by decide +kernel)

theorem wellFormedTest_8704_block_5 : Interval wellFormedTest_8704 80 96 :=
  interval_of_check wellFormedTest_8704 80 16 (by decide +kernel)

theorem wellFormedTest_8704_block_6 : Interval wellFormedTest_8704 96 112 :=
  interval_of_check wellFormedTest_8704 96 16 (by decide +kernel)

theorem wellFormedTest_8704_block_7 : Interval wellFormedTest_8704 112 128 :=
  interval_of_check wellFormedTest_8704 112 16 (by decide +kernel)

theorem wellFormedTest_8704_block_8 : Interval wellFormedTest_8704 128 144 :=
  interval_of_check wellFormedTest_8704 128 16 (by decide +kernel)

theorem wellFormedTest_8704_block_9 : Interval wellFormedTest_8704 144 160 :=
  interval_of_check wellFormedTest_8704 144 16 (by decide +kernel)

theorem wellFormedTest_8704_block_10 : Interval wellFormedTest_8704 160 176 :=
  interval_of_check wellFormedTest_8704 160 16 (by decide +kernel)

theorem wellFormedTest_8704_block_11 : Interval wellFormedTest_8704 176 192 :=
  interval_of_check wellFormedTest_8704 176 16 (by decide +kernel)

theorem wellFormedTest_8704_block_12 : Interval wellFormedTest_8704 192 208 :=
  interval_of_check wellFormedTest_8704 192 16 (by decide +kernel)

theorem wellFormedTest_8704_block_13 : Interval wellFormedTest_8704 208 224 :=
  interval_of_check wellFormedTest_8704 208 16 (by decide +kernel)

theorem wellFormedTest_8704_block_14 : Interval wellFormedTest_8704 224 240 :=
  interval_of_check wellFormedTest_8704 224 16 (by decide +kernel)

theorem wellFormedTest_8704_block_15 : Interval wellFormedTest_8704 240 256 :=
  interval_of_check wellFormedTest_8704 240 16 (by decide +kernel)

theorem wellFormedTest_8704_complete : Interval wellFormedTest_8704 0 256 :=
  (interval_append wellFormedTest_8704 0 128 256
  (interval_append wellFormedTest_8704 0 64 128
  (interval_append wellFormedTest_8704 0 32 64
  (interval_append wellFormedTest_8704 0 16 32
  wellFormedTest_8704_block_0
  wellFormedTest_8704_block_1)
  (interval_append wellFormedTest_8704 32 48 64
  wellFormedTest_8704_block_2
  wellFormedTest_8704_block_3))
  (interval_append wellFormedTest_8704 64 96 128
  (interval_append wellFormedTest_8704 64 80 96
  wellFormedTest_8704_block_4
  wellFormedTest_8704_block_5)
  (interval_append wellFormedTest_8704 96 112 128
  wellFormedTest_8704_block_6
  wellFormedTest_8704_block_7)))
  (interval_append wellFormedTest_8704 128 192 256
  (interval_append wellFormedTest_8704 128 160 192
  (interval_append wellFormedTest_8704 128 144 160
  wellFormedTest_8704_block_8
  wellFormedTest_8704_block_9)
  (interval_append wellFormedTest_8704 160 176 192
  wellFormedTest_8704_block_10
  wellFormedTest_8704_block_11))
  (interval_append wellFormedTest_8704 192 224 256
  (interval_append wellFormedTest_8704 192 208 224
  wellFormedTest_8704_block_12
  wellFormedTest_8704_block_13)
  (interval_append wellFormedTest_8704 224 240 256
  wellFormedTest_8704_block_14
  wellFormedTest_8704_block_15))))
theorem wellFormedTestInterval8704 : Interval wellFormedTest 8704 8960 := by
  intro i hlo hhi
  have h := wellFormedTest_8704_complete (i-8704) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_8704, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheWellFormed035 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_8960 (i : Nat) := wellFormedTest (i+8960)
theorem wellFormedTest_8960_block_0 : Interval wellFormedTest_8960 0 16 :=
  interval_of_check wellFormedTest_8960 0 16 (by decide +kernel)

theorem wellFormedTest_8960_block_1 : Interval wellFormedTest_8960 16 32 :=
  interval_of_check wellFormedTest_8960 16 16 (by decide +kernel)

theorem wellFormedTest_8960_block_2 : Interval wellFormedTest_8960 32 48 :=
  interval_of_check wellFormedTest_8960 32 16 (by decide +kernel)

theorem wellFormedTest_8960_block_3 : Interval wellFormedTest_8960 48 64 :=
  interval_of_check wellFormedTest_8960 48 16 (by decide +kernel)

theorem wellFormedTest_8960_block_4 : Interval wellFormedTest_8960 64 80 :=
  interval_of_check wellFormedTest_8960 64 16 (by decide +kernel)

theorem wellFormedTest_8960_block_5 : Interval wellFormedTest_8960 80 96 :=
  interval_of_check wellFormedTest_8960 80 16 (by decide +kernel)

theorem wellFormedTest_8960_block_6 : Interval wellFormedTest_8960 96 112 :=
  interval_of_check wellFormedTest_8960 96 16 (by decide +kernel)

theorem wellFormedTest_8960_block_7 : Interval wellFormedTest_8960 112 128 :=
  interval_of_check wellFormedTest_8960 112 16 (by decide +kernel)

theorem wellFormedTest_8960_block_8 : Interval wellFormedTest_8960 128 144 :=
  interval_of_check wellFormedTest_8960 128 16 (by decide +kernel)

theorem wellFormedTest_8960_block_9 : Interval wellFormedTest_8960 144 160 :=
  interval_of_check wellFormedTest_8960 144 16 (by decide +kernel)

theorem wellFormedTest_8960_block_10 : Interval wellFormedTest_8960 160 176 :=
  interval_of_check wellFormedTest_8960 160 16 (by decide +kernel)

theorem wellFormedTest_8960_block_11 : Interval wellFormedTest_8960 176 192 :=
  interval_of_check wellFormedTest_8960 176 16 (by decide +kernel)

theorem wellFormedTest_8960_block_12 : Interval wellFormedTest_8960 192 208 :=
  interval_of_check wellFormedTest_8960 192 16 (by decide +kernel)

theorem wellFormedTest_8960_block_13 : Interval wellFormedTest_8960 208 224 :=
  interval_of_check wellFormedTest_8960 208 16 (by decide +kernel)

theorem wellFormedTest_8960_block_14 : Interval wellFormedTest_8960 224 240 :=
  interval_of_check wellFormedTest_8960 224 16 (by decide +kernel)

theorem wellFormedTest_8960_block_15 : Interval wellFormedTest_8960 240 256 :=
  interval_of_check wellFormedTest_8960 240 16 (by decide +kernel)

theorem wellFormedTest_8960_complete : Interval wellFormedTest_8960 0 256 :=
  (interval_append wellFormedTest_8960 0 128 256
  (interval_append wellFormedTest_8960 0 64 128
  (interval_append wellFormedTest_8960 0 32 64
  (interval_append wellFormedTest_8960 0 16 32
  wellFormedTest_8960_block_0
  wellFormedTest_8960_block_1)
  (interval_append wellFormedTest_8960 32 48 64
  wellFormedTest_8960_block_2
  wellFormedTest_8960_block_3))
  (interval_append wellFormedTest_8960 64 96 128
  (interval_append wellFormedTest_8960 64 80 96
  wellFormedTest_8960_block_4
  wellFormedTest_8960_block_5)
  (interval_append wellFormedTest_8960 96 112 128
  wellFormedTest_8960_block_6
  wellFormedTest_8960_block_7)))
  (interval_append wellFormedTest_8960 128 192 256
  (interval_append wellFormedTest_8960 128 160 192
  (interval_append wellFormedTest_8960 128 144 160
  wellFormedTest_8960_block_8
  wellFormedTest_8960_block_9)
  (interval_append wellFormedTest_8960 160 176 192
  wellFormedTest_8960_block_10
  wellFormedTest_8960_block_11))
  (interval_append wellFormedTest_8960 192 224 256
  (interval_append wellFormedTest_8960 192 208 224
  wellFormedTest_8960_block_12
  wellFormedTest_8960_block_13)
  (interval_append wellFormedTest_8960 224 240 256
  wellFormedTest_8960_block_14
  wellFormedTest_8960_block_15))))
theorem wellFormedTestInterval8960 : Interval wellFormedTest 8960 9216 := by
  intro i hlo hhi
  have h := wellFormedTest_8960_complete (i-8960) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_8960, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
