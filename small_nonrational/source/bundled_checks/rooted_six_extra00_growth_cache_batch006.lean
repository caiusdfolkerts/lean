module
prelude
public import RootedSixExtra00GrowthCacheData

/- RootedSixExtra00GrowthCacheWellFormed026 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed027 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed028 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed029 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed030 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed031 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed032 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed033 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
/- RootedSixExtra00GrowthCacheWellFormed034 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
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

theorem wellFormedTest_8704_block_7 : Interval wellFormedTest_8704 112 120 :=
  interval_of_check wellFormedTest_8704 112 8 (by decide +kernel)

theorem wellFormedTest_8704_complete : Interval wellFormedTest_8704 0 120 :=
  (interval_append wellFormedTest_8704 0 64 120
  (interval_append wellFormedTest_8704 0 32 64
  (interval_append wellFormedTest_8704 0 16 32
  wellFormedTest_8704_block_0
  wellFormedTest_8704_block_1)
  (interval_append wellFormedTest_8704 32 48 64
  wellFormedTest_8704_block_2
  wellFormedTest_8704_block_3))
  (interval_append wellFormedTest_8704 64 96 120
  (interval_append wellFormedTest_8704 64 80 96
  wellFormedTest_8704_block_4
  wellFormedTest_8704_block_5)
  (interval_append wellFormedTest_8704 96 112 120
  wellFormedTest_8704_block_6
  wellFormedTest_8704_block_7)))
theorem wellFormedTestInterval8704 : Interval wellFormedTest 8704 8824 := by
  intro i hlo hhi
  have h := wellFormedTest_8704_complete (i-8704) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_8704, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra00

end
end
