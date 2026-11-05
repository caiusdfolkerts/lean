module
prelude
public import RootedSixBase01GrowthCacheData

/- RootedSixBase01GrowthCacheWellFormed040 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_10240 (i : Nat) := wellFormedTest (i+10240)
theorem wellFormedTest_10240_block_0 : Interval wellFormedTest_10240 0 16 :=
  interval_of_check wellFormedTest_10240 0 16 (by decide +kernel)

theorem wellFormedTest_10240_block_1 : Interval wellFormedTest_10240 16 32 :=
  interval_of_check wellFormedTest_10240 16 16 (by decide +kernel)

theorem wellFormedTest_10240_block_2 : Interval wellFormedTest_10240 32 48 :=
  interval_of_check wellFormedTest_10240 32 16 (by decide +kernel)

theorem wellFormedTest_10240_block_3 : Interval wellFormedTest_10240 48 64 :=
  interval_of_check wellFormedTest_10240 48 16 (by decide +kernel)

theorem wellFormedTest_10240_block_4 : Interval wellFormedTest_10240 64 80 :=
  interval_of_check wellFormedTest_10240 64 16 (by decide +kernel)

theorem wellFormedTest_10240_block_5 : Interval wellFormedTest_10240 80 96 :=
  interval_of_check wellFormedTest_10240 80 16 (by decide +kernel)

theorem wellFormedTest_10240_block_6 : Interval wellFormedTest_10240 96 112 :=
  interval_of_check wellFormedTest_10240 96 16 (by decide +kernel)

theorem wellFormedTest_10240_block_7 : Interval wellFormedTest_10240 112 128 :=
  interval_of_check wellFormedTest_10240 112 16 (by decide +kernel)

theorem wellFormedTest_10240_block_8 : Interval wellFormedTest_10240 128 144 :=
  interval_of_check wellFormedTest_10240 128 16 (by decide +kernel)

theorem wellFormedTest_10240_block_9 : Interval wellFormedTest_10240 144 160 :=
  interval_of_check wellFormedTest_10240 144 16 (by decide +kernel)

theorem wellFormedTest_10240_block_10 : Interval wellFormedTest_10240 160 176 :=
  interval_of_check wellFormedTest_10240 160 16 (by decide +kernel)

theorem wellFormedTest_10240_block_11 : Interval wellFormedTest_10240 176 192 :=
  interval_of_check wellFormedTest_10240 176 16 (by decide +kernel)

theorem wellFormedTest_10240_block_12 : Interval wellFormedTest_10240 192 208 :=
  interval_of_check wellFormedTest_10240 192 16 (by decide +kernel)

theorem wellFormedTest_10240_block_13 : Interval wellFormedTest_10240 208 224 :=
  interval_of_check wellFormedTest_10240 208 16 (by decide +kernel)

theorem wellFormedTest_10240_block_14 : Interval wellFormedTest_10240 224 240 :=
  interval_of_check wellFormedTest_10240 224 16 (by decide +kernel)

theorem wellFormedTest_10240_block_15 : Interval wellFormedTest_10240 240 256 :=
  interval_of_check wellFormedTest_10240 240 16 (by decide +kernel)

theorem wellFormedTest_10240_complete : Interval wellFormedTest_10240 0 256 :=
  (interval_append wellFormedTest_10240 0 128 256
  (interval_append wellFormedTest_10240 0 64 128
  (interval_append wellFormedTest_10240 0 32 64
  (interval_append wellFormedTest_10240 0 16 32
  wellFormedTest_10240_block_0
  wellFormedTest_10240_block_1)
  (interval_append wellFormedTest_10240 32 48 64
  wellFormedTest_10240_block_2
  wellFormedTest_10240_block_3))
  (interval_append wellFormedTest_10240 64 96 128
  (interval_append wellFormedTest_10240 64 80 96
  wellFormedTest_10240_block_4
  wellFormedTest_10240_block_5)
  (interval_append wellFormedTest_10240 96 112 128
  wellFormedTest_10240_block_6
  wellFormedTest_10240_block_7)))
  (interval_append wellFormedTest_10240 128 192 256
  (interval_append wellFormedTest_10240 128 160 192
  (interval_append wellFormedTest_10240 128 144 160
  wellFormedTest_10240_block_8
  wellFormedTest_10240_block_9)
  (interval_append wellFormedTest_10240 160 176 192
  wellFormedTest_10240_block_10
  wellFormedTest_10240_block_11))
  (interval_append wellFormedTest_10240 192 224 256
  (interval_append wellFormedTest_10240 192 208 224
  wellFormedTest_10240_block_12
  wellFormedTest_10240_block_13)
  (interval_append wellFormedTest_10240 224 240 256
  wellFormedTest_10240_block_14
  wellFormedTest_10240_block_15))))
theorem wellFormedTestInterval10240 : Interval wellFormedTest 10240 10496 := by
  intro i hlo hhi
  have h := wellFormedTest_10240_complete (i-10240) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_10240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed041 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_10496 (i : Nat) := wellFormedTest (i+10496)
theorem wellFormedTest_10496_block_0 : Interval wellFormedTest_10496 0 16 :=
  interval_of_check wellFormedTest_10496 0 16 (by decide +kernel)

theorem wellFormedTest_10496_block_1 : Interval wellFormedTest_10496 16 32 :=
  interval_of_check wellFormedTest_10496 16 16 (by decide +kernel)

theorem wellFormedTest_10496_block_2 : Interval wellFormedTest_10496 32 48 :=
  interval_of_check wellFormedTest_10496 32 16 (by decide +kernel)

theorem wellFormedTest_10496_block_3 : Interval wellFormedTest_10496 48 64 :=
  interval_of_check wellFormedTest_10496 48 16 (by decide +kernel)

theorem wellFormedTest_10496_block_4 : Interval wellFormedTest_10496 64 80 :=
  interval_of_check wellFormedTest_10496 64 16 (by decide +kernel)

theorem wellFormedTest_10496_block_5 : Interval wellFormedTest_10496 80 96 :=
  interval_of_check wellFormedTest_10496 80 16 (by decide +kernel)

theorem wellFormedTest_10496_block_6 : Interval wellFormedTest_10496 96 112 :=
  interval_of_check wellFormedTest_10496 96 16 (by decide +kernel)

theorem wellFormedTest_10496_block_7 : Interval wellFormedTest_10496 112 128 :=
  interval_of_check wellFormedTest_10496 112 16 (by decide +kernel)

theorem wellFormedTest_10496_block_8 : Interval wellFormedTest_10496 128 144 :=
  interval_of_check wellFormedTest_10496 128 16 (by decide +kernel)

theorem wellFormedTest_10496_block_9 : Interval wellFormedTest_10496 144 160 :=
  interval_of_check wellFormedTest_10496 144 16 (by decide +kernel)

theorem wellFormedTest_10496_block_10 : Interval wellFormedTest_10496 160 176 :=
  interval_of_check wellFormedTest_10496 160 16 (by decide +kernel)

theorem wellFormedTest_10496_block_11 : Interval wellFormedTest_10496 176 192 :=
  interval_of_check wellFormedTest_10496 176 16 (by decide +kernel)

theorem wellFormedTest_10496_block_12 : Interval wellFormedTest_10496 192 208 :=
  interval_of_check wellFormedTest_10496 192 16 (by decide +kernel)

theorem wellFormedTest_10496_block_13 : Interval wellFormedTest_10496 208 224 :=
  interval_of_check wellFormedTest_10496 208 16 (by decide +kernel)

theorem wellFormedTest_10496_block_14 : Interval wellFormedTest_10496 224 240 :=
  interval_of_check wellFormedTest_10496 224 16 (by decide +kernel)

theorem wellFormedTest_10496_block_15 : Interval wellFormedTest_10496 240 256 :=
  interval_of_check wellFormedTest_10496 240 16 (by decide +kernel)

theorem wellFormedTest_10496_complete : Interval wellFormedTest_10496 0 256 :=
  (interval_append wellFormedTest_10496 0 128 256
  (interval_append wellFormedTest_10496 0 64 128
  (interval_append wellFormedTest_10496 0 32 64
  (interval_append wellFormedTest_10496 0 16 32
  wellFormedTest_10496_block_0
  wellFormedTest_10496_block_1)
  (interval_append wellFormedTest_10496 32 48 64
  wellFormedTest_10496_block_2
  wellFormedTest_10496_block_3))
  (interval_append wellFormedTest_10496 64 96 128
  (interval_append wellFormedTest_10496 64 80 96
  wellFormedTest_10496_block_4
  wellFormedTest_10496_block_5)
  (interval_append wellFormedTest_10496 96 112 128
  wellFormedTest_10496_block_6
  wellFormedTest_10496_block_7)))
  (interval_append wellFormedTest_10496 128 192 256
  (interval_append wellFormedTest_10496 128 160 192
  (interval_append wellFormedTest_10496 128 144 160
  wellFormedTest_10496_block_8
  wellFormedTest_10496_block_9)
  (interval_append wellFormedTest_10496 160 176 192
  wellFormedTest_10496_block_10
  wellFormedTest_10496_block_11))
  (interval_append wellFormedTest_10496 192 224 256
  (interval_append wellFormedTest_10496 192 208 224
  wellFormedTest_10496_block_12
  wellFormedTest_10496_block_13)
  (interval_append wellFormedTest_10496 224 240 256
  wellFormedTest_10496_block_14
  wellFormedTest_10496_block_15))))
theorem wellFormedTestInterval10496 : Interval wellFormedTest 10496 10752 := by
  intro i hlo hhi
  have h := wellFormedTest_10496_complete (i-10496) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_10496, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed042 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_10752 (i : Nat) := wellFormedTest (i+10752)
theorem wellFormedTest_10752_block_0 : Interval wellFormedTest_10752 0 16 :=
  interval_of_check wellFormedTest_10752 0 16 (by decide +kernel)

theorem wellFormedTest_10752_block_1 : Interval wellFormedTest_10752 16 32 :=
  interval_of_check wellFormedTest_10752 16 16 (by decide +kernel)

theorem wellFormedTest_10752_block_2 : Interval wellFormedTest_10752 32 48 :=
  interval_of_check wellFormedTest_10752 32 16 (by decide +kernel)

theorem wellFormedTest_10752_block_3 : Interval wellFormedTest_10752 48 64 :=
  interval_of_check wellFormedTest_10752 48 16 (by decide +kernel)

theorem wellFormedTest_10752_block_4 : Interval wellFormedTest_10752 64 80 :=
  interval_of_check wellFormedTest_10752 64 16 (by decide +kernel)

theorem wellFormedTest_10752_block_5 : Interval wellFormedTest_10752 80 96 :=
  interval_of_check wellFormedTest_10752 80 16 (by decide +kernel)

theorem wellFormedTest_10752_block_6 : Interval wellFormedTest_10752 96 112 :=
  interval_of_check wellFormedTest_10752 96 16 (by decide +kernel)

theorem wellFormedTest_10752_block_7 : Interval wellFormedTest_10752 112 128 :=
  interval_of_check wellFormedTest_10752 112 16 (by decide +kernel)

theorem wellFormedTest_10752_block_8 : Interval wellFormedTest_10752 128 144 :=
  interval_of_check wellFormedTest_10752 128 16 (by decide +kernel)

theorem wellFormedTest_10752_block_9 : Interval wellFormedTest_10752 144 160 :=
  interval_of_check wellFormedTest_10752 144 16 (by decide +kernel)

theorem wellFormedTest_10752_block_10 : Interval wellFormedTest_10752 160 176 :=
  interval_of_check wellFormedTest_10752 160 16 (by decide +kernel)

theorem wellFormedTest_10752_block_11 : Interval wellFormedTest_10752 176 192 :=
  interval_of_check wellFormedTest_10752 176 16 (by decide +kernel)

theorem wellFormedTest_10752_block_12 : Interval wellFormedTest_10752 192 208 :=
  interval_of_check wellFormedTest_10752 192 16 (by decide +kernel)

theorem wellFormedTest_10752_block_13 : Interval wellFormedTest_10752 208 224 :=
  interval_of_check wellFormedTest_10752 208 16 (by decide +kernel)

theorem wellFormedTest_10752_block_14 : Interval wellFormedTest_10752 224 240 :=
  interval_of_check wellFormedTest_10752 224 16 (by decide +kernel)

theorem wellFormedTest_10752_block_15 : Interval wellFormedTest_10752 240 256 :=
  interval_of_check wellFormedTest_10752 240 16 (by decide +kernel)

theorem wellFormedTest_10752_complete : Interval wellFormedTest_10752 0 256 :=
  (interval_append wellFormedTest_10752 0 128 256
  (interval_append wellFormedTest_10752 0 64 128
  (interval_append wellFormedTest_10752 0 32 64
  (interval_append wellFormedTest_10752 0 16 32
  wellFormedTest_10752_block_0
  wellFormedTest_10752_block_1)
  (interval_append wellFormedTest_10752 32 48 64
  wellFormedTest_10752_block_2
  wellFormedTest_10752_block_3))
  (interval_append wellFormedTest_10752 64 96 128
  (interval_append wellFormedTest_10752 64 80 96
  wellFormedTest_10752_block_4
  wellFormedTest_10752_block_5)
  (interval_append wellFormedTest_10752 96 112 128
  wellFormedTest_10752_block_6
  wellFormedTest_10752_block_7)))
  (interval_append wellFormedTest_10752 128 192 256
  (interval_append wellFormedTest_10752 128 160 192
  (interval_append wellFormedTest_10752 128 144 160
  wellFormedTest_10752_block_8
  wellFormedTest_10752_block_9)
  (interval_append wellFormedTest_10752 160 176 192
  wellFormedTest_10752_block_10
  wellFormedTest_10752_block_11))
  (interval_append wellFormedTest_10752 192 224 256
  (interval_append wellFormedTest_10752 192 208 224
  wellFormedTest_10752_block_12
  wellFormedTest_10752_block_13)
  (interval_append wellFormedTest_10752 224 240 256
  wellFormedTest_10752_block_14
  wellFormedTest_10752_block_15))))
theorem wellFormedTestInterval10752 : Interval wellFormedTest 10752 11008 := by
  intro i hlo hhi
  have h := wellFormedTest_10752_complete (i-10752) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_10752, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed043 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_11008 (i : Nat) := wellFormedTest (i+11008)
theorem wellFormedTest_11008_block_0 : Interval wellFormedTest_11008 0 16 :=
  interval_of_check wellFormedTest_11008 0 16 (by decide +kernel)

theorem wellFormedTest_11008_block_1 : Interval wellFormedTest_11008 16 32 :=
  interval_of_check wellFormedTest_11008 16 16 (by decide +kernel)

theorem wellFormedTest_11008_block_2 : Interval wellFormedTest_11008 32 48 :=
  interval_of_check wellFormedTest_11008 32 16 (by decide +kernel)

theorem wellFormedTest_11008_block_3 : Interval wellFormedTest_11008 48 64 :=
  interval_of_check wellFormedTest_11008 48 16 (by decide +kernel)

theorem wellFormedTest_11008_block_4 : Interval wellFormedTest_11008 64 80 :=
  interval_of_check wellFormedTest_11008 64 16 (by decide +kernel)

theorem wellFormedTest_11008_block_5 : Interval wellFormedTest_11008 80 96 :=
  interval_of_check wellFormedTest_11008 80 16 (by decide +kernel)

theorem wellFormedTest_11008_block_6 : Interval wellFormedTest_11008 96 112 :=
  interval_of_check wellFormedTest_11008 96 16 (by decide +kernel)

theorem wellFormedTest_11008_block_7 : Interval wellFormedTest_11008 112 128 :=
  interval_of_check wellFormedTest_11008 112 16 (by decide +kernel)

theorem wellFormedTest_11008_block_8 : Interval wellFormedTest_11008 128 144 :=
  interval_of_check wellFormedTest_11008 128 16 (by decide +kernel)

theorem wellFormedTest_11008_block_9 : Interval wellFormedTest_11008 144 160 :=
  interval_of_check wellFormedTest_11008 144 16 (by decide +kernel)

theorem wellFormedTest_11008_block_10 : Interval wellFormedTest_11008 160 176 :=
  interval_of_check wellFormedTest_11008 160 16 (by decide +kernel)

theorem wellFormedTest_11008_block_11 : Interval wellFormedTest_11008 176 192 :=
  interval_of_check wellFormedTest_11008 176 16 (by decide +kernel)

theorem wellFormedTest_11008_block_12 : Interval wellFormedTest_11008 192 208 :=
  interval_of_check wellFormedTest_11008 192 16 (by decide +kernel)

theorem wellFormedTest_11008_block_13 : Interval wellFormedTest_11008 208 224 :=
  interval_of_check wellFormedTest_11008 208 16 (by decide +kernel)

theorem wellFormedTest_11008_block_14 : Interval wellFormedTest_11008 224 240 :=
  interval_of_check wellFormedTest_11008 224 16 (by decide +kernel)

theorem wellFormedTest_11008_block_15 : Interval wellFormedTest_11008 240 256 :=
  interval_of_check wellFormedTest_11008 240 16 (by decide +kernel)

theorem wellFormedTest_11008_complete : Interval wellFormedTest_11008 0 256 :=
  (interval_append wellFormedTest_11008 0 128 256
  (interval_append wellFormedTest_11008 0 64 128
  (interval_append wellFormedTest_11008 0 32 64
  (interval_append wellFormedTest_11008 0 16 32
  wellFormedTest_11008_block_0
  wellFormedTest_11008_block_1)
  (interval_append wellFormedTest_11008 32 48 64
  wellFormedTest_11008_block_2
  wellFormedTest_11008_block_3))
  (interval_append wellFormedTest_11008 64 96 128
  (interval_append wellFormedTest_11008 64 80 96
  wellFormedTest_11008_block_4
  wellFormedTest_11008_block_5)
  (interval_append wellFormedTest_11008 96 112 128
  wellFormedTest_11008_block_6
  wellFormedTest_11008_block_7)))
  (interval_append wellFormedTest_11008 128 192 256
  (interval_append wellFormedTest_11008 128 160 192
  (interval_append wellFormedTest_11008 128 144 160
  wellFormedTest_11008_block_8
  wellFormedTest_11008_block_9)
  (interval_append wellFormedTest_11008 160 176 192
  wellFormedTest_11008_block_10
  wellFormedTest_11008_block_11))
  (interval_append wellFormedTest_11008 192 224 256
  (interval_append wellFormedTest_11008 192 208 224
  wellFormedTest_11008_block_12
  wellFormedTest_11008_block_13)
  (interval_append wellFormedTest_11008 224 240 256
  wellFormedTest_11008_block_14
  wellFormedTest_11008_block_15))))
theorem wellFormedTestInterval11008 : Interval wellFormedTest 11008 11264 := by
  intro i hlo hhi
  have h := wellFormedTest_11008_complete (i-11008) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_11008, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed044 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_11264 (i : Nat) := wellFormedTest (i+11264)
theorem wellFormedTest_11264_block_0 : Interval wellFormedTest_11264 0 16 :=
  interval_of_check wellFormedTest_11264 0 16 (by decide +kernel)

theorem wellFormedTest_11264_block_1 : Interval wellFormedTest_11264 16 32 :=
  interval_of_check wellFormedTest_11264 16 16 (by decide +kernel)

theorem wellFormedTest_11264_block_2 : Interval wellFormedTest_11264 32 48 :=
  interval_of_check wellFormedTest_11264 32 16 (by decide +kernel)

theorem wellFormedTest_11264_block_3 : Interval wellFormedTest_11264 48 64 :=
  interval_of_check wellFormedTest_11264 48 16 (by decide +kernel)

theorem wellFormedTest_11264_block_4 : Interval wellFormedTest_11264 64 80 :=
  interval_of_check wellFormedTest_11264 64 16 (by decide +kernel)

theorem wellFormedTest_11264_block_5 : Interval wellFormedTest_11264 80 96 :=
  interval_of_check wellFormedTest_11264 80 16 (by decide +kernel)

theorem wellFormedTest_11264_block_6 : Interval wellFormedTest_11264 96 112 :=
  interval_of_check wellFormedTest_11264 96 16 (by decide +kernel)

theorem wellFormedTest_11264_block_7 : Interval wellFormedTest_11264 112 128 :=
  interval_of_check wellFormedTest_11264 112 16 (by decide +kernel)

theorem wellFormedTest_11264_block_8 : Interval wellFormedTest_11264 128 144 :=
  interval_of_check wellFormedTest_11264 128 16 (by decide +kernel)

theorem wellFormedTest_11264_block_9 : Interval wellFormedTest_11264 144 160 :=
  interval_of_check wellFormedTest_11264 144 16 (by decide +kernel)

theorem wellFormedTest_11264_block_10 : Interval wellFormedTest_11264 160 176 :=
  interval_of_check wellFormedTest_11264 160 16 (by decide +kernel)

theorem wellFormedTest_11264_block_11 : Interval wellFormedTest_11264 176 192 :=
  interval_of_check wellFormedTest_11264 176 16 (by decide +kernel)

theorem wellFormedTest_11264_block_12 : Interval wellFormedTest_11264 192 208 :=
  interval_of_check wellFormedTest_11264 192 16 (by decide +kernel)

theorem wellFormedTest_11264_block_13 : Interval wellFormedTest_11264 208 224 :=
  interval_of_check wellFormedTest_11264 208 16 (by decide +kernel)

theorem wellFormedTest_11264_block_14 : Interval wellFormedTest_11264 224 240 :=
  interval_of_check wellFormedTest_11264 224 16 (by decide +kernel)

theorem wellFormedTest_11264_block_15 : Interval wellFormedTest_11264 240 256 :=
  interval_of_check wellFormedTest_11264 240 16 (by decide +kernel)

theorem wellFormedTest_11264_complete : Interval wellFormedTest_11264 0 256 :=
  (interval_append wellFormedTest_11264 0 128 256
  (interval_append wellFormedTest_11264 0 64 128
  (interval_append wellFormedTest_11264 0 32 64
  (interval_append wellFormedTest_11264 0 16 32
  wellFormedTest_11264_block_0
  wellFormedTest_11264_block_1)
  (interval_append wellFormedTest_11264 32 48 64
  wellFormedTest_11264_block_2
  wellFormedTest_11264_block_3))
  (interval_append wellFormedTest_11264 64 96 128
  (interval_append wellFormedTest_11264 64 80 96
  wellFormedTest_11264_block_4
  wellFormedTest_11264_block_5)
  (interval_append wellFormedTest_11264 96 112 128
  wellFormedTest_11264_block_6
  wellFormedTest_11264_block_7)))
  (interval_append wellFormedTest_11264 128 192 256
  (interval_append wellFormedTest_11264 128 160 192
  (interval_append wellFormedTest_11264 128 144 160
  wellFormedTest_11264_block_8
  wellFormedTest_11264_block_9)
  (interval_append wellFormedTest_11264 160 176 192
  wellFormedTest_11264_block_10
  wellFormedTest_11264_block_11))
  (interval_append wellFormedTest_11264 192 224 256
  (interval_append wellFormedTest_11264 192 208 224
  wellFormedTest_11264_block_12
  wellFormedTest_11264_block_13)
  (interval_append wellFormedTest_11264 224 240 256
  wellFormedTest_11264_block_14
  wellFormedTest_11264_block_15))))
theorem wellFormedTestInterval11264 : Interval wellFormedTest 11264 11520 := by
  intro i hlo hhi
  have h := wellFormedTest_11264_complete (i-11264) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_11264, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed045 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_11520 (i : Nat) := wellFormedTest (i+11520)
theorem wellFormedTest_11520_block_0 : Interval wellFormedTest_11520 0 16 :=
  interval_of_check wellFormedTest_11520 0 16 (by decide +kernel)

theorem wellFormedTest_11520_block_1 : Interval wellFormedTest_11520 16 32 :=
  interval_of_check wellFormedTest_11520 16 16 (by decide +kernel)

theorem wellFormedTest_11520_block_2 : Interval wellFormedTest_11520 32 48 :=
  interval_of_check wellFormedTest_11520 32 16 (by decide +kernel)

theorem wellFormedTest_11520_block_3 : Interval wellFormedTest_11520 48 64 :=
  interval_of_check wellFormedTest_11520 48 16 (by decide +kernel)

theorem wellFormedTest_11520_block_4 : Interval wellFormedTest_11520 64 80 :=
  interval_of_check wellFormedTest_11520 64 16 (by decide +kernel)

theorem wellFormedTest_11520_block_5 : Interval wellFormedTest_11520 80 96 :=
  interval_of_check wellFormedTest_11520 80 16 (by decide +kernel)

theorem wellFormedTest_11520_block_6 : Interval wellFormedTest_11520 96 112 :=
  interval_of_check wellFormedTest_11520 96 16 (by decide +kernel)

theorem wellFormedTest_11520_block_7 : Interval wellFormedTest_11520 112 128 :=
  interval_of_check wellFormedTest_11520 112 16 (by decide +kernel)

theorem wellFormedTest_11520_block_8 : Interval wellFormedTest_11520 128 144 :=
  interval_of_check wellFormedTest_11520 128 16 (by decide +kernel)

theorem wellFormedTest_11520_block_9 : Interval wellFormedTest_11520 144 160 :=
  interval_of_check wellFormedTest_11520 144 16 (by decide +kernel)

theorem wellFormedTest_11520_block_10 : Interval wellFormedTest_11520 160 176 :=
  interval_of_check wellFormedTest_11520 160 16 (by decide +kernel)

theorem wellFormedTest_11520_block_11 : Interval wellFormedTest_11520 176 192 :=
  interval_of_check wellFormedTest_11520 176 16 (by decide +kernel)

theorem wellFormedTest_11520_block_12 : Interval wellFormedTest_11520 192 208 :=
  interval_of_check wellFormedTest_11520 192 16 (by decide +kernel)

theorem wellFormedTest_11520_block_13 : Interval wellFormedTest_11520 208 224 :=
  interval_of_check wellFormedTest_11520 208 16 (by decide +kernel)

theorem wellFormedTest_11520_block_14 : Interval wellFormedTest_11520 224 240 :=
  interval_of_check wellFormedTest_11520 224 16 (by decide +kernel)

theorem wellFormedTest_11520_block_15 : Interval wellFormedTest_11520 240 256 :=
  interval_of_check wellFormedTest_11520 240 16 (by decide +kernel)

theorem wellFormedTest_11520_complete : Interval wellFormedTest_11520 0 256 :=
  (interval_append wellFormedTest_11520 0 128 256
  (interval_append wellFormedTest_11520 0 64 128
  (interval_append wellFormedTest_11520 0 32 64
  (interval_append wellFormedTest_11520 0 16 32
  wellFormedTest_11520_block_0
  wellFormedTest_11520_block_1)
  (interval_append wellFormedTest_11520 32 48 64
  wellFormedTest_11520_block_2
  wellFormedTest_11520_block_3))
  (interval_append wellFormedTest_11520 64 96 128
  (interval_append wellFormedTest_11520 64 80 96
  wellFormedTest_11520_block_4
  wellFormedTest_11520_block_5)
  (interval_append wellFormedTest_11520 96 112 128
  wellFormedTest_11520_block_6
  wellFormedTest_11520_block_7)))
  (interval_append wellFormedTest_11520 128 192 256
  (interval_append wellFormedTest_11520 128 160 192
  (interval_append wellFormedTest_11520 128 144 160
  wellFormedTest_11520_block_8
  wellFormedTest_11520_block_9)
  (interval_append wellFormedTest_11520 160 176 192
  wellFormedTest_11520_block_10
  wellFormedTest_11520_block_11))
  (interval_append wellFormedTest_11520 192 224 256
  (interval_append wellFormedTest_11520 192 208 224
  wellFormedTest_11520_block_12
  wellFormedTest_11520_block_13)
  (interval_append wellFormedTest_11520 224 240 256
  wellFormedTest_11520_block_14
  wellFormedTest_11520_block_15))))
theorem wellFormedTestInterval11520 : Interval wellFormedTest 11520 11776 := by
  intro i hlo hhi
  have h := wellFormedTest_11520_complete (i-11520) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_11520, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed046 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_11776 (i : Nat) := wellFormedTest (i+11776)
theorem wellFormedTest_11776_block_0 : Interval wellFormedTest_11776 0 16 :=
  interval_of_check wellFormedTest_11776 0 16 (by decide +kernel)

theorem wellFormedTest_11776_block_1 : Interval wellFormedTest_11776 16 32 :=
  interval_of_check wellFormedTest_11776 16 16 (by decide +kernel)

theorem wellFormedTest_11776_block_2 : Interval wellFormedTest_11776 32 48 :=
  interval_of_check wellFormedTest_11776 32 16 (by decide +kernel)

theorem wellFormedTest_11776_block_3 : Interval wellFormedTest_11776 48 64 :=
  interval_of_check wellFormedTest_11776 48 16 (by decide +kernel)

theorem wellFormedTest_11776_block_4 : Interval wellFormedTest_11776 64 80 :=
  interval_of_check wellFormedTest_11776 64 16 (by decide +kernel)

theorem wellFormedTest_11776_block_5 : Interval wellFormedTest_11776 80 96 :=
  interval_of_check wellFormedTest_11776 80 16 (by decide +kernel)

theorem wellFormedTest_11776_block_6 : Interval wellFormedTest_11776 96 112 :=
  interval_of_check wellFormedTest_11776 96 16 (by decide +kernel)

theorem wellFormedTest_11776_block_7 : Interval wellFormedTest_11776 112 128 :=
  interval_of_check wellFormedTest_11776 112 16 (by decide +kernel)

theorem wellFormedTest_11776_block_8 : Interval wellFormedTest_11776 128 144 :=
  interval_of_check wellFormedTest_11776 128 16 (by decide +kernel)

theorem wellFormedTest_11776_block_9 : Interval wellFormedTest_11776 144 160 :=
  interval_of_check wellFormedTest_11776 144 16 (by decide +kernel)

theorem wellFormedTest_11776_block_10 : Interval wellFormedTest_11776 160 176 :=
  interval_of_check wellFormedTest_11776 160 16 (by decide +kernel)

theorem wellFormedTest_11776_block_11 : Interval wellFormedTest_11776 176 192 :=
  interval_of_check wellFormedTest_11776 176 16 (by decide +kernel)

theorem wellFormedTest_11776_block_12 : Interval wellFormedTest_11776 192 208 :=
  interval_of_check wellFormedTest_11776 192 16 (by decide +kernel)

theorem wellFormedTest_11776_block_13 : Interval wellFormedTest_11776 208 224 :=
  interval_of_check wellFormedTest_11776 208 16 (by decide +kernel)

theorem wellFormedTest_11776_block_14 : Interval wellFormedTest_11776 224 240 :=
  interval_of_check wellFormedTest_11776 224 16 (by decide +kernel)

theorem wellFormedTest_11776_block_15 : Interval wellFormedTest_11776 240 256 :=
  interval_of_check wellFormedTest_11776 240 16 (by decide +kernel)

theorem wellFormedTest_11776_complete : Interval wellFormedTest_11776 0 256 :=
  (interval_append wellFormedTest_11776 0 128 256
  (interval_append wellFormedTest_11776 0 64 128
  (interval_append wellFormedTest_11776 0 32 64
  (interval_append wellFormedTest_11776 0 16 32
  wellFormedTest_11776_block_0
  wellFormedTest_11776_block_1)
  (interval_append wellFormedTest_11776 32 48 64
  wellFormedTest_11776_block_2
  wellFormedTest_11776_block_3))
  (interval_append wellFormedTest_11776 64 96 128
  (interval_append wellFormedTest_11776 64 80 96
  wellFormedTest_11776_block_4
  wellFormedTest_11776_block_5)
  (interval_append wellFormedTest_11776 96 112 128
  wellFormedTest_11776_block_6
  wellFormedTest_11776_block_7)))
  (interval_append wellFormedTest_11776 128 192 256
  (interval_append wellFormedTest_11776 128 160 192
  (interval_append wellFormedTest_11776 128 144 160
  wellFormedTest_11776_block_8
  wellFormedTest_11776_block_9)
  (interval_append wellFormedTest_11776 160 176 192
  wellFormedTest_11776_block_10
  wellFormedTest_11776_block_11))
  (interval_append wellFormedTest_11776 192 224 256
  (interval_append wellFormedTest_11776 192 208 224
  wellFormedTest_11776_block_12
  wellFormedTest_11776_block_13)
  (interval_append wellFormedTest_11776 224 240 256
  wellFormedTest_11776_block_14
  wellFormedTest_11776_block_15))))
theorem wellFormedTestInterval11776 : Interval wellFormedTest 11776 12032 := by
  intro i hlo hhi
  have h := wellFormedTest_11776_complete (i-11776) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_11776, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed047 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_12032 (i : Nat) := wellFormedTest (i+12032)
theorem wellFormedTest_12032_block_0 : Interval wellFormedTest_12032 0 16 :=
  interval_of_check wellFormedTest_12032 0 16 (by decide +kernel)

theorem wellFormedTest_12032_block_1 : Interval wellFormedTest_12032 16 32 :=
  interval_of_check wellFormedTest_12032 16 16 (by decide +kernel)

theorem wellFormedTest_12032_block_2 : Interval wellFormedTest_12032 32 48 :=
  interval_of_check wellFormedTest_12032 32 16 (by decide +kernel)

theorem wellFormedTest_12032_block_3 : Interval wellFormedTest_12032 48 64 :=
  interval_of_check wellFormedTest_12032 48 16 (by decide +kernel)

theorem wellFormedTest_12032_block_4 : Interval wellFormedTest_12032 64 80 :=
  interval_of_check wellFormedTest_12032 64 16 (by decide +kernel)

theorem wellFormedTest_12032_block_5 : Interval wellFormedTest_12032 80 96 :=
  interval_of_check wellFormedTest_12032 80 16 (by decide +kernel)

theorem wellFormedTest_12032_block_6 : Interval wellFormedTest_12032 96 112 :=
  interval_of_check wellFormedTest_12032 96 16 (by decide +kernel)

theorem wellFormedTest_12032_block_7 : Interval wellFormedTest_12032 112 128 :=
  interval_of_check wellFormedTest_12032 112 16 (by decide +kernel)

theorem wellFormedTest_12032_block_8 : Interval wellFormedTest_12032 128 144 :=
  interval_of_check wellFormedTest_12032 128 16 (by decide +kernel)

theorem wellFormedTest_12032_block_9 : Interval wellFormedTest_12032 144 160 :=
  interval_of_check wellFormedTest_12032 144 16 (by decide +kernel)

theorem wellFormedTest_12032_block_10 : Interval wellFormedTest_12032 160 176 :=
  interval_of_check wellFormedTest_12032 160 16 (by decide +kernel)

theorem wellFormedTest_12032_block_11 : Interval wellFormedTest_12032 176 192 :=
  interval_of_check wellFormedTest_12032 176 16 (by decide +kernel)

theorem wellFormedTest_12032_block_12 : Interval wellFormedTest_12032 192 208 :=
  interval_of_check wellFormedTest_12032 192 16 (by decide +kernel)

theorem wellFormedTest_12032_block_13 : Interval wellFormedTest_12032 208 224 :=
  interval_of_check wellFormedTest_12032 208 16 (by decide +kernel)

theorem wellFormedTest_12032_block_14 : Interval wellFormedTest_12032 224 240 :=
  interval_of_check wellFormedTest_12032 224 16 (by decide +kernel)

theorem wellFormedTest_12032_block_15 : Interval wellFormedTest_12032 240 256 :=
  interval_of_check wellFormedTest_12032 240 16 (by decide +kernel)

theorem wellFormedTest_12032_complete : Interval wellFormedTest_12032 0 256 :=
  (interval_append wellFormedTest_12032 0 128 256
  (interval_append wellFormedTest_12032 0 64 128
  (interval_append wellFormedTest_12032 0 32 64
  (interval_append wellFormedTest_12032 0 16 32
  wellFormedTest_12032_block_0
  wellFormedTest_12032_block_1)
  (interval_append wellFormedTest_12032 32 48 64
  wellFormedTest_12032_block_2
  wellFormedTest_12032_block_3))
  (interval_append wellFormedTest_12032 64 96 128
  (interval_append wellFormedTest_12032 64 80 96
  wellFormedTest_12032_block_4
  wellFormedTest_12032_block_5)
  (interval_append wellFormedTest_12032 96 112 128
  wellFormedTest_12032_block_6
  wellFormedTest_12032_block_7)))
  (interval_append wellFormedTest_12032 128 192 256
  (interval_append wellFormedTest_12032 128 160 192
  (interval_append wellFormedTest_12032 128 144 160
  wellFormedTest_12032_block_8
  wellFormedTest_12032_block_9)
  (interval_append wellFormedTest_12032 160 176 192
  wellFormedTest_12032_block_10
  wellFormedTest_12032_block_11))
  (interval_append wellFormedTest_12032 192 224 256
  (interval_append wellFormedTest_12032 192 208 224
  wellFormedTest_12032_block_12
  wellFormedTest_12032_block_13)
  (interval_append wellFormedTest_12032 224 240 256
  wellFormedTest_12032_block_14
  wellFormedTest_12032_block_15))))
theorem wellFormedTestInterval12032 : Interval wellFormedTest 12032 12288 := by
  intro i hlo hhi
  have h := wellFormedTest_12032_complete (i-12032) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_12032, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed048 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_12288 (i : Nat) := wellFormedTest (i+12288)
theorem wellFormedTest_12288_block_0 : Interval wellFormedTest_12288 0 16 :=
  interval_of_check wellFormedTest_12288 0 16 (by decide +kernel)

theorem wellFormedTest_12288_block_1 : Interval wellFormedTest_12288 16 32 :=
  interval_of_check wellFormedTest_12288 16 16 (by decide +kernel)

theorem wellFormedTest_12288_block_2 : Interval wellFormedTest_12288 32 48 :=
  interval_of_check wellFormedTest_12288 32 16 (by decide +kernel)

theorem wellFormedTest_12288_block_3 : Interval wellFormedTest_12288 48 64 :=
  interval_of_check wellFormedTest_12288 48 16 (by decide +kernel)

theorem wellFormedTest_12288_block_4 : Interval wellFormedTest_12288 64 80 :=
  interval_of_check wellFormedTest_12288 64 16 (by decide +kernel)

theorem wellFormedTest_12288_block_5 : Interval wellFormedTest_12288 80 96 :=
  interval_of_check wellFormedTest_12288 80 16 (by decide +kernel)

theorem wellFormedTest_12288_block_6 : Interval wellFormedTest_12288 96 112 :=
  interval_of_check wellFormedTest_12288 96 16 (by decide +kernel)

theorem wellFormedTest_12288_block_7 : Interval wellFormedTest_12288 112 128 :=
  interval_of_check wellFormedTest_12288 112 16 (by decide +kernel)

theorem wellFormedTest_12288_block_8 : Interval wellFormedTest_12288 128 144 :=
  interval_of_check wellFormedTest_12288 128 16 (by decide +kernel)

theorem wellFormedTest_12288_block_9 : Interval wellFormedTest_12288 144 160 :=
  interval_of_check wellFormedTest_12288 144 16 (by decide +kernel)

theorem wellFormedTest_12288_block_10 : Interval wellFormedTest_12288 160 176 :=
  interval_of_check wellFormedTest_12288 160 16 (by decide +kernel)

theorem wellFormedTest_12288_block_11 : Interval wellFormedTest_12288 176 192 :=
  interval_of_check wellFormedTest_12288 176 16 (by decide +kernel)

theorem wellFormedTest_12288_block_12 : Interval wellFormedTest_12288 192 208 :=
  interval_of_check wellFormedTest_12288 192 16 (by decide +kernel)

theorem wellFormedTest_12288_block_13 : Interval wellFormedTest_12288 208 224 :=
  interval_of_check wellFormedTest_12288 208 16 (by decide +kernel)

theorem wellFormedTest_12288_block_14 : Interval wellFormedTest_12288 224 240 :=
  interval_of_check wellFormedTest_12288 224 16 (by decide +kernel)

theorem wellFormedTest_12288_block_15 : Interval wellFormedTest_12288 240 256 :=
  interval_of_check wellFormedTest_12288 240 16 (by decide +kernel)

theorem wellFormedTest_12288_complete : Interval wellFormedTest_12288 0 256 :=
  (interval_append wellFormedTest_12288 0 128 256
  (interval_append wellFormedTest_12288 0 64 128
  (interval_append wellFormedTest_12288 0 32 64
  (interval_append wellFormedTest_12288 0 16 32
  wellFormedTest_12288_block_0
  wellFormedTest_12288_block_1)
  (interval_append wellFormedTest_12288 32 48 64
  wellFormedTest_12288_block_2
  wellFormedTest_12288_block_3))
  (interval_append wellFormedTest_12288 64 96 128
  (interval_append wellFormedTest_12288 64 80 96
  wellFormedTest_12288_block_4
  wellFormedTest_12288_block_5)
  (interval_append wellFormedTest_12288 96 112 128
  wellFormedTest_12288_block_6
  wellFormedTest_12288_block_7)))
  (interval_append wellFormedTest_12288 128 192 256
  (interval_append wellFormedTest_12288 128 160 192
  (interval_append wellFormedTest_12288 128 144 160
  wellFormedTest_12288_block_8
  wellFormedTest_12288_block_9)
  (interval_append wellFormedTest_12288 160 176 192
  wellFormedTest_12288_block_10
  wellFormedTest_12288_block_11))
  (interval_append wellFormedTest_12288 192 224 256
  (interval_append wellFormedTest_12288 192 208 224
  wellFormedTest_12288_block_12
  wellFormedTest_12288_block_13)
  (interval_append wellFormedTest_12288 224 240 256
  wellFormedTest_12288_block_14
  wellFormedTest_12288_block_15))))
theorem wellFormedTestInterval12288 : Interval wellFormedTest 12288 12544 := by
  intro i hlo hhi
  have h := wellFormedTest_12288_complete (i-12288) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_12288, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed049 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_12544 (i : Nat) := wellFormedTest (i+12544)
theorem wellFormedTest_12544_block_0 : Interval wellFormedTest_12544 0 16 :=
  interval_of_check wellFormedTest_12544 0 16 (by decide +kernel)

theorem wellFormedTest_12544_block_1 : Interval wellFormedTest_12544 16 32 :=
  interval_of_check wellFormedTest_12544 16 16 (by decide +kernel)

theorem wellFormedTest_12544_block_2 : Interval wellFormedTest_12544 32 48 :=
  interval_of_check wellFormedTest_12544 32 16 (by decide +kernel)

theorem wellFormedTest_12544_block_3 : Interval wellFormedTest_12544 48 64 :=
  interval_of_check wellFormedTest_12544 48 16 (by decide +kernel)

theorem wellFormedTest_12544_block_4 : Interval wellFormedTest_12544 64 80 :=
  interval_of_check wellFormedTest_12544 64 16 (by decide +kernel)

theorem wellFormedTest_12544_block_5 : Interval wellFormedTest_12544 80 96 :=
  interval_of_check wellFormedTest_12544 80 16 (by decide +kernel)

theorem wellFormedTest_12544_block_6 : Interval wellFormedTest_12544 96 112 :=
  interval_of_check wellFormedTest_12544 96 16 (by decide +kernel)

theorem wellFormedTest_12544_block_7 : Interval wellFormedTest_12544 112 128 :=
  interval_of_check wellFormedTest_12544 112 16 (by decide +kernel)

theorem wellFormedTest_12544_block_8 : Interval wellFormedTest_12544 128 144 :=
  interval_of_check wellFormedTest_12544 128 16 (by decide +kernel)

theorem wellFormedTest_12544_block_9 : Interval wellFormedTest_12544 144 160 :=
  interval_of_check wellFormedTest_12544 144 16 (by decide +kernel)

theorem wellFormedTest_12544_block_10 : Interval wellFormedTest_12544 160 176 :=
  interval_of_check wellFormedTest_12544 160 16 (by decide +kernel)

theorem wellFormedTest_12544_block_11 : Interval wellFormedTest_12544 176 192 :=
  interval_of_check wellFormedTest_12544 176 16 (by decide +kernel)

theorem wellFormedTest_12544_block_12 : Interval wellFormedTest_12544 192 208 :=
  interval_of_check wellFormedTest_12544 192 16 (by decide +kernel)

theorem wellFormedTest_12544_block_13 : Interval wellFormedTest_12544 208 224 :=
  interval_of_check wellFormedTest_12544 208 16 (by decide +kernel)

theorem wellFormedTest_12544_block_14 : Interval wellFormedTest_12544 224 240 :=
  interval_of_check wellFormedTest_12544 224 16 (by decide +kernel)

theorem wellFormedTest_12544_block_15 : Interval wellFormedTest_12544 240 256 :=
  interval_of_check wellFormedTest_12544 240 16 (by decide +kernel)

theorem wellFormedTest_12544_complete : Interval wellFormedTest_12544 0 256 :=
  (interval_append wellFormedTest_12544 0 128 256
  (interval_append wellFormedTest_12544 0 64 128
  (interval_append wellFormedTest_12544 0 32 64
  (interval_append wellFormedTest_12544 0 16 32
  wellFormedTest_12544_block_0
  wellFormedTest_12544_block_1)
  (interval_append wellFormedTest_12544 32 48 64
  wellFormedTest_12544_block_2
  wellFormedTest_12544_block_3))
  (interval_append wellFormedTest_12544 64 96 128
  (interval_append wellFormedTest_12544 64 80 96
  wellFormedTest_12544_block_4
  wellFormedTest_12544_block_5)
  (interval_append wellFormedTest_12544 96 112 128
  wellFormedTest_12544_block_6
  wellFormedTest_12544_block_7)))
  (interval_append wellFormedTest_12544 128 192 256
  (interval_append wellFormedTest_12544 128 160 192
  (interval_append wellFormedTest_12544 128 144 160
  wellFormedTest_12544_block_8
  wellFormedTest_12544_block_9)
  (interval_append wellFormedTest_12544 160 176 192
  wellFormedTest_12544_block_10
  wellFormedTest_12544_block_11))
  (interval_append wellFormedTest_12544 192 224 256
  (interval_append wellFormedTest_12544 192 208 224
  wellFormedTest_12544_block_12
  wellFormedTest_12544_block_13)
  (interval_append wellFormedTest_12544 224 240 256
  wellFormedTest_12544_block_14
  wellFormedTest_12544_block_15))))
theorem wellFormedTestInterval12544 : Interval wellFormedTest 12544 12800 := by
  intro i hlo hhi
  have h := wellFormedTest_12544_complete (i-12544) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_12544, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed050 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_12800 (i : Nat) := wellFormedTest (i+12800)
theorem wellFormedTest_12800_block_0 : Interval wellFormedTest_12800 0 16 :=
  interval_of_check wellFormedTest_12800 0 16 (by decide +kernel)

theorem wellFormedTest_12800_block_1 : Interval wellFormedTest_12800 16 32 :=
  interval_of_check wellFormedTest_12800 16 16 (by decide +kernel)

theorem wellFormedTest_12800_block_2 : Interval wellFormedTest_12800 32 48 :=
  interval_of_check wellFormedTest_12800 32 16 (by decide +kernel)

theorem wellFormedTest_12800_block_3 : Interval wellFormedTest_12800 48 64 :=
  interval_of_check wellFormedTest_12800 48 16 (by decide +kernel)

theorem wellFormedTest_12800_block_4 : Interval wellFormedTest_12800 64 80 :=
  interval_of_check wellFormedTest_12800 64 16 (by decide +kernel)

theorem wellFormedTest_12800_block_5 : Interval wellFormedTest_12800 80 96 :=
  interval_of_check wellFormedTest_12800 80 16 (by decide +kernel)

theorem wellFormedTest_12800_block_6 : Interval wellFormedTest_12800 96 112 :=
  interval_of_check wellFormedTest_12800 96 16 (by decide +kernel)

theorem wellFormedTest_12800_block_7 : Interval wellFormedTest_12800 112 128 :=
  interval_of_check wellFormedTest_12800 112 16 (by decide +kernel)

theorem wellFormedTest_12800_block_8 : Interval wellFormedTest_12800 128 144 :=
  interval_of_check wellFormedTest_12800 128 16 (by decide +kernel)

theorem wellFormedTest_12800_block_9 : Interval wellFormedTest_12800 144 160 :=
  interval_of_check wellFormedTest_12800 144 16 (by decide +kernel)

theorem wellFormedTest_12800_block_10 : Interval wellFormedTest_12800 160 176 :=
  interval_of_check wellFormedTest_12800 160 16 (by decide +kernel)

theorem wellFormedTest_12800_block_11 : Interval wellFormedTest_12800 176 192 :=
  interval_of_check wellFormedTest_12800 176 16 (by decide +kernel)

theorem wellFormedTest_12800_block_12 : Interval wellFormedTest_12800 192 208 :=
  interval_of_check wellFormedTest_12800 192 16 (by decide +kernel)

theorem wellFormedTest_12800_block_13 : Interval wellFormedTest_12800 208 224 :=
  interval_of_check wellFormedTest_12800 208 16 (by decide +kernel)

theorem wellFormedTest_12800_block_14 : Interval wellFormedTest_12800 224 240 :=
  interval_of_check wellFormedTest_12800 224 16 (by decide +kernel)

theorem wellFormedTest_12800_block_15 : Interval wellFormedTest_12800 240 256 :=
  interval_of_check wellFormedTest_12800 240 16 (by decide +kernel)

theorem wellFormedTest_12800_complete : Interval wellFormedTest_12800 0 256 :=
  (interval_append wellFormedTest_12800 0 128 256
  (interval_append wellFormedTest_12800 0 64 128
  (interval_append wellFormedTest_12800 0 32 64
  (interval_append wellFormedTest_12800 0 16 32
  wellFormedTest_12800_block_0
  wellFormedTest_12800_block_1)
  (interval_append wellFormedTest_12800 32 48 64
  wellFormedTest_12800_block_2
  wellFormedTest_12800_block_3))
  (interval_append wellFormedTest_12800 64 96 128
  (interval_append wellFormedTest_12800 64 80 96
  wellFormedTest_12800_block_4
  wellFormedTest_12800_block_5)
  (interval_append wellFormedTest_12800 96 112 128
  wellFormedTest_12800_block_6
  wellFormedTest_12800_block_7)))
  (interval_append wellFormedTest_12800 128 192 256
  (interval_append wellFormedTest_12800 128 160 192
  (interval_append wellFormedTest_12800 128 144 160
  wellFormedTest_12800_block_8
  wellFormedTest_12800_block_9)
  (interval_append wellFormedTest_12800 160 176 192
  wellFormedTest_12800_block_10
  wellFormedTest_12800_block_11))
  (interval_append wellFormedTest_12800 192 224 256
  (interval_append wellFormedTest_12800 192 208 224
  wellFormedTest_12800_block_12
  wellFormedTest_12800_block_13)
  (interval_append wellFormedTest_12800 224 240 256
  wellFormedTest_12800_block_14
  wellFormedTest_12800_block_15))))
theorem wellFormedTestInterval12800 : Interval wellFormedTest 12800 13056 := by
  intro i hlo hhi
  have h := wellFormedTest_12800_complete (i-12800) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_12800, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed051 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_13056 (i : Nat) := wellFormedTest (i+13056)
theorem wellFormedTest_13056_block_0 : Interval wellFormedTest_13056 0 16 :=
  interval_of_check wellFormedTest_13056 0 16 (by decide +kernel)

theorem wellFormedTest_13056_block_1 : Interval wellFormedTest_13056 16 32 :=
  interval_of_check wellFormedTest_13056 16 16 (by decide +kernel)

theorem wellFormedTest_13056_block_2 : Interval wellFormedTest_13056 32 48 :=
  interval_of_check wellFormedTest_13056 32 16 (by decide +kernel)

theorem wellFormedTest_13056_block_3 : Interval wellFormedTest_13056 48 64 :=
  interval_of_check wellFormedTest_13056 48 16 (by decide +kernel)

theorem wellFormedTest_13056_block_4 : Interval wellFormedTest_13056 64 80 :=
  interval_of_check wellFormedTest_13056 64 16 (by decide +kernel)

theorem wellFormedTest_13056_block_5 : Interval wellFormedTest_13056 80 96 :=
  interval_of_check wellFormedTest_13056 80 16 (by decide +kernel)

theorem wellFormedTest_13056_block_6 : Interval wellFormedTest_13056 96 112 :=
  interval_of_check wellFormedTest_13056 96 16 (by decide +kernel)

theorem wellFormedTest_13056_block_7 : Interval wellFormedTest_13056 112 128 :=
  interval_of_check wellFormedTest_13056 112 16 (by decide +kernel)

theorem wellFormedTest_13056_block_8 : Interval wellFormedTest_13056 128 144 :=
  interval_of_check wellFormedTest_13056 128 16 (by decide +kernel)

theorem wellFormedTest_13056_block_9 : Interval wellFormedTest_13056 144 160 :=
  interval_of_check wellFormedTest_13056 144 16 (by decide +kernel)

theorem wellFormedTest_13056_block_10 : Interval wellFormedTest_13056 160 176 :=
  interval_of_check wellFormedTest_13056 160 16 (by decide +kernel)

theorem wellFormedTest_13056_block_11 : Interval wellFormedTest_13056 176 192 :=
  interval_of_check wellFormedTest_13056 176 16 (by decide +kernel)

theorem wellFormedTest_13056_block_12 : Interval wellFormedTest_13056 192 208 :=
  interval_of_check wellFormedTest_13056 192 16 (by decide +kernel)

theorem wellFormedTest_13056_block_13 : Interval wellFormedTest_13056 208 224 :=
  interval_of_check wellFormedTest_13056 208 16 (by decide +kernel)

theorem wellFormedTest_13056_block_14 : Interval wellFormedTest_13056 224 240 :=
  interval_of_check wellFormedTest_13056 224 16 (by decide +kernel)

theorem wellFormedTest_13056_block_15 : Interval wellFormedTest_13056 240 256 :=
  interval_of_check wellFormedTest_13056 240 16 (by decide +kernel)

theorem wellFormedTest_13056_complete : Interval wellFormedTest_13056 0 256 :=
  (interval_append wellFormedTest_13056 0 128 256
  (interval_append wellFormedTest_13056 0 64 128
  (interval_append wellFormedTest_13056 0 32 64
  (interval_append wellFormedTest_13056 0 16 32
  wellFormedTest_13056_block_0
  wellFormedTest_13056_block_1)
  (interval_append wellFormedTest_13056 32 48 64
  wellFormedTest_13056_block_2
  wellFormedTest_13056_block_3))
  (interval_append wellFormedTest_13056 64 96 128
  (interval_append wellFormedTest_13056 64 80 96
  wellFormedTest_13056_block_4
  wellFormedTest_13056_block_5)
  (interval_append wellFormedTest_13056 96 112 128
  wellFormedTest_13056_block_6
  wellFormedTest_13056_block_7)))
  (interval_append wellFormedTest_13056 128 192 256
  (interval_append wellFormedTest_13056 128 160 192
  (interval_append wellFormedTest_13056 128 144 160
  wellFormedTest_13056_block_8
  wellFormedTest_13056_block_9)
  (interval_append wellFormedTest_13056 160 176 192
  wellFormedTest_13056_block_10
  wellFormedTest_13056_block_11))
  (interval_append wellFormedTest_13056 192 224 256
  (interval_append wellFormedTest_13056 192 208 224
  wellFormedTest_13056_block_12
  wellFormedTest_13056_block_13)
  (interval_append wellFormedTest_13056 224 240 256
  wellFormedTest_13056_block_14
  wellFormedTest_13056_block_15))))
theorem wellFormedTestInterval13056 : Interval wellFormedTest 13056 13312 := by
  intro i hlo hhi
  have h := wellFormedTest_13056_complete (i-13056) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_13056, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed052 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed053 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed054 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed055 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
