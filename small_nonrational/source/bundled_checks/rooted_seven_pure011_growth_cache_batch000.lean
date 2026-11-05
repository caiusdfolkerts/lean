module
prelude
public import RootedSevenPure011GrowthCacheData

/- RootedSevenPure011GrowthCacheRidges006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure011
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_768 (i : Nat) := ridgeTest (i+768)
theorem ridgeTest_768_block_0 : Interval ridgeTest_768 0 8 :=
  interval_of_check ridgeTest_768 0 8 (by decide +kernel)

theorem ridgeTest_768_block_1 : Interval ridgeTest_768 8 16 :=
  interval_of_check ridgeTest_768 8 8 (by decide +kernel)

theorem ridgeTest_768_block_2 : Interval ridgeTest_768 16 24 :=
  interval_of_check ridgeTest_768 16 8 (by decide +kernel)

theorem ridgeTest_768_block_3 : Interval ridgeTest_768 24 32 :=
  interval_of_check ridgeTest_768 24 8 (by decide +kernel)

theorem ridgeTest_768_block_4 : Interval ridgeTest_768 32 40 :=
  interval_of_check ridgeTest_768 32 8 (by decide +kernel)

theorem ridgeTest_768_block_5 : Interval ridgeTest_768 40 48 :=
  interval_of_check ridgeTest_768 40 8 (by decide +kernel)

theorem ridgeTest_768_block_6 : Interval ridgeTest_768 48 56 :=
  interval_of_check ridgeTest_768 48 8 (by decide +kernel)

theorem ridgeTest_768_block_7 : Interval ridgeTest_768 56 64 :=
  interval_of_check ridgeTest_768 56 8 (by decide +kernel)

theorem ridgeTest_768_block_8 : Interval ridgeTest_768 64 72 :=
  interval_of_check ridgeTest_768 64 8 (by decide +kernel)

theorem ridgeTest_768_block_9 : Interval ridgeTest_768 72 80 :=
  interval_of_check ridgeTest_768 72 8 (by decide +kernel)

theorem ridgeTest_768_block_10 : Interval ridgeTest_768 80 88 :=
  interval_of_check ridgeTest_768 80 8 (by decide +kernel)

theorem ridgeTest_768_block_11 : Interval ridgeTest_768 88 96 :=
  interval_of_check ridgeTest_768 88 8 (by decide +kernel)

theorem ridgeTest_768_block_12 : Interval ridgeTest_768 96 104 :=
  interval_of_check ridgeTest_768 96 8 (by decide +kernel)

theorem ridgeTest_768_block_13 : Interval ridgeTest_768 104 112 :=
  interval_of_check ridgeTest_768 104 8 (by decide +kernel)

theorem ridgeTest_768_block_14 : Interval ridgeTest_768 112 120 :=
  interval_of_check ridgeTest_768 112 8 (by decide +kernel)

theorem ridgeTest_768_block_15 : Interval ridgeTest_768 120 128 :=
  interval_of_check ridgeTest_768 120 8 (by decide +kernel)

theorem ridgeTest_768_complete : Interval ridgeTest_768 0 128 :=
  (interval_append ridgeTest_768 0 64 128
  (interval_append ridgeTest_768 0 32 64
  (interval_append ridgeTest_768 0 16 32
  (interval_append ridgeTest_768 0 8 16
  ridgeTest_768_block_0
  ridgeTest_768_block_1)
  (interval_append ridgeTest_768 16 24 32
  ridgeTest_768_block_2
  ridgeTest_768_block_3))
  (interval_append ridgeTest_768 32 48 64
  (interval_append ridgeTest_768 32 40 48
  ridgeTest_768_block_4
  ridgeTest_768_block_5)
  (interval_append ridgeTest_768 48 56 64
  ridgeTest_768_block_6
  ridgeTest_768_block_7)))
  (interval_append ridgeTest_768 64 96 128
  (interval_append ridgeTest_768 64 80 96
  (interval_append ridgeTest_768 64 72 80
  ridgeTest_768_block_8
  ridgeTest_768_block_9)
  (interval_append ridgeTest_768 80 88 96
  ridgeTest_768_block_10
  ridgeTest_768_block_11))
  (interval_append ridgeTest_768 96 112 128
  (interval_append ridgeTest_768 96 104 112
  ridgeTest_768_block_12
  ridgeTest_768_block_13)
  (interval_append ridgeTest_768 112 120 128
  ridgeTest_768_block_14
  ridgeTest_768_block_15))))
theorem ridgeTestInterval768 : Interval ridgeTest 768 896 := by
  intro i hlo hhi
  have h := ridgeTest_768_complete (i-768) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure011

end
end
/- RootedSevenPure011GrowthCacheRidges007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure011
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_896 (i : Nat) := ridgeTest (i+896)
theorem ridgeTest_896_block_0 : Interval ridgeTest_896 0 8 :=
  interval_of_check ridgeTest_896 0 8 (by decide +kernel)

theorem ridgeTest_896_block_1 : Interval ridgeTest_896 8 16 :=
  interval_of_check ridgeTest_896 8 8 (by decide +kernel)

theorem ridgeTest_896_block_2 : Interval ridgeTest_896 16 24 :=
  interval_of_check ridgeTest_896 16 8 (by decide +kernel)

theorem ridgeTest_896_block_3 : Interval ridgeTest_896 24 32 :=
  interval_of_check ridgeTest_896 24 8 (by decide +kernel)

theorem ridgeTest_896_block_4 : Interval ridgeTest_896 32 40 :=
  interval_of_check ridgeTest_896 32 8 (by decide +kernel)

theorem ridgeTest_896_block_5 : Interval ridgeTest_896 40 48 :=
  interval_of_check ridgeTest_896 40 8 (by decide +kernel)

theorem ridgeTest_896_block_6 : Interval ridgeTest_896 48 56 :=
  interval_of_check ridgeTest_896 48 8 (by decide +kernel)

theorem ridgeTest_896_block_7 : Interval ridgeTest_896 56 64 :=
  interval_of_check ridgeTest_896 56 8 (by decide +kernel)

theorem ridgeTest_896_block_8 : Interval ridgeTest_896 64 72 :=
  interval_of_check ridgeTest_896 64 8 (by decide +kernel)

theorem ridgeTest_896_block_9 : Interval ridgeTest_896 72 80 :=
  interval_of_check ridgeTest_896 72 8 (by decide +kernel)

theorem ridgeTest_896_block_10 : Interval ridgeTest_896 80 88 :=
  interval_of_check ridgeTest_896 80 8 (by decide +kernel)

theorem ridgeTest_896_block_11 : Interval ridgeTest_896 88 96 :=
  interval_of_check ridgeTest_896 88 8 (by decide +kernel)

theorem ridgeTest_896_block_12 : Interval ridgeTest_896 96 104 :=
  interval_of_check ridgeTest_896 96 8 (by decide +kernel)

theorem ridgeTest_896_block_13 : Interval ridgeTest_896 104 112 :=
  interval_of_check ridgeTest_896 104 8 (by decide +kernel)

theorem ridgeTest_896_block_14 : Interval ridgeTest_896 112 120 :=
  interval_of_check ridgeTest_896 112 8 (by decide +kernel)

theorem ridgeTest_896_block_15 : Interval ridgeTest_896 120 128 :=
  interval_of_check ridgeTest_896 120 8 (by decide +kernel)

theorem ridgeTest_896_complete : Interval ridgeTest_896 0 128 :=
  (interval_append ridgeTest_896 0 64 128
  (interval_append ridgeTest_896 0 32 64
  (interval_append ridgeTest_896 0 16 32
  (interval_append ridgeTest_896 0 8 16
  ridgeTest_896_block_0
  ridgeTest_896_block_1)
  (interval_append ridgeTest_896 16 24 32
  ridgeTest_896_block_2
  ridgeTest_896_block_3))
  (interval_append ridgeTest_896 32 48 64
  (interval_append ridgeTest_896 32 40 48
  ridgeTest_896_block_4
  ridgeTest_896_block_5)
  (interval_append ridgeTest_896 48 56 64
  ridgeTest_896_block_6
  ridgeTest_896_block_7)))
  (interval_append ridgeTest_896 64 96 128
  (interval_append ridgeTest_896 64 80 96
  (interval_append ridgeTest_896 64 72 80
  ridgeTest_896_block_8
  ridgeTest_896_block_9)
  (interval_append ridgeTest_896 80 88 96
  ridgeTest_896_block_10
  ridgeTest_896_block_11))
  (interval_append ridgeTest_896 96 112 128
  (interval_append ridgeTest_896 96 104 112
  ridgeTest_896_block_12
  ridgeTest_896_block_13)
  (interval_append ridgeTest_896 112 120 128
  ridgeTest_896_block_14
  ridgeTest_896_block_15))))
theorem ridgeTestInterval896 : Interval ridgeTest 896 1024 := by
  intro i hlo hhi
  have h := ridgeTest_896_complete (i-896) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure011

end
end
/- RootedSevenPure011GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure011
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_0 (i : Nat) := wellFormedTest (i+0)
theorem wellFormedTest_0_block_0 : Interval wellFormedTest_0 0 16 :=
  interval_of_check wellFormedTest_0 0 16 (by decide +kernel)

theorem wellFormedTest_0_block_1 : Interval wellFormedTest_0 16 32 :=
  interval_of_check wellFormedTest_0 16 16 (by decide +kernel)

theorem wellFormedTest_0_block_2 : Interval wellFormedTest_0 32 48 :=
  interval_of_check wellFormedTest_0 32 16 (by decide +kernel)

theorem wellFormedTest_0_block_3 : Interval wellFormedTest_0 48 64 :=
  interval_of_check wellFormedTest_0 48 16 (by decide +kernel)

theorem wellFormedTest_0_block_4 : Interval wellFormedTest_0 64 80 :=
  interval_of_check wellFormedTest_0 64 16 (by decide +kernel)

theorem wellFormedTest_0_block_5 : Interval wellFormedTest_0 80 96 :=
  interval_of_check wellFormedTest_0 80 16 (by decide +kernel)

theorem wellFormedTest_0_block_6 : Interval wellFormedTest_0 96 112 :=
  interval_of_check wellFormedTest_0 96 16 (by decide +kernel)

theorem wellFormedTest_0_block_7 : Interval wellFormedTest_0 112 128 :=
  interval_of_check wellFormedTest_0 112 16 (by decide +kernel)

theorem wellFormedTest_0_block_8 : Interval wellFormedTest_0 128 144 :=
  interval_of_check wellFormedTest_0 128 16 (by decide +kernel)

theorem wellFormedTest_0_block_9 : Interval wellFormedTest_0 144 160 :=
  interval_of_check wellFormedTest_0 144 16 (by decide +kernel)

theorem wellFormedTest_0_block_10 : Interval wellFormedTest_0 160 176 :=
  interval_of_check wellFormedTest_0 160 16 (by decide +kernel)

theorem wellFormedTest_0_block_11 : Interval wellFormedTest_0 176 192 :=
  interval_of_check wellFormedTest_0 176 16 (by decide +kernel)

theorem wellFormedTest_0_block_12 : Interval wellFormedTest_0 192 208 :=
  interval_of_check wellFormedTest_0 192 16 (by decide +kernel)

theorem wellFormedTest_0_block_13 : Interval wellFormedTest_0 208 224 :=
  interval_of_check wellFormedTest_0 208 16 (by decide +kernel)

theorem wellFormedTest_0_block_14 : Interval wellFormedTest_0 224 240 :=
  interval_of_check wellFormedTest_0 224 16 (by decide +kernel)

theorem wellFormedTest_0_block_15 : Interval wellFormedTest_0 240 256 :=
  interval_of_check wellFormedTest_0 240 16 (by decide +kernel)

theorem wellFormedTest_0_complete : Interval wellFormedTest_0 0 256 :=
  (interval_append wellFormedTest_0 0 128 256
  (interval_append wellFormedTest_0 0 64 128
  (interval_append wellFormedTest_0 0 32 64
  (interval_append wellFormedTest_0 0 16 32
  wellFormedTest_0_block_0
  wellFormedTest_0_block_1)
  (interval_append wellFormedTest_0 32 48 64
  wellFormedTest_0_block_2
  wellFormedTest_0_block_3))
  (interval_append wellFormedTest_0 64 96 128
  (interval_append wellFormedTest_0 64 80 96
  wellFormedTest_0_block_4
  wellFormedTest_0_block_5)
  (interval_append wellFormedTest_0 96 112 128
  wellFormedTest_0_block_6
  wellFormedTest_0_block_7)))
  (interval_append wellFormedTest_0 128 192 256
  (interval_append wellFormedTest_0 128 160 192
  (interval_append wellFormedTest_0 128 144 160
  wellFormedTest_0_block_8
  wellFormedTest_0_block_9)
  (interval_append wellFormedTest_0 160 176 192
  wellFormedTest_0_block_10
  wellFormedTest_0_block_11))
  (interval_append wellFormedTest_0 192 224 256
  (interval_append wellFormedTest_0 192 208 224
  wellFormedTest_0_block_12
  wellFormedTest_0_block_13)
  (interval_append wellFormedTest_0 224 240 256
  wellFormedTest_0_block_14
  wellFormedTest_0_block_15))))
theorem wellFormedTestInterval0 : Interval wellFormedTest 0 256 := by
  intro i hlo hhi
  have h := wellFormedTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure011

end
end
/- RootedSevenPure011GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure011
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_256 (i : Nat) := wellFormedTest (i+256)
theorem wellFormedTest_256_block_0 : Interval wellFormedTest_256 0 16 :=
  interval_of_check wellFormedTest_256 0 16 (by decide +kernel)

theorem wellFormedTest_256_block_1 : Interval wellFormedTest_256 16 32 :=
  interval_of_check wellFormedTest_256 16 16 (by decide +kernel)

theorem wellFormedTest_256_block_2 : Interval wellFormedTest_256 32 48 :=
  interval_of_check wellFormedTest_256 32 16 (by decide +kernel)

theorem wellFormedTest_256_block_3 : Interval wellFormedTest_256 48 64 :=
  interval_of_check wellFormedTest_256 48 16 (by decide +kernel)

theorem wellFormedTest_256_block_4 : Interval wellFormedTest_256 64 80 :=
  interval_of_check wellFormedTest_256 64 16 (by decide +kernel)

theorem wellFormedTest_256_block_5 : Interval wellFormedTest_256 80 96 :=
  interval_of_check wellFormedTest_256 80 16 (by decide +kernel)

theorem wellFormedTest_256_block_6 : Interval wellFormedTest_256 96 112 :=
  interval_of_check wellFormedTest_256 96 16 (by decide +kernel)

theorem wellFormedTest_256_block_7 : Interval wellFormedTest_256 112 128 :=
  interval_of_check wellFormedTest_256 112 16 (by decide +kernel)

theorem wellFormedTest_256_block_8 : Interval wellFormedTest_256 128 144 :=
  interval_of_check wellFormedTest_256 128 16 (by decide +kernel)

theorem wellFormedTest_256_block_9 : Interval wellFormedTest_256 144 160 :=
  interval_of_check wellFormedTest_256 144 16 (by decide +kernel)

theorem wellFormedTest_256_block_10 : Interval wellFormedTest_256 160 176 :=
  interval_of_check wellFormedTest_256 160 16 (by decide +kernel)

theorem wellFormedTest_256_block_11 : Interval wellFormedTest_256 176 192 :=
  interval_of_check wellFormedTest_256 176 16 (by decide +kernel)

theorem wellFormedTest_256_block_12 : Interval wellFormedTest_256 192 208 :=
  interval_of_check wellFormedTest_256 192 16 (by decide +kernel)

theorem wellFormedTest_256_block_13 : Interval wellFormedTest_256 208 224 :=
  interval_of_check wellFormedTest_256 208 16 (by decide +kernel)

theorem wellFormedTest_256_block_14 : Interval wellFormedTest_256 224 240 :=
  interval_of_check wellFormedTest_256 224 16 (by decide +kernel)

theorem wellFormedTest_256_block_15 : Interval wellFormedTest_256 240 256 :=
  interval_of_check wellFormedTest_256 240 16 (by decide +kernel)

theorem wellFormedTest_256_complete : Interval wellFormedTest_256 0 256 :=
  (interval_append wellFormedTest_256 0 128 256
  (interval_append wellFormedTest_256 0 64 128
  (interval_append wellFormedTest_256 0 32 64
  (interval_append wellFormedTest_256 0 16 32
  wellFormedTest_256_block_0
  wellFormedTest_256_block_1)
  (interval_append wellFormedTest_256 32 48 64
  wellFormedTest_256_block_2
  wellFormedTest_256_block_3))
  (interval_append wellFormedTest_256 64 96 128
  (interval_append wellFormedTest_256 64 80 96
  wellFormedTest_256_block_4
  wellFormedTest_256_block_5)
  (interval_append wellFormedTest_256 96 112 128
  wellFormedTest_256_block_6
  wellFormedTest_256_block_7)))
  (interval_append wellFormedTest_256 128 192 256
  (interval_append wellFormedTest_256 128 160 192
  (interval_append wellFormedTest_256 128 144 160
  wellFormedTest_256_block_8
  wellFormedTest_256_block_9)
  (interval_append wellFormedTest_256 160 176 192
  wellFormedTest_256_block_10
  wellFormedTest_256_block_11))
  (interval_append wellFormedTest_256 192 224 256
  (interval_append wellFormedTest_256 192 208 224
  wellFormedTest_256_block_12
  wellFormedTest_256_block_13)
  (interval_append wellFormedTest_256 224 240 256
  wellFormedTest_256_block_14
  wellFormedTest_256_block_15))))
theorem wellFormedTestInterval256 : Interval wellFormedTest 256 512 := by
  intro i hlo hhi
  have h := wellFormedTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure011

end
end
/- RootedSevenPure011GrowthCacheWellFormed002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure011
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

theorem wellFormedTest_512_block_4 : Interval wellFormedTest_512 64 74 :=
  interval_of_check wellFormedTest_512 64 10 (by decide +kernel)

theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 74 :=
  (interval_append wellFormedTest_512 0 32 74
  (interval_append wellFormedTest_512 0 16 32
  wellFormedTest_512_block_0
  wellFormedTest_512_block_1)
  (interval_append wellFormedTest_512 32 48 74
  wellFormedTest_512_block_2
  (interval_append wellFormedTest_512 48 64 74
  wellFormedTest_512_block_3
  wellFormedTest_512_block_4)))
theorem wellFormedTestInterval512 : Interval wellFormedTest 512 586 := by
  intro i hlo hhi
  have h := wellFormedTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure011

end
end
