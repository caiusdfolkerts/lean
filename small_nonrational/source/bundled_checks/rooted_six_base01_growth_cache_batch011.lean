module
prelude
public import RootedSixBase01GrowthCacheData

/- RootedSixBase01GrowthCacheWellFormed056 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed057 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed058 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed059 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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

theorem wellFormedTest_15104_block_8 : Interval wellFormedTest_15104 128 142 :=
  interval_of_check wellFormedTest_15104 128 14 (by decide +kernel)

theorem wellFormedTest_15104_complete : Interval wellFormedTest_15104 0 142 :=
  (interval_append wellFormedTest_15104 0 64 142
  (interval_append wellFormedTest_15104 0 32 64
  (interval_append wellFormedTest_15104 0 16 32
  wellFormedTest_15104_block_0
  wellFormedTest_15104_block_1)
  (interval_append wellFormedTest_15104 32 48 64
  wellFormedTest_15104_block_2
  wellFormedTest_15104_block_3))
  (interval_append wellFormedTest_15104 64 96 142
  (interval_append wellFormedTest_15104 64 80 96
  wellFormedTest_15104_block_4
  wellFormedTest_15104_block_5)
  (interval_append wellFormedTest_15104 96 112 142
  wellFormedTest_15104_block_6
  (interval_append wellFormedTest_15104 112 128 142
  wellFormedTest_15104_block_7
  wellFormedTest_15104_block_8))))
theorem wellFormedTestInterval15104 : Interval wellFormedTest 15104 15246 := by
  intro i hlo hhi
  have h := wellFormedTest_15104_complete (i-15104) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_15104, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
