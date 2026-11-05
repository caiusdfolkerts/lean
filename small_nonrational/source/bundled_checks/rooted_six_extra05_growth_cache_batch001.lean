module
prelude
public import RootedSixExtra05GrowthCacheData

/- RootedSixExtra05GrowthCacheBad007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_1792 (i : Nat) := badTest (i+1792)
theorem badTest_1792_block_0 : Interval badTest_1792 0 8 :=
  interval_of_check badTest_1792 0 8 (by decide +kernel)

theorem badTest_1792_block_1 : Interval badTest_1792 8 16 :=
  interval_of_check badTest_1792 8 8 (by decide +kernel)

theorem badTest_1792_block_2 : Interval badTest_1792 16 24 :=
  interval_of_check badTest_1792 16 8 (by decide +kernel)

theorem badTest_1792_block_3 : Interval badTest_1792 24 32 :=
  interval_of_check badTest_1792 24 8 (by decide +kernel)

theorem badTest_1792_block_4 : Interval badTest_1792 32 40 :=
  interval_of_check badTest_1792 32 8 (by decide +kernel)

theorem badTest_1792_block_5 : Interval badTest_1792 40 48 :=
  interval_of_check badTest_1792 40 8 (by decide +kernel)

theorem badTest_1792_block_6 : Interval badTest_1792 48 56 :=
  interval_of_check badTest_1792 48 8 (by decide +kernel)

theorem badTest_1792_block_7 : Interval badTest_1792 56 64 :=
  interval_of_check badTest_1792 56 8 (by decide +kernel)

theorem badTest_1792_block_8 : Interval badTest_1792 64 72 :=
  interval_of_check badTest_1792 64 8 (by decide +kernel)

theorem badTest_1792_block_9 : Interval badTest_1792 72 80 :=
  interval_of_check badTest_1792 72 8 (by decide +kernel)

theorem badTest_1792_block_10 : Interval badTest_1792 80 88 :=
  interval_of_check badTest_1792 80 8 (by decide +kernel)

theorem badTest_1792_block_11 : Interval badTest_1792 88 96 :=
  interval_of_check badTest_1792 88 8 (by decide +kernel)

theorem badTest_1792_block_12 : Interval badTest_1792 96 104 :=
  interval_of_check badTest_1792 96 8 (by decide +kernel)

theorem badTest_1792_block_13 : Interval badTest_1792 104 112 :=
  interval_of_check badTest_1792 104 8 (by decide +kernel)

theorem badTest_1792_block_14 : Interval badTest_1792 112 120 :=
  interval_of_check badTest_1792 112 8 (by decide +kernel)

theorem badTest_1792_block_15 : Interval badTest_1792 120 128 :=
  interval_of_check badTest_1792 120 8 (by decide +kernel)

theorem badTest_1792_block_16 : Interval badTest_1792 128 136 :=
  interval_of_check badTest_1792 128 8 (by decide +kernel)

theorem badTest_1792_block_17 : Interval badTest_1792 136 144 :=
  interval_of_check badTest_1792 136 8 (by decide +kernel)

theorem badTest_1792_block_18 : Interval badTest_1792 144 152 :=
  interval_of_check badTest_1792 144 8 (by decide +kernel)

theorem badTest_1792_block_19 : Interval badTest_1792 152 160 :=
  interval_of_check badTest_1792 152 8 (by decide +kernel)

theorem badTest_1792_block_20 : Interval badTest_1792 160 168 :=
  interval_of_check badTest_1792 160 8 (by decide +kernel)

theorem badTest_1792_block_21 : Interval badTest_1792 168 176 :=
  interval_of_check badTest_1792 168 8 (by decide +kernel)

theorem badTest_1792_block_22 : Interval badTest_1792 176 184 :=
  interval_of_check badTest_1792 176 8 (by decide +kernel)

theorem badTest_1792_block_23 : Interval badTest_1792 184 192 :=
  interval_of_check badTest_1792 184 8 (by decide +kernel)

theorem badTest_1792_block_24 : Interval badTest_1792 192 200 :=
  interval_of_check badTest_1792 192 8 (by decide +kernel)

theorem badTest_1792_block_25 : Interval badTest_1792 200 208 :=
  interval_of_check badTest_1792 200 8 (by decide +kernel)

theorem badTest_1792_block_26 : Interval badTest_1792 208 216 :=
  interval_of_check badTest_1792 208 8 (by decide +kernel)

theorem badTest_1792_block_27 : Interval badTest_1792 216 224 :=
  interval_of_check badTest_1792 216 8 (by decide +kernel)

theorem badTest_1792_block_28 : Interval badTest_1792 224 232 :=
  interval_of_check badTest_1792 224 8 (by decide +kernel)

theorem badTest_1792_block_29 : Interval badTest_1792 232 240 :=
  interval_of_check badTest_1792 232 8 (by decide +kernel)

theorem badTest_1792_block_30 : Interval badTest_1792 240 248 :=
  interval_of_check badTest_1792 240 8 (by decide +kernel)

theorem badTest_1792_block_31 : Interval badTest_1792 248 256 :=
  interval_of_check badTest_1792 248 8 (by decide +kernel)

theorem badTest_1792_complete : Interval badTest_1792 0 256 :=
  (interval_append badTest_1792 0 128 256
  (interval_append badTest_1792 0 64 128
  (interval_append badTest_1792 0 32 64
  (interval_append badTest_1792 0 16 32
  (interval_append badTest_1792 0 8 16
  badTest_1792_block_0
  badTest_1792_block_1)
  (interval_append badTest_1792 16 24 32
  badTest_1792_block_2
  badTest_1792_block_3))
  (interval_append badTest_1792 32 48 64
  (interval_append badTest_1792 32 40 48
  badTest_1792_block_4
  badTest_1792_block_5)
  (interval_append badTest_1792 48 56 64
  badTest_1792_block_6
  badTest_1792_block_7)))
  (interval_append badTest_1792 64 96 128
  (interval_append badTest_1792 64 80 96
  (interval_append badTest_1792 64 72 80
  badTest_1792_block_8
  badTest_1792_block_9)
  (interval_append badTest_1792 80 88 96
  badTest_1792_block_10
  badTest_1792_block_11))
  (interval_append badTest_1792 96 112 128
  (interval_append badTest_1792 96 104 112
  badTest_1792_block_12
  badTest_1792_block_13)
  (interval_append badTest_1792 112 120 128
  badTest_1792_block_14
  badTest_1792_block_15))))
  (interval_append badTest_1792 128 192 256
  (interval_append badTest_1792 128 160 192
  (interval_append badTest_1792 128 144 160
  (interval_append badTest_1792 128 136 144
  badTest_1792_block_16
  badTest_1792_block_17)
  (interval_append badTest_1792 144 152 160
  badTest_1792_block_18
  badTest_1792_block_19))
  (interval_append badTest_1792 160 176 192
  (interval_append badTest_1792 160 168 176
  badTest_1792_block_20
  badTest_1792_block_21)
  (interval_append badTest_1792 176 184 192
  badTest_1792_block_22
  badTest_1792_block_23)))
  (interval_append badTest_1792 192 224 256
  (interval_append badTest_1792 192 208 224
  (interval_append badTest_1792 192 200 208
  badTest_1792_block_24
  badTest_1792_block_25)
  (interval_append badTest_1792 208 216 224
  badTest_1792_block_26
  badTest_1792_block_27))
  (interval_append badTest_1792 224 240 256
  (interval_append badTest_1792 224 232 240
  badTest_1792_block_28
  badTest_1792_block_29)
  (interval_append badTest_1792 240 248 256
  badTest_1792_block_30
  badTest_1792_block_31)))))
theorem badTestInterval1792 : Interval badTest 1792 2048 := by
  intro i hlo hhi
  have h := badTest_1792_complete (i-1792) (Nat.zero_le _) (by omega)
  simpa only [badTest_1792, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheBad008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_2048 (i : Nat) := badTest (i+2048)
theorem badTest_2048_block_0 : Interval badTest_2048 0 8 :=
  interval_of_check badTest_2048 0 8 (by decide +kernel)

theorem badTest_2048_block_1 : Interval badTest_2048 8 16 :=
  interval_of_check badTest_2048 8 8 (by decide +kernel)

theorem badTest_2048_block_2 : Interval badTest_2048 16 24 :=
  interval_of_check badTest_2048 16 8 (by decide +kernel)

theorem badTest_2048_block_3 : Interval badTest_2048 24 32 :=
  interval_of_check badTest_2048 24 8 (by decide +kernel)

theorem badTest_2048_block_4 : Interval badTest_2048 32 40 :=
  interval_of_check badTest_2048 32 8 (by decide +kernel)

theorem badTest_2048_block_5 : Interval badTest_2048 40 48 :=
  interval_of_check badTest_2048 40 8 (by decide +kernel)

theorem badTest_2048_block_6 : Interval badTest_2048 48 56 :=
  interval_of_check badTest_2048 48 8 (by decide +kernel)

theorem badTest_2048_block_7 : Interval badTest_2048 56 64 :=
  interval_of_check badTest_2048 56 8 (by decide +kernel)

theorem badTest_2048_block_8 : Interval badTest_2048 64 72 :=
  interval_of_check badTest_2048 64 8 (by decide +kernel)

theorem badTest_2048_block_9 : Interval badTest_2048 72 80 :=
  interval_of_check badTest_2048 72 8 (by decide +kernel)

theorem badTest_2048_block_10 : Interval badTest_2048 80 88 :=
  interval_of_check badTest_2048 80 8 (by decide +kernel)

theorem badTest_2048_block_11 : Interval badTest_2048 88 96 :=
  interval_of_check badTest_2048 88 8 (by decide +kernel)

theorem badTest_2048_block_12 : Interval badTest_2048 96 104 :=
  interval_of_check badTest_2048 96 8 (by decide +kernel)

theorem badTest_2048_block_13 : Interval badTest_2048 104 112 :=
  interval_of_check badTest_2048 104 8 (by decide +kernel)

theorem badTest_2048_block_14 : Interval badTest_2048 112 120 :=
  interval_of_check badTest_2048 112 8 (by decide +kernel)

theorem badTest_2048_block_15 : Interval badTest_2048 120 122 :=
  interval_of_check badTest_2048 120 2 (by decide +kernel)

theorem badTest_2048_complete : Interval badTest_2048 0 122 :=
  (interval_append badTest_2048 0 64 122
  (interval_append badTest_2048 0 32 64
  (interval_append badTest_2048 0 16 32
  (interval_append badTest_2048 0 8 16
  badTest_2048_block_0
  badTest_2048_block_1)
  (interval_append badTest_2048 16 24 32
  badTest_2048_block_2
  badTest_2048_block_3))
  (interval_append badTest_2048 32 48 64
  (interval_append badTest_2048 32 40 48
  badTest_2048_block_4
  badTest_2048_block_5)
  (interval_append badTest_2048 48 56 64
  badTest_2048_block_6
  badTest_2048_block_7)))
  (interval_append badTest_2048 64 96 122
  (interval_append badTest_2048 64 80 96
  (interval_append badTest_2048 64 72 80
  badTest_2048_block_8
  badTest_2048_block_9)
  (interval_append badTest_2048 80 88 96
  badTest_2048_block_10
  badTest_2048_block_11))
  (interval_append badTest_2048 96 112 122
  (interval_append badTest_2048 96 104 112
  badTest_2048_block_12
  badTest_2048_block_13)
  (interval_append badTest_2048 112 120 122
  badTest_2048_block_14
  badTest_2048_block_15))))
theorem badTestInterval2048 : Interval badTest 2048 2170 := by
  intro i hlo hhi
  have h := badTest_2048_complete (i-2048) (Nat.zero_le _) (by omega)
  simpa only [badTest_2048, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheRidges000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_0 (i : Nat) := ridgeTest (i+0)
theorem ridgeTest_0_block_0 : Interval ridgeTest_0 0 8 :=
  interval_of_check ridgeTest_0 0 8 (by decide +kernel)

theorem ridgeTest_0_block_1 : Interval ridgeTest_0 8 16 :=
  interval_of_check ridgeTest_0 8 8 (by decide +kernel)

theorem ridgeTest_0_block_2 : Interval ridgeTest_0 16 24 :=
  interval_of_check ridgeTest_0 16 8 (by decide +kernel)

theorem ridgeTest_0_block_3 : Interval ridgeTest_0 24 32 :=
  interval_of_check ridgeTest_0 24 8 (by decide +kernel)

theorem ridgeTest_0_block_4 : Interval ridgeTest_0 32 40 :=
  interval_of_check ridgeTest_0 32 8 (by decide +kernel)

theorem ridgeTest_0_block_5 : Interval ridgeTest_0 40 48 :=
  interval_of_check ridgeTest_0 40 8 (by decide +kernel)

theorem ridgeTest_0_block_6 : Interval ridgeTest_0 48 56 :=
  interval_of_check ridgeTest_0 48 8 (by decide +kernel)

theorem ridgeTest_0_block_7 : Interval ridgeTest_0 56 64 :=
  interval_of_check ridgeTest_0 56 8 (by decide +kernel)

theorem ridgeTest_0_block_8 : Interval ridgeTest_0 64 72 :=
  interval_of_check ridgeTest_0 64 8 (by decide +kernel)

theorem ridgeTest_0_block_9 : Interval ridgeTest_0 72 80 :=
  interval_of_check ridgeTest_0 72 8 (by decide +kernel)

theorem ridgeTest_0_block_10 : Interval ridgeTest_0 80 88 :=
  interval_of_check ridgeTest_0 80 8 (by decide +kernel)

theorem ridgeTest_0_block_11 : Interval ridgeTest_0 88 96 :=
  interval_of_check ridgeTest_0 88 8 (by decide +kernel)

theorem ridgeTest_0_block_12 : Interval ridgeTest_0 96 104 :=
  interval_of_check ridgeTest_0 96 8 (by decide +kernel)

theorem ridgeTest_0_block_13 : Interval ridgeTest_0 104 112 :=
  interval_of_check ridgeTest_0 104 8 (by decide +kernel)

theorem ridgeTest_0_block_14 : Interval ridgeTest_0 112 120 :=
  interval_of_check ridgeTest_0 112 8 (by decide +kernel)

theorem ridgeTest_0_block_15 : Interval ridgeTest_0 120 128 :=
  interval_of_check ridgeTest_0 120 8 (by decide +kernel)

theorem ridgeTest_0_complete : Interval ridgeTest_0 0 128 :=
  (interval_append ridgeTest_0 0 64 128
  (interval_append ridgeTest_0 0 32 64
  (interval_append ridgeTest_0 0 16 32
  (interval_append ridgeTest_0 0 8 16
  ridgeTest_0_block_0
  ridgeTest_0_block_1)
  (interval_append ridgeTest_0 16 24 32
  ridgeTest_0_block_2
  ridgeTest_0_block_3))
  (interval_append ridgeTest_0 32 48 64
  (interval_append ridgeTest_0 32 40 48
  ridgeTest_0_block_4
  ridgeTest_0_block_5)
  (interval_append ridgeTest_0 48 56 64
  ridgeTest_0_block_6
  ridgeTest_0_block_7)))
  (interval_append ridgeTest_0 64 96 128
  (interval_append ridgeTest_0 64 80 96
  (interval_append ridgeTest_0 64 72 80
  ridgeTest_0_block_8
  ridgeTest_0_block_9)
  (interval_append ridgeTest_0 80 88 96
  ridgeTest_0_block_10
  ridgeTest_0_block_11))
  (interval_append ridgeTest_0 96 112 128
  (interval_append ridgeTest_0 96 104 112
  ridgeTest_0_block_12
  ridgeTest_0_block_13)
  (interval_append ridgeTest_0 112 120 128
  ridgeTest_0_block_14
  ridgeTest_0_block_15))))
theorem ridgeTestInterval0 : Interval ridgeTest 0 128 := by
  intro i hlo hhi
  have h := ridgeTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheRidges001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_128 (i : Nat) := ridgeTest (i+128)
theorem ridgeTest_128_block_0 : Interval ridgeTest_128 0 8 :=
  interval_of_check ridgeTest_128 0 8 (by decide +kernel)

theorem ridgeTest_128_block_1 : Interval ridgeTest_128 8 16 :=
  interval_of_check ridgeTest_128 8 8 (by decide +kernel)

theorem ridgeTest_128_block_2 : Interval ridgeTest_128 16 24 :=
  interval_of_check ridgeTest_128 16 8 (by decide +kernel)

theorem ridgeTest_128_block_3 : Interval ridgeTest_128 24 32 :=
  interval_of_check ridgeTest_128 24 8 (by decide +kernel)

theorem ridgeTest_128_block_4 : Interval ridgeTest_128 32 40 :=
  interval_of_check ridgeTest_128 32 8 (by decide +kernel)

theorem ridgeTest_128_block_5 : Interval ridgeTest_128 40 48 :=
  interval_of_check ridgeTest_128 40 8 (by decide +kernel)

theorem ridgeTest_128_block_6 : Interval ridgeTest_128 48 56 :=
  interval_of_check ridgeTest_128 48 8 (by decide +kernel)

theorem ridgeTest_128_block_7 : Interval ridgeTest_128 56 64 :=
  interval_of_check ridgeTest_128 56 8 (by decide +kernel)

theorem ridgeTest_128_block_8 : Interval ridgeTest_128 64 72 :=
  interval_of_check ridgeTest_128 64 8 (by decide +kernel)

theorem ridgeTest_128_block_9 : Interval ridgeTest_128 72 80 :=
  interval_of_check ridgeTest_128 72 8 (by decide +kernel)

theorem ridgeTest_128_block_10 : Interval ridgeTest_128 80 88 :=
  interval_of_check ridgeTest_128 80 8 (by decide +kernel)

theorem ridgeTest_128_block_11 : Interval ridgeTest_128 88 96 :=
  interval_of_check ridgeTest_128 88 8 (by decide +kernel)

theorem ridgeTest_128_block_12 : Interval ridgeTest_128 96 104 :=
  interval_of_check ridgeTest_128 96 8 (by decide +kernel)

theorem ridgeTest_128_block_13 : Interval ridgeTest_128 104 112 :=
  interval_of_check ridgeTest_128 104 8 (by decide +kernel)

theorem ridgeTest_128_block_14 : Interval ridgeTest_128 112 120 :=
  interval_of_check ridgeTest_128 112 8 (by decide +kernel)

theorem ridgeTest_128_block_15 : Interval ridgeTest_128 120 128 :=
  interval_of_check ridgeTest_128 120 8 (by decide +kernel)

theorem ridgeTest_128_complete : Interval ridgeTest_128 0 128 :=
  (interval_append ridgeTest_128 0 64 128
  (interval_append ridgeTest_128 0 32 64
  (interval_append ridgeTest_128 0 16 32
  (interval_append ridgeTest_128 0 8 16
  ridgeTest_128_block_0
  ridgeTest_128_block_1)
  (interval_append ridgeTest_128 16 24 32
  ridgeTest_128_block_2
  ridgeTest_128_block_3))
  (interval_append ridgeTest_128 32 48 64
  (interval_append ridgeTest_128 32 40 48
  ridgeTest_128_block_4
  ridgeTest_128_block_5)
  (interval_append ridgeTest_128 48 56 64
  ridgeTest_128_block_6
  ridgeTest_128_block_7)))
  (interval_append ridgeTest_128 64 96 128
  (interval_append ridgeTest_128 64 80 96
  (interval_append ridgeTest_128 64 72 80
  ridgeTest_128_block_8
  ridgeTest_128_block_9)
  (interval_append ridgeTest_128 80 88 96
  ridgeTest_128_block_10
  ridgeTest_128_block_11))
  (interval_append ridgeTest_128 96 112 128
  (interval_append ridgeTest_128 96 104 112
  ridgeTest_128_block_12
  ridgeTest_128_block_13)
  (interval_append ridgeTest_128 112 120 128
  ridgeTest_128_block_14
  ridgeTest_128_block_15))))
theorem ridgeTestInterval128 : Interval ridgeTest 128 256 := by
  intro i hlo hhi
  have h := ridgeTest_128_complete (i-128) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheRidges002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_256 (i : Nat) := ridgeTest (i+256)
theorem ridgeTest_256_block_0 : Interval ridgeTest_256 0 8 :=
  interval_of_check ridgeTest_256 0 8 (by decide +kernel)

theorem ridgeTest_256_block_1 : Interval ridgeTest_256 8 16 :=
  interval_of_check ridgeTest_256 8 8 (by decide +kernel)

theorem ridgeTest_256_block_2 : Interval ridgeTest_256 16 24 :=
  interval_of_check ridgeTest_256 16 8 (by decide +kernel)

theorem ridgeTest_256_block_3 : Interval ridgeTest_256 24 32 :=
  interval_of_check ridgeTest_256 24 8 (by decide +kernel)

theorem ridgeTest_256_block_4 : Interval ridgeTest_256 32 40 :=
  interval_of_check ridgeTest_256 32 8 (by decide +kernel)

theorem ridgeTest_256_block_5 : Interval ridgeTest_256 40 48 :=
  interval_of_check ridgeTest_256 40 8 (by decide +kernel)

theorem ridgeTest_256_block_6 : Interval ridgeTest_256 48 56 :=
  interval_of_check ridgeTest_256 48 8 (by decide +kernel)

theorem ridgeTest_256_block_7 : Interval ridgeTest_256 56 64 :=
  interval_of_check ridgeTest_256 56 8 (by decide +kernel)

theorem ridgeTest_256_block_8 : Interval ridgeTest_256 64 72 :=
  interval_of_check ridgeTest_256 64 8 (by decide +kernel)

theorem ridgeTest_256_block_9 : Interval ridgeTest_256 72 80 :=
  interval_of_check ridgeTest_256 72 8 (by decide +kernel)

theorem ridgeTest_256_block_10 : Interval ridgeTest_256 80 88 :=
  interval_of_check ridgeTest_256 80 8 (by decide +kernel)

theorem ridgeTest_256_block_11 : Interval ridgeTest_256 88 96 :=
  interval_of_check ridgeTest_256 88 8 (by decide +kernel)

theorem ridgeTest_256_block_12 : Interval ridgeTest_256 96 104 :=
  interval_of_check ridgeTest_256 96 8 (by decide +kernel)

theorem ridgeTest_256_block_13 : Interval ridgeTest_256 104 112 :=
  interval_of_check ridgeTest_256 104 8 (by decide +kernel)

theorem ridgeTest_256_block_14 : Interval ridgeTest_256 112 120 :=
  interval_of_check ridgeTest_256 112 8 (by decide +kernel)

theorem ridgeTest_256_block_15 : Interval ridgeTest_256 120 128 :=
  interval_of_check ridgeTest_256 120 8 (by decide +kernel)

theorem ridgeTest_256_complete : Interval ridgeTest_256 0 128 :=
  (interval_append ridgeTest_256 0 64 128
  (interval_append ridgeTest_256 0 32 64
  (interval_append ridgeTest_256 0 16 32
  (interval_append ridgeTest_256 0 8 16
  ridgeTest_256_block_0
  ridgeTest_256_block_1)
  (interval_append ridgeTest_256 16 24 32
  ridgeTest_256_block_2
  ridgeTest_256_block_3))
  (interval_append ridgeTest_256 32 48 64
  (interval_append ridgeTest_256 32 40 48
  ridgeTest_256_block_4
  ridgeTest_256_block_5)
  (interval_append ridgeTest_256 48 56 64
  ridgeTest_256_block_6
  ridgeTest_256_block_7)))
  (interval_append ridgeTest_256 64 96 128
  (interval_append ridgeTest_256 64 80 96
  (interval_append ridgeTest_256 64 72 80
  ridgeTest_256_block_8
  ridgeTest_256_block_9)
  (interval_append ridgeTest_256 80 88 96
  ridgeTest_256_block_10
  ridgeTest_256_block_11))
  (interval_append ridgeTest_256 96 112 128
  (interval_append ridgeTest_256 96 104 112
  ridgeTest_256_block_12
  ridgeTest_256_block_13)
  (interval_append ridgeTest_256 112 120 128
  ridgeTest_256_block_14
  ridgeTest_256_block_15))))
theorem ridgeTestInterval256 : Interval ridgeTest 256 384 := by
  intro i hlo hhi
  have h := ridgeTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheRidges004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def ridgeTest_512 (i : Nat) := ridgeTest (i+512)
theorem ridgeTest_512_block_0 : Interval ridgeTest_512 0 8 :=
  interval_of_check ridgeTest_512 0 8 (by decide +kernel)

theorem ridgeTest_512_block_1 : Interval ridgeTest_512 8 16 :=
  interval_of_check ridgeTest_512 8 8 (by decide +kernel)

theorem ridgeTest_512_block_2 : Interval ridgeTest_512 16 24 :=
  interval_of_check ridgeTest_512 16 8 (by decide +kernel)

theorem ridgeTest_512_block_3 : Interval ridgeTest_512 24 32 :=
  interval_of_check ridgeTest_512 24 8 (by decide +kernel)

theorem ridgeTest_512_block_4 : Interval ridgeTest_512 32 40 :=
  interval_of_check ridgeTest_512 32 8 (by decide +kernel)

theorem ridgeTest_512_block_5 : Interval ridgeTest_512 40 48 :=
  interval_of_check ridgeTest_512 40 8 (by decide +kernel)

theorem ridgeTest_512_block_6 : Interval ridgeTest_512 48 56 :=
  interval_of_check ridgeTest_512 48 8 (by decide +kernel)

theorem ridgeTest_512_block_7 : Interval ridgeTest_512 56 64 :=
  interval_of_check ridgeTest_512 56 8 (by decide +kernel)

theorem ridgeTest_512_block_8 : Interval ridgeTest_512 64 72 :=
  interval_of_check ridgeTest_512 64 8 (by decide +kernel)

theorem ridgeTest_512_block_9 : Interval ridgeTest_512 72 80 :=
  interval_of_check ridgeTest_512 72 8 (by decide +kernel)

theorem ridgeTest_512_block_10 : Interval ridgeTest_512 80 88 :=
  interval_of_check ridgeTest_512 80 8 (by decide +kernel)

theorem ridgeTest_512_block_11 : Interval ridgeTest_512 88 96 :=
  interval_of_check ridgeTest_512 88 8 (by decide +kernel)

theorem ridgeTest_512_block_12 : Interval ridgeTest_512 96 104 :=
  interval_of_check ridgeTest_512 96 8 (by decide +kernel)

theorem ridgeTest_512_block_13 : Interval ridgeTest_512 104 112 :=
  interval_of_check ridgeTest_512 104 8 (by decide +kernel)

theorem ridgeTest_512_block_14 : Interval ridgeTest_512 112 120 :=
  interval_of_check ridgeTest_512 112 8 (by decide +kernel)

theorem ridgeTest_512_block_15 : Interval ridgeTest_512 120 128 :=
  interval_of_check ridgeTest_512 120 8 (by decide +kernel)

theorem ridgeTest_512_complete : Interval ridgeTest_512 0 128 :=
  (interval_append ridgeTest_512 0 64 128
  (interval_append ridgeTest_512 0 32 64
  (interval_append ridgeTest_512 0 16 32
  (interval_append ridgeTest_512 0 8 16
  ridgeTest_512_block_0
  ridgeTest_512_block_1)
  (interval_append ridgeTest_512 16 24 32
  ridgeTest_512_block_2
  ridgeTest_512_block_3))
  (interval_append ridgeTest_512 32 48 64
  (interval_append ridgeTest_512 32 40 48
  ridgeTest_512_block_4
  ridgeTest_512_block_5)
  (interval_append ridgeTest_512 48 56 64
  ridgeTest_512_block_6
  ridgeTest_512_block_7)))
  (interval_append ridgeTest_512 64 96 128
  (interval_append ridgeTest_512 64 80 96
  (interval_append ridgeTest_512 64 72 80
  ridgeTest_512_block_8
  ridgeTest_512_block_9)
  (interval_append ridgeTest_512 80 88 96
  ridgeTest_512_block_10
  ridgeTest_512_block_11))
  (interval_append ridgeTest_512 96 112 128
  (interval_append ridgeTest_512 96 104 112
  ridgeTest_512_block_12
  ridgeTest_512_block_13)
  (interval_append ridgeTest_512 112 120 128
  ridgeTest_512_block_14
  ridgeTest_512_block_15))))
theorem ridgeTestInterval512 : Interval ridgeTest 512 640 := by
  intro i hlo hhi
  have h := ridgeTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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

theorem wellFormedTest_512_block_4 : Interval wellFormedTest_512 64 80 :=
  interval_of_check wellFormedTest_512 64 16 (by decide +kernel)

theorem wellFormedTest_512_block_5 : Interval wellFormedTest_512 80 96 :=
  interval_of_check wellFormedTest_512 80 16 (by decide +kernel)

theorem wellFormedTest_512_block_6 : Interval wellFormedTest_512 96 112 :=
  interval_of_check wellFormedTest_512 96 16 (by decide +kernel)

theorem wellFormedTest_512_block_7 : Interval wellFormedTest_512 112 128 :=
  interval_of_check wellFormedTest_512 112 16 (by decide +kernel)

theorem wellFormedTest_512_block_8 : Interval wellFormedTest_512 128 144 :=
  interval_of_check wellFormedTest_512 128 16 (by decide +kernel)

theorem wellFormedTest_512_block_9 : Interval wellFormedTest_512 144 160 :=
  interval_of_check wellFormedTest_512 144 16 (by decide +kernel)

theorem wellFormedTest_512_block_10 : Interval wellFormedTest_512 160 176 :=
  interval_of_check wellFormedTest_512 160 16 (by decide +kernel)

theorem wellFormedTest_512_block_11 : Interval wellFormedTest_512 176 192 :=
  interval_of_check wellFormedTest_512 176 16 (by decide +kernel)

theorem wellFormedTest_512_block_12 : Interval wellFormedTest_512 192 208 :=
  interval_of_check wellFormedTest_512 192 16 (by decide +kernel)

theorem wellFormedTest_512_block_13 : Interval wellFormedTest_512 208 224 :=
  interval_of_check wellFormedTest_512 208 16 (by decide +kernel)

theorem wellFormedTest_512_block_14 : Interval wellFormedTest_512 224 240 :=
  interval_of_check wellFormedTest_512 224 16 (by decide +kernel)

theorem wellFormedTest_512_block_15 : Interval wellFormedTest_512 240 256 :=
  interval_of_check wellFormedTest_512 240 16 (by decide +kernel)

theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 256 :=
  (interval_append wellFormedTest_512 0 128 256
  (interval_append wellFormedTest_512 0 64 128
  (interval_append wellFormedTest_512 0 32 64
  (interval_append wellFormedTest_512 0 16 32
  wellFormedTest_512_block_0
  wellFormedTest_512_block_1)
  (interval_append wellFormedTest_512 32 48 64
  wellFormedTest_512_block_2
  wellFormedTest_512_block_3))
  (interval_append wellFormedTest_512 64 96 128
  (interval_append wellFormedTest_512 64 80 96
  wellFormedTest_512_block_4
  wellFormedTest_512_block_5)
  (interval_append wellFormedTest_512 96 112 128
  wellFormedTest_512_block_6
  wellFormedTest_512_block_7)))
  (interval_append wellFormedTest_512 128 192 256
  (interval_append wellFormedTest_512 128 160 192
  (interval_append wellFormedTest_512 128 144 160
  wellFormedTest_512_block_8
  wellFormedTest_512_block_9)
  (interval_append wellFormedTest_512 160 176 192
  wellFormedTest_512_block_10
  wellFormedTest_512_block_11))
  (interval_append wellFormedTest_512 192 224 256
  (interval_append wellFormedTest_512 192 208 224
  wellFormedTest_512_block_12
  wellFormedTest_512_block_13)
  (interval_append wellFormedTest_512 224 240 256
  wellFormedTest_512_block_14
  wellFormedTest_512_block_15))))
theorem wellFormedTestInterval512 : Interval wellFormedTest 512 768 := by
  intro i hlo hhi
  have h := wellFormedTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_768 (i : Nat) := wellFormedTest (i+768)
theorem wellFormedTest_768_block_0 : Interval wellFormedTest_768 0 16 :=
  interval_of_check wellFormedTest_768 0 16 (by decide +kernel)

theorem wellFormedTest_768_block_1 : Interval wellFormedTest_768 16 32 :=
  interval_of_check wellFormedTest_768 16 16 (by decide +kernel)

theorem wellFormedTest_768_block_2 : Interval wellFormedTest_768 32 48 :=
  interval_of_check wellFormedTest_768 32 16 (by decide +kernel)

theorem wellFormedTest_768_block_3 : Interval wellFormedTest_768 48 64 :=
  interval_of_check wellFormedTest_768 48 16 (by decide +kernel)

theorem wellFormedTest_768_block_4 : Interval wellFormedTest_768 64 80 :=
  interval_of_check wellFormedTest_768 64 16 (by decide +kernel)

theorem wellFormedTest_768_block_5 : Interval wellFormedTest_768 80 96 :=
  interval_of_check wellFormedTest_768 80 16 (by decide +kernel)

theorem wellFormedTest_768_block_6 : Interval wellFormedTest_768 96 112 :=
  interval_of_check wellFormedTest_768 96 16 (by decide +kernel)

theorem wellFormedTest_768_block_7 : Interval wellFormedTest_768 112 128 :=
  interval_of_check wellFormedTest_768 112 16 (by decide +kernel)

theorem wellFormedTest_768_block_8 : Interval wellFormedTest_768 128 144 :=
  interval_of_check wellFormedTest_768 128 16 (by decide +kernel)

theorem wellFormedTest_768_block_9 : Interval wellFormedTest_768 144 160 :=
  interval_of_check wellFormedTest_768 144 16 (by decide +kernel)

theorem wellFormedTest_768_block_10 : Interval wellFormedTest_768 160 176 :=
  interval_of_check wellFormedTest_768 160 16 (by decide +kernel)

theorem wellFormedTest_768_block_11 : Interval wellFormedTest_768 176 192 :=
  interval_of_check wellFormedTest_768 176 16 (by decide +kernel)

theorem wellFormedTest_768_block_12 : Interval wellFormedTest_768 192 208 :=
  interval_of_check wellFormedTest_768 192 16 (by decide +kernel)

theorem wellFormedTest_768_block_13 : Interval wellFormedTest_768 208 224 :=
  interval_of_check wellFormedTest_768 208 16 (by decide +kernel)

theorem wellFormedTest_768_block_14 : Interval wellFormedTest_768 224 240 :=
  interval_of_check wellFormedTest_768 224 16 (by decide +kernel)

theorem wellFormedTest_768_block_15 : Interval wellFormedTest_768 240 256 :=
  interval_of_check wellFormedTest_768 240 16 (by decide +kernel)

theorem wellFormedTest_768_complete : Interval wellFormedTest_768 0 256 :=
  (interval_append wellFormedTest_768 0 128 256
  (interval_append wellFormedTest_768 0 64 128
  (interval_append wellFormedTest_768 0 32 64
  (interval_append wellFormedTest_768 0 16 32
  wellFormedTest_768_block_0
  wellFormedTest_768_block_1)
  (interval_append wellFormedTest_768 32 48 64
  wellFormedTest_768_block_2
  wellFormedTest_768_block_3))
  (interval_append wellFormedTest_768 64 96 128
  (interval_append wellFormedTest_768 64 80 96
  wellFormedTest_768_block_4
  wellFormedTest_768_block_5)
  (interval_append wellFormedTest_768 96 112 128
  wellFormedTest_768_block_6
  wellFormedTest_768_block_7)))
  (interval_append wellFormedTest_768 128 192 256
  (interval_append wellFormedTest_768 128 160 192
  (interval_append wellFormedTest_768 128 144 160
  wellFormedTest_768_block_8
  wellFormedTest_768_block_9)
  (interval_append wellFormedTest_768 160 176 192
  wellFormedTest_768_block_10
  wellFormedTest_768_block_11))
  (interval_append wellFormedTest_768 192 224 256
  (interval_append wellFormedTest_768 192 208 224
  wellFormedTest_768_block_12
  wellFormedTest_768_block_13)
  (interval_append wellFormedTest_768 224 240 256
  wellFormedTest_768_block_14
  wellFormedTest_768_block_15))))
theorem wellFormedTestInterval768 : Interval wellFormedTest 768 1024 := by
  intro i hlo hhi
  have h := wellFormedTest_768_complete (i-768) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_1280 (i : Nat) := wellFormedTest (i+1280)
theorem wellFormedTest_1280_block_0 : Interval wellFormedTest_1280 0 16 :=
  interval_of_check wellFormedTest_1280 0 16 (by decide +kernel)

theorem wellFormedTest_1280_block_1 : Interval wellFormedTest_1280 16 32 :=
  interval_of_check wellFormedTest_1280 16 16 (by decide +kernel)

theorem wellFormedTest_1280_block_2 : Interval wellFormedTest_1280 32 48 :=
  interval_of_check wellFormedTest_1280 32 16 (by decide +kernel)

theorem wellFormedTest_1280_block_3 : Interval wellFormedTest_1280 48 64 :=
  interval_of_check wellFormedTest_1280 48 16 (by decide +kernel)

theorem wellFormedTest_1280_block_4 : Interval wellFormedTest_1280 64 80 :=
  interval_of_check wellFormedTest_1280 64 16 (by decide +kernel)

theorem wellFormedTest_1280_block_5 : Interval wellFormedTest_1280 80 96 :=
  interval_of_check wellFormedTest_1280 80 16 (by decide +kernel)

theorem wellFormedTest_1280_block_6 : Interval wellFormedTest_1280 96 112 :=
  interval_of_check wellFormedTest_1280 96 16 (by decide +kernel)

theorem wellFormedTest_1280_block_7 : Interval wellFormedTest_1280 112 128 :=
  interval_of_check wellFormedTest_1280 112 16 (by decide +kernel)

theorem wellFormedTest_1280_block_8 : Interval wellFormedTest_1280 128 144 :=
  interval_of_check wellFormedTest_1280 128 16 (by decide +kernel)

theorem wellFormedTest_1280_block_9 : Interval wellFormedTest_1280 144 160 :=
  interval_of_check wellFormedTest_1280 144 16 (by decide +kernel)

theorem wellFormedTest_1280_block_10 : Interval wellFormedTest_1280 160 176 :=
  interval_of_check wellFormedTest_1280 160 16 (by decide +kernel)

theorem wellFormedTest_1280_block_11 : Interval wellFormedTest_1280 176 192 :=
  interval_of_check wellFormedTest_1280 176 16 (by decide +kernel)

theorem wellFormedTest_1280_block_12 : Interval wellFormedTest_1280 192 208 :=
  interval_of_check wellFormedTest_1280 192 16 (by decide +kernel)

theorem wellFormedTest_1280_block_13 : Interval wellFormedTest_1280 208 224 :=
  interval_of_check wellFormedTest_1280 208 16 (by decide +kernel)

theorem wellFormedTest_1280_block_14 : Interval wellFormedTest_1280 224 240 :=
  interval_of_check wellFormedTest_1280 224 16 (by decide +kernel)

theorem wellFormedTest_1280_block_15 : Interval wellFormedTest_1280 240 256 :=
  interval_of_check wellFormedTest_1280 240 16 (by decide +kernel)

theorem wellFormedTest_1280_complete : Interval wellFormedTest_1280 0 256 :=
  (interval_append wellFormedTest_1280 0 128 256
  (interval_append wellFormedTest_1280 0 64 128
  (interval_append wellFormedTest_1280 0 32 64
  (interval_append wellFormedTest_1280 0 16 32
  wellFormedTest_1280_block_0
  wellFormedTest_1280_block_1)
  (interval_append wellFormedTest_1280 32 48 64
  wellFormedTest_1280_block_2
  wellFormedTest_1280_block_3))
  (interval_append wellFormedTest_1280 64 96 128
  (interval_append wellFormedTest_1280 64 80 96
  wellFormedTest_1280_block_4
  wellFormedTest_1280_block_5)
  (interval_append wellFormedTest_1280 96 112 128
  wellFormedTest_1280_block_6
  wellFormedTest_1280_block_7)))
  (interval_append wellFormedTest_1280 128 192 256
  (interval_append wellFormedTest_1280 128 160 192
  (interval_append wellFormedTest_1280 128 144 160
  wellFormedTest_1280_block_8
  wellFormedTest_1280_block_9)
  (interval_append wellFormedTest_1280 160 176 192
  wellFormedTest_1280_block_10
  wellFormedTest_1280_block_11))
  (interval_append wellFormedTest_1280 192 224 256
  (interval_append wellFormedTest_1280 192 208 224
  wellFormedTest_1280_block_12
  wellFormedTest_1280_block_13)
  (interval_append wellFormedTest_1280 224 240 256
  wellFormedTest_1280_block_14
  wellFormedTest_1280_block_15))))
theorem wellFormedTestInterval1280 : Interval wellFormedTest 1280 1536 := by
  intro i hlo hhi
  have h := wellFormedTest_1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_1536 (i : Nat) := wellFormedTest (i+1536)
theorem wellFormedTest_1536_block_0 : Interval wellFormedTest_1536 0 16 :=
  interval_of_check wellFormedTest_1536 0 16 (by decide +kernel)

theorem wellFormedTest_1536_block_1 : Interval wellFormedTest_1536 16 32 :=
  interval_of_check wellFormedTest_1536 16 16 (by decide +kernel)

theorem wellFormedTest_1536_block_2 : Interval wellFormedTest_1536 32 48 :=
  interval_of_check wellFormedTest_1536 32 16 (by decide +kernel)

theorem wellFormedTest_1536_block_3 : Interval wellFormedTest_1536 48 64 :=
  interval_of_check wellFormedTest_1536 48 16 (by decide +kernel)

theorem wellFormedTest_1536_block_4 : Interval wellFormedTest_1536 64 80 :=
  interval_of_check wellFormedTest_1536 64 16 (by decide +kernel)

theorem wellFormedTest_1536_block_5 : Interval wellFormedTest_1536 80 96 :=
  interval_of_check wellFormedTest_1536 80 16 (by decide +kernel)

theorem wellFormedTest_1536_block_6 : Interval wellFormedTest_1536 96 112 :=
  interval_of_check wellFormedTest_1536 96 16 (by decide +kernel)

theorem wellFormedTest_1536_block_7 : Interval wellFormedTest_1536 112 128 :=
  interval_of_check wellFormedTest_1536 112 16 (by decide +kernel)

theorem wellFormedTest_1536_block_8 : Interval wellFormedTest_1536 128 144 :=
  interval_of_check wellFormedTest_1536 128 16 (by decide +kernel)

theorem wellFormedTest_1536_block_9 : Interval wellFormedTest_1536 144 160 :=
  interval_of_check wellFormedTest_1536 144 16 (by decide +kernel)

theorem wellFormedTest_1536_block_10 : Interval wellFormedTest_1536 160 176 :=
  interval_of_check wellFormedTest_1536 160 16 (by decide +kernel)

theorem wellFormedTest_1536_block_11 : Interval wellFormedTest_1536 176 192 :=
  interval_of_check wellFormedTest_1536 176 16 (by decide +kernel)

theorem wellFormedTest_1536_block_12 : Interval wellFormedTest_1536 192 208 :=
  interval_of_check wellFormedTest_1536 192 16 (by decide +kernel)

theorem wellFormedTest_1536_block_13 : Interval wellFormedTest_1536 208 224 :=
  interval_of_check wellFormedTest_1536 208 16 (by decide +kernel)

theorem wellFormedTest_1536_block_14 : Interval wellFormedTest_1536 224 240 :=
  interval_of_check wellFormedTest_1536 224 16 (by decide +kernel)

theorem wellFormedTest_1536_block_15 : Interval wellFormedTest_1536 240 256 :=
  interval_of_check wellFormedTest_1536 240 16 (by decide +kernel)

theorem wellFormedTest_1536_complete : Interval wellFormedTest_1536 0 256 :=
  (interval_append wellFormedTest_1536 0 128 256
  (interval_append wellFormedTest_1536 0 64 128
  (interval_append wellFormedTest_1536 0 32 64
  (interval_append wellFormedTest_1536 0 16 32
  wellFormedTest_1536_block_0
  wellFormedTest_1536_block_1)
  (interval_append wellFormedTest_1536 32 48 64
  wellFormedTest_1536_block_2
  wellFormedTest_1536_block_3))
  (interval_append wellFormedTest_1536 64 96 128
  (interval_append wellFormedTest_1536 64 80 96
  wellFormedTest_1536_block_4
  wellFormedTest_1536_block_5)
  (interval_append wellFormedTest_1536 96 112 128
  wellFormedTest_1536_block_6
  wellFormedTest_1536_block_7)))
  (interval_append wellFormedTest_1536 128 192 256
  (interval_append wellFormedTest_1536 128 160 192
  (interval_append wellFormedTest_1536 128 144 160
  wellFormedTest_1536_block_8
  wellFormedTest_1536_block_9)
  (interval_append wellFormedTest_1536 160 176 192
  wellFormedTest_1536_block_10
  wellFormedTest_1536_block_11))
  (interval_append wellFormedTest_1536 192 224 256
  (interval_append wellFormedTest_1536 192 208 224
  wellFormedTest_1536_block_12
  wellFormedTest_1536_block_13)
  (interval_append wellFormedTest_1536 224 240 256
  wellFormedTest_1536_block_14
  wellFormedTest_1536_block_15))))
theorem wellFormedTestInterval1536 : Interval wellFormedTest 1536 1792 := by
  intro i hlo hhi
  have h := wellFormedTest_1536_complete (i-1536) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_1536, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_1792 (i : Nat) := wellFormedTest (i+1792)
theorem wellFormedTest_1792_block_0 : Interval wellFormedTest_1792 0 16 :=
  interval_of_check wellFormedTest_1792 0 16 (by decide +kernel)

theorem wellFormedTest_1792_block_1 : Interval wellFormedTest_1792 16 32 :=
  interval_of_check wellFormedTest_1792 16 16 (by decide +kernel)

theorem wellFormedTest_1792_block_2 : Interval wellFormedTest_1792 32 48 :=
  interval_of_check wellFormedTest_1792 32 16 (by decide +kernel)

theorem wellFormedTest_1792_block_3 : Interval wellFormedTest_1792 48 64 :=
  interval_of_check wellFormedTest_1792 48 16 (by decide +kernel)

theorem wellFormedTest_1792_block_4 : Interval wellFormedTest_1792 64 80 :=
  interval_of_check wellFormedTest_1792 64 16 (by decide +kernel)

theorem wellFormedTest_1792_block_5 : Interval wellFormedTest_1792 80 96 :=
  interval_of_check wellFormedTest_1792 80 16 (by decide +kernel)

theorem wellFormedTest_1792_block_6 : Interval wellFormedTest_1792 96 112 :=
  interval_of_check wellFormedTest_1792 96 16 (by decide +kernel)

theorem wellFormedTest_1792_block_7 : Interval wellFormedTest_1792 112 128 :=
  interval_of_check wellFormedTest_1792 112 16 (by decide +kernel)

theorem wellFormedTest_1792_block_8 : Interval wellFormedTest_1792 128 144 :=
  interval_of_check wellFormedTest_1792 128 16 (by decide +kernel)

theorem wellFormedTest_1792_block_9 : Interval wellFormedTest_1792 144 160 :=
  interval_of_check wellFormedTest_1792 144 16 (by decide +kernel)

theorem wellFormedTest_1792_block_10 : Interval wellFormedTest_1792 160 176 :=
  interval_of_check wellFormedTest_1792 160 16 (by decide +kernel)

theorem wellFormedTest_1792_block_11 : Interval wellFormedTest_1792 176 192 :=
  interval_of_check wellFormedTest_1792 176 16 (by decide +kernel)

theorem wellFormedTest_1792_block_12 : Interval wellFormedTest_1792 192 208 :=
  interval_of_check wellFormedTest_1792 192 16 (by decide +kernel)

theorem wellFormedTest_1792_block_13 : Interval wellFormedTest_1792 208 224 :=
  interval_of_check wellFormedTest_1792 208 16 (by decide +kernel)

theorem wellFormedTest_1792_block_14 : Interval wellFormedTest_1792 224 240 :=
  interval_of_check wellFormedTest_1792 224 16 (by decide +kernel)

theorem wellFormedTest_1792_block_15 : Interval wellFormedTest_1792 240 256 :=
  interval_of_check wellFormedTest_1792 240 16 (by decide +kernel)

theorem wellFormedTest_1792_complete : Interval wellFormedTest_1792 0 256 :=
  (interval_append wellFormedTest_1792 0 128 256
  (interval_append wellFormedTest_1792 0 64 128
  (interval_append wellFormedTest_1792 0 32 64
  (interval_append wellFormedTest_1792 0 16 32
  wellFormedTest_1792_block_0
  wellFormedTest_1792_block_1)
  (interval_append wellFormedTest_1792 32 48 64
  wellFormedTest_1792_block_2
  wellFormedTest_1792_block_3))
  (interval_append wellFormedTest_1792 64 96 128
  (interval_append wellFormedTest_1792 64 80 96
  wellFormedTest_1792_block_4
  wellFormedTest_1792_block_5)
  (interval_append wellFormedTest_1792 96 112 128
  wellFormedTest_1792_block_6
  wellFormedTest_1792_block_7)))
  (interval_append wellFormedTest_1792 128 192 256
  (interval_append wellFormedTest_1792 128 160 192
  (interval_append wellFormedTest_1792 128 144 160
  wellFormedTest_1792_block_8
  wellFormedTest_1792_block_9)
  (interval_append wellFormedTest_1792 160 176 192
  wellFormedTest_1792_block_10
  wellFormedTest_1792_block_11))
  (interval_append wellFormedTest_1792 192 224 256
  (interval_append wellFormedTest_1792 192 208 224
  wellFormedTest_1792_block_12
  wellFormedTest_1792_block_13)
  (interval_append wellFormedTest_1792 224 240 256
  wellFormedTest_1792_block_14
  wellFormedTest_1792_block_15))))
theorem wellFormedTestInterval1792 : Interval wellFormedTest 1792 2048 := by
  intro i hlo hhi
  have h := wellFormedTest_1792_complete (i-1792) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_1792, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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

theorem wellFormedTest_2048_block_7 : Interval wellFormedTest_2048 112 122 :=
  interval_of_check wellFormedTest_2048 112 10 (by decide +kernel)

theorem wellFormedTest_2048_complete : Interval wellFormedTest_2048 0 122 :=
  (interval_append wellFormedTest_2048 0 64 122
  (interval_append wellFormedTest_2048 0 32 64
  (interval_append wellFormedTest_2048 0 16 32
  wellFormedTest_2048_block_0
  wellFormedTest_2048_block_1)
  (interval_append wellFormedTest_2048 32 48 64
  wellFormedTest_2048_block_2
  wellFormedTest_2048_block_3))
  (interval_append wellFormedTest_2048 64 96 122
  (interval_append wellFormedTest_2048 64 80 96
  wellFormedTest_2048_block_4
  wellFormedTest_2048_block_5)
  (interval_append wellFormedTest_2048 96 112 122
  wellFormedTest_2048_block_6
  wellFormedTest_2048_block_7)))
theorem wellFormedTestInterval2048 : Interval wellFormedTest 2048 2170 := by
  intro i hlo hhi
  have h := wellFormedTest_2048_complete (i-2048) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_2048, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
