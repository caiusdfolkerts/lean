module
prelude
public import RootedSevenMixed028GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed028
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def badTest_256 (i : Nat) := badTest (i+256)
theorem badTest_256_block_0 : Interval badTest_256 0 8 :=
  interval_of_check badTest_256 0 8 (by decide +kernel)

theorem badTest_256_block_1 : Interval badTest_256 8 16 :=
  interval_of_check badTest_256 8 8 (by decide +kernel)

theorem badTest_256_block_2 : Interval badTest_256 16 24 :=
  interval_of_check badTest_256 16 8 (by decide +kernel)

theorem badTest_256_block_3 : Interval badTest_256 24 32 :=
  interval_of_check badTest_256 24 8 (by decide +kernel)

theorem badTest_256_block_4 : Interval badTest_256 32 40 :=
  interval_of_check badTest_256 32 8 (by decide +kernel)

theorem badTest_256_block_5 : Interval badTest_256 40 48 :=
  interval_of_check badTest_256 40 8 (by decide +kernel)

theorem badTest_256_block_6 : Interval badTest_256 48 56 :=
  interval_of_check badTest_256 48 8 (by decide +kernel)

theorem badTest_256_block_7 : Interval badTest_256 56 64 :=
  interval_of_check badTest_256 56 8 (by decide +kernel)

theorem badTest_256_block_8 : Interval badTest_256 64 72 :=
  interval_of_check badTest_256 64 8 (by decide +kernel)

theorem badTest_256_block_9 : Interval badTest_256 72 80 :=
  interval_of_check badTest_256 72 8 (by decide +kernel)

theorem badTest_256_block_10 : Interval badTest_256 80 88 :=
  interval_of_check badTest_256 80 8 (by decide +kernel)

theorem badTest_256_block_11 : Interval badTest_256 88 96 :=
  interval_of_check badTest_256 88 8 (by decide +kernel)

theorem badTest_256_block_12 : Interval badTest_256 96 104 :=
  interval_of_check badTest_256 96 8 (by decide +kernel)

theorem badTest_256_block_13 : Interval badTest_256 104 112 :=
  interval_of_check badTest_256 104 8 (by decide +kernel)

theorem badTest_256_block_14 : Interval badTest_256 112 120 :=
  interval_of_check badTest_256 112 8 (by decide +kernel)

theorem badTest_256_block_15 : Interval badTest_256 120 128 :=
  interval_of_check badTest_256 120 8 (by decide +kernel)

theorem badTest_256_block_16 : Interval badTest_256 128 136 :=
  interval_of_check badTest_256 128 8 (by decide +kernel)

theorem badTest_256_block_17 : Interval badTest_256 136 144 :=
  interval_of_check badTest_256 136 8 (by decide +kernel)

theorem badTest_256_block_18 : Interval badTest_256 144 152 :=
  interval_of_check badTest_256 144 8 (by decide +kernel)

theorem badTest_256_block_19 : Interval badTest_256 152 160 :=
  interval_of_check badTest_256 152 8 (by decide +kernel)

theorem badTest_256_block_20 : Interval badTest_256 160 168 :=
  interval_of_check badTest_256 160 8 (by decide +kernel)

theorem badTest_256_block_21 : Interval badTest_256 168 176 :=
  interval_of_check badTest_256 168 8 (by decide +kernel)

theorem badTest_256_block_22 : Interval badTest_256 176 184 :=
  interval_of_check badTest_256 176 8 (by decide +kernel)

theorem badTest_256_block_23 : Interval badTest_256 184 192 :=
  interval_of_check badTest_256 184 8 (by decide +kernel)

theorem badTest_256_block_24 : Interval badTest_256 192 200 :=
  interval_of_check badTest_256 192 8 (by decide +kernel)

theorem badTest_256_block_25 : Interval badTest_256 200 208 :=
  interval_of_check badTest_256 200 8 (by decide +kernel)

theorem badTest_256_block_26 : Interval badTest_256 208 210 :=
  interval_of_check badTest_256 208 2 (by decide +kernel)

theorem badTest_256_complete : Interval badTest_256 0 210 :=
  (interval_append badTest_256 0 104 210
  (interval_append badTest_256 0 48 104
  (interval_append badTest_256 0 24 48
  (interval_append badTest_256 0 8 24
  badTest_256_block_0
  (interval_append badTest_256 8 16 24
  badTest_256_block_1
  badTest_256_block_2))
  (interval_append badTest_256 24 32 48
  badTest_256_block_3
  (interval_append badTest_256 32 40 48
  badTest_256_block_4
  badTest_256_block_5)))
  (interval_append badTest_256 48 72 104
  (interval_append badTest_256 48 56 72
  badTest_256_block_6
  (interval_append badTest_256 56 64 72
  badTest_256_block_7
  badTest_256_block_8))
  (interval_append badTest_256 72 88 104
  (interval_append badTest_256 72 80 88
  badTest_256_block_9
  badTest_256_block_10)
  (interval_append badTest_256 88 96 104
  badTest_256_block_11
  badTest_256_block_12))))
  (interval_append badTest_256 104 160 210
  (interval_append badTest_256 104 128 160
  (interval_append badTest_256 104 112 128
  badTest_256_block_13
  (interval_append badTest_256 112 120 128
  badTest_256_block_14
  badTest_256_block_15))
  (interval_append badTest_256 128 144 160
  (interval_append badTest_256 128 136 144
  badTest_256_block_16
  badTest_256_block_17)
  (interval_append badTest_256 144 152 160
  badTest_256_block_18
  badTest_256_block_19)))
  (interval_append badTest_256 160 184 210
  (interval_append badTest_256 160 168 184
  badTest_256_block_20
  (interval_append badTest_256 168 176 184
  badTest_256_block_21
  badTest_256_block_22))
  (interval_append badTest_256 184 200 210
  (interval_append badTest_256 184 192 200
  badTest_256_block_23
  badTest_256_block_24)
  (interval_append badTest_256 200 208 210
  badTest_256_block_25
  badTest_256_block_26)))))
theorem badTestInterval256 : Interval badTest 256 466 := by
  intro i hlo hhi
  have h := badTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [badTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed028
