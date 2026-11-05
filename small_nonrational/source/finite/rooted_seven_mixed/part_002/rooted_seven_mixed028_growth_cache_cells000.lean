module
prelude
public import RootedSevenMixed028GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed028
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_0 (i : Nat) := cellTest (i+0)
theorem cellTest_0_block_0 : Interval cellTest_0 0 8 :=
  interval_of_check cellTest_0 0 8 (by decide +kernel)

theorem cellTest_0_block_1 : Interval cellTest_0 8 16 :=
  interval_of_check cellTest_0 8 8 (by decide +kernel)

theorem cellTest_0_block_2 : Interval cellTest_0 16 24 :=
  interval_of_check cellTest_0 16 8 (by decide +kernel)

theorem cellTest_0_block_3 : Interval cellTest_0 24 32 :=
  interval_of_check cellTest_0 24 8 (by decide +kernel)

theorem cellTest_0_block_4 : Interval cellTest_0 32 40 :=
  interval_of_check cellTest_0 32 8 (by decide +kernel)

theorem cellTest_0_block_5 : Interval cellTest_0 40 48 :=
  interval_of_check cellTest_0 40 8 (by decide +kernel)

theorem cellTest_0_block_6 : Interval cellTest_0 48 56 :=
  interval_of_check cellTest_0 48 8 (by decide +kernel)

theorem cellTest_0_block_7 : Interval cellTest_0 56 64 :=
  interval_of_check cellTest_0 56 8 (by decide +kernel)

theorem cellTest_0_block_8 : Interval cellTest_0 64 72 :=
  interval_of_check cellTest_0 64 8 (by decide +kernel)

theorem cellTest_0_block_9 : Interval cellTest_0 72 80 :=
  interval_of_check cellTest_0 72 8 (by decide +kernel)

theorem cellTest_0_block_10 : Interval cellTest_0 80 88 :=
  interval_of_check cellTest_0 80 8 (by decide +kernel)

theorem cellTest_0_block_11 : Interval cellTest_0 88 96 :=
  interval_of_check cellTest_0 88 8 (by decide +kernel)

theorem cellTest_0_block_12 : Interval cellTest_0 96 104 :=
  interval_of_check cellTest_0 96 8 (by decide +kernel)

theorem cellTest_0_block_13 : Interval cellTest_0 104 112 :=
  interval_of_check cellTest_0 104 8 (by decide +kernel)

theorem cellTest_0_block_14 : Interval cellTest_0 112 120 :=
  interval_of_check cellTest_0 112 8 (by decide +kernel)

theorem cellTest_0_block_15 : Interval cellTest_0 120 128 :=
  interval_of_check cellTest_0 120 8 (by decide +kernel)

theorem cellTest_0_block_16 : Interval cellTest_0 128 136 :=
  interval_of_check cellTest_0 128 8 (by decide +kernel)

theorem cellTest_0_block_17 : Interval cellTest_0 136 144 :=
  interval_of_check cellTest_0 136 8 (by decide +kernel)

theorem cellTest_0_block_18 : Interval cellTest_0 144 152 :=
  interval_of_check cellTest_0 144 8 (by decide +kernel)

theorem cellTest_0_block_19 : Interval cellTest_0 152 160 :=
  interval_of_check cellTest_0 152 8 (by decide +kernel)

theorem cellTest_0_block_20 : Interval cellTest_0 160 168 :=
  interval_of_check cellTest_0 160 8 (by decide +kernel)

theorem cellTest_0_block_21 : Interval cellTest_0 168 176 :=
  interval_of_check cellTest_0 168 8 (by decide +kernel)

theorem cellTest_0_block_22 : Interval cellTest_0 176 184 :=
  interval_of_check cellTest_0 176 8 (by decide +kernel)

theorem cellTest_0_block_23 : Interval cellTest_0 184 192 :=
  interval_of_check cellTest_0 184 8 (by decide +kernel)

theorem cellTest_0_block_24 : Interval cellTest_0 192 200 :=
  interval_of_check cellTest_0 192 8 (by decide +kernel)

theorem cellTest_0_block_25 : Interval cellTest_0 200 208 :=
  interval_of_check cellTest_0 200 8 (by decide +kernel)

theorem cellTest_0_block_26 : Interval cellTest_0 208 216 :=
  interval_of_check cellTest_0 208 8 (by decide +kernel)

theorem cellTest_0_block_27 : Interval cellTest_0 216 224 :=
  interval_of_check cellTest_0 216 8 (by decide +kernel)

theorem cellTest_0_block_28 : Interval cellTest_0 224 232 :=
  interval_of_check cellTest_0 224 8 (by decide +kernel)

theorem cellTest_0_block_29 : Interval cellTest_0 232 240 :=
  interval_of_check cellTest_0 232 8 (by decide +kernel)

theorem cellTest_0_block_30 : Interval cellTest_0 240 248 :=
  interval_of_check cellTest_0 240 8 (by decide +kernel)

theorem cellTest_0_block_31 : Interval cellTest_0 248 256 :=
  interval_of_check cellTest_0 248 8 (by decide +kernel)

theorem cellTest_0_complete : Interval cellTest_0 0 256 :=
  (interval_append cellTest_0 0 128 256
  (interval_append cellTest_0 0 64 128
  (interval_append cellTest_0 0 32 64
  (interval_append cellTest_0 0 16 32
  (interval_append cellTest_0 0 8 16
  cellTest_0_block_0
  cellTest_0_block_1)
  (interval_append cellTest_0 16 24 32
  cellTest_0_block_2
  cellTest_0_block_3))
  (interval_append cellTest_0 32 48 64
  (interval_append cellTest_0 32 40 48
  cellTest_0_block_4
  cellTest_0_block_5)
  (interval_append cellTest_0 48 56 64
  cellTest_0_block_6
  cellTest_0_block_7)))
  (interval_append cellTest_0 64 96 128
  (interval_append cellTest_0 64 80 96
  (interval_append cellTest_0 64 72 80
  cellTest_0_block_8
  cellTest_0_block_9)
  (interval_append cellTest_0 80 88 96
  cellTest_0_block_10
  cellTest_0_block_11))
  (interval_append cellTest_0 96 112 128
  (interval_append cellTest_0 96 104 112
  cellTest_0_block_12
  cellTest_0_block_13)
  (interval_append cellTest_0 112 120 128
  cellTest_0_block_14
  cellTest_0_block_15))))
  (interval_append cellTest_0 128 192 256
  (interval_append cellTest_0 128 160 192
  (interval_append cellTest_0 128 144 160
  (interval_append cellTest_0 128 136 144
  cellTest_0_block_16
  cellTest_0_block_17)
  (interval_append cellTest_0 144 152 160
  cellTest_0_block_18
  cellTest_0_block_19))
  (interval_append cellTest_0 160 176 192
  (interval_append cellTest_0 160 168 176
  cellTest_0_block_20
  cellTest_0_block_21)
  (interval_append cellTest_0 176 184 192
  cellTest_0_block_22
  cellTest_0_block_23)))
  (interval_append cellTest_0 192 224 256
  (interval_append cellTest_0 192 208 224
  (interval_append cellTest_0 192 200 208
  cellTest_0_block_24
  cellTest_0_block_25)
  (interval_append cellTest_0 208 216 224
  cellTest_0_block_26
  cellTest_0_block_27))
  (interval_append cellTest_0 224 240 256
  (interval_append cellTest_0 224 232 240
  cellTest_0_block_28
  cellTest_0_block_29)
  (interval_append cellTest_0 240 248 256
  cellTest_0_block_30
  cellTest_0_block_31)))))
theorem cellTestInterval0 : Interval cellTest 0 256 := by
  intro i hlo hhi
  have h := cellTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [cellTest_0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenMixed028
