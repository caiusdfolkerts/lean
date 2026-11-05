module
prelude
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_4096 (i : Nat) := cellTest (i+4096)
theorem cellTest_4096_block_0 : Interval cellTest_4096 0 8 :=
  interval_of_check cellTest_4096 0 8 (by decide +kernel)

theorem cellTest_4096_block_1 : Interval cellTest_4096 8 16 :=
  interval_of_check cellTest_4096 8 8 (by decide +kernel)

theorem cellTest_4096_block_2 : Interval cellTest_4096 16 24 :=
  interval_of_check cellTest_4096 16 8 (by decide +kernel)

theorem cellTest_4096_block_3 : Interval cellTest_4096 24 32 :=
  interval_of_check cellTest_4096 24 8 (by decide +kernel)

theorem cellTest_4096_block_4 : Interval cellTest_4096 32 40 :=
  interval_of_check cellTest_4096 32 8 (by decide +kernel)

theorem cellTest_4096_block_5 : Interval cellTest_4096 40 48 :=
  interval_of_check cellTest_4096 40 8 (by decide +kernel)

theorem cellTest_4096_block_6 : Interval cellTest_4096 48 56 :=
  interval_of_check cellTest_4096 48 8 (by decide +kernel)

theorem cellTest_4096_block_7 : Interval cellTest_4096 56 64 :=
  interval_of_check cellTest_4096 56 8 (by decide +kernel)

theorem cellTest_4096_block_8 : Interval cellTest_4096 64 72 :=
  interval_of_check cellTest_4096 64 8 (by decide +kernel)

theorem cellTest_4096_block_9 : Interval cellTest_4096 72 80 :=
  interval_of_check cellTest_4096 72 8 (by decide +kernel)

theorem cellTest_4096_block_10 : Interval cellTest_4096 80 88 :=
  interval_of_check cellTest_4096 80 8 (by decide +kernel)

theorem cellTest_4096_block_11 : Interval cellTest_4096 88 96 :=
  interval_of_check cellTest_4096 88 8 (by decide +kernel)

theorem cellTest_4096_block_12 : Interval cellTest_4096 96 104 :=
  interval_of_check cellTest_4096 96 8 (by decide +kernel)

theorem cellTest_4096_block_13 : Interval cellTest_4096 104 112 :=
  interval_of_check cellTest_4096 104 8 (by decide +kernel)

theorem cellTest_4096_block_14 : Interval cellTest_4096 112 120 :=
  interval_of_check cellTest_4096 112 8 (by decide +kernel)

theorem cellTest_4096_block_15 : Interval cellTest_4096 120 128 :=
  interval_of_check cellTest_4096 120 8 (by decide +kernel)

theorem cellTest_4096_block_16 : Interval cellTest_4096 128 136 :=
  interval_of_check cellTest_4096 128 8 (by decide +kernel)

theorem cellTest_4096_block_17 : Interval cellTest_4096 136 144 :=
  interval_of_check cellTest_4096 136 8 (by decide +kernel)

theorem cellTest_4096_block_18 : Interval cellTest_4096 144 152 :=
  interval_of_check cellTest_4096 144 8 (by decide +kernel)

theorem cellTest_4096_block_19 : Interval cellTest_4096 152 160 :=
  interval_of_check cellTest_4096 152 8 (by decide +kernel)

theorem cellTest_4096_block_20 : Interval cellTest_4096 160 168 :=
  interval_of_check cellTest_4096 160 8 (by decide +kernel)

theorem cellTest_4096_block_21 : Interval cellTest_4096 168 176 :=
  interval_of_check cellTest_4096 168 8 (by decide +kernel)

theorem cellTest_4096_block_22 : Interval cellTest_4096 176 184 :=
  interval_of_check cellTest_4096 176 8 (by decide +kernel)

theorem cellTest_4096_block_23 : Interval cellTest_4096 184 192 :=
  interval_of_check cellTest_4096 184 8 (by decide +kernel)

theorem cellTest_4096_block_24 : Interval cellTest_4096 192 200 :=
  interval_of_check cellTest_4096 192 8 (by decide +kernel)

theorem cellTest_4096_block_25 : Interval cellTest_4096 200 208 :=
  interval_of_check cellTest_4096 200 8 (by decide +kernel)

theorem cellTest_4096_block_26 : Interval cellTest_4096 208 216 :=
  interval_of_check cellTest_4096 208 8 (by decide +kernel)

theorem cellTest_4096_block_27 : Interval cellTest_4096 216 224 :=
  interval_of_check cellTest_4096 216 8 (by decide +kernel)

theorem cellTest_4096_block_28 : Interval cellTest_4096 224 232 :=
  interval_of_check cellTest_4096 224 8 (by decide +kernel)

theorem cellTest_4096_block_29 : Interval cellTest_4096 232 240 :=
  interval_of_check cellTest_4096 232 8 (by decide +kernel)

theorem cellTest_4096_block_30 : Interval cellTest_4096 240 248 :=
  interval_of_check cellTest_4096 240 8 (by decide +kernel)

theorem cellTest_4096_block_31 : Interval cellTest_4096 248 256 :=
  interval_of_check cellTest_4096 248 8 (by decide +kernel)

theorem cellTest_4096_complete : Interval cellTest_4096 0 256 :=
  (interval_append cellTest_4096 0 128 256
  (interval_append cellTest_4096 0 64 128
  (interval_append cellTest_4096 0 32 64
  (interval_append cellTest_4096 0 16 32
  (interval_append cellTest_4096 0 8 16
  cellTest_4096_block_0
  cellTest_4096_block_1)
  (interval_append cellTest_4096 16 24 32
  cellTest_4096_block_2
  cellTest_4096_block_3))
  (interval_append cellTest_4096 32 48 64
  (interval_append cellTest_4096 32 40 48
  cellTest_4096_block_4
  cellTest_4096_block_5)
  (interval_append cellTest_4096 48 56 64
  cellTest_4096_block_6
  cellTest_4096_block_7)))
  (interval_append cellTest_4096 64 96 128
  (interval_append cellTest_4096 64 80 96
  (interval_append cellTest_4096 64 72 80
  cellTest_4096_block_8
  cellTest_4096_block_9)
  (interval_append cellTest_4096 80 88 96
  cellTest_4096_block_10
  cellTest_4096_block_11))
  (interval_append cellTest_4096 96 112 128
  (interval_append cellTest_4096 96 104 112
  cellTest_4096_block_12
  cellTest_4096_block_13)
  (interval_append cellTest_4096 112 120 128
  cellTest_4096_block_14
  cellTest_4096_block_15))))
  (interval_append cellTest_4096 128 192 256
  (interval_append cellTest_4096 128 160 192
  (interval_append cellTest_4096 128 144 160
  (interval_append cellTest_4096 128 136 144
  cellTest_4096_block_16
  cellTest_4096_block_17)
  (interval_append cellTest_4096 144 152 160
  cellTest_4096_block_18
  cellTest_4096_block_19))
  (interval_append cellTest_4096 160 176 192
  (interval_append cellTest_4096 160 168 176
  cellTest_4096_block_20
  cellTest_4096_block_21)
  (interval_append cellTest_4096 176 184 192
  cellTest_4096_block_22
  cellTest_4096_block_23)))
  (interval_append cellTest_4096 192 224 256
  (interval_append cellTest_4096 192 208 224
  (interval_append cellTest_4096 192 200 208
  cellTest_4096_block_24
  cellTest_4096_block_25)
  (interval_append cellTest_4096 208 216 224
  cellTest_4096_block_26
  cellTest_4096_block_27))
  (interval_append cellTest_4096 224 240 256
  (interval_append cellTest_4096 224 232 240
  cellTest_4096_block_28
  cellTest_4096_block_29)
  (interval_append cellTest_4096 240 248 256
  cellTest_4096_block_30
  cellTest_4096_block_31)))))
theorem cellTestInterval4096 : Interval cellTest 4096 4352 := by
  intro i hlo hhi
  have h := cellTest_4096_complete (i-4096) (Nat.zero_le _) (by omega)
  simpa only [cellTest_4096, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase03
