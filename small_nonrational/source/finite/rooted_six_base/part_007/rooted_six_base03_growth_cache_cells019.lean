module
prelude
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_4864 (i : Nat) := cellTest (i+4864)
theorem cellTest_4864_block_0 : Interval cellTest_4864 0 8 :=
  interval_of_check cellTest_4864 0 8 (by decide +kernel)

theorem cellTest_4864_block_1 : Interval cellTest_4864 8 16 :=
  interval_of_check cellTest_4864 8 8 (by decide +kernel)

theorem cellTest_4864_block_2 : Interval cellTest_4864 16 24 :=
  interval_of_check cellTest_4864 16 8 (by decide +kernel)

theorem cellTest_4864_block_3 : Interval cellTest_4864 24 32 :=
  interval_of_check cellTest_4864 24 8 (by decide +kernel)

theorem cellTest_4864_block_4 : Interval cellTest_4864 32 40 :=
  interval_of_check cellTest_4864 32 8 (by decide +kernel)

theorem cellTest_4864_block_5 : Interval cellTest_4864 40 48 :=
  interval_of_check cellTest_4864 40 8 (by decide +kernel)

theorem cellTest_4864_block_6 : Interval cellTest_4864 48 56 :=
  interval_of_check cellTest_4864 48 8 (by decide +kernel)

theorem cellTest_4864_block_7 : Interval cellTest_4864 56 64 :=
  interval_of_check cellTest_4864 56 8 (by decide +kernel)

theorem cellTest_4864_block_8 : Interval cellTest_4864 64 72 :=
  interval_of_check cellTest_4864 64 8 (by decide +kernel)

theorem cellTest_4864_block_9 : Interval cellTest_4864 72 80 :=
  interval_of_check cellTest_4864 72 8 (by decide +kernel)

theorem cellTest_4864_block_10 : Interval cellTest_4864 80 88 :=
  interval_of_check cellTest_4864 80 8 (by decide +kernel)

theorem cellTest_4864_block_11 : Interval cellTest_4864 88 96 :=
  interval_of_check cellTest_4864 88 8 (by decide +kernel)

theorem cellTest_4864_block_12 : Interval cellTest_4864 96 104 :=
  interval_of_check cellTest_4864 96 8 (by decide +kernel)

theorem cellTest_4864_block_13 : Interval cellTest_4864 104 112 :=
  interval_of_check cellTest_4864 104 8 (by decide +kernel)

theorem cellTest_4864_block_14 : Interval cellTest_4864 112 120 :=
  interval_of_check cellTest_4864 112 8 (by decide +kernel)

theorem cellTest_4864_block_15 : Interval cellTest_4864 120 128 :=
  interval_of_check cellTest_4864 120 8 (by decide +kernel)

theorem cellTest_4864_block_16 : Interval cellTest_4864 128 136 :=
  interval_of_check cellTest_4864 128 8 (by decide +kernel)

theorem cellTest_4864_block_17 : Interval cellTest_4864 136 144 :=
  interval_of_check cellTest_4864 136 8 (by decide +kernel)

theorem cellTest_4864_block_18 : Interval cellTest_4864 144 152 :=
  interval_of_check cellTest_4864 144 8 (by decide +kernel)

theorem cellTest_4864_block_19 : Interval cellTest_4864 152 160 :=
  interval_of_check cellTest_4864 152 8 (by decide +kernel)

theorem cellTest_4864_block_20 : Interval cellTest_4864 160 168 :=
  interval_of_check cellTest_4864 160 8 (by decide +kernel)

theorem cellTest_4864_block_21 : Interval cellTest_4864 168 176 :=
  interval_of_check cellTest_4864 168 8 (by decide +kernel)

theorem cellTest_4864_block_22 : Interval cellTest_4864 176 184 :=
  interval_of_check cellTest_4864 176 8 (by decide +kernel)

theorem cellTest_4864_block_23 : Interval cellTest_4864 184 192 :=
  interval_of_check cellTest_4864 184 8 (by decide +kernel)

theorem cellTest_4864_block_24 : Interval cellTest_4864 192 200 :=
  interval_of_check cellTest_4864 192 8 (by decide +kernel)

theorem cellTest_4864_block_25 : Interval cellTest_4864 200 208 :=
  interval_of_check cellTest_4864 200 8 (by decide +kernel)

theorem cellTest_4864_block_26 : Interval cellTest_4864 208 216 :=
  interval_of_check cellTest_4864 208 8 (by decide +kernel)

theorem cellTest_4864_block_27 : Interval cellTest_4864 216 224 :=
  interval_of_check cellTest_4864 216 8 (by decide +kernel)

theorem cellTest_4864_block_28 : Interval cellTest_4864 224 232 :=
  interval_of_check cellTest_4864 224 8 (by decide +kernel)

theorem cellTest_4864_block_29 : Interval cellTest_4864 232 240 :=
  interval_of_check cellTest_4864 232 8 (by decide +kernel)

theorem cellTest_4864_block_30 : Interval cellTest_4864 240 248 :=
  interval_of_check cellTest_4864 240 8 (by decide +kernel)

theorem cellTest_4864_block_31 : Interval cellTest_4864 248 256 :=
  interval_of_check cellTest_4864 248 8 (by decide +kernel)

theorem cellTest_4864_complete : Interval cellTest_4864 0 256 :=
  (interval_append cellTest_4864 0 128 256
  (interval_append cellTest_4864 0 64 128
  (interval_append cellTest_4864 0 32 64
  (interval_append cellTest_4864 0 16 32
  (interval_append cellTest_4864 0 8 16
  cellTest_4864_block_0
  cellTest_4864_block_1)
  (interval_append cellTest_4864 16 24 32
  cellTest_4864_block_2
  cellTest_4864_block_3))
  (interval_append cellTest_4864 32 48 64
  (interval_append cellTest_4864 32 40 48
  cellTest_4864_block_4
  cellTest_4864_block_5)
  (interval_append cellTest_4864 48 56 64
  cellTest_4864_block_6
  cellTest_4864_block_7)))
  (interval_append cellTest_4864 64 96 128
  (interval_append cellTest_4864 64 80 96
  (interval_append cellTest_4864 64 72 80
  cellTest_4864_block_8
  cellTest_4864_block_9)
  (interval_append cellTest_4864 80 88 96
  cellTest_4864_block_10
  cellTest_4864_block_11))
  (interval_append cellTest_4864 96 112 128
  (interval_append cellTest_4864 96 104 112
  cellTest_4864_block_12
  cellTest_4864_block_13)
  (interval_append cellTest_4864 112 120 128
  cellTest_4864_block_14
  cellTest_4864_block_15))))
  (interval_append cellTest_4864 128 192 256
  (interval_append cellTest_4864 128 160 192
  (interval_append cellTest_4864 128 144 160
  (interval_append cellTest_4864 128 136 144
  cellTest_4864_block_16
  cellTest_4864_block_17)
  (interval_append cellTest_4864 144 152 160
  cellTest_4864_block_18
  cellTest_4864_block_19))
  (interval_append cellTest_4864 160 176 192
  (interval_append cellTest_4864 160 168 176
  cellTest_4864_block_20
  cellTest_4864_block_21)
  (interval_append cellTest_4864 176 184 192
  cellTest_4864_block_22
  cellTest_4864_block_23)))
  (interval_append cellTest_4864 192 224 256
  (interval_append cellTest_4864 192 208 224
  (interval_append cellTest_4864 192 200 208
  cellTest_4864_block_24
  cellTest_4864_block_25)
  (interval_append cellTest_4864 208 216 224
  cellTest_4864_block_26
  cellTest_4864_block_27))
  (interval_append cellTest_4864 224 240 256
  (interval_append cellTest_4864 224 232 240
  cellTest_4864_block_28
  cellTest_4864_block_29)
  (interval_append cellTest_4864 240 248 256
  cellTest_4864_block_30
  cellTest_4864_block_31)))))
theorem cellTestInterval4864 : Interval cellTest 4864 5120 := by
  intro i hlo hhi
  have h := cellTest_4864_complete (i-4864) (Nat.zero_le _) (by omega)
  simpa only [cellTest_4864, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixBase03
