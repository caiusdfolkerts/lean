module
prelude
public import RootedSevenPure008GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure008
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def cellTest_512 (i : Nat) := cellTest (i+512)
theorem cellTest_512_block_0 : Interval cellTest_512 0 8 :=
  interval_of_check cellTest_512 0 8 (by decide +kernel)

theorem cellTest_512_block_1 : Interval cellTest_512 8 16 :=
  interval_of_check cellTest_512 8 8 (by decide +kernel)

theorem cellTest_512_block_2 : Interval cellTest_512 16 24 :=
  interval_of_check cellTest_512 16 8 (by decide +kernel)

theorem cellTest_512_block_3 : Interval cellTest_512 24 32 :=
  interval_of_check cellTest_512 24 8 (by decide +kernel)

theorem cellTest_512_block_4 : Interval cellTest_512 32 40 :=
  interval_of_check cellTest_512 32 8 (by decide +kernel)

theorem cellTest_512_block_5 : Interval cellTest_512 40 48 :=
  interval_of_check cellTest_512 40 8 (by decide +kernel)

theorem cellTest_512_block_6 : Interval cellTest_512 48 56 :=
  interval_of_check cellTest_512 48 8 (by decide +kernel)

theorem cellTest_512_block_7 : Interval cellTest_512 56 64 :=
  interval_of_check cellTest_512 56 8 (by decide +kernel)

theorem cellTest_512_block_8 : Interval cellTest_512 64 72 :=
  interval_of_check cellTest_512 64 8 (by decide +kernel)

theorem cellTest_512_block_9 : Interval cellTest_512 72 80 :=
  interval_of_check cellTest_512 72 8 (by decide +kernel)

theorem cellTest_512_block_10 : Interval cellTest_512 80 88 :=
  interval_of_check cellTest_512 80 8 (by decide +kernel)

theorem cellTest_512_block_11 : Interval cellTest_512 88 96 :=
  interval_of_check cellTest_512 88 8 (by decide +kernel)

theorem cellTest_512_block_12 : Interval cellTest_512 96 104 :=
  interval_of_check cellTest_512 96 8 (by decide +kernel)

theorem cellTest_512_block_13 : Interval cellTest_512 104 112 :=
  interval_of_check cellTest_512 104 8 (by decide +kernel)

theorem cellTest_512_block_14 : Interval cellTest_512 112 120 :=
  interval_of_check cellTest_512 112 8 (by decide +kernel)

theorem cellTest_512_block_15 : Interval cellTest_512 120 128 :=
  interval_of_check cellTest_512 120 8 (by decide +kernel)

theorem cellTest_512_block_16 : Interval cellTest_512 128 136 :=
  interval_of_check cellTest_512 128 8 (by decide +kernel)

theorem cellTest_512_block_17 : Interval cellTest_512 136 144 :=
  interval_of_check cellTest_512 136 8 (by decide +kernel)

theorem cellTest_512_block_18 : Interval cellTest_512 144 152 :=
  interval_of_check cellTest_512 144 8 (by decide +kernel)

theorem cellTest_512_block_19 : Interval cellTest_512 152 160 :=
  interval_of_check cellTest_512 152 8 (by decide +kernel)

theorem cellTest_512_block_20 : Interval cellTest_512 160 168 :=
  interval_of_check cellTest_512 160 8 (by decide +kernel)

theorem cellTest_512_block_21 : Interval cellTest_512 168 176 :=
  interval_of_check cellTest_512 168 8 (by decide +kernel)

theorem cellTest_512_block_22 : Interval cellTest_512 176 184 :=
  interval_of_check cellTest_512 176 8 (by decide +kernel)

theorem cellTest_512_block_23 : Interval cellTest_512 184 192 :=
  interval_of_check cellTest_512 184 8 (by decide +kernel)

theorem cellTest_512_block_24 : Interval cellTest_512 192 200 :=
  interval_of_check cellTest_512 192 8 (by decide +kernel)

theorem cellTest_512_block_25 : Interval cellTest_512 200 208 :=
  interval_of_check cellTest_512 200 8 (by decide +kernel)

theorem cellTest_512_block_26 : Interval cellTest_512 208 216 :=
  interval_of_check cellTest_512 208 8 (by decide +kernel)

theorem cellTest_512_block_27 : Interval cellTest_512 216 224 :=
  interval_of_check cellTest_512 216 8 (by decide +kernel)

theorem cellTest_512_block_28 : Interval cellTest_512 224 232 :=
  interval_of_check cellTest_512 224 8 (by decide +kernel)

theorem cellTest_512_block_29 : Interval cellTest_512 232 240 :=
  interval_of_check cellTest_512 232 8 (by decide +kernel)

theorem cellTest_512_block_30 : Interval cellTest_512 240 246 :=
  interval_of_check cellTest_512 240 6 (by decide +kernel)

theorem cellTest_512_complete : Interval cellTest_512 0 246 :=
  (interval_append cellTest_512 0 120 246
  (interval_append cellTest_512 0 56 120
  (interval_append cellTest_512 0 24 56
  (interval_append cellTest_512 0 8 24
  cellTest_512_block_0
  (interval_append cellTest_512 8 16 24
  cellTest_512_block_1
  cellTest_512_block_2))
  (interval_append cellTest_512 24 40 56
  (interval_append cellTest_512 24 32 40
  cellTest_512_block_3
  cellTest_512_block_4)
  (interval_append cellTest_512 40 48 56
  cellTest_512_block_5
  cellTest_512_block_6)))
  (interval_append cellTest_512 56 88 120
  (interval_append cellTest_512 56 72 88
  (interval_append cellTest_512 56 64 72
  cellTest_512_block_7
  cellTest_512_block_8)
  (interval_append cellTest_512 72 80 88
  cellTest_512_block_9
  cellTest_512_block_10))
  (interval_append cellTest_512 88 104 120
  (interval_append cellTest_512 88 96 104
  cellTest_512_block_11
  cellTest_512_block_12)
  (interval_append cellTest_512 104 112 120
  cellTest_512_block_13
  cellTest_512_block_14))))
  (interval_append cellTest_512 120 184 246
  (interval_append cellTest_512 120 152 184
  (interval_append cellTest_512 120 136 152
  (interval_append cellTest_512 120 128 136
  cellTest_512_block_15
  cellTest_512_block_16)
  (interval_append cellTest_512 136 144 152
  cellTest_512_block_17
  cellTest_512_block_18))
  (interval_append cellTest_512 152 168 184
  (interval_append cellTest_512 152 160 168
  cellTest_512_block_19
  cellTest_512_block_20)
  (interval_append cellTest_512 168 176 184
  cellTest_512_block_21
  cellTest_512_block_22)))
  (interval_append cellTest_512 184 216 246
  (interval_append cellTest_512 184 200 216
  (interval_append cellTest_512 184 192 200
  cellTest_512_block_23
  cellTest_512_block_24)
  (interval_append cellTest_512 200 208 216
  cellTest_512_block_25
  cellTest_512_block_26))
  (interval_append cellTest_512 216 232 246
  (interval_append cellTest_512 216 224 232
  cellTest_512_block_27
  cellTest_512_block_28)
  (interval_append cellTest_512 232 240 246
  cellTest_512_block_29
  cellTest_512_block_30)))))
theorem cellTestInterval512 : Interval cellTest 512 758 := by
  intro i hlo hhi
  have h := cellTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [cellTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure008
