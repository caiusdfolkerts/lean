module
prelude
public import RootedSevenPure004GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure004
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

theorem cellTest_512_block_18 : Interval cellTest_512 144 147 :=
  interval_of_check cellTest_512 144 3 (by decide +kernel)

theorem cellTest_512_complete : Interval cellTest_512 0 147 :=
  (interval_append cellTest_512 0 72 147
  (interval_append cellTest_512 0 32 72
  (interval_append cellTest_512 0 16 32
  (interval_append cellTest_512 0 8 16
  cellTest_512_block_0
  cellTest_512_block_1)
  (interval_append cellTest_512 16 24 32
  cellTest_512_block_2
  cellTest_512_block_3))
  (interval_append cellTest_512 32 48 72
  (interval_append cellTest_512 32 40 48
  cellTest_512_block_4
  cellTest_512_block_5)
  (interval_append cellTest_512 48 56 72
  cellTest_512_block_6
  (interval_append cellTest_512 56 64 72
  cellTest_512_block_7
  cellTest_512_block_8))))
  (interval_append cellTest_512 72 112 147
  (interval_append cellTest_512 72 88 112
  (interval_append cellTest_512 72 80 88
  cellTest_512_block_9
  cellTest_512_block_10)
  (interval_append cellTest_512 88 96 112
  cellTest_512_block_11
  (interval_append cellTest_512 96 104 112
  cellTest_512_block_12
  cellTest_512_block_13)))
  (interval_append cellTest_512 112 128 147
  (interval_append cellTest_512 112 120 128
  cellTest_512_block_14
  cellTest_512_block_15)
  (interval_append cellTest_512 128 136 147
  cellTest_512_block_16
  (interval_append cellTest_512 136 144 147
  cellTest_512_block_17
  cellTest_512_block_18)))))
theorem cellTestInterval512 : Interval cellTest 512 659 := by
  intro i hlo hhi
  have h := cellTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [cellTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSevenPure004
